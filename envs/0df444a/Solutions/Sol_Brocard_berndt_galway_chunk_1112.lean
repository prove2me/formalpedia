-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1112
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:17:39.036175+00:00
-- url     : https://prove2.me/submissions/7ffade8e-5696-4aea-8d75-85436c7689f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 199820143 ≤ n < 200000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 199821393 1250 199820143 199820167
    0x7022a040608030a260105011b0501050f0435070203210901020c04140a0e1e0312100602031b030d0608010f060b090a0902130308030408031012021005 66
    0x4042040003403090222549030803000c1e80325000300d05094041800c00e035029060b108908200c100b0301d41c501d034254100340c3c40c00004451219241020106058040841c03101080b028000c60f8850041c1103d60101d03424145842c11801c50074441d110324401e040c7d0083c03401c070241503899524080c10200700f640c5400d810300029050680d007400c0b44030001c002003022104000c105028040f922000d8003610340d600007040c22b0100362201d030380400c032901d07440380300003401004140c2c0022045000d0100b02c0e20382c1c050003800d0000860419001a00590012032031308030404940542d01d44c030000704607100084900e00322010b1340d070317005002466003c040051180074444204105840020a00d14020b101c2580e030341c014640201150032000f08070700e0801c200030450442203070883d81903100c00303003e07594030703529060040c0025008480c607a614020061000800b0444c5130001c2c50055001e294107590340e003003c4403210121800b580c4807941e0885604403000260703440d00080130400c2d6440c140203664403008689 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 199822643 1250 199821393 199821463
    0x5030c040f020f0c07060f0206010b0306060703030b130f050a020408072105061501181a0708040b03280c02060a0b0f090907060e04020f0708130f09020306090109050702 74
    0x20440f01d5800100f8107600c122000540da400300c81c0b6a8a03038017408040020203e84035a02405400d884c0380080000c07c0c0175061420041c05c0c041c0c082e00d8002455518903000401e58160081d041e40d00c1d64a5a1201242000510609800445c01e03a01140f070302d440d0402868840f0000d12410f580400d912411240740310381041c01c1c02c000c580c0442503c0f40c03847c141c1440e1442603064035241d40068881428030081c0340192401c4c5098400480c12103850840d544400c2d0001c1d03000c0003080f140303600140800142103d2001c0558042c0e0000d07d10f01d21009a0007901c01ca14000d030010325105582803991780220590040f5003660800741500c1c001c030301c647c030000114900c001d4005046400521250030401006070200f040029a1030a40d13a0191010510701080241d00a04200e450b04000c03c107c0300000444580050003c00b101c40301d4803a840c2e40d95424200303059404ea00100030317035400108011135441c02400c0d4070f02500500404108605100704000d680c0c03160320090303210f112900c1c0e030003d1000d010111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 199823893 1250 199822643 199822657
    0xf0c040f060c0b07030c0215060301060f0801060311061314060c1005061f0806060a0318050102070b010e0112060903140a0203040f0501080601020d030f0615080f010605030105030c040f02 82
    0x1400c0d400035aa109001001c454001d07a00b5140e80fa002c03000302e141c0340c0c802d005d00343c45c2280310b0b03008288540d05903041a0703080901500e0180e15641e92032001407402c0b070f40001c20f8014a060000010075a2a50510701c0303070b4050000329188914400c01904800910355000d480a590703820210703040070b100701c002043c102d105171102c0f01c0b118803881c0400c652501241e004548184403d445d50040e904103d8206849856803100c03e46c0820701c0000000e60608101015041d071281510b0701046011007001804e07034813181e40b0400d480303694001481e04140b024010000380103102c0c16400e44040d42c504070619180006c0908018045c40d00e9000c96011301d80310fa00e82c1c0580b24640301a882e070b070b400131040c0079581e40c2c4107221300814640900750000d41903000364031951141c081a00501a0080e00b507204030010f1034654040721310581d072164040341e40d203080340100040a40755181d1840d40c1c01c00b040010031442c0141d000300c0401800300010300450b1408525000070110680d000714034002e040302004040c0c02490 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 199825143 1250 199823893 199823909
    0xf0106030b182a0406030b100503030a0e0d02060d05010314070f05090424020a0302040e0108010603030512071404030f0b0f070210020c0712060203190504080a0c0f0c08060916030b0f0c04 82
    0x1e40102c24000310b421441c0c01048c04051508441e65510181600d900441c0c0c62500440d111800000150038504549000702c0d200030030300740c9000c0400003200d049031002e030025034644800c040614211030042010402605922502d00c0340e00d031a01000400c00e10004100604894021580000008840f8042060601a60001e64854241001c010300035001803140108584248000240c0c800041c811201540d4040d902c040c40c1966036200f1900d1032101802d031408206880d51204c0018290350041c001951040e004010390381d5031400d01201c2d640700a44403505000e60f074401c0c005401c0d0005210940341032707200340150b22401c5030382890703041520340e6002c2d45280340049000000c11245a0044d8443c184410b5581c50f08540180200c0c222481120700400341038080200c14407103400b4462071101c691151140d00509405560341c407500600ca41d001a02c158050f2040c03254841081c002007034085643e214441c0d545180d81c031507804004004c1c115441d800c0021021a007403012880484029203944 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 199826393 1250 199825143 199825151
    0x1050f06060714011e0b060301050d030507020a03060203010e07090512100c020717010204032123160c0302011d060f03061f020c040501060516230f0106030b182a04 72
    0x10300c0224503d510240525174202d4034041c1000194a80181542e041e87d0019115882c02c201e1613500303850740c2c0e004002c2681d000c01000e000100040040c00214040c01d55440c02e2500c0b42801c103000340040072507400c054450b0f43c40c01c202c00050b03080020b120254035094a00890001030380c420a07403c0c100c0d503820403014048407544424141c803054000300116803240d04c1b440c1d003601000c1d0403c0e031400c2d0750011010000b0f005100c0d203aa020248004400786199030300e00c45240140d01400d0704501410b07614100c4008000d42420000e41d80c00034042e00e03aa41c41542e10310012148000011168440c4480000c00c0c1c007008804944652161080940307495654803200c0c1420380b031900043e58a000700c3c0607252085007004000308803944600190ba016040800d050014000c40395210f080c08031030203201a40f0140110a28500c2680800000b2407140015000141c5517045052188000030b005104100342165401d00f001b240e00001000e96140a83c180036980000450100c00c0c1094290011a44d01c2401c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 199827643 1250 199826393 199826411
    0x110906061303030c0b180a030f1701030b0f15060f07060e031204060605010c0f020607240f0f020306010903140a050604030e030105060409080301090908130b071401050f0606071401 79
    0x4403803102c0c117006800ca500c1e03c1da40c00705942912034003111050b04036080b00f00d180c0002802a0785005408100d81890400c1404c2e608030200103010903071055801c400d5000030302c01c60842a0050310b03000500030f401c05102904007004194a0720070740c00c89170500c640004600061044550203030320703100c0040d01aa50341e110850007004000c58181d9095070928500a8009015030040d601c00c0c480b05e03440281e501c0e0000541d000c1124a42082c0020745032103807074681040e682903d0421100c8486510140000c2c03180301c540e680812200d1410f8101c20032071041082c0050781e170304422003c040700d40c0a2504401c03000e0700d45615040c5003d1140040c91071040905000401d500910303400d0800d4810380c0204601d940c0c90041000340e40700071501809c0c000f4104010301078081c050b0052000c081c045c0c007080345444981500c0611000e5070717a020740060440421244104074144050900c503468080003804103082407a03141d03e0120300500020b204420001c0e41c0b40400400168252030800315500030441c50700 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 199828893 1250 199827643 199827647
    0xe0d0203030d0c260601080c0904111e0304020d0609051207050303010302040506010c03080a05180304080705011b0c050907030f240602070e1602150103050106060e09010311090606130303 82
    0x80c1d02d54103a0104803d44070013006208880941c41d0b0a480301c401810150f1034003001500c1480001d0000c20003104200f02082054484d400340203a21644038101d00e5407401c80722080c00361f8484081f01e00521503800c00130710001d07a843c021400034564010390b0000300e81141d03283c6146230200418a80c03426400200da100140900070001c1d604072030007600c023440151303a48ea0044493b5070b07881c5401004550341b64003003180415590701041d8822201c18850308084000600c40d1328640140d8800c040c6070f403000000b132205580c00700b00c5c401c0340d01c160500140031000a5449211480450041c280180b0f6036800040c5050702c40d0300440a1940b0f0b14604015650b8140b414504000701c2420780c0c045070340041c10025409100060180498505c000303511003c3d02e5400d6420088003c280860b4214840c8800443c4129406803815008501c074000000d640c500c0d0200140840701148880c920650f0202d0042000c5819912842002c0d50100c0e0141c4c07580d600c08000134040c0c0984000f10b84020000b03400441095 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 199830143 1250 199828893 199828901
    0x20c1c0f03051306090510200304030507090608060c07290405030702090f06061e0d0606050307031803051603030905031c05060303130b0a02010905011a0f0415060e0d0203030d 77
    0x1000b0f1030f0040382c845858040c103481100c403501c41d45c1d401000c94141a07208601c250080b11441d401e16400071042e01182c2c80e00d0b03103160000d4005035203581000e04104030068051017007400824a8801609541c6001d089030a81405200000780113100d44400101817004903c40007090079000002d00c0902d07040c582000c44d40c0f0340250070308a008031881d90104006c2c084000b500c5202c0c010040c10f02d450801040140d0414114003608520829002d00c5640c000f036449014a07009800c00e070fa2016140e2a100304010280c40000d03c00c1c21402c031103000e40b000469071080440f19113144820348e058480c802858200c005000b00340c0301400394040412074002d0000c149822004485003282d091016440764000c06449214480004068401d03580c0c003041002c2c3d1002c0174103074203e40c9000005050f80b4075203900b403d440306868010f074000140c0703c20390740c513103807a900703a038101c1038181d804000781200d406000c035882c07169008a82c140440016040d41079940c544000043e2a400780a42c1c5d1160b41c914001000f038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 199831393 1250 199830143 199830157
    0xf04051903030f03200c0106090219180503100c050c10020a020705090f0f04051c03150b0c0601090e010e12040e0c0c0309060a120905060a0c0e01020c1c0f0305 70
    0x1d219001100a100e04c0b030f0080c1c220454905000303484201400042c5020340e0f02c140d1446509540312500003900003002d01c00780c605996581d000e0100c01380c200400502c3d520340c41d0906850700f6034100d42846551000103203020712805400d80010b03a1040407000b503403640500300c401d16040c031441011950340140c2e03401900358559140c0032035078050741302c0c02001500002290300900c8500134600040d00b221240d0100b0740c00c50b015406a84002c0f024400161211841c0018103000c02e8503590310401100701040000001c0c45000500c5040010841c10162140010b00c0380d501e02d145c0b40ea03000800f154081d030284600402500841d48545150742100caa16040f5200302640301440c1070010303882d010218210fa66896840380134500e015414410003405401500104041142c050b046460303900061281e0201c05018500610040c900380d002141030302c502e05003441c10800080b260700120790f00000c0c8069080d004444242c09213003440085010728500d11800b030840200c121070701d0f0615401030000c1c030b01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 199832643 1250 199831393 199831397
    0xf031206051210050c0f040e01030c0b0c0613031b06060f050609060d0f110c03090f0a12020114190801081204030308060105070501290405011e03080f0405190303 71
    0x18681e8610401c0305032003100c80c20b0780c400d801c420004040a403607640180c0c0e001d1140c5c140f540c20a0a0a4103680d8244c010340c1000380326011000045c0180282422190014000c007290f070303858240c282810f07503100d90010f445e0009004010341400c041500600d40c480c00d50301500c180c030508100c00e0904201170a010700c101111300101c2c80c4042201d08182c01141c00a140c05480d4600c0c05011a0240000300b0842020701e05040d43c45280303046108104005141070041200295142c0c4072071000c0010020009034210301c90010b0000c01c00000d00007100a00d101c80e02400c1c507003682c0030700300028007840c800c440d0f12605282c41c0c03440308040e03d43c10000c1181030301e04410481d640703074030000c01615280c800c0d4000a4082101100000c1256208000600007180308500200b400040c0d4161512038040840c01c10000000740a12683d42d0b08003846454010107521000d0384500d081401c07a8031511100e03010240a400d80010300040b031080240032240141f40260602402e0f80c1104101d0307940600c85d000840c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 199833893 1250 199832643 199832651
    0x304030e09160e151c020405060406050d0b09091c110d170c070b13020402160606090e1f090813180e0d08150301110f0717030405030703080a090f0312 66
    0x3c02c03400c2c604c141440308a500c0c08040c0c030b0701c00345171201c18544002809100c207981e02000b002c561a2184000341c00100a507403a000d48034020150100252070460350141c2c007407030925013009541c40c000a980030b404000740344031f09161140e03500c0480300302d404003800341c420b48540e00c552039200f903004a0010340851201441c07211526101300c044514884c070b48000d065a0000004200e080f0b0b5003002c50005148010700051619880035201c0281111035002610301503900c0c181000300c0003190048081c50200140500190110718800d048004016812026003564a80c04c15040203a5581210b001300a41c6102845551ba41d089444800802c00590f500450070711541c070400010006400b00801c0254a99121715910079440f0030702010f0a0381001e41c03542d211121200904c9103000103120702c426031012550f1f03400720790401c0c590030300f007aa1103c0c014000400801c00492004000d075070b4030b15412b01d03010410303480c2d2088501c007800f0005000750043d480640c40400b0582c01c5140000b0a5610300400e01c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 199835143 1250 199833893 199833917
    0x204090b15180610051903050114040c2c0d0c0303020d0309050a1b170303090c0a030308010e0603010204090c080f0105011d0103020d200a110304030c0b0304030e0916 73
    0x103014902200300361007410080d001c0f030440d00c3d0503504600c3c100494a801e07030038820102410030641809460f0080425a50303001800014100c0d40180001a01175806200707044040f40024802025002c10720f07100104804040c403031419500c841207030504020000c948554107428004014007d41c030040340035202d299075054080340640074075404d45070000041c040001031340e203604031017280301c1e0b49501215200d404c000c55861001e05001219041c40d00045843e45442c4064074a00791034031840394071401002c1010000250702401140c10b41c1c410b12003140d41e603118400030070f02900a0b5001100d8175800d19001c3c0010301c0c1e100c1d182601c50340f00070110410a07660b400c010b54503403080d007042c10641891580c4880095001c0e800a060350b981d40c0300001100c4284d5010118064811425030015580001e4106242944a80f0311442ca003040707009507203494915079a070341e9000d20a2140c2800741070003200003400d05024544d035252400000e030440e0010714000c4101d64400301d10b10510000300307201801031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 199836393 1250 199835143 199835149
    0x31501030501030c063b010809060c190309120e01031a010503060d0c090c0c02030d050309030a0c03020c041d1506030c04022a061504090f0201050f04030204090b15 72
    0x740c100d80c1c01807030302c4c0425070402d04200d9039182da50f100c01205107959030704076a600b8001c094040150345400d60400d240c042d0200018410304c00500420440d900590131300211110000c00c98200301071401c111038024544000c01e40140c1017014000d0544000c500040a00e2908000303040400c103001d0341e040008880b006002e082400c1e03c822841d00241d018000a100c0d4107050b125482c08038020b201215505560f0322101d4207a588494542001803151030002045080400803c18800e41c2030800d0343c1146441c200381692402031108035003c00950110040905000784541242154041d105120214403c520074070358031000703400441c1501c60040148124004103100c40d015420080103481c2c10540c500803c000fa40001030140041d0710f11001c0744143c0d020410824418550203000340005240074030380c40c12003403003444856001c0c605201c0b41c2030015419400a0308250307824200146c49680c00740c500750f83c130f02642c0c000a4110349000d5800052242514003507100c1d940c0141003144500008041c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 199837643 1250 199836393 199836401
    0x30c12130506010b0a0306030606081c020307052e0e010507020c0103020901050d0213081e100506010c0b1506130f060e0109142b03020607050313150e03070803150103 73
    0x24015800400051007100070550041200c1d05d124900800ca40c2d4880c0c6403c400c40342254400d01055006503448006560803456008050030b0342d00146052038420340b40e880d107842c2d6045254400e01e200c4102021500d05010384401d040ca0a00001c200c10708442c400c4a000b00000c4c6c8102d009889111188187c43d0b00c240210b81c2c0e401c0041c0e441c9070038410300059010294210750640c081d101d01c0c0d030b0808540c404042003a00d0945e410841203032601c4080210b22824103401d130101490b41824282005000c0e6000410180b1065100341c2d0f24056507109055102100100b50b000c42d8002c10000b52405c0030036030300c003c0000b951400294004255523943c0159010030185403079a01141d078040c2d0030840c15404602c0d101528001401c1c05400c80441252007a424240c50750314200450005088003d16030304000850b80304042e0708101e840c5041c942c0c42c46820085650f001000c1c04503072211890210300c42d40107007802c01c4183d01260b0312086a0300c3c0040483c0c0045441c42041c00d243c038101d80c071942c401d0003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 199838893 1250 199837643 199837681
    0x6021c09211b02030705120313050402070305040308130e090307030201050f0721060302060a030204180c021b0a0b0f0301060216030305070807080909240607020a060e010212030c12 79
    0x100d00c1280b102d8110070040c00c240c100030680c3d00d03010761400000d1940385c0700c00545819005802039a9100b101401004840741b01e60803043c000e078414881d0400185d080f41c21034094a400c45a410b0300d500e0101c8020022100301e81090300c106403076070140010143d0004c041c1440c18420b400902032035440c031250341d808400445110b000143c0c0c0400c082c98880d01303c15418420b01040700d01083c172503103a8002c03901d1980686100070000390b002030b0070491235003840700c0f5044000c0e02c0c8900380650303821028020356608804460b128641d10a20580c0100d5440701d4a804c0140307400d0714101d499102d850304403c0c990304248245401340c0641960020070a00059010042d240d05031502418140c007900d68134002e4212403070031500d248082040070034a0355141906441820120f2000740044440c60001c0845030403d01c215000320000d000d110010303642d071644c1e042902c0701440c0c002900b0700341900417498000d0303c1042400d000b400100380034044001000420140307a5100e0241101d440c0c2c1e4200403101d048c005 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 199840143 1250 199838893 199838897
    0x9141c1b020108090f01020c100e011431050d0905010f090b070c121110230c0c090708010302031207030f03051f06020102030a0b01050310090906021c0921 68
    0x1003a2000543c090380140e5080500081115082c0205800309401ca07486440b00ca006a1f0022420551410315406440d891880d0a4000e020300c1d0380c0c801820480e2400035046a0021120007240c2c0310014556990a01c0390710345551508101c952418880d4a0f40240c0c2c03916400640038400c041004d500699079812022a5956038008140c40c04180c0340050300a05011504008591303c00200c11554218010080c0c1c0241041e02d14100c1240810010041c02030500044c0591169011100158040c078282c0c07420b440c0074556954030a10220354201030f00d92072607e512007490010b1059040d840401141660701c203034216541070b880f200310548240540240100011f0300c1051084015110b41c00a0f9000011403c0d148810103d0106920346800c1c0d45c1c00140042c2e502000304100c800d00343c000c1614106085c00c00528600b0b02c840e0820442d1070314024403c0c2d843d00c440c001e07000c10660f03504272680041644901303d950b54222824001902c09800b0681d5000710f40c070200441c14018000c100c1c1540715907 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 199841393 1250 199840143 199840187
    0x402040f0e0a030324030b0601020d0e010207060c050735010902060306040209150301060201200315091e01030f03020606032b020309031002090a061b021309141c 71
    0x5581c02c5000c1e01907074001c5c1224410b41e44c100c00c03030801100e8078640a140701382200700d031030701c1c000e0002031400081304501820484000e030140d00507600442c1401c10b0724818500300f000382d40c0c241444d52a020207075110064052018035141c028810400b841c3d4607400c407401ca4860509285510542a039a8000c40a58071403410000704641c2e24013030b07006002656001c2d00d1000d80720120070381d0900c00d802c268040300240c2d4441c500f0652a01c00c00d001b40b0303151000e0030740050450801e003020700580d410300c952890040d80d1303c00100e0584414030356004034000c4204921001980c50b45040d011400740b0000803005449664003140c598980840d400e00070800c0361007800240341f8514803440164400b040741c0029804104004061038605104206a00740007003400f42e0341d040e0b820180210007942c2d81c4800100300001c4050b42c141d0104507864414240c040380c40c00e41003808030189030300500807110f001308003030f440f1840c1109101c00403070a048600050416482c4910024909441441b4107604010b407030821 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 199842643 1250 199841393 199841413
    0xa0f0503071202030a0f05061918080f19030b0906011b170405032a0901061d061b0f01060b0408030405040c0516061509140a240b030402040f0e 63
    0x1602c1154500d0300050869042c0c14964a40207484100c40c41d0943d40d94020108002d4003001c20340d50180d440010b501c04004c8907014242e02100c0c1b43d0b04030001040010001100609408000242c0c6c00303034100d55041148000358000050020319000340b002d07009a42010000d20703e5801481403650b41c91061550780c0301c01c2c110350342c2d10288088009030b1491039641403101060030b441c00c100c0c0c0040310686c00450350251050101340c448413071061080c90b105111440040c003040358401c5040d60f805411074586c2040303501ca01c001413481e00a5650b4180c0700d804410082040540014032140c074580d044008001d0385803034421190b5188101e0185180b182d104200400650410b50b215528074140c0340303801410f00c0710200c4014034014140d10300703891080d160440d4032091580c2c1101a402480129420020810006264107e00c03600514401107160303511610850b000f10340f0340c1c0d00306003001c004a640c981925100c8801054006503401e0340518600005106142c1c200c0c81001c00000f00741c0014408501 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 199843893 1250 199842643 199842659
    0x606010c03030f020406050c07050a21030207030b0a1e06050d0809040209041d010b041407080907080d090e01080a05030403290c1c060f180e030a0801050a0f050307 72
    0x4400c46040302003680e102e1008007044268405403001c1c1a0a5803101e95072405000c00526052031500086e108401c1c500d01002901303080818190840182001d1a10962180c00c0590030b1110765800a09402c800104100c0340d00f07450340c4801041c0101c4035400201e4001024042d00b155028012942c1294000c07646401141f024006032551180090015152104000c081402e8449002c0c04040c0003a0f942d0104265040038080e03900ca000047e070b810440540400c1034440b01c4134001d02044140141c2c1c00100d801000140201d0001d0200350003210308561055100a0a08040384110103940741c00e0400803030400f0300403400341101c5810400035400c150850300c4800b1806d6191103050b141500b2194803900c1c0d065041980d6115900050f2120345860340100404441800c00c58000c44180c50321006000d14800707040c011050324061510b003404038031403030f612200900d1070428803d520303c0040740100d49070390f00c110030505a95080c0d0320180c420360380d0340c190614542c45028103075060b0400e40c0c05200c41d40b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 199845143 1250 199843893 199843907
    0x201111b1e040905010212070305060913080702280b040b04032d120e0d05071811030a0b010e1807080c070b240a0b070609030201021308150f0603060601 67
    0x30310201c46400c40800020704981000c0c40c02c442594000c922001c0c40840480b01d180e11100d10300302449140f502d1000502c0c0707224003c5c803030340344141c0101c200b03001d000c5146d040d201c2039a400f901c52200010300142a0000c40c9070b80c800c40003042060040492100040d60a80341250f000703204242c241800c43d40d500301840d00c080381038a103503031159112800340c0f907029840c00002c600a90107000a1103102c50002c1c04a011000000e0103807170000e41102c0090000102541102c1d860190040d20f1521059010080c1007000800e140b40000802400390100d00ea900c11200b00d242601d270f201c0224120720a10800d4107010844500040707080f80040c51140c080c2e1261580294406c20182c1340184542d9000e149010070781c1c944002024010f0001811031014440c9030201c0d804903400700d441840e20000d070906200760000208500d49440003c1d003018001d40560303402c1103e001e0000091520350545540d80c0d410f5041d03180442e40c074030340030030358882504030346c1c90050300e01a001d04401e5981800640d00c0e6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 199846393 1250 199845143 199845169
    0x6070807110a0906060314070c02040b130f0501050424090b01090b0403050c0312041505280203030a1109101b1202030405031e0a0b0901020f04120201111b 68
    0x90744407252030100c0750303142442d507000780250039000101c036420300200600312094480009000c0ca602000c0c8042150010b2040c0c15a81d41114003248140640b0003003210100900d09000d5001c0c02d10140b001d10b41480d801550582d40b0a131400c21032400501908001d409003a003c860030405055070030310403000160054000840103042003c2c58903660800c2480661050780199081e42040ca14210149401d0041d444c0c11503804804504141c00d040705d059144401c580e00340c0620000084031800c13800141c88541c131421100700c410b107591a0400019483e540100c9168904030700e4400d144060740c681d04142c0e000c0d0701e000b8000200555407007000351b55020804e41d00039903001d40d64030b9a9001030f42400040d1500070341a0f01031070b1940e14003028185001520383c0d010610810264003c0700114002646034019504440011002c1d180d001c4d01a0080c03050440d2440624000280850116210740c1224001c0e8030030780c1e030842100300c0440013580300c4080c42e10b14884040c820451062514214081e1f00340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 199847643 1250 199846393 199846403
    0x30a1e110306040c09051005031f0605030f0601062c010e0409050d091505040305030d1509090507060e04020c060f22140105010e07090303030903090801020310030b130206070807 78
    0x40d8a2800c0d0000745460b0301254121458031007201c1c1804030201500455800080d4041c0c46601d460410002a07241d50b40721041d54200b02002c101e00c100301302a900b01000412000d001c4e90080d81e14510110f407102400d014500204070102404124617024020b24080041d2200700d44541a840d50011514041141d4203160301c19280c0c3d41c440f003c107034180b0083d5440403080c1c13981c219003403401105654038034810b00d0b980203000d800e120030401308030040100c0c2c640d82d100500001d50901c0b06100a6000030303054111500040c5017561700000c12030b00040f035205584a58813900e0071881e102042005074411070400d002a50050400700b800c503031680900d16001510150050308a0040e400c1120000004000540310138003911800401c0100030b20030b0f10302421101c495203a03d032031700745c07405031068010384001000c06540320414130616204151081c090500b0b17100039580d0341001c04241040f80703c9400140d0b107184501000c50405510300c0100440d05501074034690500d03000e610340d2101a001510f091724 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 199848893 1250 199847643 199847663
    0x120c05040513140a140c010210050c130612051021080c010c0e1c0b01030b1308030109020a030c09120611040b0c031b060417030403030f05010b0702040b030a1e 70
    0x3100e0018008090550f60000c00c403054240c02e00a40c1d611250103038541d00c0e000358442150690380800c20903480150003a02244a440c3d4a051300d41c2c0744280c00a480b201c030302150000c20441d80c04040e0034005103008400b0303c002d0b11102c24060300210b032449000f4200e0f44a41880380c03140d01802002840724040e040240c180320341d924200d4203485070400c0c910006100c82d25000d80514160900c5a0642c024441d01c0144e0030081c0d42d400c0942c1030601000e45a8a150702c001600f121112403625038281e84501c40d140c50f5651240e00341c01030f40040c03d015012905008145080032b00c21025501100e042002c0c02c0340b000d0135612100014070604544020800c82000040342c40610305004019140000004594805001c6050030000c5035411a00142e03070001020300c070100d402a0401c003000d00c000c913289a901e440f603240c00e038020f020011407510360750304007000000c0384643c0001030074546000303035002e000300d002c00010540c440e094141c0041880c080c080c80f1001d10550482c008841701c0c45409150 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 199850143 1250 199848893 199848931
    0xc0907110f030a0c1703010305150c0d021b06090604050d0f02030f03090703020108090319050901030207120503090709020f0a0e0303040305100605040e0c0310151212030501120c050405 81
    0x10b42503612824007030340420483d00701041005028105035030b0000030030b02442c0c01c550560b80e40b40e403900c07000c008842c1031541c604085880d60300c0110403110742c2010924119620740c10450314030031601d00b503e0b00c80618094200042d441c007001081051003158090003410b40310781e155a042d20009404c5915004500c0140000074075201c2100085014040010080218501e0340c40010800303030000300118455003003800200300e049844941c10140c00110300300240c840d885280103c009029a40740900361040102c050200c65402c44c00a6000c0e511110036545003545604580c42030f4801c25000c1c1601c0f84041120b00295489001c280503401401001d81e80342c43d90384d86030381d49800c820496043c8402d584d074030200003500e403030311070303c0e500040c04009032281c00704c9500080e0b00c0c1d00c00e1030940100c0d1a00c69000d06094010940f4000c041e02035030317050809840c0d6500b00115115a900010b1000c246000004120301c103005180021440d8015024040b00e810328090202a01c4c5c09040d402815007000500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 199851393 1250 199850143 199850173
    0x606082b0e031516170402130b03030d1b020f0a0206090607050f030414040c0c110f06070302010504020406050405010302130207150903050a090608060a0b0c030c0f1c020c090711 78
    0x705030490380340b110324011402c184e5010940c90203100c510009000309140035410781c40001d411141d00c2a01160220460341201d11544043c102c140461941800b00203503e81428a166100c0280d00f50051421000032810b0030302030780e54401100d442885076116401210062038010010408500c002e030602c1d05005071070795041c2c0f8140b01030310300c040079420204c0c0510103c0c1200c9040e02c10030f00304403010302c620009400090040d15110740060501136004d00740c440300761108449440695005021582d9410301801c00034020709090720101d01c03690924800140929040c040c56042e0390300101480030038103111020704000e5011600444000d030000708201e00300341041c030803a41d00d14000e0715170030b80c1c0c1e4030100f200800b0002c064103d40203000d040b00034000b09845008007002960b070399221066407281c6000b002844c6009030000c02c0800c2c400d4000c1210103d8022500c007404039210605002040c2d0481c0302603854840b94158981c11400d0307500050201ca00ca2051149c50300c20180958508090700600c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 199852643 1250 199851393 199851403
    0x90a020a1205100c050d051e090c01090f03031b0501150608010e18032209060f050901091107030804060902090115090e0c090f1302030f040606082b0e03 67
    0x400c400501a1101201c2807000500a5035481e61070300310100031034031408201a0090048580d0450607aa0f0b0f0400124040040001e04503840900b00c3c88488070f18200d4451540c0380401d08440d400540b200d8800181051546c0d201020b03a40e140c2c4407100c6840c015414010386101c0c41006030340315074035407031040c2c0700c1d820004402d000751030346039100800c40d81041c1d1210340e0400c0160142d8060900e00d0000b0762000401f105442c5070f0411a000802501089a20a0900c10142d0001420135242c000001103644521000d101260b105480156280c0e0344e07034540c8130480f803004051410a00081200d0800280305001840c1e110740b2580c0002560f003000c0d0046000c1003826040442607208144000400039001040e220003401149181304191402103043c0e80350f4081d81d81e6190041d0a81002e00310716035504d020303e4100d40c600c0344046480b4503000d0741401c0c0b031150644040c1e400d180381400c0485c558501003070f01e402c0030381c0345601000d491400e09070148080340303034468800030084211425456541c1c1884 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 199853893 1250 199852643 199852649
    0x60c03220302010515030604120509010314010f06030c050307021f020409051503011a0307050d171c05010b040506120a020c10090b060603010e07030b13140f1f0509090a020a 76
    0x200000744c41c9025242c03102d10750b6100054074031940c4020101310004109080000c9804114503001d900c419095005038080d00141b0006803052140c1000031401a074402810411182e491381c0c140242610070301c003a1031500c0156800b1006803c01e0020300218440400c1240380400203820041c5020b0b074036800101107600a942409480d0001c68480c3c4a6140c2401040040c001c02c61802c000043c81400199440d651031040b05c0c00f9900c084600c8081c05095002c11241e400200b03400d0350f48800c2c801ca0007440061180c42d8040007441d040021400042420a86041c1d8030058860303464008080c5042c007000350000c2080709016000c1140d2004420144030303558820a00c18004a020803861804a041240040000d070103404d047c0010031002e690841e002e17411034401e080001e0003d0240d40411001800c0e22503000e2090708005509185203034081d0202e00c1070102015849568950070602002944024008a00d031015420144418607060034401c4c0c10614080455828503181d60100c3c0f41c90b40158 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 199855143 1250 199853893 199853897
    0x50706020706020a140307120f0905070b031006030b101b060f0b040f020a05090d1b06080411040e07051207050d0b1b12010303030e03090d06020405031608060c032203 73
    0x4c01c14524807a00070345000e00000072188011308501d44240c00034908174820000309140703615800e00c450314881f603a10a54a0b140c200003900c00703443c0c4603c005c4036140c2c000e850b410702c0034180a00c0041d46030b1107480b5034280343c100100415490241e00c2c1c0103da90420551541950803440d080b00c00001e0124441d00c402d0b09400b05001ca0f80009083c204401c4510700110402ca4900400c18109016070010803220f095030101e650380c09018042c100649001c12070042150512040400420000d8003d0703210b512503413090307080c0c44c9421468001c0c0010340b62480688600ea510683c0144690f01e40300a405400001410031522450354a0002a66803c00c440040c0e0b1004090005c0c040c1001c8a486c001100e0354226008502d0311141e40706e84580c40005101c041d0400d070f40c4010713848800a041c0110b8400010080540045040d2401d11000940c418850a403003440383c540310b50315242041c0c2440c412039405201400c000c0d65094005040c0b980010080c0303c80342d0703410000600d5440c0d0107841910b05802a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 199856393 1250 199855143 199855147
    0xf08120f0a150506030a090c0e01030f0605072f011512031713081309020d061514031f080d2109120f020f0102070b0412050301030305040b03060105070602070602 71
    0x103514450403120498103485007114640401d00c0941c032035200700d1b90003005103400000d50740f080d4141804940e4880d00001c003003001d404000001d00c01e10a007080b01c004e004034410440d030340707413150150f0f602c2e6001d0040d20001002c00004a141240200301449400c4404002203424151148850140e085036005401d00a24000b5013006065000101100a41400d88404514200f00b0407184400100b05001480105c00003080900c040000e9100030003030011200940d00c51054020520141c0300074040c8900c0c1001809400400070300c05c0c048108030075031405203c1d240d502ca00b031100e40e8404a00d41480c5950b110b5a900044c0e170781013040b86071000450b5070b4442c40800702c250b0075412112040301080e0641d40c18034400d0404150003901c003981d01d01c540d0800e00e081e941801004da0a007210701d24041c41d9948041a500240300c4801140c501c1588124284801e02180c0c0005450745d002c00c0c0000f0b80054800c1c0070a010001c0440025a04410141171950624600d0381d1204141d0303011090032213840c1c0d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 199857643 1250 199856393 199856401
    0x1504090e01020f0301090b0406050a0608090d0305060d0201080619031a060303090612091e03070c05031c0c030c05030f0c061e070509040f06090b1f0207030f08120f 72
    0x14480c03080040100030096140030703010001c01d0b4075030106000c1c010289980c0c4440780b065030380715403140004207000b40400c815542c2e0f42e68040c00f040b03012a102c0910f400b6540000d542140701b0301c80c0318483c840040c003a03c45503c0b40c0c1c004580046c0000c20703c0360007820b5448110386055020303003944015032250b400840d880d50401d150254400300680014000e51060240c0f80c03081e40d5000c1550304000400c04940100d41e1803809580c6000c420010700c842e030148071040314440550110040c40c1c2940160307512091103641e0018181e540d402424412010014803080c41181407007a026500b90500a1404002601468030345605540c40107964944280b4001074081a00b5414080d82c0c0d40418081505514031120310400100480024601c408114000405030180c0d6541d80c071091010038141401c010440e00d5490101c002c000750102613116003e101181d4060540d0680a2903040020b83d01920a440c51a03490032001025481c00325180c210a2140b010038000030040b0600c20703031301041d040c501350030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 199858893 1250 199857643 199857659
    0x12040311010605010e040f14040323090a0e0403020a0501020c03030a050f04030c11210114130c050409060b10030501031407080714180703021e030603100c09051504 72
    0x503851120510303418060200400c1c0e0300088950f03202841a2400f191041048040c0b2000305005001c0b0207000c1c550400b48424594411180314680d11013410b10640c55101b4041c01c0701038000c1e0035451358007010503407003071142c07180707000015821030f1282c0111058800c0950320703242a43c1000041420540c00403040040072030b0280540d58211000c0b41d0007076110309203510010041e01e800140545084000c24058000d0f45601c240155450040342510341754211912140d400303400204084400b8480340c20109001080c1412100031030342c0c0c00340d08000c1c6d403490308040c000646102003065500c60b5a0341506034030758484080d580600310490341c0001c2d4540c114a420f41c4252039001200d40c0691000d02c0c18010b0300c000040010554100c03a103002007c0400d640014010702c6122070501c00450805c045c00741007a0950090000ca00030809d019201e0089210848401c0c00100c501a038194411400d10ba1558990340c055554171001c2e07d00200c00030749410215408010b2828031540040c40050200207040f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 199860143 1250 199858893 199858907
    0x2040312050306210c0d0507080d02060a0b04111c0603060203040b0f070219020909100c0206012108070b06010c02100c17030106230705070f060323130c0308120403 72
    0x241400c400115041607000b50b131a030741c00a401c4590701912007007000800b481410403d11004001010444480c2c0551040003512140700351250030b4941c1c03c01481480e9407810703000d24024400c1c0489928108040e150040908004540b40d0704400b1b951520080040f43d10f40c001548120301540484016040c100807840c0c000c0c42c010800380071500450382d107040004040281003001e58049800360082d40326030807040d00340b20788013081200715032038111030089054010850701e040700e890000303a80144000004c00d980070307101c85200501c0a4410082d600008083c14007040c2c1003030701031502680c580f200d1703030115550000110f00380000c9009224000c0c00c100e03500043c0d54046070601455800d55243c50009081c4079140b151a0141e1480000d102c0002c00f44031040e5050f05400c08111480540d0301c005103d800c040034003548000030309041ca42d0001201ca1414903091080c01da031810282da6420031842074480c05d8041c11140302e0003541c80040410103e5019088100c1c54071940030f40e5003810303d009030040c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 199861393 1250 199860143 199860169
    0x41e0e07020a0c23060d0905070b04080601171c082d04020103050403140d1a040c0e0402090604050a0305030a0315081902010e030a0c030c09020f071502040312050306 73
    0x1540a4002c180c00125510314100480c0c1c03140c0900c00344140c55000341e045281d101c001040e002040880c0046200c0710302d40111050318040d40c291520943c460040e54290300c180c2c040e429103035001b04010031102c07440034540f0503024424804e984102040717000d43c914900341c030344101d00040c5c0160300703002c0e80700280034010001603481d0000002c20351186c030413404003590040000e41459510070004051601400c0740710200c000c2400c0a540d00c04a280d11a00103100d0312004001000c882c1885003100c0c03d240c8901e0f50580d400740c903809509601e4208200103544881d5003560080400d000000ea40c3c0c4491102c0d00c0918410005145c50f0b004496004003140c480d2103d07141e03150010034041000100115a6110340001521000c0e0040c4841c00103950b6808a04080e07a014400e5098950900528080e06420381e4841d04082c00035554031142d100980c081c1d0307007040103000030820a080014050b400c50703c0403004d1454015040a5580e1204042c550114000d03030f01065000007004060b14010500c40c2c16 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 199862643 1250 199861393 199861397
    0x306060210020703020a0f0203011103090a0c0501051c1509020a020708010e282d0611031b03100b13091404030c141c03020705060604090203060417041e0e07 69
    0x40c8103d54078002c2d5a08426400503100c0500010488150340b001e40040c4400301e1070a004607900e0a0507500315680f4418000251030301c8445000220f031940c0700300116011042000c4c8095901440e401e80302d00102180000b402c0050141c1c5400912248180080e004003e22138005e403031600d01d00a600c601b5103124100c250ba554218840d00f4404811410450703142c0121507a040b2004c1d045444e0a107180020950203104c10782c0c00c074003001c0c080701051a1011a9034841d80c4280186030103090003255500050341c8990780e08140c2852400800c4010002e5035000102507220b55689680c1d42880c0e5030743c0e011041516110314142e0051040900c10300820048011120026415140c00d4a004000b541603410040103140741a1a851421408001d94907450380f420064010303043c0348880160080d881628111510300500c0000f84152400c0c0c0b10310311609070003502910311603540742d580c0100030380990380d143d54038a4180004203010445007203a50240000283ca20302140c1000950f404240000b418401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 199863893 1250 199862643 199862647
    0x7050a02190f0803070201091502071104050f070507030509040f06170f150a090b0702010b130b210304091503140609070b0d180b010302040b09010605070f0c050303030403030606021002 81
    0x4000041a05640c0c0d0041c0382d041d165245c1c0c00c002ca001d40301041011301002540c400950403128141d0003005114441c840441180d405007041c482a200229510b074520005600011099030041c00100b07449407281c0307000741c0313010b80070b40014084030180010400125a100c4041c800b5030024048000720207881e0307004251900c0101d12940d5203803180c2c21401644039281000c01c0c541099078006c200c1260340038251006514180342c00900078403071881c13960b00c29907618020040341c05c20b0b03200b441004074020300151402009030307200e40552490100c034540c052208202c0001d8400a40c81500340d40b01c02000340d94500c616500700700c28803805c2d00340384142c00d80061085c0140d4440c00100702c0100c81461400c580c0303a0903689a40002040d01308803d03c00c5004100c400d41c204040d04038654141ca1080b01c4c2013014403400c00501000070024028580401c01c1041614003040c400ba48040300c00b0704c605106000c86e9161804642582c009442c100c01094890205001ca00d4052000003680c90b02000114 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 199865143 1250 199863893 199863943
    0xa08010501140d110706050403230403150c09050a03060219090e070c020406170106230607060e010b041a0a05040c090e0c0f0f040608010e100b030a09020907050a02 72
    0xc046031266200c0c10784943c0c0c0d01d070482c6900c144e41d0001d8070303592500507000f00300514281c20041d140e40c607240390a140b4502031400e2800305000500658003a00c0e0000d01402000c80303c0583c076801094003103000070a21110341d40028440e540c000e81e61000d14402c2d00090385507043d807042c0c404a444140908802d020101500b80300190a0741001035000001d4078056140c40039500100f002021186c10007407242d1011a090b8420ba08150408022103a0000440440410091385400e4028102c00350651041082000b07001080c03c54003c2c022084022000140120014000504884000b00c1010b0642000c0c880010a8a0120402c0c030084c6819a000c0c8440908540001c0820038907000325045c03010280089400c201c0c0700802d51304081d58031800320b42d43e41c607008400310983d0407502c0b400001030014800031415542c2038940c0b9020f1034a08a4266001d4100001d0041d15000100549915551100108090307034070b043c0743c24020a4282c40c0c680c0c1d00c95a0810090a0504040d402965441419540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 199866393 1250 199865143 199865177
    0x608040206072003071707090507140d0b13090b090a0302030f1b1b0a080304261504033902102001060f0801050403020c040e0c150a08010501 62
    0x20351020741d0046003840320540f02050300e0ba040000100c0340e07406110702e50300410b10300e03150114440c11044040841d01455940d42e05102561411101c0c40e00007841c5044da17999040c0140094291143c8a080200361450800c0c00300d100041e00500b541080c907141d000b40c1040c004440305054200c01c3c554060b041c00d039060313180039540e4824505070280c0791400240c188102444105588851070100c01640c0b001e0600e903444840142c40018120b11546482800240d1400000111811a02c4054503029035030b40401c42084030154800d0809818000d44041e00c000d13003255103081303104074880d8642d240d1412400607101c0007040400c0b50f00352111842d80c1c3c8070040b04000c01d021858140d0407038041107202102c01c0200c400f255851030f902940c9001c1102080c5900c81074100d4402d40e40c04090764918555600c11301030903564207440c060007507006002820200e090542250380070350303a4101100d0340804c030300340460104407121400810794880401c00700407480d40240000e004013024600104647e12158030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 199867643 1250 199866393 199866397
    0x6030d080403120212090708060f100b0f0c010f05011701020703020c0d14060c030a0b010806010e24040902040314072409030b04030e10090602100e07080a0503040306060608040206 79
    0x8090188151107100001c450810340440740300d200440358820560800801b0582da403400d5004810b01c90240d03200180d40c0030103c0b10280d105d03d40e450602e100c012300d4001a42c2a92f07200340745040e0f00031404c11941071580000d00500b880388003a03410000d0350790300d00002c907500c0f042e10220483c0540d00420038400840c1d400200002000f03000c50f1070340104c4035203181c9a0611070b071803d400f10b80c600a620822a085c00b6007006103206000400d02407000d000100e0045a04081c00c48600d4085a03040304915000c0c24a0b0903503401ca60000010090401d940c01910304007900a54410026107400140034820840180d8804100725405002030465a0505d4525004048071103034001c00e02040408821000f44942c0250000799007004500d076041c200b03800c00a040019414665025140b141c080040076446400301c40c046a10543c05400c644941d4000b0030003801440040b840144540c1c3e43c00b1500141c2804141b0301144600300442e585d0b450b41ca420380a40d08541d0058051103140410003003da1a03101c1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 199868893 1250 199867643 199867651
    0x13150c05161214132606010b0417010212011809140703020a0902090604210803070306090b030f0d0c17130806090a02060f0304030c0b0c040603060509040510050709270506030d08 78
    0x2000858a80c406814030a25400074100b00b940c3c6d200c0c5400006201e4400402802540d5541c07a09001210300e542c0001e0903480740240342e81c200009034004001e40c40d0483c2c0072089003241030001048071906070701c40e960fa07044241011149c9801c030300401c004501d001450f020003846a08025402c003004d45c0c000808a011320300c07600aa890b400380000911065040d0056901c0e54410002a102d040c680c0c80240288802d0180f1450145058002641840c00007055040044079000818007115041c40446000403641c0b002c866000f40ca60030f070f5007040102e0000d00030360303400034010f450300318641440390740b402c0d0000c3c1c4000c000750403080030b40001d6200c0408407040d54100c460b4542e542c1e101e0340703011203025040b58000f4000c231031484203100c00c008200c2e00a2044980e26601401050349890405c405200280d400900c42e50000401001501c1250041640402d181c180400c2d001d640e0400140c101c0c12054410034401903500d51710040e07400510a007600110309038024500a00705c5d00000d003014002170 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 199870143 1250 199868893 199868909
    0x2b0209040f06050a09060b060712110f06040501020c1501030b0610090806070c02030f01180b0402040b0607050c1c050d030f020d0905060108010513150c0516121413 72
    0x220025051000ca80129044681d11100400c0140740001d1988001c11504100712503150910481303007828076148080d80c1d152504440d4001040c0a400c60a4030307a11101c2c00c4c501c1143c0645024454140424000684503500401c0007507580e4140138241800c0074421a40000d4000c103078030040c0007240001c1c030300941c49402a1010302d04917020719800d440841041d844400a84508010001e000da801142500018820b0301105c1c0020500a44103013038400c041014017060101c4440341000c0307407880198a800500203080000c09802001c007240c0d49602c0306400f904c00d0b6010107412015420301c220318a40410408181004d01005580c401d030f100c00d421000c10040680724520560304400030b42c1160a0172178441410441003501e0706c9c26680703c0c0b009210303e607015442c2c0f100042450020b010f6042c030065000070b0001d0b1480d400705104004003100c28a0300200319044c071105041e00e00605039184020b0084602010200d0090002031550502c05811401ca540900103c0c80001c109000381b030540b070b021 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 199871393 1250 199870143 199870159
    0x91b03080a05090301061511060c0a020c01030b040f060b0403050f0705060a0c030e060c0a050f0d0e190504110702040c030e0628020f03010501020d03060803030103020f060d06090b2b02 81
    0x83c0082d002d841c403500111600d1600110100c0441d802c1171462400c000c03604142c403040d50307c0d003400f00d007036000300c0001c9405078010140c103105540c400e07030100f80c02003001032000480b4808602036804844080d049001c16240008081c030503c10208102503841c08401c000303180160030013010a40a00441c0c84041c18000c1844240c000c01d80103060801c01c49074060600d9803212260303890300d6a140308084050b00e01e4001c1403d0002080c0300428260711704601512074064048519083c40f035000284001003114550984004c00c0079512400b0701c924540c414992070351030303102600400048031100064241454500004240030b95030102d100c3c0d62041c1c03000c00c0c40010400e40100100249803030714140401502c001a00400816110007071811303113500fa0300f100e92407800104203074101c035002c0c02038034580c1e441440100700510b414180003032080d0010300440e04126880c0202c000742c81c043e801c038922564035070f0342c3e21040b424040c6100e1500b001c044480c0200820380f04a404e0044002a4064000c44103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 199872643 1250 199871393 199871407
    0x1602210c060d140c0913050f18250f06050a0e100c0b1f0501111f090203030c070816180522030c030207060305071d030c060a03091b03080a05 62
    0x407550103aa03103404442800c0d4890324051302200c8140d400305650520950909002da894508184036071442820744002d10700140d11b9808088011103001c0042c8542c520410b440c04146040e01c1e0144040100128602094642414044d1031181e4103600014104a000e20518007403a5001090381d1001609840e40500c00c000728900700d820501d643e80203003003400e20030140512210144050000710b144500d00c0203901c0c0c0c0f00c0004489806a90302d0305038180c2d10245040348034002040154912170818000050050700713503804281035801c8681118480e0704454820018078070705100c4c0f03010300a030410310040c9041c20112414500c40c0c02100700403201c1e9a440006031660942400c00c0c0c07070591030100580c0304011034a80209403203121103088006000f10607000468902034020640a40039a466560b0480d04190481d420050060388984d418411210001d455441e200001d211802460364080741000407030401100e0040c0a8440701c10260600781c2c10000b20300800203480e0400814a4a01e5076548 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 199873893 1250 199872643 199872667
    0x6041817120a1b0e010212070b090c0d2003070f080a1101030e1203040807020a03152313020109181d0705060906180306070518010f0e01050f0705031602210c06 70
    0x209145c003004c2d5003080001c442c010f001c200752400340720b0071845042f103c81c0c5010605020740c1003000d0100600c0311a05409400354481142100c042103800a030485062942e0346040c2441106190300c0020755130000c0422000b80100c1140448028800382420f109150b200e003140d568851032200b50200e980008408181001074a2044901d21900205210131158076420141403003203111003209100d502c1e02c2000c1c0d134007124807540e1030015452100191016a51140e120040d070496070400c0b8100050b410004c0391102e020408074044410700d12000a0500030b171741c0139000e4007000c0c1b20802d143d6800083d080001d0360b2400c08881c4244002d41e401601d41c00820f107119005603804612a9150203035800b0020b03a5580302c8058000400754030b402c00b01001c4503000660342e64079110b02d0305c000904214501e034480d50241d001019081c0588036485d11300034042d100c20b401c42d0401e4844454008051848406500d424802c101040d6050841a0007415596018030380d51101c00c0d44103402540c000c036080c00854 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 199875143 1250 199873893 199873903
    0xb0114040c0c02060306061803010507050a09120f060f020c01092316090b010c06140a1112040204050916030b01060806090108031228060501120209030606041817120a1b0e0102 77
    0x5230016000f40000e01703040310045c0a9411180d45440060328032080025504151074504000365004110001c07004a03039200c85001d00544002d0b202465000c100c2d01401c030700c1c01d218401c0748501404681180c140301d68240d41e414220000c844a081e40321040d0740c40004164a551422190300403000a070014003540141c40c0c90b40c1000002c0c01252805886800c0f042e5074001703040c4200c00d00e801c1000700b01ca40ba2880c2d1140c0c001c500b058010104032000140050800d94003443d00700d1016000c6a200d821090000520348086400441d104846c07031004114858021583d690401030403606000a58180034031a9034a024010018500000c03400201c0d8102e900c2c8043c490300000258030400b42c0101c0141a00081c012034804c0342c1c0052503c045903811010603109a500c1d20000601514864030707200c0401c8060306c1400510711502c1d6205183c0300000360091406c0900c0301c06013100b40c0d141d000d604050828240028000e55503a42070023610901780f006a8150450f107c0c85003041c0c0c0c0c5803880800100e242c2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 199876393 1250 199875143 199875187
    0x6090405010e030c0607090b0a05160302120d1d0604080307270b03101505090405041505070f270302010507030c0b07020703020f030c0d080f070b0114040c0c0206030606 74
    0xb900000442e41c00300c2d50701040903403049200d503d40b00ca203107582c5c41104800384200380488000960a002100c900c0800720741900005d070003841183c1c00078a85141c004100d5000c034038104406642c6101248101c2580c140c00e0300619007a8025106a10300383d00d400a0902c801080103042284420401490001c3d5821a11079101501e984240c0d0f03035140e2009002035403040c2d903090381410307403038000041c807424142007188800c075141c1d81c640c104804c04062001400c0c002c0e004540d1021007001c0e4944051403840340c20320a078001e0b0f48924412522400c09012807031800442100c84200c68942e0361414606400b800c00c9a9080c6803042c1c1d910030720304040351550302c4031400820000340c1c40309220101d580006e414054074000c666040450300c94004040e070b6954094110341e081007a04000002103007586018280c09040d014115140004039a24002003940c260001ea481031958502901e00d4205441400c1070101c003410040420320303107500000d5150100405540c800c03003001401195103920f0102c103480c1e07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 199877643 1250 199876393 199876421
    0x18011a1c0c030507021b0102030a0509011112070c090623031009200a080601050120060a050f130209010e1801050c120903041208180607030e040b180609040501 70
    0x4021070810010043c2a081c0c0c1c84000500c620355903d03009401401c8200e40d070090580085292944c8400203503441d82000300f41905101040401d000c10351824010124a01030f90b01c2515500c1d400c1d0b2074241c1c074442d00d50700060006803401c8020f0148044040c0840d82c000698202d0091100700c0b200017910b0b000405c00400340301400e1100e50000c01c2002d449102c980801b01141c1820a440d130424441651500d202d0310029600c141c00401c0554080c10103071100d091404814640d5a8800203041d190007170554500301d00d99500c07000c101490030702c0c0c2c11954105040d00c824046010050700016401c50041c01510780c44928000482d0b0317400d2a0b11114400d02d035070040244001e20301400d06040301d80040010a090300100c500045a00c6030100450b4150382c4240d42d0b15000c02c0e000c2c0c0307461601d80c102c1260161900c000c4140e9140c541c1d99100903003201c034801c0c1da812502a4070030041c04182c0c0c12680242d4054542c03550303544041498180c11562001050310089110b503220b040840c0034250b44e503060b1078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 199878893 1250 199877643 199877651
    0x18101a061308070519121e0c0e01140d15061203090302031903021504151b02010605040c0c080d0906020403030503090f0a12030c1808030918011a1c 65
    0x10a14500300c403902161000ba007910145640c8805004480c1000c60120031181140c0134180001c8030285032102c0460701403110194a079640070032509a40071900b8091300d0765190003074100301046001040c3ca01600904aa09060600c050041124000b1840c0300400707610000040c182c1540480c2d22400043c0070050080300400d03d1402c2c00b038164040da00003640a8014401c41c08503894107074421643c050740c554001e008202203c3c004031604a0098011580820403210100044120b0300485440840e08584041c681d8000e0340c0181c21074800c2c2c0d00680c082c038141101c441c007031604942100d180c0b60704602c41907603a2030940d0b1200000e1003000b0005000070720204000c024154850003443c4a40038040447d00c0c801c83c1c522086981b5144a08002d2448010f010700c100a28442c0d00031480354800390400c442c00c4901e411040c010365090b504458101d07400420403608524180c600d202c80507682440c0c109541d414040c0c0c500041034a5200d00018200001d03a410764032481c052210200d00100001308 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 199880143 1250 199878893 199878907
    0x30209220c17162105010207021816140904020c070902040f0512120f28081b0c03071707120e09070e090403080a11030a020a02010518101a06 62
    0x256039542a01901c2d005104009004094074600078115003603503000c0320802941c20700130401a18950810f04202d071155028881440142c0ba041051442e4060348d0725031030150303d402c1c00f0300b032143d4800100ca40d08214040648600a072041412501c070581c042da00580c2e28080500c1d01441c1070050350104082c2d41c0f00090020b00d890850040a041d5a821036030203500003040c0000f540e440b80a034800b01e8182008000d014070200244004100301440303401100c03030b0050510030908040c1019101d01002ca1901401c00c140000024039840c2d81d00d2560340f2807410308480050460f41c82c01600002440c403000c0070210302c50900604250f80c103d035400700e14a4000035003000005d010400b140441401028050003140300d243c01000d0703404404070054005800b546d01c40c0c41c02c54807040302903ca01540c95442d50f803a410402000019885000018070250b500c500340c2c0002800c44000400e041a01360350300351312041040020a14066154003824041000410300c04c0c3c1012400000d1002540414001440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 199881393 1250 199880143 199880159
    0x903050604050705150f04060c060f0e0c04050c04030b0f090a0c08030c0c1f1202090d08070510090201270e0405100e010501050120010f0c180b04030209220c 69
    0x100b426034806865000d611117080c81c12062500403c5110005250248024003003244919284c4000310b004503404500c0044480e0344000301c41d065010011190081d0144007202d0070240159030304042c80450052a19165440c5c000c0d4099000d000071000008550214007200030420001d851150407030383c0702074265901c5603110364039401001490854000c0c0e10f201411480d0515041c052262820410011001c10020458144000c5049041c4150382408244103584071540c3d00f0540383e1050058030340d24882420080c4c03600020702603504410317040092a80040c2d074401c2e41881105211484d2406107040c0f66540d1030a50016005010f580401508000510500240e0038104041c41d50042103642d81007811035003601c03003d020301408296030384c2031242c600b580340e03040c503413005011800083c218240400c0c120075202d00d803049000003411701001041001c0b2842580000b01142034460389400d180da400b00f8004400242280c3e500780d541003c0c0d031a07000b00c85007000302060f4084000c030714194681c024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 199882643 1250 199881393 199881403
    0xf05102a030c05040e07030e031801080901020c03120a0e011401062d0f030b101106090a0f0816140106091103040f060c050d0f0b1c031e090305060405 66
    0x91000011011000508980240b00b1004041c990307a45041c5410300b4082d404003803c5020306020304050340d0754001e590500b414000b42c44000d08500c0040600d428005c0014641d14024081c1c0015034810000c03403407044d10010072a10340c885068a0b0600c03a42e0380c0b030f043d40010201c030558605d45500789503c0700710b01c14125140c2410389000303840381031044002d01d0400a108003c1d2a03409403141e1150b03440d1210f94002c6200315100c2046207404240058044082041440d01107140c101080180c00503901001081c402c1c0c40e03121541100501c0314001c9500c030301205815840020740007850005828400310030740110b0700461500030340c1e51401d040411898500a040c9441407682c1c0c0c84c0790641003004540d210080740c2c0540d030003a010700301014840e01c0740001130031a900005e041c44410003200401600c6406111049020380134005694201c1c1000d02003920888403c0042403c1d418494000090300135074080058000c620117030b003580c960000c0556045415800c0540a0303c580004c10041202c0051 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 199883893 1250 199882643 199882691
    0xc0e040c0806030604080d021c0203010311030a03091a0702120f0706090305120c0c0a03060b0f060a05030a150b0c011505030a0201050a030c1202070f020109210f0510 73
    0x8003000520a4003a0486100c030007038a0b5560305811290104020858860281c01082083c0c500145002d8441d088c4007024800200d0072584990040010020310002d001455a295415800703403041154580e0003d14403819030003400080d07c142010004950700e00c00c00e0f40c9444c2d50190024590008002c942903030340c02c0052404100c4d1040d0240030400358440d0500ba4200c03035010005001021030482d2101d0176412a00c04644107205000406a056681451460056008580014031928918240141001d103110360f18028401004100c00d02075202c002ca076800340c1c100f0720000b00b1403402204e00304200c45650042003001d401046c480365009040d8424103080e500e5010b43d012042d6110301745900c600c0040c8020340440e0041c00a100058065040101020f03801e15100c031007014038440343c400301e8100e442c05407134084166140808650f04500e801e07000d0013100040001d800c07020264003150251300d05004011500c1c51400b001009420801b01642e040d50000074807240160415100300c1001e042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 199885143 1250 199883893 199883899
    0x1e060509010614010c02030a020306070807020f0106060c03110a0c0914060a050306060603090708100e1506100309030311030a02030f0a09020f010f0c14010204150306050a0302010c0201120c0e 84
    0x200200342860014460502101c3c0c2c40848580141c001600554600c2c0414109030303010302071020301a00594060210b54491303031070f640394030040b4105108024a041211141d0340896850010184080c0c2d40294115011b664145051045107021003902400d120075000d0040c1070808183d00070402c510f8641202106d8501c0c0c500f4442070790b03206020005542c01900c00c03550141c01c03900100d10b25003042001107600c544200d00300e4601940e46c1500b207240a00302c50003403070541c0e551010484480c41c2844800c02c036130400c60150310b00f07060200000c1d20007070808080105050380c942941003010301941180724141d0b410120340d600d0385004611100079500480358085500f1102d000030350b03104914451071880f250003a100882d642423000041d0f500c86004840c00c0140003e20341400d000980406914942000b18000036844505d0140b11201c08009a46020103150403d44248491740314040410200c03602468115651802400141c0d10303030fa821390501c40c10038144803500c1e8455030400100d4095020903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 199886393 1250 199885143 199885151
    0x7020c01020304030b04020d1b060e040c11070b340209070c0b040b15040f0c0305010b07030c201e03070501110a060915020705010b1906090603050c071e06 68
    0x90001241c40b48118000140031a4400c00850090306002e001d030810140320740100f401120035101ca566071904507a010000050403c91305034a0b5042074000c1c4011081c2c6400e04160381d802045209855264500030710740c003444003103060740c07502c10030071030450210511501040001c6008441c420550000300d1007640686095804114403d110f60341004030103800c1641541c80d91070f1a07540b4030400e071020304050103541d20000183c600399260f108010207200d182d0400142e1007006c100140c15074005a1081e40300032814000807001c03a8011000c17540040d07100814040340e001d00d10740d00c5002c4030041d81c41600704d0140108182131500101c1104180b0390128111a000ca9a8000446000c829015070090310b400428950000034940d4219003049403103160a168a9403a0f9106e56040b41c0250b0002c0e1801d0707448400b045030a082046a00904150003c1c54043c01420107001400440b010f125000405503940b0004000101d400207480d00a54001307100f47d81314030003854401e910302c41c0090548490b440c0c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 199887643 1250 199886393 199886413
    0x6061c0f111e0408060408070201021618050601050901020322080a0b070e06030618070905060c0d03050105060909041b0b030408030703150e1909020301020c28051c03020d11030702 79
    0xc402c0c10340f0115400e1400424540d9200d40d18201c043d04845c40c102d0561060021403841642d00c03e22650240070507510103e80700c00e00f120380700c0c243c0c0c4c0050103c1d4144602000741c50034a9901208031810075101c420a1a0304181e54407900c11208103551128105000740c510329000c01284c051140e02400300c40d920843c4540000c002c100311880700b90b620303039801034004258004e20041c0140059008074681000310180781d075800400c0c0035a0081d9008101174000070000c0d032115800d4891240134150aa0f001802c00e203800c03006c52408103001d40f02420f030701550700c0c0b14403074104d00c81011001f4000b921070443d00d90625203400080e0f41c0040d50144040f0f810540f0580a011f02201100f01b1215512503a09250f01e5442400d80412214134170f400c2c2a9803100c030018056142400200f1000800e000101025a414183c501d40c0d6407230600e801d00069080c05040f4042100058025507074040da0a08845402d803504040d00207108120960502c2d501340301d0040118000080554401c00190f0241d900b4001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 199888893 1250 199887643 199887697
    0x11010c05030103061d0d05040612050c0d020f0c0f0a060e0d02100f0b0a0b0a0305100308030a020a0302070b10030b0912030112020a030812010f0e06061c0f11 69
    0x5001920000042080c001080404c0150308602d46117880080d032800b0800704892080e05041001e0200c03400b141e80024208189684903107080c0301c0000b0340c1c50400c11030034107500c40e11151003042d00701c42586d9008509032105541c01d10440b070301880800d0869150000c4031920030f4070340340714400555296107059034107003024801144003550380c903c0d5400f17400340c140c8030702c911001003100301c6103001416692402100c0903261107070244090400060f582da111101caa20090a5a000900028020600003020000161454180c4e40c00c140f24400140e25128510700c1113009028621010740001c0348882482031048681c110f20b801d40707000d405070b01c20035a16140d00c6030381c0d00300b0703400403005a0408000411070300c11560a100502e91004000d0300c070392070b542d454050694000d04546030032902c000004020384402d10041500034803180307029808038504200000c0c0c1500405d05502100100344042c80c5600c00b084d0321040050408007010841c3e60014010151543c00a1180406030341c00c500720342158003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 199890143 1250 199888893 199888901
    0x102130603060f150806091005060f0c01060f030807121403010b0706050c1620120d0305061f030207060906020a030b0103110702030705010c0c0f170d09030308151c0807031101 77
    0x4804c030340340c0d1406900c40000b48450514000c154a1510074580e6000c1134a40d5031400804030030303031422102a142d004141c003035404c64407a9880300c034035144811810000203041000751040250001d4401501d41d141200944210400361081010404c001002140c0921500b0280c66150b00a04c020000c0d03503140740c0c41c82c80900c200b46900e0605a440201c507400a0025a9401c2c0d41101454680e00343e083e4100c003050344618480440300654000300810141554503104582d400a422501c00c0380110a000222200740c4201c62007a0400d60000b6440b02130101c941c01001909134041421035982000c01001002800e250086034002403c0c00301143c18898854181c1e0090b9070018040c0409a240c8401501c1d03a01c171891048404040408000603842d40d4440e00e20b00800084003901c030025011000c890a00311507001e18000d001c0741010a1020a82c001c0d802a8050400c8030650b5800c041040054900410540c204894007030b41a20001042409805021900d119442d111490002c940720682a2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 199891393 1250 199890143 199890179
    0xd020406031a04110d0c0908060a050702150c0715090c2c010807140d0c06020c0f0301050702070501080a061a070c0510140904021204050c10030212010b0c0102130603060f 75
    0x4000d1112200302c043c42d0341b01d09690403150074803140281c0d50b2034000742820412902c21309500d6450f81003084060301404129031900c102c3d41a101145071031700d0307803200c0c41c0107001015140400d0380c100c445034a2aa603001012840d008280340d980183d8860403201035200211718100307042140120b0003081c15103d00118140d42d0990b01600d54141002c0581340c070b44202082407544080455200404601c0480480c4098400da602810001416a060210880f030504406010360724144c1009851a40443c012050751000d103030180b031ba40c544142140c0601074541003600c036403410390b80312490782220b14020482d02d031040d100e8642050355402000400300d0402d4800d400f049c03101e152800002c0912000b4002d62400070001810f0100078400c45610704001c9178101c070310303501c15029010145400c0e032880c40081ca0313328041d03141450002c051008200c0611400105400c0421440c09a250a4055401402001500c40d2a45550301002000361006214000300400d1005d004280c0100c021191050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 199892643 1250 199891393 199891421
    0x1210290a03020616020d050304030501060e06060306010c05030903070905060907020708070303031517030912030c0703140102040914010f06020d05070b13080301140306090a03020703021003020d020406031a04 91
    0x300e240385400780907071503125080001451451400c1c110050303444000c020140340c010030040d0346039070442c900b85003141c9a50300045141c4000008010b22991000c0440c2d910800a20708418100f10500d41030349540201446968103021f051400306801c107140e4000c500c248d40c21070300d4041c1ca0701c0389002661114000d0240e8101c540010360b0500c003085c000d400c003c0e00b401c041151881e25607510070710042e400043c2060b0000d944c00c001040b000d07502d0243c9161940c9041c150140d490f1482c0c07484209e682e45281e11004040304110303a00040359140c01c0d410744008100110341880f10042c92000340e03611002c00d0007004000302d80150017003210380c40040c0b5500581c0b0369445e00d0b8034012258030707900c1d80c11000500c0340034500d0268140100241422010f14020300704804902d40f0703600c440341010f003002c50007440b005152344006028030210754000390080850b60107468010040c2e03070b070035070440c064840c5426008481d40000349c0044d00c20391503800240c0c41105c84400240003000d200402003035036400c44900342 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 199893893 1250 199892643 199892659
    0x90e060607080c0a150f051f060c0501140f0402011202030906010b0f1e04090e16090b120604110a0602010c0806060a0302120c03041101022802121029 66
    0x180340d10010484002c0b00f900304d0361600025a6004c0b240300341025890304d8140c6400303003c4103100140c041c16806c0040401d0821680c02038104c0c1c000420280e1103204104052810b0303d83c10b011081d4801c10004160005050180c60111a14004250250703800c85c00034010421510b1880d0382d601c240c9008054240140509134a42045001c039600580030354004c80da002c10100503504034103054620102e19048500c3d8846180c043e00070f007111000c0c1540c0d911600700944580d14400400010400c2d80c50710400081e01c009191b02143c1e101c82105040c9040e4491503013030100744100d01483e200005421119603031160b8440100f2404d8032101d40d203143c04a422800400c10070302c0c0540c090140c00b0450700e0014184407120045000181d02600d640d00e0702d000000c00c5c40300780582c0218803a100c283c00e00040607500212036800202161098500340320071000c508003011550386461310134010b483c90f0304541800395440e8110005042000140c0340c902041c54502102840c202e504000700580107100340 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 199895143 1250 199893893 199893907
    0x3053303061b1e0c1609051b0403060507090b030a0209130b090412030e0316060c090501020601030b04210f030608070503071701060915142b0f08030c0901090e0606 72
    0x18540384000f60b10100d50701c0140402c02c400841000401707200364610300c00220417480c0c032000c2c00c21107401030700401d007031b90611908041d00311030901101c2c216980720100050603601c40c070084803242c00f19080103540200c0001070244081840e00a49064070782221815400e80d400e6500f0300880e801c4118007900f05108100150201d40d001301c060302440c03290309010944d00400f800460456000c090740001c207c4116800f8014014a4032441402082508112a0990400b4000717990345105200050180e80c09100050801410f000c00312045003407611031202c0307440c403260041c215041c0c5d641c0401c002881c000c4002100c00002030105e08a0b10050050704009080040c020420a01d40442d024659221038000038486902c2c8941d411501071140302d8901e540c180074101980040b84418248901308a1203034091840044004c042440c042114603000d800c49498071200b00c04030044042c01c4018003008100303120505c480240260304090b83c40ea03e243c2d84802c9042180003041d28650f80001d03080c802c103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 199896393 1250 199895143 199895167
    0xd020111010f0509160b030411060304140307120806090412030c05090a0e040b0703050c090402161703150105041208030421020a120507030f03053303061b 68
    0x100100444003002140805041070b210b0181c80003590a04070781d9000d6001d10074036048011001c0080c00321660028070b90300f4661030b040e030b6032035030001c24911414002000c981000703041c80403161045d000805803922602d56003009030511100502003000b0a4001d000034842d8601074500c503206641c032003601c006600c0c00c1c5d035045005180150000c000d020080004552650312484004010f042040e03000d451031416143c20405840090b1240081c5414401481030074403c45056a460240684006071182c131011211074041038409006400300e14400029100003048900452003454951040b85a61031740c0401190240300b507206810600c4420341c04280018180740003950024012418940e18100c031124140024002040ca1000350380039440c48000c01c040c04802101c04180c605040c2d092404d1070301c0140080701c141c10058201599080019500d802d0300325000d5201c8035500e145041681c10302c0b8a244450300000c20a07120f8442c0d1400500b810b50101c5502080220900c3c0c450300f81401ca4445c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 199897643 1250 199896393 199896407
    0x71d060103061403100b150c0607030b03161a041502010c1812020906041118010201061211010f020106150e0f0306010b0706090203030f07050c0906030f0d110c1c030f030b0d0201 78
    0xc0036901595545d1107d4101103440081c08000341c104003d44094200031901034101ca031030b074070f22a000b034201e515250000405010101d08603510701e5100c2d695920400c3c005c0c01c241c8603035084803503c1d41010700030460346a815400141001c0c11a16010050042d81e4041c0c0c0d2003818510a104950310316444890040c140181340903045000504003054511502d13920001d80d800076420034070070301c441c1f08045000b0340c0c0c2401144014501c0194a007030551041c0c941062035200d02c103002303062050407805c0c10b021502c02d5002400074001c6113006e0b2028984e00d4070050003940060209440f4040403560790540c0d01c0c010a080d4100e4283d8120186010100c1c1e4640c80588404e00d01070340e140c00180110114520b1a100408980d1711500103418200d1001d4100443c7c010b000e0410b902075400b4100f0f60011a20003c2e613a404100c403424000200c002c81003400c3e16040040142d00c0e0824480110042008495881c90090b1071007600c805440c0c40b9400710440c21a1070340c110031603010050444031070140d4003440d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 199898893 1250 199897643 199897661
    0xb0c03040b09060f03130c1a03010b07050a06050c040504050a05162a0b250503131103030426010b0d060b0105120c040501120527071d06010306140310 66
    0x1526044c25069001407280707400895407030090405a100f1001003005403c1d070030300582624000c0800403507101d00749081da80014041e200301c80ca0001061801d010040004000b441e03803122042c0300500e484040e03204140c000303218503401030f41000f01007907402d041800350510a1804468049141c40d03d010101c480c0ca514602c0c0c542c0000d898000003200241d2122681d4445003c3c040d403d0581c24014044111500342a0380e0039000e04a030002c120009030702200722a08040d42403461b0040c000581003040d010b0516042c000c2d4544000200010003444881c0050035000b5903807500c5250740120001142a07a81035041c242e4800d44201c4d0504c000380c92588254082c0806150041c00c0841c1c12180620082e010b644e008080040803404100940c2c2c80744070303036801500e6458280442e050050b21403580a924070a41c50081d4454840c25246400411428004204003500c0100440c111440e600b080b40007030300d000d80040d01305200402ca00ca8040200d110240014005107188a40072100500510201c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 199900143 1250 199898893 199898899
    0x105030c0c100b0109080a0f060b130f14090d0f0804080d0504110901080a170304061806060905130f030311040503070f051905060f0705010f090302010903090b0c03040b09 75
    0x1000c64980d81c50208003940c001c5294040004000c04040005000301c1555031259056a01101c0c1004c000f80c0c056800701ca80b03030340c49040440d07514011030008218150400070348c00c5c1d0500d881d440305084216a0820a241d06002c440040b058030b4101800d40c5401444102102090415040111076442990b000740d00c80d00441499080900c25142c0701d05480c2d00f501c3c01c0d41e40781c040640b013503400c0c50158215401440c240009040d40103040e5503d40c504c0d0038010584a002d8000f0000606008130358002140f014004151303900711707480f5813803c0c10041846000342c103560f03490080010414218817041d0b48030541c00955079103c0d4103942d03500306d02800107052001c1100000b400005020b84041240c50041d040740003545080038101003c0c00203100c0150010304199601910401081d100c1ca0121203840c84400c64681c0d50f04410f04103070307002d007400d000c591303001c180741c47d402c801407650641c450020940f00c0c0e601e44c0c2806a40d80804441405103c0d85610260000c0008108401c1c1000007801c20f40d00c09 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 199901393 1250 199900143 199900147
    0x105031f0312020303040b01060912080c0309061c11040302010e040207140601120512090a15020a020d0c050102060604090203030301050f0f090411120d05030403030908070b04061b0813020105030c 86
    0x10b80c0e600303025101c5032010742000da840482800100b1a9540c0368030b0140100e407070704081a514040340b01031081c1c44141c015011403c0000c8000701c10005000710703a03034208083d00c80c6540d400803040c4c2032019030b2800d6802c484989820701c0e80205003035500c22035007241d80503903d1501d0a1020f20401000358004101217400c3c0808074a00c5400650901003035008000b400f2600b48841d0285c248a818689a0740082c004103504001c440040c0d0b5400700c0318000da502c08408000c501d03880300c000b6803820291100195000200d180720004011041a0040642d002039090365415124413090109581c0e0014000b03506802c2440184154241144080101c0000402d5400e0349003030240810040b07030003a581a40c6800c00003510701190706000580d00051504400242140d07040144014840d01001d40020308058071526a0420710007081c4c1070710004e036000052481e041c202480c2001c0240300c1440520322070303900c207540c00c1943c03401004c2a81c0b0404a0314000c4601c018182d004403165403008080a00400c01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 199902643 1250 199901393 199901399
    0x1e05030d0806010525020d03020c010917030406030c05220311030a0b0402090702030d0905030d050c0406020d120207051c021204030209010e09150f040b10060e21010c2003090105031f 80
    0x20b000c18450031f6a0294000d00701101036200010f1034001541c212000c0e00d84545403075034056100208990840d0304a150001c0c080c0361414040300d02d44104000402c1a000042c00f00e5480e4a4043c84401142e104ad42403201e440048414952601319a84019160343d403040005405810109002c0344d104600c0d1068a10f09403207100b03050200c0301c8500381925117130f00108800c40600254403415420a510340340c1c07682050700e41070009507181040c04080040042c4184000b10008160301611000c640c0725068990031900c04070400d09013000c1c04007190043c400c155414041c0c1c9d07402002c88040c0c5e178000e0400c10103682442200d009688c006461b0100910800c1019440120040d0100740122281091a84c882c00d2038145850404c2001d8048003c0c801001c6081040f2a003000c00300c004298155100040300c01d2a542000040c05400c068241079424889240380869000040030b0090307680001108581b4141d0310f4150342d900414184502082c02040817070300c801c00e0170200c20600c14041410040c02d40c0c0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 199903893 1250 199902643 199902649
    0x109050a140f010c050307060c021906020c0105060103020c1b031005090318030c010905010e0f100905030f070303080c0315030a0b0403080717010b131e05030d080601052502 76
    0x403a9070081104400441e00304009107442510b21002d04004d1070301224400c003036260300b5200c4c458414010407440d501e50704200f00c140280244080308102800040f181e50090404074003030740c08045000003035442c2000041d04d40d8080c1c401d0724010b501d5940100303c110b451a003004080d00640c840540d06104010018484001a002e00f40c810a803550165494000b11300701850301c090125a041e00c00d802c5079140f1080d61368004140070441d4024600305003060420340104940081aa2a585d000507444100b0240b1a4021400100300e03003040c0d088402e120243c0c03080720740f5005240001030004d440b1201140c3c1260713280c0e01940d0000c034114040039400101d000020314210108134203c0c2d0042c106400c0005068200c54000d901181c1030030401c00780c59121003620302c420014054071581c160080703412980220169660303405803a450380300104424413201040900c030024410544607218174030030b95407000c0c4254601c50103141c041e11602e0070a180d080d00c0f0115105100f4010b03541440c41020713980543c2d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 199905143 1250 199903893 199903909
    0xd03050d150501020d0905180c07061a010f05030c120702070b04030506150405060d2006042603040e060f060c190606140303030604090c030f1506090506100c02010905 73
    0x80101c0d403008400901c1c0000190420802c01d00e02c005101400c00c04102c42c1d110707154001400382e801050020560340b500d40e02e00090161074000307080f03d40381504412003404181c12440003031400340c0b03070341300d0660b14800d0440d580d1200b1160120f0004090004c0114100c2c15a05180c10120a0043c1c03480ba035280d50000300b16400550051b030f45030380300781d061107498595240c40380c550f65800e8500380254900240410203030030700345a000300822500d41d03848600d50144d000c00c400302030008241c590703250fa81d000800d040c40308481441c02d81007070904400102c107c3c00011101140e901002d22025030b40d89108120000981d051043d40161017085034a506140c207000d84005a03076906480b007600780380d6050500071106141c001021807402c0302b6010764030750380000c2a04d52101e021180407039044e134149000e403001c02143e4002080350120002070002c01c06014041d0301451202101000306a0740e40c86540190340c01034402c141c10102e880c4405e844244076002e0000114018108401c0c160b41c0c0d4000700d8004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 199906393 1250 199905143 199905161
    0x3070e0403080a18031d0301060f0b090f01050c1005251e03180b10030f0b0406110a0813020414070906091e061206030c03080d05090105150d03050d 65
    0x1a68180030020020300307134407a44114404600c0000c100701c41658000c0e0030310700b04002d100e08208045131411011350b401d4109101400f002e21021410350358030840e81c0450340229000f14818401c0c01c203a0390b0340e94480c07019210244143c80081907090007000c0c49100a04014000b42c003041d911201507407020006000d40c260340060360341c038071001a021290591600381030810b0181058244100c2a54481400026004440d00440ca000361a2180c0145990450031030b40020540e50070f00d2584c80a214410761503030320403806002c080c01000e20b00300035003a50313114820392540481c2c4d03820007140c0c41c00c0c2d0b04a007013690684043d00010b00040c1400c03503041150011565040000c05050017400031550220b51a002811f114030144036964401c15601c0c0407480c10b0245000304841c511440c840d040700c640210f001107400c030100704074140d120b0600e00e0440c0e1104103030540d01800d01011902d122814442c0a2007844011250800101e001c01000b00f04900343e5815370030080c0c14000381541486074810020340e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 199907643 1250 199906393 199906397
    0xa030c12050f06100e101d181909020d050a0203060c0304020d06020c0102071a070f031b0c031b0b070e0306100b0a020307061103010305010e191b030510060e0c1806030603070e0403 79
    0x204051004078a49900c003002c074004e1040c504902303681d00f0016042904010134003d48a03d03c4844514075009100d41d0002941c442800d840c1d080c1800030105404160a00a9064482980d82c03070360901028031080d00d001350800c800100104c0030601d036070b000d4201c1080407400540340c44c405440340b507003c042c8840c100044c08001e40511205642100d458400e1000b035003018001d04900c1c5400d802000d195a120368148803800c40c0000c20544110400040500711002c81d2481d0101d41c20800102003040310740b900440c01300d408014862400181d410311680301c41c0c481d00750003070801c100c01100d50042e1500f40c0541c03000780550000a941c5004101c030400c0d40d030b940c1a4030707903140d0300740182501d401584071a201d81103401d815100260040c074642c401d0b50402da8030000011088043c1e50540c2e07550744040c086000702c042c81c1e5000105e40c0c10400440b8112000e1240c00e48428180c400c442c800d040c1d10644100c039000400050b03040690107140d002c100101521340316a917925504086074421581140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 199908893 1250 199907643 199907657
    0x50105070807030b0a0e06120303070201051501110c010c08040b0f121503150402010c0b0903091806030d1209020a0b070b0a1107150e030a030c12050f06100e10 70
    0x450360061009030302c51020b103030601030010000702103400108a4058507980406020005245481e0100fa151400c400e100440b0780e80e01d42254000e009040960390341c0c4030713101904810142c942c41440c01100c2800f910001d0143c00d21810015191901009400c40715000c081c0000601c079041c84014140071081c80d00c00f01c0d618100380700c0720003d280004251084041e007406d0414031036103000907a01d881c0c0084140380328454850380010384440e0307118003008054400035000c0084001d0040050716030010207481d42240a002145e410034000c2c0c0032070b50b258041e4048030f070211030303544a61707412054401001000a04010360750045043d561094010101c81c40700080c00008002406042940c08003001804205201c140b00500401d8410a103000c2c00b101e08034010b21818401c55840054007103420000c4039aa001c00c614040c2c041d006606002020403450950003950010b640201440f42003000c8400803160b99290070000c02c01c070020310f1201080001903800c0c00c035449441b0b101e40ca9082d2929800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 199910143 1250 199908893 199908901
    0xc050a08060603010e1b0702040f06060806180a020f0d0218090a020c06070e19030c150e0307030201140c0102040e040b0a09030c03030e010b0603161b080909041509050105 75
    0x142000001800740d5004000400040011112251400d5008124004410003008594540c039100c2d010b0707010007039442407900424010b8510150300040480d07965495403000c564800c001c1000420b680d2404600302440b9000041c03001c12198010207146e52040f000c0c50804001c10f980c042240c0113148190004050030004580134038080300310650180d0424015071408091980c0e0300d03103d000c080e200c041800600c000310718a80e5110484102e0740c200e41c1a2a0300c81d04c2d903038245004000c810703100f41c0c000da58400d40056074807882028411b01031100600240751140c038550045a40d9030310507147e50080041440803000300b8500b030004000502e541207002020b801c050618650185e005401920031614000741400000e801540180703c039505418006003101c0a42c0030305d400b604149180f20392003000001000100e000a00749240008150380d078142c403000071682000720340c640f280c40c0608201010b02240c009440d0484201c0c1d031043c400d00080d46003480d01c45072a03090343c500010464050f5103441c104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 199911393 1250 199910143 199910147
    0xf060204090e0a0f020603060a080102072001090f031b03050613300e0f0a060302071109190507030609020a030c080f0717040501270c2702090d05010c050a 68
    0x4442c041080070050000140345640e007603400c0c2843c00000b40620000310002d1110340d5034541b204020140540207540c2c9100502d00410b281c0d09a0213080c014001d480e0003040c1329441810000159600010710200f054290f81764a5030b109008541d100742d0702117000e0b02100044051101601640c545c060510a0040c989405950361944034443d041180703036040804080c4a90243d1115038081c035041440d803240c15480402c2a45401405039a003241c014400001e4071a819401040540e0044e00c5100e4501f2008042114036441070352910224052206001d40081c030551005030008050f041c0011030965568a010a0b0f070016507680d00071907607403204885103c1d0444109030307101601d104c0c003001c41d00c0d1042c1e02400400385503e00080080c8400e0018080143c00d510004041d0b0300051480c0701c0b452034416003080c614403204100c0b00c05180c660001410307800a00100002004440007852854a081e203020003500012001544550f8841c8608046503013803249030005800c55568687c1d4801c10341d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 199912643 1250 199911393 199911401
    0x92b0f050f06250809010608030f07060b040501030804150e030d0806040c080108030412030e092a0403050d050c01090b0c1801020721080403060615110105040b0f07020a0f06020409 79
    0x9a007000c0418841c010514035460041d05980c4822820008644c3d191004001e0047c5801d4101d04614400003445c2e070b070f4841c2c10304042c2a00318412502404441d0222040c0020b0700c800f80701c002c042d140e0620060001c04100f58203040758400d0b42c603140301103444140001c1c0c90716486c3c2801602250340030052000608080c002d20704c1c0c1c43e655081c41c4500e5490a45031907a00e2180d4810103a2801070030032040105072103104404604580106180c60900302814203c0030180040d0002c241d80301e04560402c052031810080c0c500b100d0f044800b500550305900815584c030f41c030040c590f082555031486d0210010b18031050300d50080e000c0407006a1194903400f06102c0a9000001c030350305640c8225010004030048440b45003884c03d0708803000034809130703a2030140228041c90700700408590405001080ca05080a40c440d0131003074a90fa010f45a5184041c40c40c00c072076040c0d030094045c0080744009120300055411980e00881ca07403040300c891200903182d41c620903907035580c1100d02e160001001c100386c0602c2c0c01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 199913893 1250 199912643 199912651
    0x60b040e01050f0414070807090f0b090c03040f080c0f0f0f161a04050d051c03060b031803160b04050607210506130903030917092b0f050f06 62
    0x704070b281031040e4a01e490910003400200142a0324a0021703200c1c400303100c0540104004c00444172200d458400c100058801031800410302490240c0211032450a10729060083d91203501c1e842c41c58a4645032031404461000c0e05030348022040201081d0f102e410800c45003c0e00c400006844c0440e00720788268107010002c1d843d00f42961000132181c0f541c3c2d0300b105054003140c0303040011100c152440c81e11200c40d80036540c8100c0d80320a2032404d020900002107048203944040240d2040399071140c100170341c100c90241c0034401d010f0303909100043c0003003030296141c940000d8400440b07040c85440002041070041e41c0b281194605d0613001030000b040820400c10750802d42c0c0d41001d1400541c3d80d0f042090340f4200300c0c130705964240c0311000b02d0540c0e268400c2d85144c0c0d5520a50501003030865042c06005003250a00c00c560041100001c08445d00400c01542c4e4590401807440322640105040c045030060503c41c072032070301211208902c1c00114410140340701c8a00c20340141c1152600b041782e103030912000030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 199915143 1250 199913893 199913921
    0x17060906030d080a0f0504030801031703010b03060f0a181a03010b01020a031d06070609031b050c01050a02070b03150109060305090705101b050303010f0807030c03080a170103060b04 80
    0x10080c0141660080703000308068070300f8540341c045a42d40411401c041c00c040340e0a440e00d180b8010521080c0b5512954007410b0b60b008400150300c0800080550020703100c24411207045c03510500200c2e0079843c2000070fa814640d4010105e107440e640b00c84c10003509003180ca58002d2a9503035a024000741da0500a550452803004070001c10581000b40000707510f4101298004041112098420180401c80c00b0641b000c2c01d4060b10854580006150010061070034541c1a400b1805800d0260603001c442c9110307241c410707807000180c01aa9000c0005580c2134205e11007440940c002c004010a0018491000e10320408200c0301010350080410005042c0440940082007010304181c00c01600704070000b000404c507a015030b14582c070640450b101b1140c1440f60061009422007410302da4092150000145050f24000041090740079658401103030344409a1100610358140813104101160500c0d0240841484900340241c10b80c58071140c8420781e560982084548644d01c14103c1c1c00c60505100701d00c070041c1e1403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 199916393 1250 199915143 199915159
    0x40603020d03080c12010305030a0306081903110f19030e0901030f0206070c0e0906040203070501020c01140c070302061b010507030203041a18010204030c1401020a08180117071706 79
    0x154022400401400070701800b4812120040f60030030031141d040781d45840b0098a91005941c40b407414940300d0307004182200c002401d0100224007130a010071440da107001c408801c0354002c8000e50b01907030a0b885445038800c41c1d004800100c0c04182051107130b484581f4050101005015440c0380103401c010200012030700070380164005000042500c041d00203015011034240d9214407a40c0780419905401e5088002c0110156050108030700b0300140d081e000d140700300c003510350541d12000126602c3c0008070300180040c0704c039800721078041082d030010504101c000080d610300380e80726000308907581d02a0390400701c04040c1483c52500c0890030720840c0e400103044d02d130a600d1420580c65400e20007107121310000d882007031180031810b42e00741c5008134450035907100001d540383c3c0e580e0f003420120110540304079501400c0c4d00c1c0d403a505e41d40c80842c0c6101a95408082281800c911f260510450050003c8442c1800040ca6500e85260300300703010680b06d00308556510301d140e840140080c041c01c6001d07011902903550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 199917643 1250 199916393 199916399
    0x105160206091207030b0130150f051806071715060a05030103060c0518010815040501090f050a1b18090f05091603080a0f1202030103050a03180f06140d0e030d0b0406 73
    0x321200d494401c12011140c1212842350f07007000c0340c02d00115401e0b6026031389041d41080d0b0800998101510804a4003144141941000d10a545400e421a41400018080c2c00302441c0d030303072074405044c0e0006481007102a42911103000f00e00c0617031103501a0404690080010410095a03020b039582000071483c2407801d00714003a48540f003041c2031169150601036243d000070042c10042191001032000204207100c29603540c1d419000030800f04c0151100a401c1c0000a1003460070390207880c0c802e0385010780c0c00300140c0e04110100c0b100c0010803440301900b413440030002400c880c1ca0080007582c4000a40000b000c3c00c10302c105030f1908200d0102d030b000c61811650104089404a001d035000c088603401d000003548025030040f203100c00e6544003803001e10310210003c0140040029020310180c441e446013404d10740036207000780e1021820700c20220821240202072099910441000d2032000152107410300380110822818150f4205245040980d0b02c0820007010250031030103070415080041d60300300640b0381 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 199918893 1250 199917643 199917689
    0x1002190e06070201210507120b191401020a060507020601050f19090b0307090218031513060f0b060a0f0207120c0e07050403020a0605130b090105160206091207030b01 73
    0x80c0c2c00b4003a05000a000810f500d0140b1a98200982403202c07804220f40d14100ca0050300724081c1d45152a4801d15280c2421400e05180f403098070102d1a09201302280c61801c0010402e09079850b0130f1a046001e14114036001645070701441e4094130594000d030001d9030419040c012622466096944994028200d00e61484407034a09001a28044000412080501070109140ca4860350010804502c0050484494000304034048951007040b0240c4c3e080035025204040d10810a0781c0008110702c0d1546c0c440f00281141c0e0121405880e410300208140e04d4010005036960010550000443d00c14100d48541e16814000e074409000401d0350b00d1012a510386885107640601c1c001d071007000200c01c000c1482c00e80140155401581d004015044175601c50300000c15030b03003000c0b29042455900c04408140c2d41c5501e41074034075040d4180e58050412494064003800d0030f200150590300304204005030340c3d042d1101001704a4420000000707010292862400801e8258160b000c8030102c100d800075802024 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 199920143 1250 199918893 199918897
    0x14070c0b0f0a0b060f030f07030b100309030917060603010c020d17060f06040b0c0c032806060503010e01090512090102070b03071403010e0402040b0a03020105030c0705010603051002190e06 83
    0x4481d854200350242d40e40d0740e00900801030422801c0d840301c800f0942c1035208811100943c0f00740ca05261a00954030b55110680a803a10400c0081d4854007500307201490b68801d0740000030103406450f007828050360701c0d050510403915005000300340d03410010801c140c0d03040901440c00000040e2000b400d0309468294010007004070340c80148094500030b00801c105070740b400e404c2d8500c2600189502d035665547d00c01e600c030603840140d106400340074114105030149404a00300803070050b42040c8003406080513070218035855444900301c40c0142d84410110f43c68909100704540900408000589401d160400b00c0c070301800240d1186181034104000100c90341d010401380120340101646da610380e112403a041d2045404902e008031100c5011000140b180d242650950085009540800c080003911080c4007451141f8000a0f010a0040021072420344403030006011083c015000011582d4403a40c800e400d0095107904401c12a401041c4d1848405c0403003c640e081044d42c0c14010400d2081401140303081c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 199921393 1250 199920143 199920151
    0x1020c13110a0906032d0f1e090309080304050d06020c0a0c08010606121a041107060c030b0901091a0f0604091505330708190207090606050a1d04020c0d0314070c0b 72
    0x106441303204200102e041a00721402050099291230803180143e04808020a04000c041d80000d050040000f250540402101c040c1c1c0d9000c2c2c001d41c0c4040c12a02c812001e54001e00d00c0c2d409900c51501060089030820034540068180c200001c90700614180005141c0f0f0f034414083e901203840c0c10644c1c1c411070b594140124200303c017540c000c205808002129005030090440c00b4041a007401400f001d030b103501d680030361214401140c00e465603988a01c0520200c40c0040c000c84265010001052914076090b41151040e060040c04580390589861000040d191011040701503511940340074813041c6080310054100451200b0001c0d0380b0340401502d80c2414092181210345082c00041c01c0d0140301c1c1c00c408584d000055001148105c14010400a41c1c8070010b1085880c498600314020400c288079400702c450010884e5250b65401a0b00c0f14010069400c042c50030f944150b0810500080203000e0200105141094070001282c41181c01034514000b4020800b404010004141d6000030b00149215504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 199922643 1250 199921393 199921481
    0x71d0328050c1206040b0a02090306070c080d0606080901050108010209030703060b0616150b0301021303020f0301060e07090603061a030c090316092901020c13110a090603 75
    0x50015824480e0070810380000300742e00f114900c60104286040024803501540c880c0141c4015a41d42840c0038080b4003482e4041603144e00104c2c0410140c0e0b1282c640c4000007401160314a14080900b00d884081758107542c03040340400d1503503080205140003881000c0c01807006c40025403070092458000b94480726103000041541ea6120034046958a0b4002900d54100003402e0501c0c019a45090005079511b00c03003c143e11440c200480400581010f001b80c1d6007a46008581404030743c150342c00c00c007041501a198680540d43c0e0f41c800203030107200d464100d00440726601c8090300c181c2040310003400d0314002d03000b604001e0500860940c3c04034590040360342c401810802191247d2925001a04141400030140e01070740d41541c0202c0c0011555000c48050002d00518a880e1700c031011440b01800352924145026030072000c0c03020380605088050741a421600e80000524207188070704440641c2000c003100d80081c0020409000e8290188200e00008000d14510842281040101c3c820940c54040c9028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 199923893 1250 199922643 199922713
    0x3050303040312021c0e0c040e0d0e04090c030605011e0b0406050307020c12030301050a080a050304030305090a030f03081e0f0103080f1204060203040c0e0103082d03071d03 76
    0x3140d0001603050700e049040c170018101c2600030010403c00600408171208410740101c0200c05d10510b064482ca20046406c58081c18921415000680e07404441c540a40c0c0c019490b400300000141d40000c848001e54840c0c01d00103090f50602c000240e0202e504d00c2c1c0b0005000b9610801e1044205510558045a00314905241e80e039a403007104a050002d031800f0b250f04420707038601004607a507001c07001d58185e5006513600d6210595801d039407070b603640003100040c246800c10841440424030410082105030409400d040011b55203a8401e15040d0b143d240a070001609007040c090030b1120811080315241e0310000c140040e04103444100e01001d01840000e102a10001c1c07441002c08000341034814250903420801c510f440d0074100b1328041d510442d01104d022100c44004103500c40b5601d41345068a070000000c0307080500da41012000d00d060540007001103454013040d81c84032003255000350b12800007503565007000c601944e1401d00700301034000100d209403c5150840c510b441c03c90a9102144116240e0b02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 199925143 1250 199923893 199923917
    0x20303150a031b08061303050d1505090901050901050606040e070e03010e1002040f080303070f0804050c04020d0e06090601060c030c114501050927010911030304030503030403 77
    0x41d0840c0741a42c40184000c200c40315000c120301c1c0d586902822900d0030300c01c1e50040e03a91a6000011800328800c000c010072428450022104c00342ea1021409a411046540380552220300145001004540300302c100e80d100c4c01002051002070140c260890020740d08142083c0c1091401801c200300200b070f0508000344201c2c0d0307181e55a000d411082d280e400b000d044e138800b03081121104000e940903000b10702100c200343c2070001d01010004102c0e486050113030b80303003070b41c40040341001c07564414040d02c107403410712a0000000d290751b254030080554034902000000d030450040c205a0604400a21880b0560441401044026008103010300da5640c1464690742508031303841c0c280c650010201c141500418a00b846404014100c0001b001c040c6080300c6068080b040b81d2003e03070b00c03100c400c20601e071a00320071801000282421740c24150400e03001c4600074103040d016440790b54500d8070b034010311304180c0d140e600d80010700000300641446102c1c00d401030f5241500310b40b666a50780c480030380b00804214070b4107554 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 199926393 1250 199925143 199925149
    0xc08040b0601030e1005010f0806060603070203030c0a05040305160611010c08180114070f110106050319031214181c0c021c0602130b0c12030c04050604030f06050108030a02030315 79
    0x505da4003942000400803543c4450404503448128000d1481764828540400ca003442c00d03c00780c034410303030a47d4005d41c6190740e00c200120258101c424041d080c00320900010001a605001d041c2c201c1032488101c0551502e0100001d00702940300b48140d20740d91600718401c0e0300d503601a46541d44042c03c4000250300c140ca2051550041c400744e40e08014492900c000e001d02d541d0b0001400100e4242036582c00360980074007250038202d403003500c10140e155100c1881c20107400e207800b10b144040ca020b41091070145085150a40c1a12410031505d21a00b06040c20407038401000f032448182c032034040f00144280e40d041c0071280c82901d01b254909041c0003035252090215074441224160b0300e24245a500b0070304603113103040c0e0302a421504144440e4540c961022031241e409205a442c0122100020081c2600329a840c400c9584050300041c0a40310030000880c0a4940100810055102c1c0c0c0e945c0d0301c98001400c3c0a0308546040e00901455001080044d01c001d0b40081981c0e040109500a60310802001c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 199927643 1250 199926393 199926403
    0x60f01020c0114090a090603060c0f0905090c0c031204140705011205060f0307060e040f0b061b0c040e0f0708120304150603200f2413050301090c06030c08040b0601030e 74
    0x1300d9840408005c2c040b80003021a005942104d208480078003a00c441a242903402e0203200079030b900046c0300c02000700310798075080450940003484940081e1501c026202d14030b040d031340480010034070410000248810403100d92600c0003c1d4500300c014044507410720000074905c044000b800040300b0b403075a0200740310766149203c00056400c000d040752186a96000e000e4481d5502c0c880c8030f0b1046240040d4000f038003a95000c1c131400a40010811361800b03131030440e04141c00e0760044150209209441415540ba125807040c40754401089005010000d14600c40e1450031503650030102c010b03044001203052108503001a660020360000040c029151200d00500007485142d001626a6142a60100f50210700c07a00c0002400404c1c1e071520840218581402260051341c6201194128035503a045040e00c0381c00050241600d400701c4181d880c0d5034410009080d0313807071980140c0305414030b5a802c2221a41512541d00b0b00015410301c480d1615250302d420100e043d00424103070505881d0b07056801d4081c0c013806 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 199928893 1250 199927643 199927657
    0x21023070515040302060a0506150301180b03061e01080d091205030c010203040c0510020a020f010f0c0b010603060e010e060d0b0a180809010f05030f01120c0e0c0a0305060f01020c0114 81
    0xe041111440c060500075031746c00003074491b030b86100c1c5000e0104105051071286400703108400c2c001640717544d00e001c85120034104a04581e00c05256504c00d00e100139135040c0186400740303011602e0001100c00030807240101c00f00681c02191164005108031b00783c5500801c20b142110002e09121404034254103120b4114400d81d10040001d510010801040100d0484a403080d9a0191004116405001010317650382030513880207507000f5065404800e107907110f990207031207454185c5003010300c12006540300c0340305400a8008001280c1ca41c0c8043c00103c8900102c2c900400440100a41600703180f4081007800c00a01006460b02c000080006c00880982d00301c008010381e285c41e216011801401d046010390018810f150005801e1012000721510500640c5d010b07402c01403159006074a000c00400350a407071248101c0c0d94210803000000c220b40b9100865124900e50403000f6624072103d403000b811a0b2006121921500c0030300d02961190340c1c0028041c071411002c2c03c0295544148800b41c1302c0a0007aa0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 199930143 1250 199928893 199928923
    0x30c0c090507090504090209010b0f0d181118070c0309050d05100e03090109050d06110a0801090b061c0b1302070311010f061d04080f0c01090210230705 67
    0x414002540303295680100c0c441ca20a6440300009030301c038420001601c40c00100179600602c03a0006004030b07460700000300413040030015103501e0840e9201d0204141c036402c1454103501b40000d030a07102880b03499054510080381c2120723806440c1c0001400d42d02003510241c400400c0065860a103810075005148100151070002c1ca95410400a80740143c1e503040000c2c102201141003c2441c002d40c00c00106071220581e0503114a0340e01400c20091040c1c1d540d800e1400d40340c2c1030729020744060f07401e000c0004040084c241e9a0b049819810a1600e80030b947c02e107258980540c0b010080c98000c00c0d0200024090354a03c0c07107000c5010b40c41500000c0000d851004101115880000c07601c04040c0c001c4801c503181c01400307009111140404c9901421502c1038420040792407007144400c90a07850501c61154003a03c20761030b10341494003041204003e90003000d4009a01da5440c1e21003c258034045040400e104040c0c0f40c89a40c0f421054550700c0e100d41c0851080c0324450b0b01041e584104042408418134221002d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 199931393 1250 199930143 199930163
    0x50702060711031608030610020105130201050c0307060212040501050c0702090703050601020a120f08010f050109030308100b3702100e07150305070f1103030c0306130e0f01150e13030c 81
    0x9017066080b9510560b14144a01c88520505c5000c80c018000e951144c4140401c40406000ea500190384c1030344000c1e54401c03180030400440340000c180d88060000c0585050844005207014902103003191805407500c0c5144905000280060380c8165805611240034640407034a525550f0040c2c0c902914400010724494000c4403602440d90b102100c0c0c104040c40c2e0303481c100d1a0b41e0701c0c0d01440400041e4000d9a0000c0c00d40030003400840d005a49082c0c1140f440780d11040d805035034010b00c0c1d40c0d54009500f5070350521402c0e9203417507807804001e10385400f850b0b205041c803921225a0b90701075992013500241d8012181c58a50301c000d140024080310000b03201f40c20000c41d85648802d40240101821580040807455804c1c68101c1d00d48205204040d1b10f9900d0021032035900c4160310070700c0c3c0350001441c0a9000b000c9001c40307400d5118034000c40d06d8000441c0010109407400301c01143c29520000c415640950099008204040f00b014101d5004500c02d15080d0300542242011078103058980d00c05010a100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 199932643 1250 199931393 199931437
    0x305180a080f0d0e030726060103060f27060b0102010906021c110406020d05030a0b0607030201090309050105070b040605040204141501080f07120f1806061805070206071103 76
    0x10440016520b4642c098030142c100500043e502420a801c809415a22101303050040d080c0101070f141201007285048083d6040c94000c90707240032400d80040381c2050715100b104031208403600607a058410112100200004040400703000105101405014562250189015a4000c0d03014170b2649812801c00e558072003440c000f01110940c0e0780c80c20b01c03545242010111301d6559000c00d0320251140c542c080c100400c00c800046419030005000b46070220f83c0c2c0c9012040d290745240052411501c80e80001c2a6145242000b801602c80781e4029814403008200510007e0440c00380c803640103501a01c0011142c80c0c500204000340f421507103205c100083d850500c250080018060480c8480990b101000d543d07681e40314660303d43d410384810380464410340348940011580d412282400c100c40100092000c1485130345034002c488010b0070b0b15443c2c0d560509100803408294002c8015401c010280b00f0f80c1015030300255212401818581006072090b85000051030a004640040070344144500604034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 199933893 1250 199932643 199932659
    0x901200a031d0a09021e0906070f02010e0a06020d110106080309041112040507140f090a1805010609020a11031201062001021b0c010e090115020708060903030712060e040305180a 78
    0xf201e1906d2a01403680f02036861180c440420803a030309030783c0c00b0703005030706028880e42c9010040e03420385000c1741030190b40039142d01c0e43c2c2c8810020f200200160750003486c801406030405803030050b1515014040f039041c034500b44000c00d40041222110309059800058146030054506410300070b01071036100c5100c900003480180180090b020f000d99090461203a90310041c14100480219141d52082e00110034a0000e2903a452030762000c100d102c040300d240c0c000701040b46d5901b401c549032a0480c414031507001c00ea404003168001000c2d00b04a540750700035860421080d070200c4025105129400400003170850720340101400c40403c1241542940c0295120660050b601100c03501d1303e14540c48a02c503000740c01031150310a09a400184a000d400300e840341e4240005890308000c0321040009500c1803400011300b20f001002610710640d4082e0165450b800c29642c0200003040396805016098101001440741d043e40c0b0700b0841d040381d40350a00c169582c40c81d800b03d501c4a10a520b407580e00c401e0190002500310 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 199935143 1250 199933893 199933897
    0x50406030c060f17040b1909120e0109030203070306181a0a0c051215011713030207050901030302060106030518150f012115090c0b0901200a031d0a0902 67
    0x40d000343c803802d240b10440c400c2251400940128100544c03004008140810281c078407498104402124145401c1e41d04d2403d18180c440c0c2000484520843d800c0d00c9024590000498034000c1c2c0034648414141d1842c0c0000e951400c0c42c0c00f0240806a40d1042d0068804140405400055100c0e0261540090748842c0b154203400403100700c40c502c0d041002d900c4000344a0421500d4102c05801080e10039102e0b50281641030940100d0241441110223042014104640d4003510420031501101c02009113450000e0610f51168451805903c440005200081e004a8810706454103440d0008456a41540303140f80b03501107410002160062401c0d512080c041140628030442010040d0907503642d030b0f900e250800349011110f03004200c0c8400360b40310025891080f001c60550380c1034001305100b281e9480d101c0c400459035114213800c0c00c0025802c0ae483d600407005c196070810503155401002d142000441c0c480c0d00e000d10003020800c46090082101e08141140100090003514651800b611039a400000f5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 199936393 1250 199935143 199935149
    0x3151c060603031209120305060f150d060602062505071515081903030b120607080906130f0f05011b0e151312051002031914010f05120106050406030c 66
    0x210070742500e035442000d80c029283c0846d1304c20003048078419041d400700d0080802401581d4000303842400ca02d400c0d554005a50500240d50700b44071390326662003025004036482035100c00705541014041000d403041c0644000340900d0414149911112002000c0300c8070300c60210002e041d41120055141c3c80d803d079030f011100c0031011000f400c02c0c036070f00da002c0907517604201507001045078240c140880000e07119410035980760b140504400e0390b00b44285210350500204483e11000074410340c0030050089001c001d095088000902008605000c1f612040c1041d421000050510b40700080210f04011096200c140c00c1c0c2d044a451081107806602c00401040c41008003074880e600000010305503654007022109241030030395846121901d0039035800484200d0382c20688071401a00740c1c4c06608009400110310649039117800700085020398006400300c0c1d03841c0605004000300d400c0140044a400325441c0c00f075900454051810001a10139030b805400c09810164229080c44000801c00182880110a0f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 199937643 1250 199936393 199936397
    0x10303140313050313170601050a0b090f03100902090106030908040b0702010c0203100606090e0903030a270c0609080a02030c090901020d1109180c030c07032f0609010902010503151c06060303 84
    0xd0124035047e0b50740a003802071542c080c90442c001c0103140c2c09140140000d08000c0e190355140444000001e007401202010081d500e84c450000700c00714500440303030344e02419040c2010000c8407403e403209400e50080707001e101000c801c0001c418040d0780c01100440b4109900504503254090303a0040b52025101a200d00804079a4030308000c58400c812116046c400c4405000850031030750ba0030000e50140a0711294109030340301002e1121008821440006040d0340110b08281500d841c1c44402001e075042580161030302d810146002006907030208004540c10011180d80c2c02940340c03400001d0080c403c0742e4071400d415140941c40036044511038003520700003204440405039600301c01d06904545000f103500e80c0042c001040003d03005540b1501a21501c0d000c0d1926441c18003681407060a070f00208141802c903030342d600060100c1080104480c80d07000d41d5610090021b50708550001c0d0441c08040e00b4507165a6205503a1062600c0304c4c0d1744070000e60b200d150030300040d11081c2403860082c8103c0c041600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 199938893 1250 199937643 199937669
    0xf05070f060c09050f0f09040f0804030506010602070f1d04031b051b0105070b07080a0204091e0c0203040b07060b030109050a0305030702062203081005040c0e03060f010303140313050313 82
    0x212413030070341d00400440c04080c0404010310740c91400c1060391f070340c01001244e070108003842c140c2c00314a018001d0005144248010640e650402ca0080e1402e01e0310b030b000c81341140303100e4801e00508802143d10700b02c03c20509003034501030b02c9030702d0b080c7c4645c9082400000503410504248003400000540449405110303015604012840c07001105c0d14410598003500e41481c01c00460b26070751281c40250350180384040c0050030140c8581c020001d544d02d180940d8060350f8120040c88800e217291091002200c41d17030009600c1c06150982c000e5441c01010000344c040c41d07a800c0070300303980c4d14290040d8880541c4001641e0350b884075480c02a1054000380c426a0040c031600c40000c0c250300303030440340d0781400d14410b0b066180b501d0140c0d000c07074800c0ca00510000070006201e00005441e1a240034112405d82c05813941054241e0890034549424001002d07849401c4246004101090f0481c01015010f559030313100317954968aa01590315007040580c00246144000110f00382400441d240000544254a104103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 199940143 1250 199938893 199938899
    0xf031407230a051c080a0e06010e0406090203030a0c0b060d1e03030204150504180e03120406150e0106030f02130515040e0c0306040605030d0e1908030c0a03080601020a050c010f05070f060c09 84
    0x12003218000d401f030206940c0303d40018441a00608203160348248641d0005c2045e8560b0b030302003411078101046c8100492038a05411003001940d4009d940d200d2400d580d451072000064a44001c0c01c01c400081d0460f00c1d10304828001818402c2d0111405400a90f42500440c0ca144d14002c00b280d02a1156106645041c80140d00e2501103000385148240010001c5d0705001017440840302120002c0d104840c6540d8642000203440703903612100004000c5000564599031410802500340d40264034101111441000401607003400392a14900b0b41d41d050361200c50006000c1c01d004440d01c503c1c1c010052641c072007007c1100c9506100000e5202e42002e075800e100d00caa80b10300f170542d142d0300500340340041744003400a448241401c02c1d160141c1d5550851031040365590b904c5490556102c0745802d20a5044100e158050603040458160001400c0c4000d01131000740e903d0300c54442c81d400130340710b04001c14641a490074034440c600391000c03590865100640629649810f000901c00030031a20007041d0042000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 199941393 1250 199940143 199940161
    0x160c0806011e0513091212050a090b0c0304141b010f1d13061805040615050a060c05010f0606170105040501061d06160f031407230a051c08 61
    0x1650b042c00142002411040c100010402e6010060740d02d0305076141e40e01c00710000310b0700d09480560b401400303450f52006009800e0245050707513401040650a5400d00185000180d001b0a41079440b60b001100c05807a40c0b030f146040828484228280d410710300c60701501d4006c54104160201d4003940c00d81705c0244890503180c0039641000310704516010340d9041400d00b04941000304240346040280c0000091190300c662100619004940095079070990b204200410404913214985200c11000c900ca220286048001600e80790140941c000704201c400c001c5040220940004201044020041c00607030344a110041030b0424141c070102c81031100c140001b46508103403003418140da00d1603480031965a054005050200d40f10460581c0110040002c058520b41c100920114603204950310098403095044c01440d07070281d00c1c194003541d4000c00c215000030300803032103142c03810000300041c141d01c0608410150501c82001070203400c0d0f000d10840320301524214030302c00031101c440e41c641c00c1c400d849060762 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 199942643 1250 199941393 199941419
    0x4211805010f080126060c09090a060b030105010507032a021008010803090409020a15081902030609070e04150603020a020f0a0c060302090312070c0513090b0103030f05160c080601 79
    0xb9000200b1062001071111030304400b0801001c140080000c0e0007103e90310083c0c1c0c41d007401110640e0031280045810f00040c60300301c3d516500110284804d112050510021400390b00c010711410b8140100010403c04060059000340c641400c04e000c0d9400c220500856400309015111049214243c2040030b1340c0e441d401900c03454162403060f4000c0d0300b0920750300144801810004000d80e80103100e140000f804405140c1e10402c11117440c0c1d121219800c0001c1085484018803400100c0746005104010b0140c0352140d0300780e48410075140443c7d50320300d400041001040131031500c4402402519003c1402ca0300b42c0c008104001059085448082c05281007913125042d101d40142085080d460411019110b500902240803000b026180318004131002640c1607800320710110341c0805000320420082c0f401f20591540000380c00000c1c010380a044d5611408094140001400d00c9086607a1803001c903c03c5040d50b40c01e17007203c0c0009500b5640d43c2040801c1281ca489548241d220780d400100b042024851 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 199943893 1250 199942643 199942667
    0x305030306100c0f14030c0f030415020703050c0d0602040506030708150301060803071419060e0d0813260d0b0319020904030f1202070f05210406080421180501 70
    0x1303040c000240d507202c014141e543c41100d0854403050242502e48202402042c6100c1490401507980d5440d11a80e424440d440542c3c0d2000d40d0800c540c10800300700d000c108410500011a21145044440d141200080c0078580002d0340004012040000041d040b60a81d4080e5a46c504080301c1e20140c80201401d031003150299025541060000c000010548044441086842030585043c049110065a501d100c07034032003a43c48070707200c40692055800a00c099270f20407515140082040c946200b00f01d210000c0d00d00c0051103140c00000c170740b950001c0c00803100c41c5664003621003a0b44e2a8220794600150040310a17840c824040c50240e000b080a80c5401043c49540c00340c090300d0f040e0b4aa44080e0b540040080002e000d1008205445803208064801003071480d11800c1146402292820a2460300d010543c0d24008240c00c109036089031800c00080c1c404546143c0f80c122216aa145046003508071401a002c50303035a4256007540701141c11200000a401107202107581407076440004441000e100300e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 199945143 1250 199943893 199943903
    0x80105090706110a050a0803161706010e0f09071112071721180607140409021c0501090c1b0201080601081e01060207090c261f0305030306100c 63
    0x58010003036280101c010f921280d008005031000c0781200e807221410291034250880c0c0210000003040034040c1d400c101d0f0841d100d441c3c50700c9a9049145c81c10070790f0b00503018080301d050049946004640c1e07690940341d03801e0680040e188400d02d05041402900800d18003244140b14001c02d65480155401072003a58202038001ca42c644612582c00c05454250f808640c0c1c03058213014081c00d400c2030a4030003036601e0080d101007001c800d0ba28a901c1c130103070071700304090494020017400c88078000f0054100e42c01d58095070025180180e55002240018010030303012010b40c40345034244070000076600c00640c441c40c0294081d440f00c8007410500180d10402d0015000001c0c00301e08500301003400c0c0d500c40c07108141d024044824a0710050b03849201058844000d0f480000164070208041c440300340c0b28002c1d0110628503083c194803641000c01408940e201051740910a040241d0001d07500c40016034810903410500400c8000c0182c43e07041c001d0701d0b07a1044034002e00421001c15200c05080c46107101c0c0c100c903a000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 199946393 1250 199945143 199945153
    0xa05150702102702060c010204080307030f02150109050702010b040603060b15130b18031905010b1002030d0b06090a0303020601051509030a03140d14010e0a0e2503080304030203070c08010509 84
    0x82c0c1154400c2da035800c10700f603800c0320f810b020a11b6404003d00c0104050070000c1c0085860b8003040ca4000c15040d4040d0b0440219000b041a401e10704d1382900c2e99505403510104042025a1101412801890a2840b5603405820503000009100f6038ad807211209200550342040340f00c1071442c4040c0507105103610740d14400c14150f000c2040303546a07000b800c0f601c1e180011264001002400180c9030000c0070302e15421840f0070711256010001c09100760720642c60152191400c03c649800040e489000d5500c6d19640241c5458180500e03990300d0007140c0c10300034010103020356180c503820002d503036903002d010b001e0003034000c50700301d00b0054606002d4801c80c0c1c400600510105105640071140d52070400c03602c82c0c42140900282d004d0381100c1c040d6010552031700a2611a070340c9000c442603141e2502510051020307250003541d41c2949400300e000b0702540b800d240c03c05001e851a031706d04944400300364005002c005001c014070007016408001030251a0041003e00105900c13062200d0885000381c03210505070b400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 199947643 1250 199946393 199946441
    0x304050f07050108070e0a05060319060806070f180f06020601080607050301300819080c030402100f021915051f120f02060301060201061a09030d0c050a0515070210 72
    0x100751b0950041c80009848001c00d25a80c40100d1595001907920910785c2000f684042890301e4180300354070051802c100200101c0c02e200201403d00101038255604000b00c000c035011401c02042030b004010110b944610b4910b9030303036410007925005d0a0066195034040e00e408289403503c96429241600d00c01a0301d48003045031604500414803840c0810050318480296007400320341400c018282a000b0090064400720b582c60000b440c03400c0040c58000392440c28000d200c0542c642e540d00a08188650600c0e51800d000014181c0c84c0c0441c14410b4a050200107080304c041125050013142d007043c0002c0240151303200c001c10741078150784c034498250010041103070811a820501500c49000d80c0181d11481240107140c01103450759000340c00010150391210f00c2008541035009240007000c08040e6514200302c00340e00000d0302c620b5110303d40170410a40082c0c01d42448028080015003a602504a802880c1c890b100700c0d503601411111100940141e081041c01c0c1002800740c04045800c400300e00d002048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 199948893 1250 199947643 199947647
    0xa021c15090e0f1c0f0305191112070201090c060509010f081302040e0d020d08010e060d02011101020a180503010c0203031b040305070b0d060515030f18010c050304050f0705010807 79
    0x10312082001140c0b00b05540c944102405000140030078900c0101d0003030604040f0700117000b0904404079441014982000c010310305075540642e2400c0030340417001051802108002d04454068408005080501c46043c0710b030301c5405612041150b44610403e4142c15501e10741a2075a004019280303000c0b58841ba491120140310701950382e400411a04d0100c200c02c42900480c01b10b9864502108081d4052038060181c2c1c0e404003e104c082d1246841c227004a0760500310441040c000192034103001c1c3c2c2211404404580c0280e8440086440d41c00085495039800c030002461807410400c1c0040c890b03103e10000ca1a8141801003030344d40d4a058004603e1901c0c2c0340242c560b500b1415010000c0c6c81c1c3d050001000150013800f04c04014800c1158a41e00c5502c00c0071040e085030100e0340b0940c030400d0341446ea50741c0f92070740f041a00e40c41044150540c134250f0f0b45d1900403110916082040b201c9510b0410990000c541100255002e00d0045089840784000350310404d940d03410601840340401e180d44009141c1074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 199950143 1250 199948893 199948901
    0x40503031819080418051308030405010b09040807030306060e01090e090f06010303020706030e0c0f01030911060417060c03071403041b0b0703110a0209180a0b0a021c1509 75
    0x107004034121200b039108260740308a582910030084910f00c2c0c001804000da00303489214000c040b52500c0082156081c101e200c0c0443d03280f0018001e0030810007200007414070400b0350040d109100c01520b2000c0710301e4075290204e5640d124a0342140468500708021900c80d10409050800d40410707102d01410074244008040c0600c0001c00c859520b01c9030f444010784a60303003401070354003e41c030940003800c4079070a00300c014041d40d041d0301098056502103401d860aa60794803061521401003824001040415410030351880f0102c0c254043c3c00c00f60014000a0040036895904615020b450944130580c480e81818100382c1310940709500014070401541c10064a10301c001c6401030310a84d01c1d071401884150f20091113140c26442076449101c0480c14000303164016004210b050100405860b51540c0c40e80001c0305560f01a10704900184400c0c01441001c0c030410005c0d07080c9403c4079414100d451308141510103503001c0c2c2c45107403414040448114000580740126000140e4600500d0000741c202001e6000070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 199951393 1250 199950143 199950181
    0xb04051207030f0803100605071203470f0f100c0b01060c1109071205090102041d0103031403010e010315060302120f0d090e0408070c03120c0606060804050303 70
    0x16010740080040081c0005140481c000e00c180e451a88914085640011001003603000000380082040340e44000780404a030804401000d0a00045c00002c146030358045080b17000f00802140e048040d002120b001c08081040b1040c9190700d45141100c44609110b0840030a403d5140c000d202c96203082d0451070101d81040c0640014500810041000d80300c03140340c840282e00c42d03004660340d18044030600281d0001c46140020503200800c582c01c21040092006046030f16a11400d41c2d01c4e000304065500170b40488000303211035820f1003074010f083c404080e0480402c0c0301c11404100207901c90380c2044000340a0300c0c12030380041d0b4a000268038580320644c1c40b85424034030070442c6913910804001a9070300140c5082c1101c80300010b111528004034110301d0004816198828440c400c1c1c0c041000c000c541c0021603200c1c3e40b02180340d882d408030b45000f4520f00340b1508002d10105440062143e850b9000c44040000e40c000c050a2101c4c0d51b03180c009403480b2800f40c030094000d4108000080c0c08400c0c3c000903142c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 199952643 1250 199951393 199951429
    0xd0203060d0b0103080a090b0705030306040509030f040305010204050a0f0503031c020708030a050f060405060a050613170609010c0e0607080306030f0d02010209011106011d0a140c04150201060b0405 87
    0x81e485a59a0209801c098104403010100440d0f001000c5502c0806400540a503603021441e211158580340e41e03d000007081c81c2d00c40e40d2202d000455100301842030f54003200c042540580c955440c3c1ca0068003075001401440e001d0146044002010442005c01c1000c5a5001c6d000e07514285449401801e850744401a0304075941d000c2000301c001400030b40086206600c281d0300019103040c10400d440d0320040250005215509102c18020b29544a00800703003141d20440e10290f4400c440d0790403000b0000d85134080340208850010001d030310140414124402c094003c020410700200314015206144d5540c285a0400410710400c000514408010b40d0400c4005044510403026612032030300d44810000c600d00140d40218070402e165800040440109801d0000f40c06a076041c00e2400d2200c0090785654041240c0580104110030301c00da02c041e0b15041c900d000da04061070283e01e0300107181c0c804d00c28011240390f100710002031a4818441c0e9030a44452058403441c09123080100300b101da02011220f09 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 199953893 1250 199952643 199952659
    0xf0f070f030204260c090615090112090303090b010806040c17010f050103060f06210f03120603230303130602460f050d090f12020a060b010f050d020306 67
    0x5208100300003100c00020b041c4c42005000c00d00c5511590505100c4030f00c0c01e0049001d00c0070b2040f1540e07500e2440c05d95a2000701820340742d03d80000101d403541c01e4100701005445c07420240300107065060b001180c00a0068010309440d036a200031141d510b00c0f040b10040d18aa000c5c10043c03080c200391004155040e00359000104900c203402c010001150000e90003200d000da44c4504a0030004120f0096100034280a5002c3c22855085480000c0c0c410b075210000b0062003c2c00007500c10180200120001240300c44020000c5136200d2400010301d060707401e0b0340e00300103400c550a06803d0000000301d901c5030000385007210030624207503146801f94109190b4018840302012807507114106041c40c1081034590800d52000c01020020407403902205040e803402017007500d0009001e00c61b08501120056180e042d40003500a280b410000a1508d014400412484519141000e02a800103400704281d001e40c6040111a40c0c00005407001c0485a0000d00803036028030000c80a0b0326154013641d40808040e000c14 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 199955143 1250 199953893 199953899
    0x2160504180803090c040b06041d0421050a080c0301051c020103020d0e0106090e010c0903031107150c030206070806310207050f01050c03040807080702150a170f0f070f030204 77
    0x202d5a40c00888a405069129400000d02c42ca003c1c0142d00141e0303000e54626140c1800c04001c4204220380c494032141c00c0100402140800541d085c0525130400c0f0580855003191030711000a10903444000c158001425490114018100280459040f90802000e20410342401c0c2c0e80c6c082d090a0081d0141e0516a00b8440c00301411500d00a030ba01624100c000001c0990415000108543d03210340c05440c20381c5002200304009400a210b0341c00e40380c05003404402c01b00f805101510b409000e80200000d0881590a5a10702c0c0d003200c203002585200b5000d603500303640d41c0c9408071074042080f69400c1e0b0010f40210540c1c0400040100010380b103144c402d00c000e0816078402d8120603a40110403c40301c941c000640308400810070b01c200381e004648000f00520314105901c44c2009401540340c00350214500040795401c660711400d80080c0c2008201059450b42c0c0c0481e4054400310103a00c2d480104a60b200001d03d034100000c014505c2038030f0304400303511a074a43c6101110b42040c1c038040c040070703da400c00c404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 199956393 1250 199955143 199955153
    0x90a06051005030616050909090a02060a0807120902011e200d0216080c01031d01051816081903020a141606031503020f0a0f0311100216050418 63
    0x400d10036464119181901c1d860a01414606034000f009059821000c0c0301c1546807550000032a01500000ca40b441140c5e12413030452400c0c83c06e1044000d51002001556030080b07078001014501c61204c603101d410b49210001802000d40303003000740081c00190610208445800f80c0c4441841e80036046c5403181d0620701c0700c80e01c6420840700b9081c641d82a40302040103404c03e40e041094001c110342d0160308858142c501281165078119035079010f0305040c0c5485a960050144c03010201440e00564000d00883c100542808180c041034207080b5444c1c010288004000402001504100c0e00c04ca0020031541c98071541c2ca0803a42d0760b80300100c085004d01480000440d0000c5c1152401412010103010798041c60205d4180703425803540700d44149420f01140324400b04c0c2c0d104841c1d040780d806031454405801001b00042c1e40c0442c68200206400c4a0500802845000d840408101c03d041e51100c0010501040603030f40ca541148040d11040b205400c01c1c01242401c0d0013580c40c18841940a0301003214030b542d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 199957643 1250 199956393 199956401
    0x2a0301060b0c010510150c241d03070309090f0603020306071107060c0f0b070203130b0c0d0504050a090c020c09070203030a06051c03050f0910021605091905090a06 72
    0x1c200e0380d400c0810080d20042d000e206007030b0004441d40340c0502c8a0714101c0d2603408150f421030b0820610442c0e07040b1500f84114902c600300c81d150b001c1c10f0030a8506554100c0d0340100041043e4400900d441c0000340d40b210000812203042079056101d03546000d01c1c1407092070140c0511842c5418464aa490010040c0ca0801245000795420340700d600451100005083c9000c40f1580810100706a200d2410301286260482404450700036558910503a80d0240a03481c61040b02080a001c045401000851410440241c80780149410035907480b04001c840449031405a0300a45a1101d04440c0400c03407442a030380301446812a9005a4642060440000b90a41822104000560400000c11128609510829014040481c0c08040c0c6001c0c1004815200d100020010140170001a1481c1080c0942e802c0d1503102900070800303411080441002500e41c10240d600107503024068001040ca840d003140040d2040c6000702d041a0380445180c4500041c06000d801310711140a12210b4501155403401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 199958893 1250 199957643 199957649
    0xb070c0504022706040506180d0506010b040f09061419030b07050c01050a06060f0f0c0b0103051e010b03030d0209010e120102131215110f0703030501050901172a030106 74
    0x203d40119000c29101e076403d4074030524509104400421003030183d551960b00340c5a003c00d85200c002451032034100071171020112140040c05510074640005014070750203006000b039540d07030307126050401d035521403030004d403409801000454070300307440b0341c0240c0c0c10811500d146440c4103644152100da82c0351903480c0c0f40329080e25200b0006100182c41400c03905d00f40a0690003440030700c0104807640c41c02c0c07001001d100302200114200302c08801c006a8481c490122448c419800481c00c51a0f96501d01e00299902c0349400a84504440501d07422003040040c03081114005010b07014515104e81d00030184002c0d40290100350500498854400d501d84550b41c0c5d070512803d04800060ba1403034801a1038404a03003e80c40040840c6140104400140e1115100380c1508192080031030074005200c282e6103035002e1049078443d010750200e10502859416000385049030025108171490340d072510b502c015122001c1c1c0a0030720940c80b0039000b0802550040500d95480c08003440e80c8000d419030b80001e402e541c4568 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 199960143 1250 199958893 199958917
    0x504020a1401050d0e0c04061e0501110703050f0c010f020610290309010603031b0f1205070b090106050f01090308120702010e0a050a1505090703080f0706020301150f030c02070b070c050402 83
    0x31b403962026040610800d00640101d924402100700403d030f0301c8800359110302130f450400c03154040c1e071130110310208909000303151711070103450300c2681007580342d5502c00c440d03200c3e035002861004103400c0c1c80c2c4c0042021805459100700c041c9504e420083d50081e0f140304611050034030310104040100001c80c50700514054805080045172462540c20010030304048815110807540c1c0800385a000203000c2103440324000d50111180701c1c10340d03040704207454601550b500944a415400200241440198490410380c0c1003100c1c010094107843c0011102e00c0c0407400001c2201c0810012801c1300340074080b09651080c0c0b035100200e00180740380011810100410b200300c0c0c0310ba110b500c2c21020080602c408602d480c107044410482c5140a10301ca6594100d170f031001510341e9000060114a2001e1541121005c42d081801590380356516112250460341c13210078040010f070011007404401d03100303024807000117005034010406c0a00b815100d000341e6120200841d002c00e01e481c80000c2a072110f001500d50103802c6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 199961393 1250 199960143 199960153
    0x90305030402090906131502041e030b16081f03140109030306082b0c060614030c010206070e010e13090c0626130206090d0c050111010504020a1401050d0e 68
    0xa00c1401400741014044c90b135160054402c0140990041000d16184d5801040400325042a441039078024420354010b440000c84180d40e150318900c03807a09040c101c921890b500c486540c0c405091050301d40030006010001500000810700c0101c0c11030007841310343c2d490b07406100c400c0c2c0d8903910004136641c001c0400d0b041d0707511080c02c1c03000c0c0751b054407401c0020300c0c0703040242081c0b181003400b0f03840c0300880401c4420f03161021005103d4252040700c0354001158890750401c11a61141109d40b0024000c05066120348103640c01001954408110340780980000c0c3c482c074445101c160019503079100303c0c4022030f420102e040c440404120150048410090090303803d90020390070300c0c80042144950181408040da0002c1c800401004040c02042d4000824101140f1081c407a00c0007501d144a4854147e900100c100844010b01000c1c02180c4100c1d00c01b62144494500c181140a003030700c40880d4048e40c0240915010132016010804145405105140452900120142401c21504020652074155000d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 199962643 1250 199961393 199961401
    0x3090c03010c0f110f0309010c05102301060302070b160320091005030103080409021b0114011818020f03030903070e04030e01030e102c03030f060604080604030c0c050409030503 78
    0xd00c900c6500c00d2400e0140c17050800b4854800e40d240308291416040020004a00303090107004d0100310303900c8011902c1440310090a03040f15409180355903580c0e000540c11400010700500034400c4803007081e03000c2c40e9145503a4561000030115522310f09940c003456107419111020b6880d00c1e2041050300c03070b08050f40307444040307040c00c1c40184800c41c603109080c0700042006002003040f91080c0c904840d060030016a49107140d150310a080740003e028650b480d0300b442d9a01d4500003504204505803160f4038a0b42e04440741c3c8528000130f440461040580b40b040c0004001c000d414441e038031050100014044a19000c0d10324003280c5400c0081e880340356505d1012091004042d40807141d174600007070034a41404080000c84209841c4d00e1010010000c896503036008100221201c80d08003c04030340e03030080203070244441c0f52240d00c907481210442078140071000003a41760710309070007542c080e1100347d8010103040d525564240c135505c20000007a01c94400078240080d190391240601c0808502c0f0703590702610707414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 199963893 1250 199962643 199962647
    0x8070f020c060a051e032e05060d0c030e070b0f090a1a0301080f0115060e0a03020a0f380307050d090309050f0d02030c060901050403120203130b0408070b03090c03010c0f 75
    0x82070051100904000c00c02d020603c50600340301c2d10404001c00840350100e04158180003094008e80c8201d07002400403454801e08100c682c05041a00c1c00e0791000e02003103c1d0900c1c00c0341c90302502e0098005d0303007105003c00e441d01000c69002d0400900c02804480b1080d0b102c03021000e444445152001081c400080140420b0905201a034088519580244820040c5400007006c0036114040ca070700b00550751f400500650703580b0b00100c004507009032445030301c56200e51803100141c0d4907000d801802c0205814061401101d0440c2900000c0c2d81c41c2e00c0b0002040304244010b031a0720103045001080018001d41a151001c1d20410040034401e4940d40c0c441894001071252144404143c0c40c85043d04041c0040903843c0825942c1d8102e80417160990380780000d42c0140c806001d07a41020b01040314a03000f00d034203030703030000000d000e1004a9540452503030b6031100c50340c1c030910640c05049004c1d040b0320400c1003207000080c06550030a0300c100c01e07a158a50004046400c4509500c16040004d0a19510500d03140e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 199965143 1250 199963893 199963927
    0x6050603090a1e02010914030a020d110102240c03090f12070606050118170111071208011707050906041812030e0c0a1404021e030a05010f050108070f020c060a05 71
    0x14540f1085a030702c4806a00040c1c41010710b8070a0380c0700858a0004c0200e150750a0000030f5600768010100d59940403a410718803120110340d80514050301c0b40c022040344a8403010700d0002d00300c280a05200d5150381c1d02c150070f0040d0304090a880319a206030800c0109100081c07004910300c9418002d9151141281d040c038000b903540039400305d418004d0113681100f008100d00080001c1d00c008410102d031014803451034500400d1300c4409251042004200142041002d105851241c1d405587e205004c0e6280c000c01014603400c0044100b0a030302144d0104040d042040045a0000000b003002031105135500c0a00c200440848045076041d070084402441e2a0b054800d414018094000a080420503180411702d072003414081e0591244941101000380c1c0e0340c640440c1c0205d0306151240420328100000f444040d04182d810003180e604120000c9114a81c00000b90120b40050f512108c094542e600d0035500307210030341c000c4011401211406441e075182c6c0802800b554600e41c1e9616621001804114104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 199966393 1250 199965143 199965173
    0x50303120f1006120902150723060c2203150506030d02011a0405040602070203011415030307030f0f12020a020f0f010b101103090405010308092110020a0306050603090a 74
    0x7092200b00c107000c80ca510103100420741e407604a000030104c4440c00042c0c00240c2d000d00c21b442425001541100300061403071030b113010903e1600840006043c0700c1c80c4c5502d9040445140c0b04070641803000c041c20488078107020345d5050380c00360b042c1300194494542c5a4410a0840b42ca9080c80d05c0300103207c04d40c1403c000550081c3c1c41440200440042442c424640c400c1645009108640700d00204090004543c1106d2030594010020043c8108041c0703596001201144c05c82c07003100010701c00e2040c50030040129540c042d450340e02c0140741c1850402c181c8003241c84143d2541009100f1216550b00281440148200401d68008241d4094090b203598034001c8110b0740254240d0400e0701300d40660b152550040060342260801401050280d000503195014140b0b0180d405401c00000005002087e0020304500e00191355412101d402074600d80d030903901d0b2003911415a40f02d8240c419a440700c5034050500c0064516010503680d0b40ca4000880c203801c180c40c003101e103804c0344013400100021901142c4103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 199967643 1250 199966393 199966411
    0x180d030b03061305060a0c0e060c0601050102150114090405030c0d09050f06040f0506030c0705010515090609090a1e0204060807240c03030b180709030203070807050906040f06050303120f 82
    0x50f0b1583e5201501d40101070090301da01c688848201401a0154900307440d40b0001808503515014811489a80c40000388200340c058015805140c0410320031210b20341c1030f40c003a5900203101c111207209204044e50010405d42d0315000c00d00048040d400d00344418009900107586040c420b030708200130407a41c1c0c0381601e00184148001c0008008207915072800d1400c4510072590345842c0e035110030303081c01c00b84200040103005503c1e000c100302c21400b8500e41030314008025100768005070382b8801072118407801910507641b2940030340c00150018a580c2034888504001503140340010000d98041019502a5000440300d07400020061095060048032414050300400c44910680001103000c0e000d0404c0c1c1d4005801c054a41421001c1030301c070701408042d5002ca00b080f140c01d034039081c04001c1040420740801c81c0319000d401000140b22400141c44002c1c0c07800103001454684480c404c000080c035180c0404810765450710030000c0c03169420301c060800d0b404840c144006602d0012805040c2c0500100781100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 199968893 1250 199967643 199967671
    0x603020a09092301080607020601060f0503160302040801020a030203011d01050d14120c2103010b1204061512030909111210080d090302120123180d030b0306 69
    0x90154010820022140846400500800d9985909002d0240b0546000c203600f41d20f40001040480000c5079440f40c0c0c52507013a1503207640ca480b02141c1501c98020848001502400818910302d808081020f0703400e210b0500518041d41c0c0c40041d42640c1100d000200800c0c0e002c0010043c0c2103910390b2400c90024038480e1038000b0340c181030003d42d0030400c400c0068803c2903090180d4582100800400084c030b607542ea0b2240c2c580b0369007071b407840d075074842d41650b81c1c10001c4100e510504440c140c01035a042c0d0b0a58038400e402c2c1340041465460349039000300b0075511592202c44480003000c1e0143c280340540003010740075078120654107026055188507801041001d1610034a4480c040004042c0d50074503d0823142550355480b16203a4611511030740c0c01004540c02810b010300580d942207412181240d2003502c02903c00d2216050b80c0c0e089842c1d03a03540c1020160382518061201000034440781d444414080c1c0f02c00660380a00b400d5143c15030501048000c01d90312840704800d860f04124284d0320002c020660b03c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 199970143 1250 199968893 199968907
    0x109060b0304260d051603150b070510020301060e010912050303070c11090906070927090201090906120212061b1b0f060a1d0a020904020406090f05040c060302 70
    0x24403a00c4020000780c40e42c0329000000e04401040448100d030309060701c01c803540b114465006400100b005480d42005981c0280240f4203441c0640550740d100c420100c8003011981c03601200c0700d12588080c2c81100da900800e1070113800d005440c4055406481c440d035840740401100701c00500404100d4000141000ca012441400124004100da510421502e0b101540c001d0074680015001d0302481d00960050050007003106081001074141c1c401e1140303507216030a140d5101c00c210103a240182915088580c1008015141c1e041e03500b020001320b1062501c0c03a0601d5540b900c0b0341c1141e0140c2c0001207440c01a141e10001d5243c04204d160101c200302c3c004e0042810500f8000329010301c200302080800c50081540080c101e4990300000400002000752280010301c1034001c0c1d11020105d482e408d406280c030b00007100c01490700c09000c01c150104001860100b9442e02003140c1d00000030001c99001c1c0d100c500c0400d0b030290501610040f4150708138007154a0a007442c01960003040c0f500000308041c8144049 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 199971393 1250 199970143 199970159
    0x6060303070c05190806090c0411040305070506030702031927050f0d05160b0705010e0d0203120405071203030e120f041205010f0203040f030206130f030f03150803070b010906 77
    0x2e1044840494070000c4500c0c0c00c5502d200c0281d8039500110791130180c0000c01c2041c55004c220210481c204403420800e0040044281429005500000e00039600041e01840789061150046400c400940112802c000d1145100f81c000612610250001400241b004074003c03d0b2850001e4007103500c000700c00300a810200811032492040c101c044c0f09504d4910355a0500100388030380507803040d0031201c40c442e064076803003001c18660105004a5841d0700c0c0c000d030148122808030323405d600303c0c511364051850090221508508010f002d001a22540035114001030754800040411240c584039890100b000e0514901c82406c0c00320340300007104030200c108103800040d65880122000e580d502112100702520500303090780148010014452510320001c144024040e110040c90340d8248240d089a10a6881c9140c40701c4190590000800701051b01125200181c0a18061901c4c4042e915000401d01034150380c50b07480132215485144c40f60000102402071294020042e405029881307402d0099030300d080c0c20303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 199972643 1250 199971393 199971413
    0x3020307080718030501020d060302091f031401060504060f0801050702070503030a2109060501050a0b0403050c010f0309020306190605040501150804020105071a07030b120d030c140711030606030307 87
    0x4402c100301c81c038000740215031110500e00c0007840e00f010007152100401c50340403005000700e00090784520064030000718040c2d000454903200d00c4011003140030702480d5685108034551700c81b2000341655246c0d08003040da5201c03032242030000c00010a20722910f501d000d03811821107101400f82011074200c94818000b580f800001c851140030940b5010006122040c09080c1024101840c00e40603414146410240300c103030340150b070590743d0840f11403100c21b60f600a0302280e48284d210041c4982c10607003200541398015008020314038500e027808186220301c0d9001a08151044500d60020001200018885072151188001811083d9010421541412140e40306101c8030310b81002040081d000281c00c5905c128107560450703a101d0a059500d01c4842c00810440380100c40702c1c00000d1408883c081a4901035003103003691802c11003d00040855010120080c10002c0803040034000f03100d01180395624214000c01071039004003034001008035501d08050070024040c0200e4800c0e40103015003408103d400c80 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 199973893 1250 199972643 199972651
    0x206010302010509150f1305010801030c091802030f0610051002070312050c0a2607080702131d0f0607050301050102060a0b010c020618041d12181f09060302030708 72
    0xa0280c4c4510012000038040751450b5010342c484140462912071131001e2801400640021003d0380314801e0b1038000454120b0000d100c090900300c4031a8041010340d000d54080f5001d041d100c440406580c0c10382c1c01092a06100090020695028800b00404440c0c40e2000c0070290a0846a42d440340c44410b000960b258040e00018003000e2808011140d004e0091040302c40c801e0145081d102a050603080103544805c0b14280d000f160b00207050321040036040042124801540620f00e03e04044042d0284094044022201b401595413038888918111302e000d55042d400002d8402800032850121682e410b0030b0010380204241f100070f00043c4241c4c0e0300403416942c840e9600d500001c40122075401207541040c62000a5005000003d6003001c0412618140d042c2d42c400350390074030800f14400c0c40c200700c48100188006054018410841031014100c00800c5e00340c201c2810001d203415a0000980c0307440e0740d118180b020300c0d007051003610441d401030904070041629040441c00d44c0380c5104042c0510500074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 199975143 1250 199973893 199973897
    0x415060e030304150c050105070f0f1211131a03150108090120041d061f03110c06040506071b02042f0c33060a1a030f070f020601030201 60
    0x405001207600c0c1041a1001040b0700d42d400305000c0d800120180009030b40000c1506d882d420100040e1029003c0d2052202d2902641d892929031443e460040f6a900c0c03020709807868041e00c40484006039140311014240c4405245016640c580c0383c07441244402604c810b4014a00c10144104070281c09100d0b1804071462007030a0a03036580d038038080b2840c0104100800a48003070310000d0a4085070b616900a0815106e040c000c0142c203640f881d8288040039400c0f0f5146900c108208181d988601c000b2012005503031043c1004601ca0303900d440764642075044900000850380c0500108000d02c60100207590300703e0b00314142030070000307a03040c990903d581441c00064042d03034803100400300715403a110f460182c0c500c0c010140e00019603114030070f6009a0102d4101d00c4944680c42d00b1011100381c01c1d40d000b103145502c007104000818150982a2410300007007055900c16002500001c402c82840c40b1401c0b04490121050ba4a2403c1d04c1401003104019000030208808490251a455000610103040d65024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 199976393 1250 199975143 199975157
    0x60a0302030c04030606120b01120521090a080109120503040b0402041515021c09230a03021801030201030f0506090406111606150518010b090301090c030302060f06041506 75
    0xd400c1c1030b1051146034401440c05140880004946c082c10700c030803030528801c221b5400c6a90761007411440303400001c07801501725044900402d4000445484d03641c203a22140304d03614240b1041800081c1d09040c01ea01440859466003461030411240040c00c0220340903900b00f0301c2c1541019150003004420040000b4000d40e51124020814164603640d400100b0391030318000701c4401e82d210000e4591744002c0f401c41c8000309503008800c409002d0b02040080d100d150b0b1008401698038400c101c0300710a9984c0498000c2c205850120150300d5a02c02340f85014035820a1480fa07524520004042750410044440420300d0300381844159a10080d091390000d42044000c44c000c01c1520741500f482c442c0d54450182601408418820072007190040c1001942c1804144240ca83c0d52051204003101602c081c00c80034ce60800611820009902612128001030000210040702c3c0e9207155400f00c1da50029000b503400768040206000411451560100090303c061000b1000c0440881d800c140e14050031050102c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 199977643 1250 199976393 199976401
    0x309031221090516030813080c10200a080703080601020d050f070219082404050304031211070902030604050907030b0c0d0e07060e18010e040b180105090705130605060a030203 77
    0x10812150701035136402141c50344401c1e42e0b0718100d11540c7c4140c200d81380d01a1a85000160000042851108008040d2211a0554012104032008000c10b0301c0e0704401e901c00d045100400b041000484441882202d000750703200800d060280040c40300a03c0750381198005130101400c1076104055440c0404240b02560302d4040c244000341c001c450504c000c09009440e1000040c520034001444441440c8409601500d4410b43c0b0511a1560044402600aa104010800005680c6142118003000d01d19280c0b5440c0c0b84514050700f03001141d8850051590084140410384c03525210703047e0000c030004000c0c0309103469540c4e1220402c50003001c9481003100030034107603204095078002c000142c0b820b000780d415164562102610100c900490680030300b49102c2c251903d80042140e150507a40d1150882c061541c1d1503440b15040d0720020015010070b4100d8a01c0d014040c0309015050090f100c0202601c0340c42e0506007848802c03075040079400d400e5414020200420303196142220028202d0f403a0150f62951 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 199978893 1250 199977643 199977653
    0x207050f0d0909111303080a1b0602041a090d15060803070804140909072108070b071b0b0c07060207140106061803110118050d030903122109 62
    0x1905101165a0140c8401298803551280e500e000f52403842d1010000103d640b00220a0350103664442148102105400d10102d090a000303030081040354034040080212a9000100c09040c4503400c440083e004602402512040c0c050b581d441a072850200741044000000501844403905010740201e840501e031042a0507035401c41c00107008080704880d0345001078a04400240e1040c855005004918640c90600d031801c4152035004980b940300a108140c1030030006400c880c200c002140d540e01c824545000003a0b0580c01401c4d5207400f40c10704114900e00754a01a11242d081c40002003e1111081c28000062010180c181c00407194103080b6100e031180c2c5407100081c0f01d040030281c9902d001c44c00c1100c00f004d0541284090b94859510802101c0d0b00030000f4448650902005050100711045145254442c00d2010f40d1440010102100d1681ea00041880401030740380540021381c03607150a1041c440a941c091482e6081b520b4107964040300840246440c0494110184441c1e442d140b120341800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 199980143 1250 199978893 199978903
    0xb180309040903030b19090b0303030103030203040924080f0c030f100b0315010e01090b030c0105030606090a030c09141012020d0807120804140703020a090b0303070501060602010b03100509030409020705 89
    0xc80c007501c6503c0d6406c41030452025168984034070040c290034013071030b84400d007000320940f0704a276030540065082605214144c03001d00803034402c11744400050000180003446030a046001804c410020b4000c0f900c540c80c2250820900c041c04501aa002001d9004194000203000c803203000d41490000e02c000907440000d0610340d091407004040c3d8184800420410303800001141290240b250030045d00c41752005040d03d5011106459021070401d200052050078500006d00c0190001482c0c440401c3c3c80340d03204184600b190b000456036950b109100400d0124110039540c00041d041c42d034104181c50280c012041282004000380260a0701c1840e00070411107109440d1340e00e602945004040700a9200201044402c071800e440241900351100180c03500812100d0660b03170050318042e07a4131705144402000e000381900c07690b01440104003040c04104288565000340c54958000310742d410140c82010705e0400031201c0741c00c080d881d0001f40456403070300100315401c880d038400d00541c6520380c40c20264101 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 199981393 1250 199980143 199980161
    0x7030216030b0a0c0516080309061807062d030204090606050702060301151101050a0b10030c02060f1911090405010b030705071101030603050604030f08010605120c070521070b18030904090303 84
    0x5040101b8102c0c00b0010700002841c884c0700005c0888196030707101e840401522004103490886a04002c406001180c4608405001000d494084061031030600510002c9010505810383c006a401b05003480342071054081e040003049180360190804400d90005403503480184039410410f0031204000e52032902400c01403030100c6003007000300624a00b005094001d000c00791081c41c410918100145038141c0039101e600b148501a41c01044140d82c1c0400d0076803042d0740603180c16000c58403424072407007203003090060700c00000102038041e8a40400714184415100180c20210010381d0500802224580c40310950f40e0f02e98100c8009a04880b018005030700504044d0005422402004200030505402c0400240030b10495030380e15000d60b03a0340d6401c4a041c02400c40704001c2e040c9003000f16984004a0000d0840103005100395a0000e4455107c8144051030900d1010560b00c0400d080080c8145c41e1941903102c01c0d1013140c045074406148260780c80f88119000c4038030880da919039000505100760700c09c00075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 199982643 1250 199981393 199981417
    0x506041503141002160303050402030c0d050106050f01030c1e05071e0212030301050a12210207080c03030901080109050a0b041d060a09080301290d0207030216030b0a0c05 75
    0x5640c582c01d140e000101d4108031000b02e84200400081c880d0071a00c2161448003040300010b510f10b005940c204d0161070040e000b40d0789840b40385401d14450b80c034604403111191160300002303204c84c5400248144040c0070901a03050510340708a18100c1500980895203840e03000c109110001020348095030709018160003c1d0503480c901c181c2d01d0115012b1103030040c40e00d00840e8880002c2d104200103a03504c0c030090082a810482540e001c11500381404050490203101d004840c800034048003c01d0302844c010784440005070b01142d030411440d00103001c0000302d001c040d0701540c80c04503003100107407840c1c00c10320a0340e014955640000780d4403810b65001007800ca8005200748500241e5070f0300740d00701d011381b58218080e0f40200c03000700303442a1443c032490318a29440940c40b41960311701821601c1c0c4100e50002c0003443c207404450b4110038500d0400420041c071a00c6001a1100f646040003845e12400b0011142400e80000c1d090000c0b8580c40d0541d0342c080407031000807400c1d044008040701d07640100401040c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 199983893 1250 199982643 199982681
    0xb090106030c090506010e0f150f0903010e0601050a080120030c0d0504030503060406080708060610050705150a050a15031103150f0103050d0503010605031f0b03070801080c0a050a0504050604 84
    0x6a01500383c01150190071700b641d171105904800801c00c404140c0940042c0c0d40250000804074005144802424000d14014811814955084082170a48031603242001d15500040c1c0140814580b0442c80c1c070251a40c00020003030313004c60590b0710b156520314581882c8041d4000c40094400b01140d412550b90b020040014007050800c0e15018219400036280c00c0d00c12400c0050104041c50001350000c01c42d02508000d26191b101c4c581030010300c400020155041010030045500400e2040202920050b100344d14240940360a1120078215600a4011000207041034582d1100c403400400000503a40c01807a0341ca00c04d8182d4000a251104c0e141d0b1940581299104200310040a24201c42c1224060001d03901e040081c0c4c0d070112058402405400040f403014000706d000c6000d41104a0400500c9010034200346480d1010040d0700d0704222007010000360001f005100400c5e0034050a4104002907880781800c60a00d0002505602c003401010700803580d80340021500e56440d0030840301002d0401070a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 199985143 1250 199983893 199983899
    0x6061611030609030c060a05130b040f030807030e1b04150605030402030c040903080408031e25090b070201120b0918070b040f05090417031e150a030b090106030c 71
    0x10620058031540d240c424001c81c00010400403002c02214001d80882000d0510340d541c800341d880c01014041d02969401118608440000b0090000c1c18062800340b0001285c00c051381c600144070360002003149040604208101c6501302001542100208508801402405840d80400e0041011007120a0100604000041c1154000700107500682c000c5c2d081d034080700700750380c00d00041e00d0141c1d00c01000075040000003404205520085c40c2c2041d41e00740e4240b4118101c01c008038002e00c0940317285155001324803910f592000550854a2000003030309001c80a98545030151000d80500c2d04080e06110380244d030304041c0c0e49603920104401c5002002c0c6030700e41c105009810030b4081c9101800845106920b401700e02250700d0f0060740c0c1111075640e44c0d51000b50524091000c400c20150085516072482e6414480c9900440060362081d44030080030200c0380c0d40c0c0c0d038601d84412800703041801000c200b0020782505843d2a240c0c403095075080402000d0325110089180e00600c0f090b4000380801500041c08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 199986393 1250 199985143 199985153
    0x81209220b042f0c030406050a0201113609160c0f050f0609010203060904110f09150a0b040302030307030f02120a0c1a070e041e060b0c060c030f0f060616 68
    0xb4207200d4583c400c0300c400c51203088500a55901c6210100d82c600d0780140f01c10884603119500a0440140f248008034402c2840c90314074031540c004102e05804a182082040201d11504d0340e000300090070800c04080107440da4000c41d0f03d00d07034045c2803030280058001c2c4595056004400100046034000198a103025042c01c14585807254100c00c03070f545004e0351001c0755141c038050096038002c14004010300c2c004d8441d82e079407d00c03140a5142c441e4101c586504421856a0b441c48110711540448007021450780b13260080101240703080e00104101e0718140014009a01c0000c1503030003040d4141040822107403c55400d07850b11074003080308440110002525031699610a00c06c1c601d1a01c6203d2100c82013081e00c55103845a00225150400074140284400182c41c05800c80c104451901c4004100305c03800d0000901a01c0c001d0300500d01c120700008095032030040810079551301c240711084071821401c0c8600e070840c55240180616650b41a5440070400d280da40c0e600300d440840c0403040301210798801d4901 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 199987643 1250 199986393 199986431
    0x90420042103020c0607032d0905120705090a0212010306021305010c050c13020c030c07030506090a15050901060b0c01090b0108060108030a12060b0a020304081209220b04 75
    0x269000d044240090030400e0307070107940c0d0070304500d0745a0060712100350700a09001310f60f04655030541c20020b02580000e101605481012511641000350003e0482c2c00003019059080603403050780552405014500e14070804a01c0c04255041291201358039100c3c6020140640202090034402c4203400c400003080040325402001100000301d8000c0c0074598a5005482049032a000039119030880c010f0a196440c1c25602c140826981d56001403d00080b0100c16146030002c42c80d0040b540e000c03440070300601508201d50740d0320510b000001c1c1841c84e125030fa120441c4070700e40f101110064a80021599240c0203400200141800761215501d80311802600c0340640134106041e603800950742c002288201e0082030550507150450300551910146050484e200301c02c1060b8529116511100031030701c884004010600754040703500540d00c0700d06100303a107420541200c2041030b015404010211003500e404d0a205905640000803010303803070411011201034802c014150303900c03d140c031403070390641440005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 199988893 1250 199987643 199987649
    0x203042105031b0705030f03100e091506040905010615120e1903050703020705090705030402210d120902090103061b0c030e121e01060f081216051204090f0f180809042004 75
    0x24ac0190ba00c60350b4034542c82e103000048031000f16207200001059414139400c0840307128810760002424599907170180c2050751441c001071000403051842180860414010040102c11400140000043c5028800c1c014a0b00c000c1c0181070120218000040c51b0007840000001d10303000c0e02c4032465242041c002001c40c0e2045030200d1260301c07505441000c0400500c0210609040791004141c10b014444003074460188030520400c200d82c58400c19030050b00c5071038943d8021845202c000ca45c07990154414150302c0440f130701c441e0420100300000c0340400c0e4454445080c0d09000d8542c001300183c01200c7c141414288012104a0a228003480d4602d260560041c0c0848100507020f500035900e5005181d00c402403100145c6221400b131213a5582e8039221041c00e030750f10303120310100c880d200c1c0760044082c01354100c2c2d4444455190b07600340781c0c0748101484c09582200d28503490100010f02e00922440001c480f040006400c000d4085940c10041e252980f050188080c2c02414410100d111088a000c551240c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 199990143 1250 199988893 199988909
    0x21006060309020102061b04030f11030705010c050c010f050c0d090306111215061b06060a12020904030f0e03030f03041203090c090c050d0203042105031b0705030f0310 74
    0x9100000d00358481c1c0309a1034460b82c16409000c0d0340d1141031240da440f401c0d0005030f80c0400d0081100000007005680d162140354411002140038201c0b003001c040c00c0c03a0160303000b40e041c494103404200010310041013443e603241d000d00305104940c03a254000c60303444c011010902102e20584000d211020f400208100480c0d20517181404582080b9044622a008100c2c8055221854ad00070482c4039942600040380318a01808172420075803001082d058074908500c0c81f1840b42c022905004850802d0221507002e40700c00c0da58450341484541c00f10340b403580010005810400011408400030344107104c00314483d50300804803501c2d880405000c40712907006850032900c0000206880f2003850103405400301180d00a00d81030711162401c20010050706244424004201c4100b000e50709140c0319201841c020350140b100ba00030b218004100440309400d009426040c0f081c01d0040181c12002003142c100d5489049011944802c0d440c9080ba14500455060f0b41c000c110110410030802d110300c80d0101222001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 199991393 1250 199990143 199990151
    0x220803030a0c030204060912020d0206071401050a05060f010f0905030618010509010b0f060d02090a15110c090106030903140403051c0905060a03021c1505100806030c011413060210 79
    0x340c07a00f81c0480c852071144a0100c0c00c500070130401f840b410003140b51090300140c0b2030081500a5400500c00b513115100841350550540221015004248205540103100c42c03010450f43c28104000740300303111800c0c1c510741005102c60200004074880d62501000380009001c03102c00b424a00d050320480c1000f00cc1c01d08603036281100180444005015544142101421024100e03031f2030b4041c004164410703260031802a808120700c21003919581d18050060400040089221030001c10041211060107124112503100d50525449030741d0b081280c904544040c20001580c000602e0103660300c0c03403011440c48a4100210f40001849004203507000d0555441c1844000b08000240a540b66002c41c01100d402c02c10070702100031040c0c041d40c010031384840a04c503003d60848a28400f0415100e03d21030040b90204809000c0001d0b0401c1c0100c1c00340700404c2c1c180b10303010b40380240100303070b903403541d100000e0400480a05401c000107100c0c089820b44140f07015054900b40e2900006580d0700c0d80880390b8006503182c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 199992643 1250 199991393 199991411
    0x1b02030a021506090604020a18080309090108031201300609060e070e040b0c09030d020106030318080a0602033402240703050a0e03043003050d02220803030a 69
    0xc0b0104500c284801441c0008948030380f400d0000941080f03d02d4801d01c06850084840709490300320500c0101019402140c0c2d41c90900e041c00014030040e4080c0900350b1061011000d2890360411040c1541c03000710301b180d29241003244078103030030345803d9110355022409212042880340c6030704204039141c05500c0a00011803810010307560751446108603032070040910086400140c3c455095a0000104c140341c500b80480ca00c002810b06a19030030100150303648141c20010590400d4400e0807401d000005407800c240307469074050312200c0c604001400d4550000000d500301104c1010503140181d03035038003a4419000850310b048520148040d0300007500c030720350b040600b00349502c40e403150f0250f451a5070301181d01d0350802500a42400b130920007c66490b9150000304407001c0014100400116800203000e0000390301104920b0000e19207050301c081142005008a50401d045540b11090303075500503911594a01108052004100000741070716003403000241e8400004082c50151855a20401c14448 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 199993893 1250 199992643 199992673
    0x190504180609110a1b05070e0c190201050601020a0311070b0c0f07090504080a21020c0115050301020903030f0a0e0306040b010501201b01030618020703140405030304090902041b02030a02 82
    0x1451309070310005080b200781080c0e601c000c40f00120341d0343c85202140e11075502c41c0001000c40310708484c1040c61040110301010700d4102803000e0000d00d00790340004c00c09070030b040e80000e44508090310050140080f002010a141e2801c002d400c000380441340e40a900c1c1c08080d02d5441c2c80c0d00c401d0302e040c5d810b446403113404100040e05210352030003941d204c03ca07149410180301043c0c03004116003070032401800814600f8100c8580a000400c0408d28000c0002007000c5010b442902044150b000705019a10500c01500c01c0d840001c216030002c0c000d90100e6482d142c101404a54100840208540500400051100704482c8040c0d60b411307150300340c940468070300003031141c0c2c0c0c00400c8140480e45c090b8400301c050240704010a0602081e0301c01171501080c0035032942801010111409807400081d90300194850605901172000900c50141808051500740b8040000e6070b24029405801d92403039880d64148119a1581e100e481900c0c080c04208070700841ca210060746135007240c0001405030003641c82e609903401c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 199995143 1250 199993893 199993897
    0x8060705040302130f05070207051809070608090f030f040603180c03021c02030a0b060a0602061005040203101d0103020f10090905041b030c03061b0519050418060911 73
    0x848150355050615145400304600b10b04845109403101341d9550300f040d2113003424002c03944200e800b600200603040c501001d00002c0e04401050491543c0d0040c14400e10203030101e00802142d4461802e0011a100c4a080b90304020310300700c1c452881c0c40300041060b0007243d448041c200301d844a40301046a009008001404420002d00013055816501000d000500d440c040091850322041203c032180e4102d07a0100e40b404080700010784007060b0b5202000700500d82400300d1000341075188054002d03410105000060440381c0e000d0b091007290080002100080b90f0b05030300c402010101c0c41d1580c201d841c001412212207003030005900923209050881910704120050400012240c1d0707840503042e04d030800c034900801e006003003124881d082143c2c1d44039003214160b6280203580114001cbc0c5485195142150459040c1c01c0204261a4045e10160070503400c40180d500c214490107600c10354020350501200c00d40b1880e001f20b80c16002c041c22205a40206078085030540c0d0510008000100f28611000e4440c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 199996393 1250 199995143 199995151
    0xf071b081c0f050403120c150204090e01060602030a0906080c091008240a030204020304110303040f0e071b02211e010b0f150706020d09060f05061005040b0c120301090212010806 78
    0x32546c0444a417120038819a13168000703030300034007203001da446006510200340da10641c040100c1686a6202c01314138142842503900a0031540001d40c6449518400035104001d40e200c2d20060200900000700c501940d001111014880144005404290100b0140c4219400d6446c008542181d40c01074802140301c400c1c0541d40c0b08001c120452803465030742004060340c401803080750f00c00718051090805440420142c0f028129a620301d014403410310020b81180c0b07800030804003c0080070541d4089000c41c010211421a03015281d403031251840180c0d5140c92117002081d07a201d88510480896a0b40b1403075000c2c458408040c000f0300142119a040161807400c509003240d00170000c2c42c4071010260311030010074005101c0c1401609080003441c41008a580b804d009039040c9444814407201c12040b4481c03503a20950480340c1c101203010106c0018070a0003103008403141d00c140001d0024141000701304106802e40915026982ea68603041124040e40024594059025000002045141011078003502c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 199997643 1250 199996393 199996403
    0x110d050615030a1505040b100e040201050702010512012709080a1b0f0302030d0e06040c03030302030705130b0d050c0a021b010c0b070815060f071b081c0f050403 71
    0x2080c1c446101d803494a04001a915500d807159810034400900c2c403003011220b94210030030000b040c3c9032134100f4561022004240c3c0a116aa0410501c46480c07242c041c19005178080c60540d0b16000310f0701c0140c034284901444100540d001c0790002030b2030300540051210065840c81c1c0c0001c20a100c01564060700e00c0c00f070340103045100911046030302038407070990060b06161100707110900d45070315200d446581030143c50030f6006070400205000c3c25411030044801404d440300003000f041c0b905817640079000b03040e07000080806400201082d100d900c0780b0195000d00c003810545141c5d041c0e41d0303200304400d58004060303900c20781d040c5400601c0b101030784000e030740c00700d036240d0080d001c12940402c034000707180b11407900c841c10b102e0100c1d03490020800d00300300d0520030901916010301a080c040e10340c0c41a610400f0505100c0d1108001a0821101c1d1200383d4100c02e50001008080030340c41140704402080c40c0d080b2812510a411081c1044200b260302502505240d0300c0d4040c0c0d188801b032044949100364000508 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 199998893 1250 199997643 199997653
    0x903020303040212150a140112031706060f0d090215120103031107090f020a32030a0e030f0d0c0903080919050402190e030c01081b0f030f04110d05 65
    0x2c094148003020000d41e0342a08241c03500c0c440b1480a010071701c07200352946000a60f98032504900e401410040501400c2c840608102170340c050b9034000c1544071810101000400070401107074080c0c40340c1c4c003541d0905540300705103600c0f4000c1010040003400c80755016413043d0b0302c40c1d071013419050b110812294001c00d0307170a4101e481d03801c5460940c0d1840c082c1d000c00c4418442c050700040d80c0c600c079214182803d05071240260761400e0715407000741a40b400040c4410560904804400700c408240a001040300700071144a8580e90703081120002004441c10404844c000090280ca04150303080c018856128040c004020707060103840208d81e40303001030000903d1168100040780b550b141c1603a4503e142d404404008034890f803101d02040036a080094147c01015101186080c000e81000d155504182d0540080c1401e1010ba0f00082ca9028058884180341d9180a07100842803d008129584801610001aa6030519005140380a60300300c0c0c0075143d0b5403200c102c0700098500400b01044003900180105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 200000000 1107 199998893 199998901
    0x30106090603150e0304090e0106120605061504050a090906090606140103063510020a09090f020703020c010e0117040b0919030c06050a02071506090f0903020303 71
    0x202245080180444558500005690480f403010700c0200388230010018460041005070080b0380804410300100381440f205800031402a841501ca41080096010001109006600980340d002d0b0034440104100070b0203400465406025031030015001c1120360f43c0e9070460307503580d1110407d40d2400912860560f0148211001403111a8080d00172203001d0f02070420003082860301002040410503100701219027004030303c2111003a0b103402c669032803200002800ca1049071041000560501000165406090094603445607041c5c001b800c0e40c01100e8010b40f5070b1444003410790304004204007020310b01c0064964403030240d8054000c92526040c00c08070079040003003001c03107100d514090840003400a54001d44180d111a041000002c01e9118402501c0203803240e130384054160b100b004180c50201100e1f074007000449818540801c0311000c09a0b0210079141c5010010f009a00280001 = true := by decide +kernel

theorem cover : BRFrame.Cov 199820143 200000000 := by
  have h0 := BRFrame.cov_init 199820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 199820143 ≤ n) (h2 : n < 200000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
