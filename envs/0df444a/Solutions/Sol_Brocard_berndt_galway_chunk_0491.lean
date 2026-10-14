-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0491
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:04:55.905556+00:00
-- url     : https://prove2.me/submissions/380db049-14e9-4820-a620-b10cf64f9683

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 88129497 ≤ n < 88309353 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 88130747 1250 88129497 88129499
    0xc140433090306050f041106090a09150302040c0206010b1206060408030a02010e01050c04030203060402040e010e03031608011a160c05120102030a050c1e090a0512060702060a0b1c0c0b04 82
    0x80204080410b00c0292445420080400ca00e140c1800ca1540a00e0707100e914000310400c0e0000f031100a40202d0034441d4842c100c0340c4001049481402401d5501140c28441d5660314103510401c400c55681c100d001c021540800014008a41c920044401100c01307680f802c1800d41d100c800043c9580b003290400465400046028090190150806840d84d00094001c0c8420f50390381da92011280200d01c0040e606621001c00315000d414107034442910003414100124440c1d01944ca014035650003900c1400b05030007450401000030390321024140c0501a880080d8100c5907240907a000c50380260042c1c2c8000940c0300c95180204524032842038003c3c00068260480d20302c0c00f15000e4000e42046582d103c0d81801e200004013841000411501c0b032020b001c90560010000810000b2290401280b07644c0006500c60086502d55441d641c009409401c03038014140c070b182c03000e0000d04140c4044c2c50040c0c1542010400704095450300c2c004030b40b800e02d1500c0012a540242820506a20154408070b000000014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 88131997 1250 88130747 88130849
    0x3040503030a0f09081c06061d0402030406090611190f0c02010f09090510050a120f150e060f09010c020a02030d0f022506090e0f011a070210020d030c1404 68
    0x21b91181c0b10030b00b0100012640d5100941d0b001c030b501082c000000c00b80c540c004000c0e1915501850b00305004400c001760856003aa500002c44400c4503032800034440118034100e0040f07505401409076021391414072040840340602420581c91110008d0602421195070f6a405215140d00c80c000c10b114070081c002401c04160441100585000c2c46018401c050340202e11217110030500398405a2240c0c0304081c0002d2500c41c1c0c4081c00c03100f618408402d0322120712283c920b41c1084400d000780c81c0c06001070520f040601107a402c4030822035820041d0b41011511001581d0302148100c6041c100d402e10804142e449502203003401d03001488180d5108141042180404038031101e182507821030f4640c0d10515031100c0700d4119100301107a56855a00302c0300300511282c0e03120f00345540c48080c00184e1a00300352559001a4001c441c0c3c801140060b032000040111031070b0706000350340c00c04103d401c189d414034484004410492045004404012070352180c1100c100c650322a065404016254107844440c0c0c003d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 88133247 1250 88131997 88132027
    0x7060c03051b031c06050f03070308030106180f0e060f010314070e0409080412030e010c0b0705090a0302030a0f0209010504090203060121020d03021c08090a140c0d0f050d020303040503030a0f0908 86
    0x4010b5602407c03c1001500240c100000d440c0b0650340c1102429003160300c0c1460072150130b150034030800c00e110b41c3d4081c00101403003d00c403d0b070064000c01001640c585011010300c10219603030780000d81003504010341c25034208500b40500b60800440c1c07414003841ca02200204018100006005110310800540003070420b440c0f03021030030403502c2a501e03030940d40680d4004580e03d29502a024162401600104605601030710082074420f10140000c1c030307002d94940010b403c08101b2241940d00050714504041180303840d0b805c00b405090221020000807120703402103583c41c1c105000301c0032040807140d1004504200c2d022104070a07a030080007005090fa10380380007920740c02114600c081d0141e180c0c100d101414000c035141c900c40c2e403500c4020202c4440340e80310040c180829021641d603c0c0a040000b0000c1d8588031511a641401910b801c1ca5600c3c0d00c0c0340140c544044c1c0a03030346045400601c207000000780b02008a03900041c4603a004180213000103880380081503000070003840103100098403c4006003034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 88134497 1250 88133247 88133249
    0x151e13080307050c0f010504092007050c0a06110d0302090607020613080f0105130b270a170412080f090a0603050601110d0504050103090312021b07060c03051b031c06 73
    0x1642501d414000700414803075440f840d01c5c0942d021550503c414007102409034454900c82160007009841d0b80030003804060385601100e402e0b12030750080d01c60310f40642050405407004041900d015030b02d44411542d680e440b40f81d0307802e841c03041540015110300540da8a0303055840040d0001d00e00c80d6104845451a030034003402d88500b000758000d542083d0044a4180f00f028071a50900e03050008824195840c860080801003150700401d000c1602da444424200342503010302d01c1440000c251240d6a410b168501407149030119228640401c010b10005640003011518294041d001c0d0b070700d5940c02c0149024600480c0307130580d00010004800240280e15400041c090042038858410004541c852151200c00400c83c1d200400d0003088104903d5100b94002d8280342e0081c80e001d00819400c01d400f0f01642d01140040c003c0d805490307080c2e05405401c0c03220400521403410010306514a83c0e40c05011030040074a074040d0544100710a1000302401e0003215009848140da0403400640d100c14a402080f603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 88135747 1250 88134497 88134503
    0x80a05120c03040503040b030406020c1b0f0303030103080a0503071715040e03072003030c190606150906050f040302130e0c0406120f0c05030a050307060b151e13080307 74
    0x300d0110701c2201120701100d0107903801a024601e0075061900102540d8000381044500c1070b400c001e0343c18200024840c1c080380c1c1c001e240c00705d10005038000030880701c4e25103100c2d007910030f8104000401c0000d1240c000c0b01d015007001c0c10400c1e180d5440c109c1c2034403c80301640c000c100c003846003420030ad00c1124110014075884170443c3d040007400c10880e1655561300801400078500851886c8040e6801e00318000140c45000090840c0e1034407032003010450078041542028440700f969045a4000c004c071500a54024000032842074a8000401d01c00806c5c80410f88035010902c400065518290582602120003454002c2c2200302c8402003903280d100240f145152074082c5000c1c0d0b020300c2c80c5a00e030501031082220108208480500710076194003084010302030b82101d5072011302c68000b800362400d0003a1400c01c0c0c014005161102210f08080e801d1754568040e480c421080b81010310314000c565410344522600034200e0b0a808140850301100a08c80c005141020f05c54032040042d020f41e0000c002c00500744 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 88136997 1250 88135747 88135777
    0x11090d03020a0f110405070504060503060910050d0303050912030603071217031f05040606020d080a09140607080907050d140c061c0609060b040302100201021207030b031603020907050a0c080a05 85
    0x241c7c961040359039010750b00805000401c01c00c041001450a120340d44d400903420b0702907450183d076844c00500c010200010403000300f0b848a00300714240da810b0003003940c1c0d540c420500c0c919524041000980b00c105c58000c800100303a0407220181480600c5402084002001451b140e581c20701450000002c0c040d98014014408400e0f0003003510b050034003403a000c550301a0003c00b4505c13118803081c0c0d4030300c0d0024403c01e42142d07164400d00c0850060007846220b0600d044c042d1120342070000c40146542c0f001404903c146d441050200100e0302e4031215464400d0300a001388a80c3c05c00a041d060403c52503929995000f500841c001510b0343c000c035140c1c1c03040901d6100802070fa590300c1c62000d094410b248501040c002c1c0034001000075090901907024030403124400140b4098a06111a5040c041661034100107680c42442248074102003024025680340150513801c010314540c0000c0318100020f0180b4104440489c3d442d400c0360156443d8074195520001142d11007802080040c0301d03070403001038010411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 88138247 1250 88136997 88137001
    0x190f120815030a0c05100c06020403080a090e070f0503070c0506010f052803111305010308032211060d0e0601030602130e04051b01050d050f010e0a11090d03020a0f110405 75
    0x85000150301460f5a8000d03031400005207803100300b0010f00d410501c90b1090109040d01c00c00064182d00c000e2018510644140d0340391203c0300c0008004500c560000041000c01d081446030315a0170503019525a441071805d42c0e502d035903581c400c80b481174091200502030f00c6a18008145a04030548407000d840c41a80d1180c09001011a01c0d40440c032800d0168803928540d56051000c00c0542000c48900c10018000704487c00c1d0030340361541120026441650480e0012052080e0400901729020917001071070103c4a0b100c96039200e2103100c00030a41d641d4400c101c000340c4092401056002a16920b000c4000e82d4015030b5241084000395000003880b507903a290444000c01c0f081800f200e190300507500310303000300541030b0b0321140036100440034450181800740038482481500d1039070154500c036200380781000300c0952400c420881ca0b840b01910400980c0c5c200581811821104825600100c1044505d6540c00049040c146d00300300001170054503516110b40c0040510409400455900006840070032090b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 88139497 1250 88138247 88138249
    0x10c0306080f071a28030f110405010e0904060e100e07050919020c01021603020a02120c0d020d0c0306091208010e060907030b03010e030a1d0f03190f120815 69
    0xd0000f074003032643c00c0e403480084c0c10100e1101c00050038104240e07001659150030f600c0c0305450007041c120320000010761601d2003074034000e185e8001ca101a030210030443d07040c14200f10010740b4007070700202950b0080c0340e4500028140301094204988124075102a01c1345010491483c5001e4454003508078418030800000003124200f81041500c40c8105c078050000d0707507a0b41c0101364041e61004803081e18540d000d121100070f111480c6034460446100b0780090002301010f206100e440f010440880138203421030f85444015482d0318003d0880da43d411510801c0310742039880d1000f95a80140c0001e400a4680b40295080140b60840550075403080e80307900764aa0390f240003020f0022000c80b40260041107110100d14142e000b81c00041455070003e00204a04c084c400d1814a107811200c050744c0040c40062402c08503541090380050900390542c0d0440b000908000403d50b01c40b20034102c910750b44010200c40c001d109110b4003040c14542e11a40c014000036000702c0051542009940342c13101ca00108140e8892 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 88140747 1250 88139497 88139503
    0x20a1106070b040b040609060c0c0201030f0608030409361505310b04060c09080f0703020906030a060e03030103020f0108090c1002100207080408060601050c0703020603060f03010c0306080f 83
    0x20050303020b20064003d81e80c6555006100d04040e204682c156120442c20000035032a02a0400390a12555800028400303800010191103803e4445a00c042c90014103000401d80802200c040e2600b600300862a04034a034100b800d18038107420041210703c0d51041000d01d00301c038507854000190080304803070303a00175210f024a41140d10559001d4001480b440b0852007942e50008850034044811104110080702c0c3e480751040c00100700c0e01141d00035507405010200580001e50314004e8203900e4010041c01e00f506403060f40c2d0313490b580400303071050761800d0024040341d4040000d070032100e50144040c4841409813a80640c2c0790002e0000701d10424428002940039442560b803a8420070500700144910030000040c8503115482032280720460003086942c443c00d0413507000a0601d244180310721695036251104850400101400c1e071410130000308041c501d00600000d943c0b003520340403200c00c3d07500d403201030000e6059128402c1031509542008865801e960301503101030101c0f10440166100034003001c502d0ba031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 88141997 1250 88140747 88140757
    0x17090721060f092d0615090504030c0308010807030803010b0d06050a1701061a030f060109080f0f07080a2402160f020f0f210c0d122607050a0e10020a1106 68
    0x440b10134000c20003c10065009160350850b0204982038a42c0c0300c0c03d401054417021101a40807440102285040590059145005010501c058010b1609564405910b48418402ca64100c68040b4010503040d02d69400b0b40c004140c001c0802094680e40c2c0703d0b0075110700c00700c500110154a01000011080900006980300000b07400c505c030f00d10341da20030704140542005001d41d410044c100e42e010800c201c0800107040c650100400030100342021151285c540310694222440642210032000c2c00612080307100070040c4034800c0a520135071070b40c0003200020700824001c9962a9080403080303080c05004009218544d00a850316035200c0076031800d001c0712800040c05150403c0c420550314036a000ea04807a200892041c800b82c86618202800050348004140425101d80c00b4007803051241e0f03074005604042800449980d80420001840d5403182020020300820600200240004145205000c00721100340000c00701400d00d40a800c00035610004010200d07a100c984075006452880c040c0140d034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 88143247 1250 88141997 88142063
    0x30f06090e070801140c250c0b0c071205032508030103060504060e0c150d18060203060a1205060f04050321192a110f030a17090721060f09 61
    0x391810451131b14002110380351000091040d046d07e546000020840d4980704010030800c68040c0e02c49000d4a5600d00707100b4290310850315880d100020500040c4040240c40300c9440c400000e4110101c0c01505030545078842000815800001002000b0080c07a50b024034050342c0104420080198040c202d1075969004400059103d4502070900466101c0c000c02007400341c403020008101c00c8400c42840070800e0900ca4200c41403038002c01086031500b0492a804020280d40100107081f16042d1921034540070007411031442942d1483c00202400010001c0b524803844041d070100003010b0107801340c00f9189007a11100030704465007010f51400d04e02030003a0f050001d00b058911a400108000b04d942c3d4410405526050081c1001c0a400000c0f003071002c500c0003800c1c3c01c06140d4403011004000c00b8000010550020019031030140440488001034120036100d200307040c5900551510001901da4224a5000b000d0f641000c1403403100840a0b04040042403040f0b4500e4940303860041e40e01040c8c1c4a1034040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 88144497 1250 88143247 88143271
    0x30501120c0302042c010204030b06090408070204050c0c0f0a0204110c060c1810080118050f0426040602011407030c0f0e060f0409090212070501050a030f06090e07080114 75
    0x2c0c805450302d90f0060014590b070150b6031500040e100d002e001c101d20413801e0094107035404502002070224000001303034410070480e0002881d2909a54804d081c0c0511030019004031755035030002e0701044030f00b8100e480507550034048502c00b00c04c008450349c2c0c0c8d0401d6a000c0b805036042c41300c6152207503184000e0b40c5080c0e000c00054551076035200d000f00c3d070076080349105100403603100b07400480d10b460740c460074194600c03140d03070700700c4d50350304080b811200c9058030b02800e40b40524110800c170302e40402c4c04100380c205a0013070881e034021201550186860042030f1003090441400140044e10b2a015403242030000c1c1150754201d0141d4500d03034107030308803882102170f140820300d07030411091760741d00c201e614a04170b0708001d00b52420b04000d10100051500903410900100e580c410484055180c401e0ac030715540d01a500061100605100008000d0b0140842d00c1d410301d900d0b4500d02e5a0b90103d074206030050403c3e49400c10200e414207500d59510b19440c8030764002d5518086032040034075150000c2501c6440c80a40d1 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 88145747 1250 88144497 88144499
    0x4050c2221050106170303091c170a0605060d020d0f090506061c0b040c060e030d02070902341e030c030f03090b0c03090c03010203011809050304090903020d030501120c 74
    0x1294100c0280c120700702c0d215541c400010514803081103100304c0b520000030003151039151440980e89008508007840c10300500324400151103036449030340d84040494020511200b41c90302c0710104041e01c419040b41c2d0b444480418610740b403070300507805044800081242404a17000011040c2d08640d0f29840103440b6402c80740000b42603091001030404442c0012207007003100d084917220388010a80564003100c029450780d10420506900ca62034180f104421009006400c20003440130b0340d20500d40c4125490b650700031a40200c1500c030b4190003021142030b2840207140d5a840e800164102c80b151900321140c50042d80704200c80002070060300c414a0f03250310780001a1940c2c0d00c0560b030100282c0104000c140d1207681c0000002c0d141c4081a0040d1300e0001219128140410050b040c030300030b81c500a00a030302c10b00040040141d40710420805109001c00021007000030700f400c0d42035208580001910a060955444c02c140d0300142c104940071140d5002c01c5981d88400220111400b0070401070f2030022080c030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 88146997 1250 88145747 88145789
    0x7050a1805061b07030803070806041d07061b150c02060c04080c01051b01090b101d060f0a0305120d0609020403020306060907020304270608030a02030f070f0204050c22 74
    0x1203543c07034850b006422a13400703994a982d6241603900464030400040c12904c103200346030410340100e60203102e001d240c1751444411a110117030b4038951441a4000c001d50038000e02c80c1c1c180c036071405a29070758001c4204114030030721001403000351803000c4068006204203400940c00c80807402c152000c0c0c0d41c6440c05400030010310001151680c00c50300b00700840e001c181c0c40c9092016400d1084040e074510500345852546030802180f051210281d00031003881040300e0680021038060312805030301210460b42883d0f5030000701c0c08212100725980000341180b00e861922421100d40788060800301920842c00e20015840f01802c0d000e0380150f04c0003d402d548000007081c09894080722450307106401303104a07400c01e07940c0c0085206246a140d0718a50b4101071103034503026035480780a1707140a8420803008501c3c007114424001e54900c0f0342003102c030304031501040f600100044a180d980a0a400500601c9507081035580c00129038000e000ea40d0402989100000501c10a8162202104e440c402c0303034100007001070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 88148247 1250 88146997 88147027
    0x40501020a08070623090c01051903110f03071205090109020d150f06090b0f0301021603050304050304031506090e06060a090e030d0e0a021219021002030d0507050a180506 75
    0x16007283d16545600c0170006100d800d64440e180d0f4220074a1110542c10510701c0300e4144003e01242504000c0b0402c0700700512803004510710303241c0f0040d190010700c41c01b507144216000d019102c540c01030b01d00004240030071650310100c05d04240c00284420070064583c0ea0049d0f00300c07455000020b410440070041c1c00d000c1000302c141100c2192a0302ca0100d0b0051041c401d00b4111542608141406960b600c0c2800c0381c0d051890300103d41040030780c021403509802c000c20b41c080d0441c1c55030080c100f04001001600b0000c091090710011940440b101104640418406010341014020384001c0c51903c001d01d0700541c000503169000d0100501070540b554109000340024101d0b032040042d8506c02040181501c0045101d06082500c249000d003c0d4076009104000440c40f0703501d0303e130b9055402181a000a0b0b412095511030185d0b040fa901748416408a605900f10b0049070b0801c3c4070b0030328200c01c2009072a00030300280410786103551000380b84c0c0784000021024815a016154001e1014007000c0403d15038a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 88149497 1250 88148247 88148257
    0x806090a020307111c120510031103030f0c06160201090b06040507020a05061306050603160501080402120105040507030b0108030f07151407090503010b0d0803161e09030c0902040501020a08 83
    0x380c136100e0000d40100c600a840c0ca50185242000c10001c2101c08010a0344020b00640c0140781031070034440c40c10900a48451b81140c0e0102070b01410103941030788401c0c1d804004480040c2c980c980300e9903d9499200074a6200c2d07004988240749004ca0a000d402500c3c03044c8035500c5229404140206941c031000140b00c01850001d0050b0305620403070714600e01051081240303c7c8290121008000d02c09060710f0444260f9001420031401380c1d1200d140d00355205070088996050311020328024480f540c4e02d0000540c070440c0d1421040c04c41d480c10f420702c02844400714074076060b0b900032061390203e82da80ba044980d1b81d00c26200c2c540328010307081c0701140c0018001c941c001400c449048021500c80f81462601c05403000036503030540031134510700c01000300d801c0a0007440f60081040311103030590000750b00d50046510004003800301c000c602d20203c5280c94000c1b201000884a0801e00210044004002030480501c6000950700c007003895000081b01d141303900840c0c09480701070780500541c1100e5505e0101ca5000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 88150747 1250 88149497 88149511
    0x1120204111c15091406031006120602070c0b1204170307020a080313050312011e03030e0108040c080304091e05010303051215130b0112060605030105061e1305100806090a0203 77
    0x40b030a00000d10313500c41e004108860459420b100e110742404000c0500d0401141e044144641c10608100a1441160401c40741550400c0025a9032090340c44c014002c0000354000c10240200804c4031080c1c100d10301d00580c4960700c102c00704103414401c407010b01304600007195207030010b03170141e8404130020b914903001d9500001300014208003050580d80d446e046806c41d2400d005170501c00f00040223282421104030a400f035040d810006c0040c1191002000c0188048407a414170180c0382c08102001080ba03241c4000300f501c2401d6a40b01c5840e4034940b00a050b001c8500c2a40141c0c000501020074024030800381200c1c0d04d9101c591a080d131800701d000450030010404d0180300d6615003034201c3c03a150081c9400200c01d1400d03000812203d010b001501c1c1102210031503074220f18140341070000b542c02c0703002c0707074152103044030160317200d5014000d0900d200e6100c0d010455079031404240124900342003032071a005d4850443d0965510081d244046800c1c10086603499071000c1d01402041d0015416401190000b003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 88151997 1250 88150747 88150781
    0x90601050c01020c010513230c0405041a04030503010501170906040b0c130608010e0a18110d0204060e010302120d050313030e120717030a020714031501120204111c 72
    0x240c1c0f2209135084030300854407440c0503030782543c4a104203d03100c0c00860300f5907140e0341d0060303d00807542506c6989041100701d95016568400205060003842c038403030b525000d01000802000d1805140040981c0c0080c410f19010480083c5900d04030004460614403074103c0754010600d560ba103480e541c00c1c0c003101404182160750104512148507541084103400341030307140c642e1a125450003900a40d031420003003841c502c0d64a0409103200c103042480908030b0580c0c1155a813110028031400050507110220030007035025161010004552004080c114100c83c000c0300c81110503081111140d440f000b840880e040069000c1000400c0c11503890f0f00d002e40c55000303140502280c05148046484170703030158459101035100c41010003010440c43d2200c055807501314060346c145200284041e65807102c5000f01c840d214140c004142554401304201d81092020462400a079691940c003810340e4018414160301460522506402003420b02d42246d0403460000c010491640c0341d02d900b0350050000c4c0d004032003401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 88153247 1250 88151997 88152007
    0x1401020312040c030b0405030702010e060c0c0108040320010902040609020703090303180e130b01090606051b120313050c01090e0103020409050f030a050406030b09060604031401020f12010e15090601050c0102 91
    0x90000417600344260320400c000d40e900c040782c0c00054100c0d110300c140c086c803407101000002c60780400481c56a1400308c003824a010b0540301d5107000e40d0303007110000310010032232104842d020752540150071903400300307000350303000c101d03954645061506900c507200c070140100da0f4400c0300700300080c401c00007103407401c02c480310b00361000ea00d48901c02000d08003600c20310048980b40b0300c0c80d010312035810a21070040c80359000400807240b80a001800601034824105404030282e0780301840f000d0b0501c1a070a031503e002140c00e6603858550190012982000c1050b00d140c421601c01102950003258000d064880c102d0b0324071a00d83c41c6070300f00405802d0b0900c0c03c43d0303c0d000d40006100c07412001c001030508091541c81d126192400c03d040101155440301c2c406114030600c00c140316081c0c6410040b1401d4a4020591005070a00c0e0340c84240a886820300d20b900710030700003420540340e03018400c81506941135400c044049440365207800741a000c9036030215500410380800301d1000d40c090350041164014450000d4144 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 88154497 1250 88153247 88153253
    0x6090403020d0c05010212010b091c02090114041b091508060a03080a050d0501030c0503160b0d020c0f030d02030709090207050d18050607080703020706110303060405061c1b1401020312040c03 84
    0x5802c0e4400b007414580415620030920f4030304940c01050040c1140b608280b81c251700042c0de11401072041c80b0034000751008001150321981c02180c000c2d042c20381d000010402c2d4078401064940c00380b1038084d070304104040301d9042901c00d4641c1800707244000c180c0c600240c2540c036105426403014004406010b020002c100a50700c2502965000718010310110391030612701001e15041c1180303201380041d42c2d50300e80024170114a800083c0c030724040139660700507110303d011801180382ca1084901001c0311700c4042508244402542c0007584280f009980750100c10b03503a0210780b0142d0040c0781d8010700580110010660203486014001942c816101a400d40315a41e031010030020f0307004201c03d07a1914000111078040c141c04005460003006146400c900b441c80c0007084503184e0101500c0603101c0c5071510b000c56040c0e40c800f0000c07903016626000d5480030100c81c2c50f220005c0002d00f11580b0600a0410f0001452802e608036800484010f801440c5441088104403d82210081040742d0500d150900071000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 88155747 1250 88154497 88154527
    0xf0403120f080c03130b0f060a170a0f05031201090f0b0a080d081902070c150509090a0f14070309031e0507060b04020c0d020f121305040504020d0618020906090403020d0c050102 78
    0x7d10610b005000303090401400f1301104040f150004596020391460030940818000f030351a440315001104100c07031403518a00b05045102e0b01218a001c2d421050000c9640d24907580504083c665904080140c0b4200d1014440241040e2040030041c1d0000520080098000d11071260f1080c0700c80002000400003071b29010482e00043c01c2916494000e0605011400106e25000305000890400c0360421061000061072070b40020030307000c0c510303840314210320024000f40c1001ca0400c02101c104c65035442c00001c02001840e0f01030301640060303c43e074110708000034103441e403140a400c6070380d440740380402b541c413004064010423003229000755081014030303807883c1c00748002c4506880315805420780380c03440c10b0f040d807420961030950020003508000c03480082c040b981c1844111581130b980030031290786034000100c414000142c040d01040c03c0c82e2816004114190ba0010045e108480b05000f40d00d606040c441c00c04002c03900100580e02000c01c250089000300e0b002e0200d24400c0c2c00151408092004803d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 88156997 1250 88155747 88155751
    0x5032502062a01111b0102030f01050607140703110306060a05060a0309020f1215090601060504060e01031425080606031f03050312010e060102010212071209080f0403120f080c03130b 80
    0x4c9014000310700d8110704000d403100c0c020007896402c003d601f1402e1030000148640810320840307205a0001800302d00700900313111108414100d0f0404d5626040c1d4030b0402590204100c09824030134000c00d800035072146045400d0300306841e0003a203003c0c00c040700510150020000d441059902801019640055580390440c000d44002400c000d0084900c00380d02d000c00034440580160b4158000b18010701c8031079401411369044481b1340c6020858000901c00680003008001404149014100100001d881103c8402040510a1000e0348640f05d020344d01100c0900c0c5c1500e4070782e80300d01c04002140700c4a0007542c01304500d81088403032030700f507540e40c0d50782502c0c1da80300e039490030030140300440104a4400e882e03043c15030000c4280025072030701200c0038503401203c0e0002c20303035024001c0d01c072204069000d4940c400b15105d03500c200026599549060034492642062104075500d022044e0700b404818031400c420318005451340c9455120340c46909286030182c00c018001c4410b4038070b03000384c4008902e901c00118 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 88158247 1250 88156997 88157021
    0x60705010609020a0327170f0a0903110102010605180705040b07050d1704030c120203090312090901060302070507060c020609040c031b0305090c0108090705030a05032502062a01 78
    0x43e130300c040d005005010307100011a40c0c40d55100030403400c3d1314142c00300c070401c41a0f40d0217110481006158030100300c4501811018244904005c50514503e50b0007032900c00c1603038014076006090300c281c00012800d0381d64038002d240d0021568103e442c000b44514008039040211420511305003038580580c403603590042401500c15900c250103034540503800c405010643c540c5206400001e01d0300c0d44028012551604c0000c2a00e04005210f0504601c24030942e291810010140e91416601e84086040ba400c00001e4620800e2240700004180b8024421142801e500c20040c02c0f00c680740074000d0b240c108407018141c2c0c06c00c00c20000d0700060756440c4100c5890211a803000680300c40c800300c41c0340a5400510842090604d05003c2c480301540024280c070700d0510920f410441c82d901e0500c01824005507600080d058400c12240703100b040030110203440100c0980e0919180c580c007115207142240003000000c2d4002c801044560b500956070745002da55040b03840058100e03105c03110461400c485c9214401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 88159497 1250 88158247 88158251
    0x703020607140a23030412030e0a03080c070e0a0203060a1a130e01080609060403020304260703050132040305070623010513050402091501090305010c0c02040b06120a0209060705010609 81
    0x8640c1c2c02c02c4c0321494500c420907500c0103605090078850014503c003c02c110140134050f0049520166540d082c0c211809140c0c810201034540c40e500c2042a600e08442c012a0040c05050001440c100d843e442500c0c400d001c01040e008040d860485008080380210f0720f1700488a00030070942c0a058411140c7d4001404420280b03a40c0e50f01d0040b00c5400c02c00041d0844990303410103014030021075400401d4a0580d402d16200c2e04241182c0c0030100c1003c036600c01d204201d40107a2400105104065009142802800a812001304001d5150002200000510352401001c01c03020501091184014111991040c4070001e10710000b030342d144281c0201c070005004411003500040c0050b0400b070540504010101e0020301070b505080d0b0020b00700074001081e5024006031000c0601580c0c0c0300e045190000d64004000300310754842d050008000c807554410581c012400c04c820014241021000c03a01c1041c1c02401c0c45041380c54209400001e5070007421480d512003c184042d03c0407070300a12a035402801c41442c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 88160747 1250 88159497 88159523
    0xc02010909090230010e01020405040c020708060a0c030902120601050406050a03050c130207020607050c01170c0d0c02070906090218040605090a0c021c0c0201021005090703020607140a 81
    0x142100c0c09500041c0c2001e00704a10440183c0783e0183c480d0110072941d496080d22500400440f07502036401c802c0034802c4d804c0501d41c4079240410340c003c1007540c17002d490620000c243c44006076a00d407818420500755030302610000300d103031800743d21240b03034603405140106900c006e5400041d00c070500000201510340100d00104920302d4207104000c006d01d8150f80046209240d07480d4191a8420380d034032a030041d803820510b1110301c1d00d80d904850300d83c0d60041c889521442c950914580e00d504880d50075010031210308100c0d400d1030b0381c800014420740c5043c5200e1310f8a284540e50001900c01070f00c0040c294455940045030f035180794020390303018107503210300140c55845131030350000801a00c0152600540c0381510502c01921000c0e00360b03611000c8ca0002103100079010204a203070011040e00c1c0114108070744c06a01c40d071544203c01c480e4850003607084820125442180108a4506852240c00c80c0d003c404204014100755003d80701c103501590300c07020700399104d0542a0802c2c2e01d1074811221907910350130b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 88161997 1250 88160747 88160749
    0x30109020d0b071e0912020604030609080a080a02030408030a091b090f05010b07030207031211010c0801030203060a06060806100c0b01090504020a0b04030503030f0a020d06080c03010608060408030412021203070c02 94
    0x714220041440082043c19030f221400185c0555058010394121881c2001c4d0745065480b4901141c00841d0f11a10400c6a105242045210f641003503001200041420010812a91700c50081e40d004941000c0c14615603242c03031203088020321000d80c003241c4920b2071407499004100c1c2c03802c000c2c00601d81014003103011410850410708480e016005540c48060620992000c6903000406600780c0e07500840c14000da00008030152054203c00c0003001066080c44031034081154004d01c103a040720b06c29412603c0e01c0d00d0340f40440c030aa680600400000500c503800144c8586000c40c1101c0c01400d040c10301e044940e45545a500450303109030032035002903883e036003880210708048000c0c40040c2000e51410f400c25042d070b500d054491201428025120784018003090f44010554103e49400e40034010800109903a450140e80307e482c011802d80c440d5113072800004042a003c20882d1040e5800101c451a60b0703031315564000c07140b000103901c04c11407041038805226248981c0041d40501c206440391184101c0ca88 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 88163247 1250 88161997 88162007
    0xe09090c030d0210111207050f0412030201021921020a051201150906080702071203030b0306040606031e0512031807030803010e0115120b03031603110106050d0f03030b030109020d0b07 81
    0x84c510708200d170400c40d65000c0210391904a4000b40185001c0b6034501c07200103404140c3c0500d4002c000c0c003445881d021001c064055008004000e107020400c3e0708000c40c1e240a55202070300304080020801141498481c80490f98000d0100381c3c100d050003402d00c9980c1c0020000c1c0030f0260030104a0362080340e00b100c00d0a0300118804010001450305842c01d14103d0402525a405885160b8000d11448240d0b4101030094210401200b801b40c201c074035038a4941010009041c0920064a0036501c921207000c0c4201200303164135125810100038402e08454000118180c0e0004010340804d080e00034080601c200c05001c0400110b0181100c140c40e541031012240e5280c0c810780c0140e152650000d1611049a049056500c12030826200025807080f50404079086201e240d0400e00e0300210207003054101030b080111541c1c00b90300038000300030312901c4038107215244080c1c045c042c1c60404140607442c000303840b90300700d00d68101000e400030030b0100150340030a00420101004a59011014040001e00ca91103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 88164497 1250 88163247 88163261
    0x203032205090c25020d2108010b040501021906150f08010c020c1f200d0306081908030901020909010e07080703060f050d060608121209030304030e09090c030d0210 72
    0x20724062130120502d6902e1800c42c46104038000c40040b22000710155a16000198500b680051140c0c840d68007150020a000102c4502d150110b5132503800860711010103400c1d503081d90381c10b80040944003d4064200e8140064003800c451040d02c503144a0058154074070b05000404060003500d030040e08019000d4203695502c1c00d51411076028885040469456001041107120015190b0b01c1021640801300c0301c0b00010040c2e000003140c3c0b544080d215980c0029044e081400a40d001c0041d80c4e00c3d5040d240d20340040c03100000c82d04c11580340e08804544031400650300705000c0360006140840304008105240d07402da02c9900030001c3d80741003240380e40c0c011a03051b50040d90ba280401080341028030f0344c2080081c6014441c040c01600424004000e410b034803400150003050112044113407101c9601d10b0603441064039222b51409600803408200d400419680280c3e85520350045454a4000340407082c0d4000b05003298911401860140d6500c050260081004495014104640805000c00b09581c0c1d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 88165747 1250 88164497 88164511
    0xa06110406141206040c0216030b090c03010e1b0a120804051302030609010303080a140f010602010c0f120c12090f0b130803040f030e060a0804050c0108010b0702010804020303220509 80
    0xc1240700f0608480036052984104111800100c50b404544200d00d026045c082e44503230360318041c80c00b00a105440c5d2031f1901c03c004038012600750603a40c0c402d00d801e0303410a50500b0b02540c04100d0019022002442e115008035001c0c001200c81d039a9030a580241301d0500b0340564890038006014400e60034012081c2c030f400710f5800020351031424542c000c83e00b8200e0520000d4100198100402e0092955400800304007621800840e01414080c03040e1051610078410100598a04a045400c9074000d044403200e00c06191900451403403822510800b52007280304032170410032402c001d003104400b1481680021070140c941006074580760310301084c7e0300c0000b400c6418074010681114001480c00c8044a60082d4400750040c4071002901c4c00392519541506000d03030140300403464059241c0d024403680e01c224003420449105580640041d94401003e0089429020041001c840594046d000190f040742c8041c007280d280c040d40c081c1100110703586141c5918075009041040040b03290003c41c0705d400900c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 88166997 1250 88165747 88165787
    0x81806130b0c0601060c080702010e010306090213090c08011203050304051c030c030b09010506040308070804030c06020d0e04050f24061b06061c1203060e040809010318050d110a06110406 82
    0x38451f15070600038003d0000003410480010b00f440507a900c240c00100052407613100035921040c941001403402c00c100d0080700340203490046542d07202446400c0c00d034100c40d100d2840c112024540d4034103e6040d80002c0054502d440317508030001484107100d181014040486c0d4001840c00010301004003a10080442c86206075030b860014003881c3d44503811101226070100d0201c0c2d40e18028078001e0b81d58000c03030780041c6c64800c8401000410940100e00800411607942e10074000070f045108100c2161820f403081c1d40c000720300500096000200313840613045208203c501341c80c031700500000907482c2d80c02000d00140382040c01100c085560070401104d030f0841011148001810341103e070182d01d15001420103417040600303006500546000ea4401c1014000d901d0b03140e007040c90b00e410240d0079503001020107800246007641d0400700c580e1b01e200d284017107988100980100c0e00034000171181100c10b54102c60090103100703400000908240b045130421920b1340f203a207403198030705000509080c0041100c00030220b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 88168247 1250 88166997 88167017
    0x91a010b04090e0708030307030510080304030b01050d0203010b21010f0e0a060903050d02040b1305030a0302120307030e1603051203010315020d1e060e06030307081806130b0c060106 80
    0x20400e006640c159889003400060400048604030700e0000c2c1070344481c00c140000010b0000b4280d040c0c05c254492030100c400e10380707100d44d51440d290b41c1f44075510003d8030703100d42000107203e985462104a0103082c0001c002062807040030380001e02041c0508060b1011349060008207952000a0240c0741c241c100d1030104110540701d90b01c0c05615009851801400d2654550103a800c15000e8001e072050758481a40840d11152034440307120071039100c1d031541c010032448508005800c0c9400200c104001d68542d02034100c200d1000c4010342160806081b100c04e060b2a4408a0081801040300d450001180c0d1200c00b0074500c2c42c01c004d03040a600035445061040e00304014408541d02d2255120701d413840d85001030b030f100800116080142800741200c6c1095003174060324513035120b03650414400e90765903690000c81501d4010400d9582d1082d0000284005414030006541c0b5030b026842104558010b4981850540f44032080b40d1001482d4210303200e005030110b00422a91400c010b41405480942003403a003003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 88169497 1250 88168247 88168259
    0x5090a050613080c03030901051b0708070f11030a06021201060f140703090f0605090108070e0d020402180405090304060801060216031104110408030403050c0d020f090a0209060d091a01 81
    0x480e8000c28501c82c1040d081a0401002500c0040710541e1002005490312818031a01c094040c11058887c6180c00080082c0040381d202d0307003422190225440707052946004450383d51210321120040040e02c41c3d00120018040d251002d2164803091445500010ba541c000d40701800c80002041c1c001c0303001c100e0030b4000070312081d4100d00d40e0782e00c42091600c1103850383e42d203150499048185400c211039100100c080011015000409007030000d5090301c546081c5d0ba03507000e080712020300f200c00a0380e04c4800c1c10b5100d80035083c194000c02c44082103004054006141c500400e0039100d095a42c00c409510016003040b030f5a0b80b0107a80303405040343d403000d81220810f400d43c0706c0e02200d02d8080684002c00301c0c20001000d99032684080c02e000c080f00038a83c1c60360782c0c440880d0780720b400621081c1c810340541103015041d4600700c881a620f0070b030700030302d82c40d0100214424011884002000320031210340c00c00c600080c03035452501403c100460084049039244061034150070b14660716040d110700f805150018481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 88170747 1250 88169497 88169503
    0x8010302010c050c03010c0f02010c080907051c051914061902030601020a120f17060a0b090a0e01090605040f090f0b070507020d060f06120f260a02010b01020105090a05 74
    0x1180e03024606150260360900b405828840c0c0c0d06050f61703066181428103041d030354025041e03d020442940080000d0818444140d9180d941110300032030503000305400380007510f06070901c0c10711102007050080c2c0e40308060340ca03540b400711031100552014182c0d052200030024444a85034550030300d04086c20650401c4003601000e07449030110b164407160084000342c003c1c1d100f0800d02c01541c1d0030841da4640d27a80d04900c003400c20401c0040e0940040c9108210f44070b5403514031200b0b405144040c0c01c55420900d001c10709002c640125181c1c69000302541070015101d0341c400501e5010300340501c800038042d498141007008448507005582002424501c07031102080c400c010030a941600441d20501607500c06c40112401c0c030a52800a506c49401100300050002c0703035000c00d03040144c002d0200b0100d51200010030300f04034a20070042c4402c2c0c280026400148010318031034954844030030002c40d120031b101980a150b0304031400c1c0c400140c2d51003034115039035070703090107000d4202c4040000380540019030784619132 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 88171997 1250 88170747 88170749
    0x1903080604020906120402040b0d11130b060d060603050a052202040b0402070f0b010803030405071a090604080c0301110f09090c0d2301050604060f0807030e0111070303060906060801 80
    0x51026000000300903031500d804980e50260020a1140e03110a83da540c0c9019220a9400781d001c0c524141d15650b003424201c06044482d50002c017084039070002c2c10204003004541d400e0805400d81c488540d07224a85800b0050556074680c40c40104000e814076600600f100c0008100da4109400c1c1000e1117030030302c006c50504040000413084200503040710b0010801400c003101c8440d800610004000c070a101c800c0c0810036441d403003584c41d84400d99940b01042c1c0e50b0700040d2005881508880e07003c1283e05800e42a02c00f10340000c002950801d491707400040d003942c00c6540456003982040c0b141440920f402c0c0308140010f9087c4240d24200307001040b04503407074040c0c009428024046800803c080801c0703981510040ca003c0701d02400410403e0580700440c844458041008544010010815140c80c100362019116190b40b03050b0040070411046031803290143c000c0050507650059a101c481081c091005404a03501e2155540c91062074020304803295580300308141d07440c00606102c3d243d80418014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 88173247 1250 88171997 88172003
    0x303150b090f01020708031303061b2a020a0b030406051b04150e0604120203120705030a0318021906020c0402090f0411120403091404020901020d0f050c1b0a060219 72
    0x201882c10000145c1c940030203600264124440840d00c081281801800c1d042900d11400050240300750400c410220041c003c1000004544072401d441d054819003040314854000301c1040f00c010390300326008030340d9a138142d82120720702a000004000902110303008142c2c01c1906860440e20000c02406d00c02410b0285018007504503030600d60700071401e4800d071001104e015000342004c1d038403540c0701302142c10881c107148101c2c024020000d41c109142c403144103070342081e83c000024500e02020641c0c00c4004240c0340340f8501c04189a01e21050140c2c480e20b003142c2e041f200244624414a007002000303403403c914805014440d900410900c01580c4549640c1d004013502a90081441400d110180e80310b4041c002c038848500c1c1035441040300f4590b01821110031918000010003940401c0c50a1100341d211381c08030385001d40c0c8100c3c80244c4003885800364031850702c1c11345050b50030416901d4001d400e00c01c0760702c5103414154000301c14160034039146050100429250000700005119410016500c8044178005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 88174497 1250 88173247 88173259
    0x1d0108060112150b1e0703120b060408031207111603060b040618060302190509040f02060c0d021e06100b0703051b0604031706010e09040c0f0e040303150b09 69
    0x2516a105543c0215500e68000c050300050b49880d0070340da50568104011000d20801d0725940410111045000c41d0901ca03019525020f400e8180040d100180c00b1908400c1e4000008000c0014840000c0c40500b40304d800781c8075940458208890300800198040345104550741114442c1c031603540c50750b240101142e920400c00300300008808002402050740d5031100c022240c031450121300040d11644031506484c400c40d000c10011103606581040c3c103805001e415041000c0c40003050102da1403726840800d4401009a072a140071105624140a00e059020000d0f070f025004400c2c0c81c022000d40040300740203600c02401d0030b20f011240158680790902c640030b0b4000c0f0000d02c04003814440c4040740d011a080e06008209200107038040c958440c0102c50580010b507269081d44440400000b03001d0061005135188e00c0b1200b1103000300080c0700340c060400c40300e2031f40000002804400a21004000b080f2041c6642c0700da00d4913003000340039504498550450041c03450014800c840c03084003521440b00095542d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 88175747 1250 88174497 88174517
    0xc03060a090b1012180c0303080106030515060d09021c02030c0906101b06020406080105100201060501021c120908030702060709031e0201170a0c1202191b0b07050306011d01080601 79
    0x14107009041c1403000c171a05041c04010582441100200031040300d129a0703c80300c5680c0d071350300114211181907811070007000c3d0852400c0c201d460400c0141002c070313a0580300007409411940c0007503810302d00d59000c400b141340074942a100303524050141c14042241902c99842030310b81940043d08000008299005100703408000c000c480c550030304038562447d0300400c00c559640d1036002c06402c042c801d100700d0380724030307540d5a031140038038418002c038000c83c1c4040c1c0061201c2450760780e10a8146510481034410070802801522180000340140303940280503250f42c0c0d0f40d0341007442000741000b0700240150240440c0036001c100181c5890a03060500d0f9800180e0001221140b00407180d070403118625402e901101010b219040e011075004041e4040c00d903c0741c1c41e40d1b038101034819050780178507000d42d20a812140c141c8807505019006c2c007448428209190081b05109076281e94400d001176a1013000101e002c41003080741c0d604421100c5050b110440100703400940035000030605540200000e041000d08c030b0b5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 88176997 1250 88175747 88175777
    0xf1808090603130501090f0b070c0f0b0c09030a0605062d0402070614091e070f050f06090604031113021c0e0309030a0b0603010518060103030302130e0c03060a090b10 73
    0x100901080e43e104000703000c200d400e400d109006501c00c10f41511090074200106404500171301d03d03102e0ad158002c010311444926900c40f50003101d0000d1034110000700403c440610313541c0a011001d90148030300c4c4001013504000e01800301d88030159983d01005a01031041c5050800000102c040c0017500310f5000da40e5801074a0100060b01a0b015000f1640070130106000d03d208001c51401d20441c000c2204040600843d68003594801d200d100310010190f00c26002e0000e8182070240112410300540846c2c41c1c81c050310042109c0d50b0180d441039581200303030144003415203092050b200004a220609500788580b004400d40c400d1141c106003050070390740d1602c00801440510a03552000c42c002d0a44440e240e060902010882c1708640d150700c6546410f0018004000340f4252191664224008081603803e44c2d03030a4000f035100d86031404142d500c04038000741d11060b505401e07104000800116449081540521403c100b054102040050401035002004d881c2ca140c804c4001c1c005181c40c03940d0b648072076 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 88178247 1250 88176997 88177021
    0x60f0204050619030b120f06070219111203190f0e060f07170c070e3d0905180d080411040908090603090c01020d03060b0a030504081b010f1808090603 66
    0x82c0500f80c00c812011b0000325010400b0854004e0001c40f5419203007203941d100c004036182c509103114000300c01001c44402e004182407400b03550503602c002c2c060020a10110380308518680207a1744090001c00148491400903902c400c0d4031051308110700702100d00c600301b2000070301d29024003007406010010104500f0f09018900110f404000b00623280e0a580d0781d880c040c82c42d100d21180c01800800d0007540d0210303a07090004400358042c007994600070b101d82c80d441071050200c1c401585545200c2d070388825001c41e820769248551401003800c5100d030015840d03001d005030308112030754030480280301c00322003044041600300c101d1055183c0212000103c0c06518170f8010302038064a090729412040c04001c000c0b03440c2c40000c196516410980855071407800000d001ca09841040c0580210000c090210140440c0a03800107604144582001030429501036581c03400b00440c80840403060703441c2e03465044919507910a8100c440482c00c08c071049003405803200c40407072161400c924000c540c0040020384c031008030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 88179497 1250 88178247 88178261
    0x50301420201050a060519090e100507020615030f0709021b030c0a06050105120a060b0105070210021c030c021903020f0624040501180504061b0903060f020405061903 73
    0x10120862500c000c090001c0c000c100450302c5810301458040081114601504107522403941c5003010114036041501c028003800d402e00e642c0c0260b04c1010b0204011080600809100340d030300740c0c01040b40b483d20100510383c80302d4005102d402604030b0f450380028410003044400c2a41c15040015070766024500c412012400700821001c1207020109000002c03080208154800c1800b60300d00340f003140d88a10800001003850344010707110b41c0c080c4220100003213082d0821501d082050410505040e4207801054480100c41d15aa00680210300d501e60302c0348540c038130b590740625a0300e0204900e42c02020080e60f9520920030310302e03514807940d004404151080280440125014003641c41d54281a03040c0540040c50071003603c2c2040c0c600302001a01d040611036281203413081d5242000da003803903114100040002400a6401a8071403011207151403425050140d030503004c4c0c0d121041c09140d424007030111402800303030400312801048204100d03650300d07081d58581d02c03041c108040d2890f0100fa0590040100d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 88180747 1250 88179497 88179599
    0x712090503030406030b0307091b0e04060308160203060901061224020f040f050108060a051212040b0a02010e01050402060a1404090f0e010c0306061b03021908040302010f050301 78
    0x300083c04241568142c00603607070a01c042d003c03640d50f140c4038610213064800c8001001280200b0078040c44403544070710748624041801600002d2655100d80314030030250b00c42d03160702d03a5942038040b4803003c42c02c0420507180d10107440e070000c2003c03504080d0400550070950a002d090020307130510000b0741415000d88080b80c042541003c5559103030f442d40e0302c4a19080741c802e1070403100c50400f0014655008980c00c81c0304003070007480c01c0280c80c01e0204000d0b982000458000251007584c0c4107034001e10140e8000d0028040c1d010107070ba00e0716642d0b5002403c0d118061003d6a0b00d074108006c0c040141c591905036090a01c19003081309140c80b0101d0f2000c83d030b00a03548144940d0f414050100d903017900303e5120300b9542c44020001e00a8000d00300060b010749045101c0c48001840101c40242d0039003c603011580e8240c842d10549005040400c01c014900484170003d1724000c1000508000310340c0c10082041100015083c01410b642c0340240c0c1c65604480e0101d50752191811030018003404103000856410034207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 88181997 1250 88180747 88180753
    0x90606040921111902130501030312050915270102090603070509121f0f200f0403020405010f0e010602070311010305101e030c1a040902090103090b0a02070507090209060712090503 79
    0x403e194421411130b070780c000e038081e800761180f690082031240500da050b29013549640c281c56034101e40d030b90f0003050000c0400f4420300a404000380c8258801d00c0150040060600e0b05c03080c41705801450b21320080240003003480b42e06c10016913403192541802c2e0b0b0342c03201140c2400d50702c030321810020410600c040e038401d0807180505111416100c00501c020031041540340350802c0840d1504450004075448186003c0300c0c1800000001e000210074001024095072922400c0d03b09aa00d502060640f0300c00e0b0402840000005c0041c48039040401906006000c80e1008060071851a00c3c0d4641c085049030100d41050344480c00a8010340410140c00c1c000c2054070102d8081c00c0c10030301c00340303800040b07804100c0c0c069040e20380005011002d100c084800034101d0091500d024900b0f04804000d6000020346418903480d8455400465100004103109265005002da036850486c50518180030307035600920392242c0305024480e150740303c00d000d0f00c2c01f2561194440d80d4034002c01e40251100081e80c0c0c440355140c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 88183247 1250 88181997 88182013
    0x31d061209060a0c2f1c020307060b030304030308010b030907030c090e07090c02030405040207140d050c0c060a0c020607020a0b031006080903030912160204110309060604092111 78
    0x7110024415102e00f9904070304010601121204031080705c42c00301a850842c04401492503c420025092240c0010711400c0342d146000c480d0f1200480c20b001e440b08000b681002c00c480040c441240100651010128080c5107000e09686e805402c011040c00345c0c4107aa4004400a20011020000c00003c6c58112960b00201982e0b581341c00081c246800380400507010b408800168000b83c0e00820400340700c1ca401450a09042400740402904074a0066400300345401582001074401c0c030843e14402d10969030581e03184a0384201518000302005290701400040102800855004462043c0785c0c5c1d04466141c1e03134010900008070740c0700040e000008140c00c00400d10480040360700042c800c80d203041e11140181c0d9250642d003500c0e40412110f04901d50003045040f50380710030030740041107070088000049400c602c554001c102101c8414401c40714a000000c107015004801b00966988001c044405104491969a44010341c80000764409079159503c0b55614401d03006200e1090105494002c40d43e042c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 88184497 1250 88183247 88183261
    0x6020c01091101030b150d09111e0a06020312070f110d1101060506070f02010818030a020a1e03020d14090d0803040b010b2104030c080c0106080c01020a031d0612 71
    0xe40b40078214042440e20380c0c03240d058104103010003901e0403e11403031810448948007000c09040c5d150001ca034002c0d1102586600740e612182d511140e64040b41c104c44941c12140180001d01c003040d0040415507000748400d03105030001c1c20f500ba031f0003a602d26124400840000044e02d080e4140003a903071482c05411740d050a11948100c0641803884e904d0004c0c44060360303030000d1082902c10700102510ba2442c1d00c10702e402550041c15126004809680c81d2001c4004000b2a00e0031904645400401030308422502c5003131056145a051505201d50740c503490680d46a50040d56030902426601c00f40301107140d414528035030a401b990400034028104041c1d02c2070303a10b029a050b038012a03042742c1d041d40e088008038010038414280c1e25000030103421400d1080c402404c045459100400c110100450000420001000e50020340040601e04001251280c01e001c0854200306403001c3c01411035001101840c00301741c2c44007a2072003240100c490700410b100c22101184140c4107000e451380c02c2d070740c21206004c41 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 88185747 1250 88184497 88184513
    0x507020d1208040c051c08090a12030e010f1e03092d0c0806040f0b10091a0103050612070b0906070c120507050609060304030e0409020405090703030210060b030c030406020c0109 78
    0x800d904c180610112070351a4000c0141c001e042c050400d401c0803e2003e04030010b10318000a2105200c001e007407444480d03884d0700c0e1041d18215904c0031000612289072820055800c641001e200c05100d0800d9210340d25220108180c80c00b506031203404050311070b00a041800380c020000c440401c3d41d031449060804d01c10144080211440c1c000711800c1d001620001080704021400a00035940280c1030f59105c800f640741d220b002400904403c1e040c40c07004000082016051061940601652081085c05190328001404441d03006084c24001c50304a40c103000f07401c1003c42d409007510240440c0c141c869895401040d16030161140061003850041e00c08030f54003c00080e0021124810000c42e22469210010300a00c0d0080340d4550b0f80000c028804200000d0081001d6840403030050400121810300ba000036043c0c0300181c4509004d50460745003032050507414032005003500d52885003808098134200340481544030050042c0320556001c0702080402c034903601140c01f890002070003846407030040d081c0a40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 88186997 1250 88185747 88185751
    0x40b04090203010c170121080f0d06031103100501060e061e0a0201020403050618070905071710050307081506100908011401151e080a021303121404030b04030507020d1208 75
    0x300017a80000000700790302d0405480130903851540c0f003802c030b01c56180d4a1400343e07040036580e962090b40034000c00700d00c06414410100114040c0c1900d04400c1c0e5a681803604224401c1002007800e400d000042c810359801003262140920192031083c0d9030741c55803031030001d0815848820011501c1c000350982200d60b0540150059901540a8900c10b0300c900d09202e012040008564002d6000000e0401c40a402c9610907648403200303082c812050a03100341415001001252051014a07084400380460f00b410884800a030040030000c2c240030f941e0340560b800707004008289a1060582c180030651b12441410540014a01c0c4402413104100d1801440402a02405548200440342000c0c58545114101c0c04090010301400c001148552100c00c0702e80e164010b198004098080282464404140d00d59000440c040e00000c1c0350036800d090010200d88401d40a043c180100740028008181c0c0d44006a401640c141000c646d14455840801c0100c080184064411a0801920446250080300f058 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 88188247 1250 88186997 88187027
    0x70b0f040209010f0e01030201050a090e100609140612091e06070e0108041505070905210c121902030c090109090c080319030e030f04081011030114040b04090203010c 73
    0x122607a132100e03144251400d107446040103400040d001000554002c10003002d5800d21031403d030f600c498036a00181c551030019039500f8004d24105404106032030344400b0403070140c901d100e00d01c09200d058000180b003a025111699640440c0381c8040781c80c80350108680e80b00e4400000b00060845428010035807108411515040031950305942c420b1258803502d5902e00c40e5030302605c00b04c20f0070284010f690040c003004202d203050007a0644081002d50307400152100080061107145030003403901000905000d00725032101e01070110fa0305403100000003c44c8002e100044141c100c0030407e003a00001c0e28004540100341e03003000500002242a2285801c54600c4500800308444481d6640c0d0417941d80784500c0a000450250203404811141d1081d000020192410b60403641840e401c41e400f00712561040e0b01c420034583c811500c0300021002800b030b42c01d552141a0b0050305640c985942d40f0490908001580d2050f0707601c04240020f035440c0d9200410b0300740c000c0c0c002c000d104104a80904020010344caa1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 88189497 1250 88188247 88188259
    0x1e08070303090f0e0601050f030612061f0b1e0a050d021305101419090302150318010915050406020c0703230705030a0f0203030c060a0603300e06070b0f0402 69
    0x820780700344c034280c018012107061751291b18180034082c40b4a519000540310f00d40c009158111440b00703131400c104140c02900c007440e00c68880e4041c0282d6816440969018044084d4240a0500200e1150040002618041c03201c2540c400f00030704219030038818a09200c80c001e1000c100480103000340140325058070020340e18200c0d04a440d00d170540d00c0e0300420340400c000303c20030015561424858885111403040c20b0070040e807400d4413940007a082122207090020b0542011003080070069201080e0300341c080101008001340f01046d10749a150001c00041e1850042e02c400c00b18080003140d50407180d9102d12042501c08460f181d20b070003c001da0007203041030041420842c40c50b0a880c9c002c04d2070012074100600602101ca0703582e8031088940c040d420140d0f0305002c03c0c0325800d1003180601031a80f1941d002e0000251081c11440d0100ca0744c3d81c1d5040101d81640088501c00c1c2140d141421003980da141c0d400c00b10708007403a02000034881c4c420340c180100700c81d9044091060b044401d181042c005d80c801c9610b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 88190747 1250 88189497 88189499
    0x10f0c11061b120108010902010e04051b0d06030807080c060c030106020607200a0b0108060705090607150207020d0506010612020c1506041803080f0105030105091b0a030c03080c06010f0803041e08070303090f 91
    0x108400d8330b1094660240d6010411941081c51110301d0040411100c03440000ca5640e0b07803a00c41d02c1058000130000e0300d2280000844400c040f90911803168084042d0030a00c1c15035040c584000c1d9030b100c2c02040f1509101c1044000b0b43c0f842070543e803205141d03103020205c035a403444528120b242c0c04400e20420f00548902030200f141c1034012801d0300c01521019040038200540c03612000c1c0c600e04060183c14400b40d080000d000562152115140494004c2009220381d51510800401802000a6030126113105210300381200c43e001c205640241990200c0c0400da456280004008207080070b0080c02c0c2600da4880e400c2015002558248524614a041c1a00760385e90000d1609861088a030f40c0c009170040180c2654001800e943c120420502400c0320715a25101c4d179038200d83c1c140740d4205440c814404560034000b4182007100c5070241c940c41442c1c0c44454604101c0c41d54901940c000d0640380c00110801110305404203080c4c80040420030308030752140c4da0780d0034040c203001c015006a200b003004020b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 88191997 1250 88190747 88190749
    0xc08010e0108030702040f02071707030207121101030902030c04050115080c0a0512040807080a09141002120903030706050a0501150c1203091a0405010f0c11061b120108010902010e 79
    0x4038604030346050000c0c3d031030100240d0812005007404d20714810440d03400d012080c041245c0c00c0750700ca41100d5000c1c3c1c0700c0e41c1d0b0745503040103031610009038013480c1141214403210f40050f00030401d000c002002801c0c04a45040c01e031000908184401d208290010301e4000000303005803803d620200d1034541c0d5101c01d45143c030b0f14004d0000d648960040c1e00c000c280200000f00080c2c40101d211948076000d020590304100a9035500c1602d980b10341c0341d000000c0c401201c240500407004103800d440d0b5a048640b40c0f242e07140d94002a454460654102143d0003010404807101e803420f01c01c0311041c507400310040110340713006034920008080c213000d202c440281401c00c1d8145907002e80c034a640c0440e0011102c0c2c00c0101c1405089001e0450700d4005c07074401c81c1030403404c0041c1212100d40d50003580f190001144007121040250111a0324a0341d9600700700e003a03210030820050120340c0e0b03904900e014040240540348542501c14506c0f0705078050f0040b10790f0b200009400030040d8851300405100741e07501702d000d0361488 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 88193247 1250 88191997 88192019
    0x604050c15070b070e0109081002300f06040b031e0c010206010b09040209060c16060e0406050a0e042109031502040509070f0e0d0804150309030807030911060a030c0801 74
    0xd02c000f0403402d02e1a0120307240e68001e00104d03600300c0301490100f0328261aa41828205001c8500c484010b940118001d80840c100c0611041c0e4104c414001a01184006d000e4842c046d00140c00041c0300050705002c51500d48494005401d0f1030b00190480c0e03103481ca02550140e600b0706846046405008a991103200e46d072002c1107490481e03101e03004850805101c0410800207620002c29154444810080ca0543d41c80c01e1004403e03c190180d024100a458600302801e103a909500c2c9038440c0303240070021f201c0e65488205100645c1c92030410b10302903941c1c614205200c00c9240100c0119020f000c464500325075031100c1d484065902c9000c80007000c40c00708560780c0a07802140903490303010340000009110107115501e048003601c070b940360045050803040c021444c0e0f104c3c8030200b900d80080000741889011240d0b14520404250f510341002150030580b0020302843c4090058010113407a55030312400d01109540b40d10000f20b0060a8554030f40703103480041c0007070003c01803c0010600344000003802e44215 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 88194497 1250 88193247 88193257
    0x31e07020a06140d0507020f010501050a05060d0906020f040e0a11030106080c030402131811030f1e03040918020102011a01020706030c050d061d0a050403090306020306120604050c15 80
    0x1c1c15445045003044015581d0388151041c414105000380090b182c000b0b15402058005d50454001d45240000d940d40c05d0b09554050304404d001d0b40d0f000c5000c00a540390007085a100d0010228002800c0000d0325180340a88542480580c40382e10210300032858910a8400901420215400304100e9035000040c80b0f440c082440780e1000b1400640020711000807142c000c65125200074500c1c1240036000d0311800481c0d00454010901c40003a40c5404204088500b10b0007112004030000c1003011049d0143e41e56640c1030f00306a5142c050132000f4400e0041040003680c0141405540071302000c0d03c5a107422648aa0b8604168019820085807a43e603034007042c1141055030041c1d0240c54400e040c800c003074010b40f40c0400c044d400c01404000d0500b0008552190b90081d083c81d07500d50740c1e05007851401e000d06585c0906411503691a04042c0400650003070909000c4a031b01400168696480c240060629161487e00c03100c1409448100010043e0110f04103400c0c070002c444850012088440000050180b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 88195747 1250 88194497 88194499
    0x20c0c01081005090403030e0a0204060905090d0309050c0f011e030203060406050d0c060305090f0105010f05040e070f0311010c050d080a050903091c02030715090f23040c031d031e0702 81
    0xc0d20105d008248a90803110703070070080808450a40241d035001c642290701c41d900440305903aa40050010581d024850100c0d0584186401e01407051162180e03500c44002101c000c4c41421424446072480e401081241d2a00405242401c8902607000d0045c02030b5000729401032045141c502c01162300d152100300c0c042c0080c2c100510800c49420a1420740c000e201c09440c3d10751a00c10255100040c0d0024028070303001e0041d0072000c9402920380800d0000b640c058403055410787e04244000e2040c46020380000003144d41010314107003030100141c0107070783c2c0060030799001d0054010520188261504401540e000b46841710040159688910960340c49004908485501440300d01c0b00c18030002ca105640c02c0020300040075100035542c4d0b00703a88501028250302200104000c0c0c04104401072000146130018000601c00190480080c1032407155540920405485950395541c4601801d00c254003c00e04040700005014540c000d00010640d41d8110384024400828030098003c0000c1540d42660241a8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 88196997 1250 88195747 88195759
    0x10f05030f10080703030e04140103030f0e1f02030306010216050a030803060f030105162c220203070207030219062a08030f04060b01080f15010210020c0c01081005 72
    0x15100c0350854400c070050511414001d002c400843d01c15414016000114441e842e0400c2c1203007a80b0034807080d5100724626030003005d400001080403d820140e100c0f0b01d0000d42c6080c4415008100c0001c400d482000105241c0c00000c450340c001c0f1940020040d0b024000036000c031031800e034582c10b101c005400f071170041c181c002c2075810701000054400005182c0080c0001d2402d8102900c000200c0d0031500100d0340c07004841d41c000c0c002c0c401c0740d41007200da060345402c002031030068540c064540814103850055660065203c3d0114283d0b0040711010303644c038000403904c10355481c10503c40003542c1e030b00c0900040e03100300307543d508103040f50001d00041d004030b030741a8482064403604500083c4500704440804035103c0c102c0c0084a0018880b00c00030f61282c900160840030900741400c04000b140c840c0410141401a0817042c841240f4920010a40c095002c8103154250401070004030300300b07444034451640c440d00101e080c0d005a800458035041640702039888450b680d4030316580300c40010380c6209160b0002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 88198247 1250 88196997 88197001
    0xf040305090f010212070303020909130b0601050d2904142707090f02070c05030a030e0f030f0708070305060906040f0209041a0a050403020f0c030309121203010807050f010f0503 78
    0x800d0001840b401c081c01401900c8044641100346202580203071030841c000795000440701200d24080d040c142d00700b800d03c0700540142c281a903e201703d9a1010340b040c1d060001c040361200c6409070703903080398844610340d2540c0d1180b50f502c0c80d036154015070341d10380c018862820050114494008208407a1081c0c04400148110f00e244c106562102c0520100207503080c0983d403404200c031401e900604c540001444001070381c03100309003004520b00545400c40b0340300e900003032004804243d125070040071400c07040fa0a0764068000f20b0020349403003030541c020200ca02820000050303403400801c06a00b1280103030306a41d0241d0b5007640d1241c54178411a0000c102d50340400301c440140c1410100789500c18485e4420301c0e54280981282150280700310707a6031880c21f4032402017004142e0f0600401540c1d421081c010711003401c608001a40f04d0040c0060320f80920044242d0041d0490200b115002070000703a0003c0c0e40c0d0b541c40e224a99291806d41c024907004004554030502154030840b861030107081d455403254115 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 88199497 1250 88198247 88198249
    0x3080103030206240d080408060108100b010903082205031005041406010602060f070504051507060b060405061c090f05030a020c01051309050711030a032708030103030c030c08130e0f04030509 84
    0x201d8041170a81c1c107581d0500010600038810440c4501902d20180281000100380319000c05070b4600310401170402c0b2100302c007040007581820075074650550940d440100d2044118590304618456804164580306001018a480040394003940c0114001c0e85007000000101503103aa85641c28480c0c1801a0710402c00900380500b402c488030b07000100340c5400fa25180e5114005030a0b60100b20007030740b00c1d100005200341000294400c40303541c1c04007a0380c0d1508103841c05001a405005000c100c078840d501c42001c41c030707902101d980f00c49005036102c807104941031380c0741c10a66a650171130f021a002510901c0c52603185903000d20182e80b104d20442180244181c2810a04001740001034496030a20000301c40300300c41003000303101811000046690006580f921007120298023003240c0c4203a1800c46604070702c1c1000c501454100c07419a070b01414051044540b078907080742c0d6820b06107000380c80920081561420090026070b102c0c1204c556481c0032075140ca82c4510005160020354004000c61801c0000c5003036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 88200747 1250 88199497 88199509
    0x1d0603031602120102040801090305040e07020705010906030e03040302040501091b08040209060f01030e070305010510090905070501052a0105040201080a141b070b090d110a08030604180206070308010303020624 92
    0x10f60031044009820903940f803030107a00750744480c60f040380494000308081c02801c00e0b0b0001c841d401003d80c8014071080d482c180000e00b00100e40d0180808054a07252144180141082141c00a66018208014541c2c0d1040e5000046c040c42c54070707600f40b2113889064100c06205103038450169070014032594503502d4071003c001140f0420a1942d06054860048900e0031005000c00e2000714020000829140b070520103000030036103603402520b2a540703003040c0c0704041800003890070161602824895603803070303140758600c3c030035400e54203244003403604000d489001110642005010b03078403e0b26600030940310400c1e81000c0c2c40f0b00a64614a01c1d8210001a10030f0b4040481081d540e800c280c0907900e04102c3d0303141c440b80314204031259900756020300f117000b507070130f031f0060780021042e840201074490700180f5594100c041c030018044500c240e446a075132440f0071200b007554010f0160700402032681c035001e03407402030001072091000b5400350182c0400103200c101d2001e8207204c40550300308031080b0f108070a401c00c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 88201997 1250 88200747 88200769
    0xf020607081b070605060f0d08160311060a02070303061d1603021603020a051c09060e060904020417010c050f0f030c25110414010e060414011d0603031602 68
    0xb00618800c2808641c0391040030080003102d0150501140c41c1c60102d0501248000c0c90348400e001d045218501c0d00812110300660350070540c003c440d17a00ca120641011220400320340584185401840e042c454920f41b16401003440340d00c6030310180f20169607140c1400641c90300820b0000114801400a42c01001105491a6003846402d0050800c0f0588030303078020f20340d40007508402685c4030030095014010b04210301d41021500714003103100c6610001d8014446203241c840d200910141010741c5c003180c1d8074036058444100c40a4421511a940c90950364141581c2030313228401946048400340645108508940d50842241e600c180390814001c1070300b1080e40010090008140c09001304100403035010f02160400d2243e0f0302c0f90103103492600300070130201241c400c41d038411441c1c81e449101c490b540e50540f42c11a1500c58203206c041c0c0d903220120b07014104551119464403810000815505030400040103070042c1425524043d40c0d881d02070691760702c0748442400c00c60b4003400c95040146070104c00f0786 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 88203247 1250 88201997 88202011
    0x803030601050a030c0201140112050c090c120901140406020a030c0804020f1c060509010c020f0d020604120e04110301090c0c020a03080906160f12030c080412022406030c010f02060708 81
    0x5110700c448448c01007001800e0b0001c03000b100348880314005000f4100007444400404030785508007400d110610b40c131749109031206040c404413190000360760000d0070f43c8850a09081c1f051000360700c1c90240380c110029848140c51001081c50300e032110742c03c1c52280c20359510895003d06003d0300c102501c810400003101c692241c0c401000321082c0e100001d929800703440e0082c4140d00012a21502d80200a41070100c1f0384040001d42d0300449044400e00c4d8002038054010b87c00a03040012045520012507d000119411a41050501c041170281e1a002c00055040380c0070707040e04100350300c0c40f030000b140c0d1700d060400040e5010391850b10a20105002030000d10790b010f00144402c3ca88080c8021240000f1001d601c192150b031003100062061010190102c0928605407608101c0590310070805011021301400140003c15101c0c0540c0e0a14002c002044c45145015140003ca0030301004600009004884c124028010040001e0036540a14052240c03241903401800f141c0d510030390b00300d50520008290f4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 88204497 1250 88203247 88203251
    0x809012d1d030408070614070b071710150f0804060507031503030909140402130e16090501050a0812031810060303021e030a0518040209030106080303010305070803030601050a030c0201 81
    0x4000495403036100c0d10740e0081c20790156482e5481e088809007821455404201441030090103e440b44007890229900260300945107481c6440e1140c08540140405002c4c4084172992020b21174030b0708800e1403840440d0101e6086000c1545001ca044071400001000000820410303808140003507a250022130313204240d03140c0003a02000303c114400184d02d640e0310940116810b0380d02440051080c0c06462892050400050003030f040a1740898254000807840501880d52128004a50b02c0c0500c6007032011580e001d140c581c803d840304540d1005180031311078284512001e41000810007004104c010342402000c400500b196120195201c000464040d244003500800e041008003001c5031052201442c0030f0f5000b048490440400c444944000b1000351a413544188a01c4100c90350190884443c1c01602c2c5240c00c19402900224000e4041c105105903d54203100c000300c0d006a001010314101d030701840446110b40c0e03940081640fa4402610074900250381000b808820b68080d81104402071014400 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 88205747 1250 88204497 88204511
    0xd08090f0603070c0302060f1003110301060b1804050a0b31050709060807020c09150d060609051f0515070201050d11031506031006140c010f020306010809012d 70
    0x20a0342c0d100700c840a0110301c9a95241c0141a810015a54010303c0e1790010a00e81c10186c0501e113010449100081c8403400e100d40054240d10700307400007401014902881d0b520b529090941c002811701084034640030b24a0000000e001c2e0100780607000c20500040c2c414018181c400b40b19241044001d84010f03480c0108001d0548541040d00c5a28401c0348282d0790201c445084c54001440100080c20f22011944a003580010030b6851901441e0041c024146110380b807248880030405561300d180c030107420f15207004000100c060180c1c000134032030a144500c00d92034201103c1d101c0048070070350003402e8000c20180c1110b004500814003d01055005040060800c0c2c01c2e0b1246006485030004140b06c02d020120910650f84100318501d689041e04440c03203411440c084441070510b030030901c40d034410403035010000c0380e04070030721003c0701c4002820000030311060031014000b001070340c0250342c041d001402c4580080c0d2090410b100b00140f51441d1a5002400c116050740308401da2510b01d244514550707a802 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 88206997 1250 88205747 88205749
    0x102060c091908160f05030d090603020c071a03150901120201030b0f0915010915021c0306150504030312060b07230109053a0c030509040216020f010e0d08090f 70
    0xc0804c00410702190400040c42c01c003104410f8441c6240d100b14066440034000340e000581080304802030f90018580145c90750004100103142c0316081c0c0c0480b00072181d0070380340078131504540020341c803550350300070210900e0036260180680001c00744680880b420300d21000c1c000562094001e803500da18020014061000388900064089100340ca9038020700e81da14190440369604441c505004002c0c3c6034501b4911036103124042d40301c0031800c031144034090b04611080380150103032b03100320080c010f84070540341078940c1d000020b011584240402e5010581c1581c01040c07511240c080c10098401e001080c43c00c00701c040d61800d81c41000d1192054030840c4401107a070700001e0900c01c112000b03006000410340c0c55801040c1142c0c50b90040340d041c1c1340c10000c1030300e00e61404007009800f03002c80709480c00042102c80350030708407441d0155080b060b600c140005a07034698405900304001200303000301da0100c0c0c0c42030040015240054401019604529002c0324400410701b014050050008007602180d000c42a281c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 88208247 1250 88206997 88207003
    0x30903020309090f040224120c04030b010303080a050a021801031806020c0a031101060324060f12050c101409061b030309060901051e070e09010303031a0102060c091908 74
    0x7544c0c244502d8003082004150310300400307845407034801010507001c9401c0d401c000e1034044c410000c00107500c4030b206020545075207602085400840c1c00546540303055849240c0104030003419100c0b0300c1c0980c20306d030104540c6074492007203414001542e81c0e1012007020a20040d0080c141899001000503240055800810b400d0300003400302c0d013051000f03020f2498a515001d840b564030080f03014207a0380340900900018030702660901c8565810706503e4040600b584003400600600d42080c07400e2400c0300000507041d9480401d444015100b00700762200007002806012442ca488045031002486104c03420b40200350040c000c1c00e170410003a002c2460280030680885510100f00241d280380c2d8000000c21010030000d06c9140d400c00c400700000d000701d050424484107200032509400751041d16a4003c2403101d40150000c2051301030240c02e11400b580c2d00d0030050001c0c1410031408008030414080d84806600c0840d10030720603940b052200c1e007441e06990920010303491304245400d4504402170041f452840030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 88209497 1250 88208247 88208251
    0x50903010c020f1002030f0c16050f01090c1211040209040e070f0302090105060f040e060117090a0b010b04050a090e0c0d0c1a030106050901030b0a12050f0c010207080d03090302030909 81
    0x30303001000d50711040840b003031400d0484da034250222481032003401840105403407099080b000d440c8001d41c07500c03119050034084170100d51000700340b44242d89200080740410b40159807800c1c0540710304a0303107540e10b01c82a00c0d07a0700440d100500d410803140200300c0c46d2030203501030100c043d07001d0800104100d0850308a440d018943d00310415a40e2005000c20441c81c03c3e244888c05000300741e8440341001c0750b0074089004c0d8051401100301c0d07254600c0000c0d689910612202c0500c070301c10340d0100180c0c1000441d95031110380104d001d8a40c40c1c0c1c030000108204004908503812240041c0c580e0182501d040002030003007459450f942c010340541c02c2c101080c0d903580c001c205143d034007860390a02d21514080030310034ac0b890105141d480112040c0010401e1942010070b607003d424080c01c0c0480e05a60b4440065080a603e07002078030205e019401e11824814001862801e0001030811030b9981c011010041ea6508000c0c8255641540310807204a0028825000490054407900450f424048024000b800541003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 88210747 1250 88209497 88209521
    0xf20040609021c060609090b0d0b0a0b03011113050108041502030106090609050306040305120604091514060315010303050a0905040c05070b070c0b1b04080a030503010512030301080a060b0105090301 87
    0x128003514004100c2c440140c0d03c001a620810030149407a0780030305036580520510164036034800071700c02a611403c4034079043c135a01070700b009518a0900340d46001449588180e0b8000e62031b01e4100903a00524804403020045200101e0008501e088011581410010b0084420402164003900a000da41c00038601802660711620f400c6800d0200c000c1040007030340e010607c80c0e071181d01407101007034105c4111500c408844060074030a42d601008180a0a00001d00903c18800358140840c41e11480d44070025940714542d00080380d40b144004c1694031500d405807010044084801040003e001d1001413030501e61504044c8040caa4a0000500301d07021000060041900003400e003007013280000702350382e024040d400c140e25144d030035403101c200045000704050803251101807103040d42c0742000c0070750380285044401c9a1010701585401803d80e0028801c0c00d024002c2070b580410301c482d000c401d481c140c8010340010b003810002610340c41c0c0980381561103c0e050000401501540b81c07800e014180890300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 88211997 1250 88210747 88210751
    0x2d1b0c070909020102150411151207020c011d030606010503100e040b07030c030c0c080903030f030406061d010612200307020105010311010c0314030405070e01030c1d040f20040609 79
    0xb540000790038507041c0c40644030301003201c0c0100400584040441d0b08030f0300d4155400c1c1c4403d407c200c241170041c4540032102038500d400c0c0007080520341c1d0008071015001c07420303a2441c4207888040e080405c0c091002c40516495041003000640301e500ca9030185600131141900c612040360b0301e002d60b000a44003034400303451079403119040000440c4c140c010f203500c0118600d1700f003040309450741005026504990b03005004100005500005a4082003900d10391544c0741a420b50703d0a02d0b02c0d0010040c0302622a0040d03100411808007840010184258100c1d200c41c3c48088680781c9200c1c5131801400c880d942850100f00d802c1000c0c00c83c4c0d24400c0950700c1946c050300000b03003550540c24100403108401440c00d041101c107002540009601049150500700700701e030800cac2c481c2c98a203041d81c00c2000c90f40002c070500c95400000001d2020038000b200c12a42c041018082c14052005411500c4804a4000d0840760a4071403a1700020740c0a80c0300168001001c01c0c002550002d2000501908c5850303010700c0d00d6039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 88213247 1250 88211997 88212011
    0x20a120911100f080c090904110a09020412050d030b090106030e150a1a09060112020f090607081903090305071118100302010e0a05010206040b130203030708032d1b0c0709 75
    0xc1e000034445410064001961b4240300d0b80c200094610400100300514860083c55500103039107034803103d2030103440710540a42d207a6864043d11040c10425410a4886200300090901141d0003442013562100d03026000350491780c24440300707401800d0b100740c0b5400c051050300c841d140d84005a0100a004d08400c10012801c1040140251480c440340141148964a5401800203a0f0f801038002c0c400e003003405001581701c0031440031000302d50007061580c540040f80022103104002c80301009245146440d030b40301c0000c0c0900c4100b1803c852000307a0003408240100007900c0801e141126855083c0070080040203507100c0c1030700000c0e9a003c00d850000c0950400c460610466812001c60508240280d44c000852440c210000350740e0a4090400780c090001440444e0203034040b00e020711a0140c002d400c0300d956124601e002038442d44100d403955006007511a80700b0802d200304240c41c0300449102d1104c44e181e00d5030b4451000c01c0340c41100d00c8808030002c0040c28104002440300600800640800003401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 88214497 1250 88213247 88213277
    0x209070305011805060a060c0318030b091605010e060f0706060f05040b0102150f0405120f1306030513030305060102071d0f06030307120e01050912071404020a12091110 74
    0x1408041c8500301c0c1844c20001040415150050703007500311104d52612242c0c0d042c0500302035030500d281040c0084990b103000408410f10407460038007406036040404071001c00c407008090f502003240b1070043c540050100700c08125640740001c060072164201075421860410346655610407500c441e400058078181c0ca460800031450a841000c09505c0e0a0001e0001c84103140b85c040d0002c07100400e810003e0a600001ca03061181c2001104040700b0313031186803035480070704400d49851600204910400c1807815140400d105101340551409038000760000c0041e541039a03825005804000d09442c114400d116000880503a081140e0300564440302103484c0d0743c10314402d80080c07004000c0440d4000e50042003002c00091205020401451482c80c281c01045510001240d040c49490001903001c5040c480491306614081080c0f000c070f841c009254690102d041040c00168020086c210700400c078071061981c2c6040caa5000080580c2c410702d140660107100300e001454001c01400c070080025041e800c80540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 88215747 1250 88214497 88214519
    0x21050402040f06213305010f080a0201110c0d0f06050a2009030304031415091c030203180a03080108150f01061b0503030901151a0a0f020a020907030501 67
    0x8030510754050003d24140640c0c050456462003581c520710440300c4003241801003907200840480d8401000d036000315001030084049002041d000d05615203050000603800786040340d2031003100c410001400210340304d90019185800792404540360360041c500c242c0415a9048640e40c43c0e00d101d44885440845242454411a0350041c8030024aa01c2c2540050f0b051003002c1c0e4030158111107646942d0b0340c0300400f02190450140d0b0313000034140b44003000b10700020400032445000b4004031101c0c50f440c2e940c03401e110a41d58080c140d1198000c070305035400c04010303e1098004592160a1002c1c0c2075400303003072286180c0f419601e40300540000750f001006100c6041d0501030503140e21000540380c00d542c1070160202c080e40c4018032a0701d050049607004080c000c0900e10454070925040b8082e41d44030300d400da562502a211003a0991400e0800f500c011404003410005071040c6030256506608203c80044141d41c4000b2002843c402c0d031103140b002c0c5006a0f148070845100b655155004507036540350568442d4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 88216997 1250 88215747 88215761
    0xd0605161103090a180e0d08090f01050402130b040e03030c040e0109020316032415020d18030b0402030f0304030c050901170c01051e070506070e010801030f020f012105040204 77
    0x8990340042000070b109950b04a5500251a50305c4007100c0f00003000b080b180f0082c60f400440750054050a001c1802094100b00d0052146240780103460b1034905205845080707400c1110000c2d84005e110715041c480710200d910012442c1d4000d000056080f299030309151071500111a040e4074040c1c0090309100911095210a004082c070300c00960a5051107210111404070443c1c00c5403c055450511010700c503006480320b030303270300388415681781d01d90b0f171a55220329040d050309491901501c10789818010b01c80c4038480f2000c1d00841a01401030690071942c1e04200c400014105aa051080e40c0502c0a03144043c0000e100640c490350480925610304401e002c030451051b0701401070003da80203034840360704001c20034801861003403800c07560301c100000e68820410403003817010001d10710100b0250100000040e142d4014003258690706090b03480c110044814820134000107040c00c42010940c030040c05c08141d01c1860010504110800c1c030f1404000700c043d00e83e04800214015100c4007030005504251082c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 88218247 1250 88216997 88217027
    0xa20030f060307120c1e1707080607051204020607020d02031009030201140103031e050f0403030203040315051009020c011d060f06120d050d0207020406030503030403030501080714010e0d060516 85
    0x44c0340700e0ba03140d88440c02e07098840e0807510f80d81e0121096a00b000000a1800742c0440071840e042d4446449116070349442601840d41144a60004200703054000c40a890040c48210f01883e11581e9560071700285401c01d24080760481d0900d081c090040c1d41c140490640b44c10011400200321149080082c00d40e40001d08500107048210010320200360b02801010040d01801042519806c5400c3d04a0302e510800c0f02c0680702a80210b4003208260b0302100500c2120300801341004036045d820700a404440043c3c4215054110034079082090980a40143c420000030400024095000c03040302a00026444920200e5030071500400a480b00d90015a41d00700394103803102c210480300044e8071595924400c010a0500c01c0228001c0d28802964044030525603001d4004e001c220381d245401c035070765041541d040303000c607040100101c1c0f190350003d0f20030200d81c614901c1ca0f41e0a80b1003070040d00e4001d03c4c654120b4200700240e4040001c02d503030740144d501a040d07070f02403c8030a4040070030042404094070300e10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 88219497 1250 88218247 88218269
    0x301120c0e010e070f0c05030d0905070801051e07050f0403060609050f07080106030902060c010c021e0a050d05030402061b06090c0f030a030503100e070201020a091403060a20030f060307 82
    0x5228071420403500ca54800c505007171125030b4500071034050b00e88050005000744140b0001500005006507070300002c1d42c0500c54000c80d1001c075190705200e820384100f02c51040e44a00c8a968a1510100b11450b043c0c03c81d01c42d00f003907441e04d01c0048880740a644250800e0352415104c2c2000c1040803410711078a544104d203040b410a035400c10407c014042d80040c450202010345691400056546d400304442024800e00300800910a0100c0d000c2d4484040841030303117800142400c2800c0421010501c00f405c00e034001c0c00b90043d40a481010350701608050700c1aa00060148840703519403c0c607941c812208001e0130002c0a462421001c120701e42200d00c80c0142c046c201d5203d002002c0d444c001900154103070305050140d10303903a40300b03103244185550fa8403540d0301c800900d0511811135010350003000c4592441c1d9070300841a80f13441c05c03603c0305c1d0725480c0e0f99501540240700090b1000c0203544212209414820326203a85941600c1880142e0400d036290018a01c440091190500d002c01c0b0b8000100000265 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 88220747 1250 88219497 88219499
    0x60509010801090b03011d01050702160f0603050a09050f0a11040207080304020d0302030f0a03090210050c06070f030b0a030302010515030c0d0809180c09010201060f0506070311010b060301120c0e01 87
    0x1c0c0100010f102d0340040907112056081507a03400c0d0420556210760b54180040402d2203034580e07000e80030684130354015008030002e80404101882c90041904c03112070300780300c1c01440d10701d0840082000520006440e5503e10446001030310522040007520324180003130180c10381074108540ca903900faa400900c6244100400f20001d9078080940760f2064044800f60300982d9141000c0e0b06601c501d8101c1e02d40740c50001101c1c4c041c150143e10002006000f034511807080d00040e802610b16115078205090a40d120030f000881c00d900c61130002c1046040c0b80f4000c10000c2c0c0710408542e521403d900b084025035154030402584501d2500c03131600c401000c500070309008d0030300c1010400816003810060b241050000e035030402ca44a86c3c441c18103074048040407282624004140918076001070f103140e4019406c0c200002030400c005882c24080e5100144001c0c80c256450b581518540c10a242004865484801241c159a00c1c0ba0185008086c81a07104a42d182c561509084a4039560000240c88c021200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 88221997 1250 88220747 88220749
    0xa0e0f0d02010c050106030c030b160c0317060a031704050418022d0901062d0207050d0f1b060210020a080105010507060e120a12140f0415060b090901060509 69
    0x2582940007902800c1c20705503039800b030030194090500343d0006000715400c1440082003141001105225a80a005a00000303031081d02c01c407a085000c1c0c2024001650400014035150304900c03005400101c000d042c400059542d54a80d50a54680003682e459a04013260400c000c0c1007a00490780300c0b1031107401e11144202c041d8001307409190b90007c119214482e01c042441d10790401042c20002200c018070082d1a5a96820018031581031394155554040140c1549410503200004601300c003121038000d820400d017020188800510140c60685106020303045800c0452a14802c211504030f41d00f5800c11001e0910501a02d4080020807407001240f04000c40c600066214003a541910b0007464100d95500c1c0609185010b4140385c100d142e440c2c050740c40601d82101000c0300a181090003034035502008d617070401e4811704503003c801000e4540d459940002c0c1140c040d515079268030a00c00c11411344198001b111000c2180d480d900035a81c0000700040c02c1c1a0344c1342071624035005140e07602e0241e281c050303060 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 88223247 1250 88221997 88222009
    0x3040b070803060a0f032d050a0b0a0b060304050601080f06010e070806041e050a0f061206020702010221030604150510030e010609110306130c05071b030f06020a0e0f 73
    0x460007800110380440070031403030380e16031602000a05c0250098003c0c0d5490f410038076000003039002c2c0c050fa414030040d55001c2c1500c42c004030404c0c0c6071b00301000c0c1465039503a0300c9243d607002008203504211581c40030043c1c210398400f030141d4003540c021001003907a90b0400080d203141000320203180300b19500120040010b4840000c5003a40030806103401003e50315010702007009013516100710400d001400b0784900707807480180d20542c45003145020501401e08104144404c0b5000e5000c2c5003911440303841c0360030114100e50000c140e014410310440303542c8440c103040352600010b00805e4241122001061256a103050300845940b1300810b03250300480b07803804000030403291288100c40241500c4280b028181e001c203500010080100030340c00d0001c4021041000119403045460301c4c0700307203145400110340e08800c1c40b95591000098076424900b04c81d42e2103919210b5400d0b64491480b00f485500400068000d951851040d40b10703040c0540c4803020326001500d02c04220a107c0d0041e803198600b14070540d204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 88224497 1250 88223247 88223257
    0x4050303040f02030304030611090a050604051311120709030b070203030708040212010905030a0203040303030f0506090105010c11040218040b040b0102061306151e150c0206090102031603030501090b0303040b 91
    0x8444407801c00b1075101107402c600a40c1e102408040c90301140383c80503c2c05030010f2001500484a03d94142d80710004c001c0c040c00341b4000d254102a07001e8028540e44c010b50302c2080f00f010b00d03000d42810401d414803172001e42201110407000007500040200204441e182180350801c4a5002450441c80e060200a20702c40004002034400c142c241d0703001060040039030003a04e00c1d6411000f0769030385040d0550701940c0e0760300511003240020300d4a10080c48074186486014000c08005182812036441c0200444150984e82026181c51050080300c4025036190301c018000071500101c20400300071450f0070007084488442c0201e01503801d0002c5a5a0707680c0c0494443e500030794030300398958100c07030505120008010300600f41c4c1c220103188001040c40c1c0c010380798900d2819450118a0415900c031240403a068044015100c0401c0007100740d2401843c010300681411901071040b24100108141c10080c91143d01c00140e01281d038490052041200f9805040d22150042d00114541450000f25100c2c900c50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 88225747 1250 88224497 88224503
    0x90311190812061201050f15030a0b070e06040807060e04061508041212060807090e070b0307050711180f06030d120b04060e090f3705070f0f0f05090405030304 70
    0x1640d000407a00c2d42c405011011132003074400204000d24003a600c03603041240a1301d8100341e04030180943d0044c0d02e00060141e40351540002d1041442c1c54001d41030b81e0300c650860089a004900740001708601c4000c1020400402866441c152085200e8040c002240c96a420202d0190104e000d40e0460395040500d00f074100c1d0348111079000154140000300d400f0b040c807030f02c19032030141401000101d10b100080c0c2c103402e954032640100b014040250f0100d0340c0e00a148a18100002c0600c0000d141302e0291002d00b00d50760280d030801c8024002c8030006031020b0413400d420703542d098801c3d0900c41100482609164012401e800400d010001c4070ba0140ca140920b00c9244007894803040f42c405580c8590300018001c0000700811070040c1025094244c80b65908280446d05109490720250510210422121000d10415444800d00209101012400c04044040c1d5040c85181000035007207203003d0064001b46991300010b180507080c42241e401100c00d6a004911403c02031050002280010040340d41282c0c2c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 88226997 1250 88225747 88225777
    0x18020c1b01050405040207080408010b01020c1008040201120c050c1606020a080702030a1a04030e040b100f02070f0803120a050408121302030d030516090f09020904020403060903111908 81
    0x400801210b0701e1285800103034129002041755001c00a9030340107841580ea900009002c108141001240d440c40c00014099000d4000380d9248046401294866041170040c074004260b00c500c404c0c04010b403000300e0b41041c00101e001400c040c0b1407206200d0485031b5130040c03040308059868000000c0d50380314640400382c41c2050006150085550800112071050303444004040c038501c03a07100910100e001254140d020410701000c2d500c00d4a8280310392039011100900100d0b0701403c0c00421035021102054034000d5105100f004180d03841440002001002c24070005e55581502131284108440041c1650083e181010240400a104030084d2100c0449075401401300d550b5444119040e03059022029405d40180040c40c1c3c0300d00d0345a000544140c24140c6401000e4080200469100d0705520802d030070300701901410b1107074a010360001c2000d001c1c010800f50810740c482d1564401c440c5801411004100d4440d0084030510050200c001f031030004500d1641102101e8640800c2c0c0d1040f8550818540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 88228247 1250 88226997 88227043
    0x1103010c0801061d0411040e09070e0412020f070b031006021507110a0605010f031e020f091b0c01060602070803070515070504031401090506090c0a030b0c09030d0918020c 75
    0xb41c1060014801348500801c1403100501008080107141d0140c01550340a0749110006035814000080f60780840d102460f0645c02d941e610380320030703001c0903a8542640440c0a101c01008401e5002c10494024000500004d5507a0410240c41c0c0d03411f03d00751b80502d0075034200c0d40d0404560003110003503c0e4004424142424000b056846981c2441405075006010274034280003c01c00c940500b49810030390f131007808000140c1d0540c450340e51032000a64002075000003a41009016404c10781030071508200b0041c5900d220002c025943d0007a070700400da0104003695104070401c4041e1741000b03290014003885000d18a416950b880e01d94130b640d074100210303060b82e003081d01056003c0d00c00e00840e4002c41d04a0816041481c54410082c040e000c807003001d0300c07940705890100e621a000030031117055041c4000d045001c414078654901003007200c000d140c150754220502c425806a1818840340c8034405d0305a64410300d1500b032103404042c3d408141c1034080c035140b040c800c031500c0400000b8180302682490250380c10b61 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 88229497 1250 88228247 88228277
    0x1180c031b17030301180b03060601121806090b07090602030703030903120905150a020a0504090b060d0e030a020111040f03080c07050604060309020109140913060b0604030309031103010c080106 85
    0x10032250384000780500c8200c4440259000c084050b50580f606810550a0340042090305d400352042d8940807036054002c030b00410340d958068203096400c150070900213700d0204000c00d03040d5491015205031103803510b0341681001c01a0100410ba440459401d28400c0316050850007503690180600040c1811f50b9040402e09150040001540711040f83c18140000081d82c0b401507210016a030f500410356582c00b02140e664442402540c0c1c070076a460b520603051031310380303c00007020b803441a8040b500514108602c00850345240501c000040a550003190340e1124510700900311101d00000c440c0d8000c00744070074002c018406000c142101c2d00503d000344c07201c21000d241820149258040303030340900000340c009070050705504540c4099001740c841c00e10003a0380d208002c541c820040032159018100800080205068810403811140100700000e0721100b0f01001c207480d42d009400680200d80f444200304100b11141c1407034a02c042003035000340000140c2a90240001d04180134500a0158010b624481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 88230747 1250 88229497 88229543
    0x903040f1203120c080a0902040e030703050304050706050918180717010b010e0a0b0a05070609060f0b030109020901050f0111011506030605060a090b030c040e0702070801180c03 78
    0xd02008010280034507900c00c20303007100e00345038103007140810005044040e502c0c0c40351003012408040c0751030381c4040381e81d5840190014002800101d038019603420b0480782950040000c2d002d900c3c400e4641079524102030338001e1034040e260b03200d0750812804101c44641038070b400030384044071054549403801c1c7d41c5648843c0608400340c045210128031541c1c1c03001a170785601ca03002c64482d00317682d03000300407240307000c4011100b02034503081c140d4105819503400c00c50016110018024a07040c4d181181c10102181e440b901910280c120076238011b40c03a9100d00c1d1182d81c1512030060704401c110000c014690041d07022820110052041038030443c2004104a8281d0090b01c0204501c18010300030403407556803608041e0a22118040c2400107490201c000c10310b0701b495821180802410b0720344a80703141c40d000550180380c1c40102030f200b1240051000082103001c0680301400746820303401404515082c0120302c2c3c02c40e002c00755201403c00440d4a800302080718000d0007400d0303e402c040c0c500014501d07008102d074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 88231997 1250 88230747 88230749
    0x90f12030418020702061207030606030e0c060d021b03090301060f06080f040302030f0706050114030307030504032a23040614010806030a02030313080607091404020d0603080a090609050a1a03090304 87
    0x2400075070009039881140c0b0082c051f503109450586007008860b455030000c40c05c070784200103007d00660000700c82207554034005015042103d24801d0141ca82980d025054100c64100b1b040800117620208104906250070700a10016045120f00c40104038039010300100076602c0035140c0103c8255000c08101454400d0040368421160b07450215a20b203924506440203240034032891710381140101030085946004801c4031507140c0c050383c07024141400d40d16800d200401c0000c1d0384c180c45000100d110b140c441c075601c10b00c00600117943d42070005243d0034220043c880d085a01540b00c0c0b8034010003840316024904a090451000380b9155441340e0386c00c0c02091800a000f01c029505100100d5410280c07800c04d01480140c92801041e6902900c2d030310400e6a0640d046d00540c4006040b8200da00f107141802d501408c1e0913450050041580395807a19214415809207003043c2c0000c1031140c1c103000300741d0850901c10051030252343c41c207441860000b0702c03407420b07510205101e981c00d8000f020401c55503042065038 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 88233247 1250 88231997 88231999
    0x105090a03020a0609031a070503040b0a060f0e0a0509070302060a050a12090f12020a02090417090405010602070807060c05030304030507020607060c0e01080702060f2206050a02090f12030418020702 87
    0xf945440b9400a0202c0d21a488122210130f202e140c43d10b80c044078403e02c2c034044c1d15540c451505641361303a92180105c080080c64a050a660b8010000c1c4010303180c1031500081c43d040c2070246940c10504c42c50401c0e40c00c01041d050359940101c400f0001a00d42d607048505085035440c25a85a8030b0101046842103040c92850f44802c0c03c03c0c0d060018002d810305804a043e105042d16507100da06108103a0300c9484c1d052000e540120320030b0009000c52010740b051080301d02c00b0b444940c6485034810000302101d60a0f0080030050b03100140910100b503040180d00301602c918100541c900b8642d68440d5135920000300300400300040403680c501107440d40c41c10365032425031222060101050300030000342134403c1e490959001540f6030300031a1400740003045180c01071200d107100d120319541c0c40943c00c49281520f1803410b8140a8840314001044007486802d02503034140d4800369848040b07004200c552000c605003544600340c601214850004000116011180d8071010700070b0751044510280024001e50340c2c0030b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 88234497 1250 88233247 88233259
    0x20c011805030901031b090b070606080f0a1e02030307140a020a0b09040c030204120303050718060903020306090d080714070b09030912010203010510030f0b040606050703111603020105090a0302 85
    0x108100d000300c080c3c100f012083e6030800000381c4d4500007600741c900644a180200f050307030350140007100070705000f448a1070041002140031583c4d00032003440d1044a034031900903900010043c404114201100c0488502c984610000002007900080e80300c0c40340c004001e05601c02c9906c84061040148842000241c00802e40d9014607546c59503141c03a503210304515480340d442c0c00c90000445020f8805e5400b500c0c1d401d0b40b15601d6595642c0e060b00207000291449003882050124810005515203401c4040c02165480212441c0707580305043c68040701401084050300414925090703135070304c103160603403241c5145003403440d4040c1400903001034421010041d040c4407001080200303080c4004002e0062110030f44440002e90001e0a002d0b00702c0c00203008055001075000030240503144a500010144446101c002503c0310790703000005c04403940c90f40881e0100388041001020305401818100540340003c0180c15000c0c04021a00c60580320303030100034144400402d26030f00a888a840d0179000c1d503405005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 88235747 1250 88234497 88234541
    0x3050610110a050f0312060307320405091006050603040b1b09030114090613030e040f02040902030f040b070e0a051005071a0109180b07030902150703030203060f01080f060103020c01 80
    0x1e0316588550300242c0c00c2d07070b580e44c040b40c03003820f0002e0110700b1a04650042500ca10103480585e244076920070ad11188241a4180c801c0c076a6100d12645000f0b02e0400c00505000b0150302c3c80344141c1e01c40754000d5109100500c10480480c075007220b01c540c0315420351100e00c40703212108001e50640c003e01c1c1c0704907059860682d60026002142108500078802c200844a003599102034080d0046a0454000c00240600c050200d55050a420032032480301c42c03103005401c0c151581442da0481c0c10031070b20016030f14400320500c000d20511004458100381185092510740d6140300108078920641c0c8602800350f1b15840e2a207031040c1c440c90684c0c130030682c0008110080031703214000d211308500070300807242070070703c4d004104480b80f51000f000307400203601c04d042d202c00d90b840000035001041c0d2200241e8001c03480c002c020030201007040c01440c1d034030f01caa1001a01ca007014001c0c80107101910704603605202501d070520402c481c1c03103150607510940034079000d030795494240046030141911140050038081c1040b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 88236997 1250 88235747 88235773
    0x5060c12071101200d0807050405120604020f010c1e06020d0e07030308090307051f02040e0403030204061b08030604110c0d0c02040c0816050a0302160b060405010603050610110a05 79
    0x54142c00002d9031460007801c40c045106822075410034a095181d4014841c2d001641c0c09401d40315030100c99400c2c003d0500381d0340ca002c00d11111100c55030010304e41005003007000314a41852004000f110030320704000e008400c2d695500d00c1990087c15055510f09001854042003070580407504c0c40c2c8205070b01840000c4131002a00d9031400140022000703e44800002801200c3c008291807116805c039000340905a0702000d20b03c3c03010440c205441607640c082101040d02419440454050391007aa00103a40703034275265008050324003081100222038600034220000c01c60301030550750428400c9500180c0d0010030b000b00113181c8540c0b9400c0d10a070182e0000180215009204818a54001c1d5400c2c040c00071074450850f4800303012122040380303585c45e40404092501c504007070b11354503626041c0140b03000b03a0502200707202c20000b04c080740c80103400e10070441c540c01d0a010301401050542018059401c00800241c022034044401d1030420401038048180b043c000c008950206400c1020348280c018528 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 88238247 1250 88236997 88237013
    0xe03190501062103020d1407060e33010b09011403062b0201021203070c080a11010f0504050f060106020709020c01060b0703020303040203060f1e1519170601030c05060c1207 76
    0x240e0250150306140012240643c0e4002480c000421150307141041d550b649c04010000b044000c4040c0c0714442041c036404211460601440c1200000e1800319030103908990b00074101600a038400013014843c0442c1030340c00c100440b02e4508401e07001d9850f5540c240c0858400400d460b0a420140704001106619508009114180b54001e81c2950120351010200ca040c03888141c139000005020b40c0740c454080385550300580f4178900320b4580401d1550358181d00609640e041030b580601680d40d0320900041060400003440d04003010380140180f503240601c003035203c0e0801e1213062052600061903100803902035202601500d114050a80c49542c3c0e0300b00296a038104440890080c0700d0040461140c1903482c1000c0d1140680d000030700314030580c1032504035105034054035007440e80ca404140100c1e43d545406001c1141c034402c107225044c0614101c0030a0f11124900400b00803030300810014000708107181c1d00181074400075242c00380e4906c0301031481450700c9150040465109004204002081080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 88239497 1250 88238247 88238309
    0xa052803060f060504080309100c0506041a01053703050105010e0105010311040f090903030204080f2a1e03030f0315040f0501060804020f031e06010f060e0319050106 73
    0xb40128440007600e6110030307642c42c03089001d035424070340c070500001c001b038501400342080410b068a84507110840b282e84452401c4400d44045401c141200c1140c9020301150034464010101203400c1903070040620341c10143c09021000b0088603004240d00c0d4400c1c1c0f01d01101d0300008552102c0200f1007503030346d00d6260002100030700503e070000f4100410b91500d500c4600c00d4909560016110f00c0190b4900007804008001d4440c088003411340903c030005c2e01680900c1502a200b2001c0080d00b888101c030004980c140010610341c5801c0070700e0030040d0305140c60b00e1005110002c41d82243d0a541e240800009295000744800840c96070301c00804c201000d080008a41c040b0201500e007885085c02204599040e6507090040344005821080084e0140ca400a4800303580b40e0050103451019500055242e4050600c2c04480703500d51144004022442210384008020f00b003a103010183c544075040000e0700c0c0e080c0ca0311040301c0b048241a408040c094290710040c012b1030043d45140c0c0c0300300841001c1d60010f0304 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 88240747 1250 88239497 88239509
    0x40507051b0f0c37030c03060203060108070503010815090a060e07090b030c01051813230108010e0618010e03042304110405060f0708160506011205030a05280306 71
    0x40b0443d64045091080142140d2040d208a907100616900340c14190016060b500c088146030b42c0200001150300c041108024500079040941d2740e00d406000901200000391204082010800042004c15004560009502000124071007192030f0382c0a528a0400d2880303000d0207982c9000d401e100c440000090b13840407160388500a100b803480f04420551510440d085039400304404100e6071362100044003007549440070041108a41d88009061441107444015950b40d42a12102e000080d50011110b92030042414038020710100c204240c5841d21102e0107030414661000ca80e11241c600e003000c2d048010003006d46c0d011a03880302c1c1c1d0740d140c103000340043d84010010740c40d2103c600a5207042500883c00c20b05118014545050726000a00c8441c0d449001da803240184c06210303000c00202d04a00406184d406566030201860f1242880c909005060340004845280510300100041c000b00a03200342c1c41039070a00d2038903501c510840d400141000c0481991580004441d2180d054240d0b0141007541c0c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 88241997 1250 88240747 88240753
    0xc0d08011509090c050d0f0f0609050c1b0717030403021e011e0203040b071b050102030a080402040b0f0d1406070e06041203090b030411101d040507051b0f 68
    0x641c40740d1650510700010010030000b401048140901501e54214214803071a901d055440d240c0c0c241c4100c421103003001c4041c000582c030b41c00802d040e0041c43c01980080c1800540400050404141950b01e91065401400c044030a0110b025030800c07045c08204d004201a801c5122078440210416441c0e60003404124825400c0c603507890b010040d200d02070644140103031100250740c641d812409009030300411100e41144810440410205201070140406500c1010032803442c0011400700c1040c885203400240c110f5005200030003490383e000c4891504207170151800203840b0403160100700721420071100076800415038464101008540080d00f506013180c0c605a58582c0c64803a012a0210410f420352036000d2002c0c0428401d0a91100c15441058031906114003056500c00c03004005070401c480035581044410784460741401e0028030070441111501d0801c400302d0501d1011800400360b0145980200d07a40c80c00034004078003d070102c841d04962919510100ba01120116a94180002051a41d40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 88243247 1250 88241997 88241999
    0x60504051c020102150910020406030e010e010e0303040b0a11070b0a050906010b0d020d020c0a03020a1208010b03010e070c1403040305010b0f090417070602040f032f0d030201020706020c0d0801 85
    0x50200703800d0340d04164143c0c081c1100201c0b5400550340c152001c2c0c46400350b80111907800a6209040c402400100401d407004503078203260340d00c001d00716001900c500c001a41840742d403003c00c035004012a42e000c3e41c81000140306454040c0c60030003c140c0b0056450104c1310000d00a4140305019840a206946502040c00700396207160300d450300d910f020b00c205013030800b042c047c0300740100c004d4020340061004948014140607220304803d103000810a015000350b006802e0314070a100b4412200348004000e41400b00711549080e0781441688414440c1c9101682d0303110101c0ea034644202d4000308400e4007c128050118403900040361070b9071040c0700c1111250301e0104030705d00c2c0703042250f05501c602400515401c0039030343e0f41e203a6600480010644e00c0d260002044000000782252000d08098286440400e4020b420b6180c0203a00100891170b400c01c04e00f04510190407106425903051000f08103503400404079140f89020381c06400b900030024407182c008101c2e10b01180b80000c641c0c0004450b5038541c2d0f02c80e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 88244497 1250 88243247 88243279
    0xc03020f12070504020c011803050a090b03010b030403030e01090f03031b09030807120903120801090b0303031303030b1306091a0d081206130504030201140105100507020d02010e060406050405 84
    0x445070741a403070011504603280c100442e140503409880c9086800f00041a0311400c10700411054094042c22008190040f5038000d2441e07011000e00c0c05808803007800f514550500c0324904203400002c0008040648400c14056010401e400840c1c4c1c06034041c0c0c4065252186107400f40c003400307070075414005503100d454201001170b03c9060b6450460381c0185a445c601081c944071003000c075640e05103620a02c115903000000044d03070f51500f4064121160b840e100315506240c0c0c90010782e09540e040c94420740c414000d0211054038103481c05902d56160600040800d02c030408555041409a01215141d14261000800d002150000c40740c945506000802d201074280411215101d13000d00548900350600000503401140120340d0340001009241c411a138181102c00c5042d20000c40d011801070f516515200500c01000010b280074041c00c50f03200c05d8400d01158010800d00442002034420455910144150f90040403106e1204401038800c6559075181c1c20b01912035801072040c1400344680341424840 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 88245747 1250 88244497 88244509
    0xe030405060d11120a050703230a091106070f0507050d0b04060203070c0204020c03090102070e070c03050d090807120e010c020f010e010314150102060f011a07050c09040c03020f 78
    0x603648014402030512032184044001010003030315034559044108a04a81d000c2d41d80c00c0c00d032092491440100c3c00345050003000f401d070740030102804442c0c0400d03c00400039403d90700e01e455002103d01030004080923141072400194040390246a0095000500c1406212482e4001e00d41d56005008580545549100740245070140000142c08d48581d803012600103890350b001140c000c155854010300f50300c11900020103d0380b00710145134880c1c1c0009030001c104e50701801104014154108444564900743c80c0103810342407590401801c0280c00680c40c07100c0102035100300405038000030303001e0711031030f5500c1c1156110048022400102c2c001348001b14203584226614810254040c3c140c038402c11101c8010b49500251111140c14161510915241f40b684d0400007407181ca08100005400480e40c2c0001e41880e601500d100ca11468840050003034214442900320350f502030500f059650310181c2005800d1004101380e5942c803010341820322061100d652150343c00d0342d000b20f0b90103007002d5088040100b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 88246997 1250 88245747 88245749
    0x1080a140d091a0d020a27050306180109050a03020303190b010203090108040204090204050a0f0b0603040809190e040818030a030801050405070504050a2d080c06070f0b1501030e0304 80
    0x300140b40c4000c140560005410150900f80414402c01d08082c110801801070740c0101c1c8580000480d40d40e07172041031116200c2a1880881c25021400c2410304190110b0740f2040c00603d40c0481c244e48005010f400002540700f032080e1f540040581c1c11800142c84c0007500c81e8004e8440d541742c03d40002041d82c0b42d02c482e10500243e82d1050f0011882c010380d0000648840500a00c26a80a990750203001c000d620345000c1d417032080060420002d2880f20100c191012030307240506043c0110014010080001c561100710b5055001c04c960f03103002200030200e0821412007a412034400960802c0912040203107640140070808802c50303203108030f041c002092541e42e0625000c0900019000700042049003056032149410580c41d203001c1c0e240584034004580c5242180e40a10104440d44009144a200b82e07450000c00c1a100700160050302e01d030450503503450399200c0c16948034160004205040113005820619480c2e0300c0310f41c80c41c5a02c1c00211551240c100700c0304060210307040150b02100240c0100440e8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 88248247 1250 88246997 88247023
    0xf0c0f0f0504050403030e010c0f0f050403021c050f0a030f080f0c180609030f03042903041403070606060f0e01020607050a0c05010605091311040902060d020d090b01080a14 76
    0x8810310314100c00c01c8090200075100390305040d51404240c00b01e142c28006c8125101c415210f41403541807940c40100807001441c244000c0000601050005a072101d08080c0b404a148002d91a912440d003049428040c1e0741038160180d201b020345a004061b04000044001c42d42900d45040701d950f409002414140c04680840c2400310400c10110108071604100344500c1c8094951418000d010012038500800e00301c9900440d400402c0400024040745a400d006c05840040d01c1c42c501c01c5030a044010740000b41008045040f6150320140103141081034038105a00440c1c20701c00c0640d602000f524610500b411280000c161545c1a03603554000a00a405030301d80b69035092424010b14012500c0c9681010200c5140d501c03007900040320342e40c070790b09180034030701a40410744a0401c0d480c0c2209007160b01900140918203051001004d650f620040d1800d04400d4100903a45d0085a40030100901d144d5000406400341710001046080380040d0084100e44100c2c1c00324800b1030b901c038210741d82c0e0030b000b0120 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 88249497 1250 88248247 88248269
    0xf0314151512070503030c011d010c02070302010f1202040e180109020a050f0604050603150909070b1204020d050105042603100b0903030c030406020a020a05040207030207210506040f0c0f 82
    0x8030007942030115410402c420440141c503006501c0300002030450f032000081440702c3c0c3d12074034410040921000072425142d58003000300714000107144040e40b41c405510000c1d0600c88008815607600f8042e220a01003050700d00d208643c0e80351101611950440e040d02d250209615005c55420751440501c0b582040540040c800d41000c1d14020812008076000361000d03402c0823092200082a03121413020714050002c2c43c1c0002e04059100c4140084044003c080340320507440b04404020780c44c860000c0343d04141c50a00d08120b90754450020520302800200020f006600e003000300010300031850b500b0403a445120880c0d07550102c000c070021010b40000d035020b9640744c000e01820060180c80c1c42c000c01c0c0e91b80020381981c0c10480c04140d100e046402c15031280002d1303008041c01c2c00c2140307054000d40000d00408c860850414150342c40c000d594803454064414020a0940701c0d072610b020b6940700b080c0165216003261650714061800000d282503028003203803132540f050f03400f2130110800c0d02c020041d03581e20011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 88250747 1250 88249497 88249531
    0x20c15040c410a03080f090f01140301230d03080103050106050a030b06090612060106080601022103060904050f010204090f0605060304031e051e070c09151208040f031415 75
    0x103100684011802e1859120b9004040040000c800780041c002051400c04010340b5103842105010700180744400141c1088aa07180d0500d00d142c0d10400e1703a0550743d40c1124100354078101c2405030526142c4808003035100c9031442e0030780c00300b580c09081c02c1c1c10380f407180c4000e000b0103a8460500559100a0200030003c02060002030403d08181c00719580c8504014503c3e00007640c0c00220030b051080a8100e080000c00c007604002d159601000b102044e055401e12880981c0c0080c2a00c20081c0400f82c002c81c0700b407061002080520208004100020b5071160086540780d80d40e006520041500302401c4002d41d00300f200c00070343d92400f50240d80c41140c058441c9000312000a401000c8088201c2002041c40424800d061821419603009903803075000c0300d40700d640ca004504142420f40b205500c43e0080e40d05250a140050400e41000c00485040c0380240d200000c0601d05103e0901580c3c0000d190400c2010001043c442c1c0c00500e02d000315940000e846c443c40707074036540700024813049400d4050203075401c2c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 88251997 1250 88250747 88250849
    0x3060801020a0917120f04080601050f0a1502070f1d060a0806040305071a0f0108010f0c0f0f0203042310030509030702310b01020c0a120204020c15040c 67
    0x101000d101d0654050345c8140c18032112242107500f0103d2140c1c241000406d05000a040401105014217001c031000201f50f408080007410840040c05258440e02c00807501c8030740c0c903000b00200005000f8020b010507665856421012031410700440900c0305c100d407240454101c0c10310b0350101081d20350481c080c1c0744030340d640d03142a00c041d440000100d030100207100440d0b1820703490800240c0152070025107844154074007014103003503c0141500044191401880505182e00500e0f29444240345042c0043c000101c0001641140200d030b020b10158101e4116400740c00700140703511312100c6000c07110300c1c213900c1881208904071a802c440c0c105055108015100141c40d106a030781d24202d80a801e05191318901641c0b03510f4454061b00408841078907950502500d42c0c060041a0303034080103846074050a40b5056a14109070019200a4011540055105800c01d01481601248040d0542d07850040c01c19181c00d0359105040e22403001800200064072444090095451041401850003942400c070350b04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 88253247 1250 88251997 88252019
    0x6090d0e150a0516050c0411090f04050703020903010603050109031803080a0302070606081f061211040e0a0512040509180619021314040c02030a050304260409050703060801020a09 79
    0x10340038400c003800b03203103420000200804e803081d200302c0207800320450f100107002c152101204101907004d81400344080c60b0700c448004400815040394045a0380c0c60302c000681c024400c03d24043e4055081c510084107000054105600f403071b11954518080b00881c0300c24254003c03003400300501d414010442741c07100307a100e0f8018042d00c8d4003c4900207441a50749401900c0d00d650140443c94529400c41c50280c0d4007601c0c49420f004011401840c408a1001d81e42c2005443c5504840d510960303950071502801c3e901004441301840d44030086404091440c65407604940080c031405100302d403900002540c54907115060789242000c0d000420312600d500f446c0d00101d49001241103102503007400704000d214021907451000300351442d1144010b503c05002d010a55100c0c443e50000d540c002c100c000c03016540708084070343c01038204810010201c8007810804000009401d54402c0c1c1e03202007000f00d403102c19503000b64000c6400c1d441c20404179130b45948044c20b034082d80c0741201c00710360041d01c100403200f4030f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 88254497 1250 88253247 88253257
    0x309020a0b030403030507030b010306060f12020f04030825030903080a21060f0b1602122a0102060f01030201020d0507030e061b0709090c0302040903030f050906090d0e15 75
    0xc122045040d00c810701040341d6001150107400003034070f9505005803d5014031417403031440c5081c40c0512056003458001380400d034207001c09104003c3d108070140141c0220790305403100f96100c0035841e60340d03a940c1c2c1003556132900483d640e05180c0d0808850407422030b82102c10840810341c95100e45c0940f81ca103854034910740d0800d02034041030041c000c0303180040000c1851404009190358900250203420f054414421402c5038000640d4000c0401000300d4401ca00000c03081840d604450000d2140e11110300f140c1070640041070030404030300001c4040c0b284481845100115002a400c441c00c40c0e40348080401c0d0080f082c032000e40560000c58034102c2d003e11900c010702c202406410200d6008050501051480e4000303c5886144d401e080030020804000b480020010b0014480c2441500755a4031980c0f040c115500c0001e208980c0c9100442c101030081d00a10540800c0550400c00da20b424101e003038a80f04121043e240a02882c4030940c1c03014052040d80d10308031006000b9011071540400b000d01940c2c01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 88255747 1250 88254497 88254499
    0x903030a030e1e1908120703060807050414060d15061401031113050108090f0a05060412020d120b010e091302040506030d080a050907030219060305010b03040515071206030c15030b03030307030902 86
    0x410000b100c582c04080146d28028a95982c00264a40c5000c0d4582d04004103a000544103038103220104851034594003aa50f00007200f01c032103840f140514584900040f5850811020310f50402c040000d54045007503000d204c0240c280c80031312603241803190704d402c6841010395000d0701003030104040c405544908d080c02d40c400000812100345003d030f9908186488101041101c47d58011020401004044910790f00d89422600041900c660450b1010309a40c00c1034520103d200d40c0c504508503580e20924800c502c80c0f40103000000075040540c1500d580c6411401d05074052400d10300411507a00700000e0f003024012056984070095151543e484000d804064407072074180c442d046001c000361f5a0000603101c406543d18184612603c1c01a0190542e24140d200c800409002e104000c08610040f0300d2200041001c20380d08130f1503417400b0341503441030035100242208615000303001c810000003d003a44203491041d0503401c8100404001101034400051280d0313010b4100740085400c890007a080901020300c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 88256997 1250 88255747 88255763
    0x60c0b041106090402280201090507060f0306090c08061005030114060f070503030928080405060c0111031801050105030316020909011b03020909070c0203030406050a050903030a030e1e19 82
    0x101c00f00004050707800c41d00d4048079082003d070f010f02da1260080702500c6c400c1d030740d0f0000340400c0b038150316410745481d69481404188804c016070301c00d0380d40c42544194007808041c60100244d04011400500d0f02c6412250785000d0a036205101001c41e0145017564102c8114946800305040e9031801d100403508001c80c0c007440d8010501ca080d00081c0c00b480914415000f030070040000d1760301ca003400800304a44850520a8205c82000e910210b9050012201a60000d40e81d03d41c2d29240d02e40014010802c00760381d160315074408802d100d90100c03008100d58164001000901c41641c0340c40c00c258907032103110601503e0101d56160315005081c05178038142c3c0158044000680d000c103880d4014002d601403180c040000742c4c00a416a054544608510b4004043e80b42140c2e4400e11503022036560300c514020741e4240a008901022014443c41c100c640d607603005415240c032000e020300b0140280290303ca1050b003500800c603811014041070104d0824000c4004010440401c1400c545103000e5940315050712408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 88258247 1250 88256997 88257007
    0xb030a050d050720030604020904111e01030606051c0c05070506010608060901060305090a0303051302030f01020c01050c070c140105040b0316110309030601030b0726060a060c0b041106 81
    0x303042448078407001140c03034844964966842c0b4201101140131101d80e40f800c00a1340401015460000b11203510079030544a89100e5282c83c10210b1000400400c050390004c42200b0b00585c032640007402c040c00f20b4080c0c80501109841d00c40c20394060161a148010781d4000c4110515030581c2900f109110b0b4515013070892400610b501c406040c81d00980100c000f054484082c8a00da0070540341d101d005100c039181c20007050404040c241d03154211700f44050f00301a01c0d04c000c9802c1240003088604036550082c200c600c4115949882c0e401b0b90411085149954a41000180105454800c0380d61255100d81c48030f0840d41400c500c4010912000700c4e01d410044284408142d0300a03010046015650b0b0058910041007601e000400030682c945c2039031050340080c0540314240d00d000840c03e0540f07510a440180e560388481c412581e6252421881d48080460742030716550005240486000300c8050743c11410040e00c5442c103540780109103900030011040040000e01050000300c09104001c00100104d1401d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 88259497 1250 88258247 88258253
    0x30c181308040e1810060b1209010b03150406060602060603070611010f0504060b090a020a1209060e150702010e060717090c030f07060216051507050a05010f0509060601180501030b030a 81
    0x84074084609203404030790304a000311350860420060144040c944002e002141c24481c08401c0c1d80681c10308040500c0e606004605c290340d081d045800110350217402c4078220300d0002d0741450498420f56003075814900d00b83d4081451707440443c945124900140003440c8080c64040121000d0078510b104401035581d48142c00c10940460082c180907502407840800c2039021030741005001a405006808050310400001410341d42245241d0903800300d000d0001510343d2181003990280461007d2160035009480c1401e50880c0b0040b6187d001d01d106038000c100e0040705c044440c5ea2040c09482d0b40f400302c0d5045c0224803031034004001056101d620401034403021f07201c610220f450002807007400724050300615000c0c000307650304110800b0b0040313010070f04080c002e02e040045100091080b04007601d01c03100080d0300d0709100c41081220405603002c0b000700100ba50303550f803003401804290f030b680900c0c3c062000803403150740c8140991480107404410510a081c500300056000b4038074000f0454050244001d0031000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 88260747 1250 88259497 88259519
    0xa121b06060605030405010e0c01090b0a090308030109021308060103020906130b03070b0a1418040902180405010603030e030a03020c0120030d0501260a030305040c05100c02030c18130804 82
    0x100b440703458258417402c0600e019400e4401d0b4494607107a80d400380e40080c22980e4445040400c85040c038060700c1e9a000d06203000c82e640d201582000d40009000000004d10b200158010104c0c07001c04910103081c2500d5062640e22000203100c060f40c44511300d80440c00903e407942c00c0d016040b00001000841c0ea02030004241821a2607200404400000c83d442407401c0c4c010390700c5c1c030020301740102e451701d40010b100c11106450407118480d80a55621b420b800210b4407a102581003500201020920700d281a290441c003030540c50004600296480d8102080c0d4140024800480350341a009407084005440c011034048503c0c66103d010b10601c1aa2a252070b8420700090519031002d090200340341d1304020f12040007452645840341503041c004000080c0c0c490100f9507002c030f41d905103000b007400e85590a10981400545e00002c0d070003024002c01421080c1c20102d2074184620940680c1c0000072076000308201490302001c080e6020281c50000340f00042c0040b0168903480c41140700c241800d80300e66170000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 88261997 1250 88260747 88260749
    0x16080f07051e0c0a122d0f0515011d0615070c03020306090a030f03020903031c020921030f030606120403020a17030403090501032d0605010306080a121b0606 69
    0x2951401642c92000e00c030105015110b40020251001800c8905e0301320400a442c440c048040c14003040740e44003c0c1c5006102c850441c2d894400c02613502c506c0354a060413200002c90800444440c070a4900814000000010032412030b4158201c0341300495010b601040c81c101d004080c170354014090740061511480c07000142c00301c01d00460246003250f095206040c5001d00180010916500113985240001c1d8400c05480365144280741c00f60312000c41c0c40200b4a58080d441c00600947c03e92030704030f04182069809060700ba0011500100c00d0090000a10101d40f1504040030302900108480141e000341c643c01180c103e00040c2005261a050340b810f40203801c001e8504400503084001c221041c081d4802025852000000582d865410319941c0545504140d02c21a0306054490a211207401e903d5200f0344000000030140e03142044000c003100005058601a1501081c075000c2d0200b2908000250002c1042d84209119280c85100909492060900d15140304403696814080006403650003940 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 88263247 1250 88261997 88262023
    0x2010909050a06081005040f020111011e0e060609070f0507080f0403051e1209010c14070312020f010b100c020a1d061f0914030a0503030114030c0616080f0705 70
    0x40071824044d0342410107041d030094800703490804e014000494400e41c01c413601c41c0e0b42420103544010420f804c83e0701409110070a2400900c2032010426038403034542140b00d8205480d815503543c0d81e154810044c00d414141e4007000061540c249140c3d020b401000100350b024081c1000506100c4511888903151f48903410131a5160031002c680300c5142c0802c656064a059090082c002c40007446010140d60300074905603a040051384140360b002e02c080c8407003082100319a5001e0b00e00036074681c10021002050341101000602c14400300004068043c811013849120041000080168944080780d0103a01110142c0c0d002410320b100291071000900e0914580c007104c03d00414505d4610f04000341144510703080382c02c104005102442055022188800b80d80041c0d1816000044000c0824500103954000030020f110000011620036074a400b1000714030720840c1100c01301c10943c0c003840024000d000c1c028050101005e900400200c840c00a8161044010700e000c0c204292516140c0c82c00301c4074070030701d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 88264497 1250 88263247 88263251
    0x17030a060911190207030807020906120607020a050c0f010203121b0a1206050d0519030e12070f0b070503030a05130b01090906050f22290108010e0d0c0f02010909050a 73
    0x1824441c003000000e03103c039000c24005010a1072654640402c4e61082d130100902c03d91003200000ca442c1c0c1d0703085080d1200d1303030f1082c119141403500410181d503d44100340e060303409120b00d0a001d4941c0c0342a2442c41d0104d41c043e40990f09004203140101c4207040050109006140d4002e43e22094286a801030701d003251907a903514402c0c04105030b4030317400c480030b5030022409020340c0d043c03550200d20002007418000003110340700302802c0302c00c0c10110354a5840314406039201c0342400d401600f000e00041c00b10141d0701c45403140e031020369890014110038410644002c019800900003d480d0003455488158000441c207040c100f142c1065942c0c2a840038240c01992039030b0307a07540c40442404440c2c404c143d4403140440b00a0300070b081406001022411504001c00894070340b4000310100210384084d02c0301300c02d6038071401c070340b402101e41511780005c024081d103560b039882d182e009802d151001034841c80914064440c60164002602c4014008100010680c140040d4410015210b0311600c079191160641100c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 88265747 1250 88264497 88264507
    0x41805060f0a110f0a0e0310150503070519060c050f0a080a02010c0c171309050702030c060a021612020129010e010e0f0f03190f020a05090417030a060911 68
    0x346100311903407002010b40003c41844034480300c101c1482101c0040160b81003803030100b19480c000038a4208524a8040d000d0b081400101141c01408500415030f00104e0549050310344030801d2000e001030b8040400c05c6000c0c1da03002000024003031000c3d11000c0307006006a40390000c001028902c1e080c0d002c28121803400f000140340704030b02d40c28450001d24103203919140d100100d42d5250014801e001c0c01da4081c000c0000196481100c0100c0344103001404078013018000c0d41713070000010351240c0280f1404030750360090000041042d41907108403420300d0112010201c22441589801d20b18000009248041d90340c4c1d042c083c18890801c1039158000b107070b45410030050400c09000101716204104810381070212160400003d551110654102403c040d1098000d40c001c440009141c4140c0c3c40703600b40314000c81500e038030a001048c03c0424030b2500903250300c48940c0d076400a0051442e02110007900c03403c821540310010300700440040d6000b100c0c0890201d03415459904800444542c2c403040f610803000015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 88266997 1250 88265747 88265761
    0xa08030a02070e06060901090e070c02180708060612070c020d0506040f030905030d1d0406120b0105091302060904090c0f060801180b0a0b09060d0c0314090705030a02041805060f 78
    0x1030f42a0303c40d80507252076091028240010303050300707164050205000c049134001084640b1502c454101a90020700c10300000d01c0b5460644408141a14108001503e0400080301803c0441c1111042d6019aa040c0c000b59a0340d082102e031010000c0040741d00c00c0300e038110000410420010346019901a030720350400b02559140c06010054140d018034004d40180605407000d58001c0149000c02404400d01316850a0000c0003c0082c03c80d600180b5000d00c0b6007a050050108102210341070314020349681c04203071102101020524440e080007540114100884403043c11b107504a00049441000c0d081c04203a02c034000c08070304103859007100f4000380e8038800422020442244002c551101c3d82d508006003842030300401d5505c40c07607000d100c024800001e8400c075a0f444003000c41e903010046810804c084c01900303400070060300310180909140217440000c603160400c00720300c9400310380c0300400070030100f8403680c20f020144c194284030b0b005605000002e100894800d0080c1840f403000070360031914a2810b24 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 88268247 1250 88266997 88267019
    0xb030a02180103051303030e0f0106151d060403260301090b01120501080604020603180312061206012105010b0604080f0d020a030509010518032e0203130602090a08030a0207 76
    0x41d00c0d0304240c104010b00c0421000c81181c0d4001503054640850b10155012015190406519200c07803590b1a00c2d4000500d0411150050580300442c0d42c0c03954001e2a00d4a21390420403006031007039209104000400c00503181c4a080e038045190701c0c040c031801540030034184005030000d030f210700c1c4100e4172124516119a40308081c2c0c0e4040941800400c0303a941410b200e15600c15004000a0003080d0000104903890224102d14881004a0048a0b52040202d0703652901041c26500b184c014203c1440d03811403100c0105541d4182c0e90380191005001e0707030030f00041c400c0d6040d2407015203481d581c8003000030300d54461000a00103043c01030001c00600c44050521464280801400f004541042d0650030000c0c0d8060300702e0305140424a0010f4881950009611035400102d41055151050659403401170300c6401e1808100c0c02507121420205008403007250507413000b150310034079081803400e20764000b403440d5000d0050540081c1c00a2405522801903524541c42815510050313480300c502001240006 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 88269497 1250 88268247 88268287
    0x1003020307031409060106050705120a030b0f030102071a070e03160302120d091202010504051801080f030f030a151d0f01060e0105030402010807030e070605070c0801180303050405070b030a02 84
    0x110043c5015240c031000858440d28117004a00800c0710020341e550034404200000e0120b545109035031580e511a4038000340052004403005030003140d40e40e4040034585418070a540546070009010b1114032141c40400810000042a43c81400540c0c4d40600c0103482c200035401140c550b144108a03640c0c1980100440494458140402c40d80b040c607a0f0380907250f00c6540f5030121026429003030020201880140c8042c09030707030046600304030088000c6103007803810150b09041ba480c80c42561204481aa0b465440f071080c0c0550b140102801c0002c00d80d10b40440e409090b085408031540030355143c8410719000c0c4030541050a61480740e0950510200401c0311240b0b6006055504007403c3e083c4031b5800107401383c040200064180071034600050484d40c0250480c14034003850b5010b88440b41d445036409842030b040001c040d174000302d00040102d1120014403585101114000d060344040f00300e1399080300900350040048130b980c0a20000041e000b1848805940688032840c40561030390b01c0b10420650f10044 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 88270747 1250 88269497 88269521
    0xa05010807060507080f07080f1b0d02150405070e1008100203131401090c0b07060605310b030a1101030e0c0a0b0f04050303070f0308090303040302030406050c0c100302030703 77
    0x1205080010b55081000c803182c00b64001d03010350321040600030484035030041c2d02e00940075010015071450312102070402007203495039031091003510072100c00995654180d0394940701e000d6070011000d03041d030801850850398007600c1401200c041d030303172618504132981c071050360341c0d94031b51081060500000d01c040c042d10700d68000711a4210b044d0700d0171612402060301500340c0544085021189180000c40a400c00143e45400c206d030f04c0b801c1d40d900d0340000042e5200003010344202d46010b0000c2034a00e081c0350581c01c102c43c42c0e29074001a0100221070340c1018001c03a01c40e01c16a9480028880c152014085024000c6c005c0000c0c038000c1c051540050255a00d00741c21910300d42000c1e40360452640e800c00b0501c1a10700c0702404e9a04d90f840709040142a124a4111035814400030a8400801080c0d4004031500d5201ea0303901441900d030041003603030703d000590f001400340c2c0003030006000040c450800f82c8414000e084c02c0718450a1100080703030071000b040445900003900003040110340c5416018102e16804 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 88271997 1250 88270747 88270753
    0x6150513050906130f140c131109150d0501060807090e070f120f060e10080601032f0913060c0c03050904050c04030c0f030317130b06270a050108 64
    0x6040040745489543c000c0c90321150110300001101880f00348064854603e61080d20480303101d8180700c0e400d50f148103000a403442450307540d00090419a5900545268003036807040340d0b0909a4080c00c0003824429124840d11134401808883c001548034010f180c020301040c0c4800380181000b807001000f0f501e6540103c174130351035080c0038044403035030080d180c5a403103e0710b10340202c01e00b45405c4008007904460b10010361850402c030b00419507160b54203619004140f204c0c5905881c17541c4041d0261070300d07800d02c0060310310443c442c908a002800300502c80b00c208010384507168880702d400e00003a10b20405951007405450003801540400919110300b02c15000a82452307000c2c00c86580e0000d20620410034503500607078845000c1070081046100340c030051a405400039000300d8072040d0160508030140310580000c0c4070f0001560759207851010440c011101c001c0802251030720354445a07032050000c0c0c1441e410904a4010001420503043c0c103803200b1030103035002980e505200290409446042c0c00c0315081703070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 88273247 1250 88271997 88272001
    0x1030605061804030f181503020310080601030506180115090504050708120a0c05010b0312070303150f23191a0f0406080a020409090305071209050603010614070615051305 75
    0xb40c0040c0c5540d10170565241401a5122460080641403da54012180c1108807c50406d41076056005140300e0407190b20081c0c0c8890703a82c10000c2c3c2c0c41000b848060095003141001c500c501031100101030015100d2000420740320ba01c40d45066501946500c14140c20740e881c1c00380800c00c1414082c44000f0300029008026044c061515107000744100c070009010300241d03036005030070881e00390484100740400406441c44095401c030b9190541c0e008100841c0043d02e841f2500e0400049101018199404030071407507032140c10425008052035003201c0300d0703018811403c1495a90740d94608800c0e002c01704031039280d041a01c0c000d84100401000c4035014441d440038402c0074501080103040e1404c036105403402820603194500440000d03c07584e000740380c4503070030503203440145a000001440c680784074002411024144170fa08403025079030340c01401d91101c0c1c10001006408d10409a0340c500f00150354241c1e24158207596004122414000d004d090100320607c00c102c0ca28122201c41040b220703810b802c0c400c038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 88274497 1250 88273247 88273253
    0x22d04060b0f161704050a0b0a020a060b011e05041e030803220f0302060106080105121506151801020c030d050a031112040311060603010902090105040914030301030605061804 77
    0x20b01985020070750003140810350b8071840031030b10b014052a40e00100a1001c1040800c0000490303801402543d02420020000282c1400000119001d264080e400780843e14015600e071000b03042d04211460400803e25134803401050840c0c00d5002d8101c0d1038840d190384518003014000c2d5040060319419210600c0310f0304001244000e0308407588520004040e85039495000003481c0464070221020b8282034113920054101900018210b060755050307220061607030390313500411200c02c1c3c2440f0744007140d41201c6401e681082c46a014143c100c039000300540e103200c281031a070501c43d41013205200606100356254481c5960140803204580c102900604520300140c000600107103d91070307081e020550780d00364985103400140140c840f075502000b00030200b810507090003000d540d85512010307100d014207000700d00e040c50140301d00d168542d80a00402890780c03030302e0104401010150000d40390403070f080505c00407a81003440214040d602c1903200050030300744a1700303112414050800358000c25212400380404 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 88275747 1250 88274497 88274519
    0x503030408090d080414011d0102030d0e1e0309040f0c08150315070305180c03070b1305040204030f0302010b0108060d060c03092f060301030c06080c07022d0406 71
    0x800341d0410000e560310005031001c0b44590000c100003422564000c00d02007403505002c2c0c1c0e40f0000c2c041c240c0e200784a881d00300c1d406c4000d9104c01d000e0240564410010101e0030a05504250050764100c0242d9034209101034809010080c1c2e40020000758000007060340e1146018070810550843c0460304110503000f03c60098402c16000d400564401460400c9602c036560411070441c40d01500060b400140c14144000347c01741605a684a40514820745d441c40103c4000810704c05c070410040040401e245040081e1445900c542c0e0445503191400d8004030f000d072514002040214880c51442d06105420705000782111350f0354035100d0400040806200c480d5031200c50404482e604a41e0024400f489480164000c100c180c2008051401c0c1e2120320f550003d0103445420f0103000c001042c20140030040400c0000c0c4404d0000500e0f06144407410f20000c0d03c5001503991004020302c4407483c10540b078000440001580d03604544120070340d201c50356501801b080c8952103c6050740d0500503241041d03101c842c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 88276997 1250 88275747 88275751
    0xc03070503130507050a0f05030d0c030e01030c030b032409030301060903240e060106090801180b1b0403050309010e10020601140d0b01080c01170103050a0816080307020106030c0f03050303 83
    0x41c1140c0c2c1094407000c1c0075062041600404000340908842903031900000c05070300c10b40c40342c603100340190100000d00394000c81e951142c00303504d0341c0e400311009030620040d0b005102d240040e204140da07608021206031003c03c01030b0410104000b003009401965003144004030001441c0d600c00d9003003400100200b54000708076030143c0340e0181c12a5104420880c0440842c2030716002040d020382050144000f4440206456040c0d07051030796040030403600e440e01c0a090710a69456a491020b80002c0b07000840c0c000c03507400341c00c45180200400c0450f00c40400340c0103600700b500143d4441e080003401c00710560300420400c038481030a60318107415429802c80070303440703c2051280300000340c46607001c880c070756035141400c01426500180080c0d2a584501c100c554030064120341a02080b03046081003140002c9404160480e507201000705007003141c903a00c13003010303821040c400141d00511b070710f65070300080d0503a0186100702c5850f400085d909155007070070891136049602041d02920032580070b002081004c000c0766 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 88278247 1250 88276997 88277011
    0x1110050306041d0303070c0201020c0a0b27120c09060f1e0a0b040f080c01090e150f04020c0d021006080c010320041503050603010b0a030605180f0d02060c03070503 72
    0x680f0048000308024036500d400000e481404000204031038280c001030071328402d600070b17800c4840c003102c200c062143ea2a5075008580c031000007848039408001d014640e156014034651a80d0030410100c101040b08802400703c038031982d82064010482e0b60a041c05800d5002030121060340c0440ea048000c01d082401d400d0b00f000101010108502194a940600c5d0008041c00c0703042903611946c030345040023005190700500c0d0a60080c1c0c540d100d655031144009000781c44e40b80543e00d03c01e49070322103103a10b40d546c0480410b400211380c0300c000d10700355a1480a009540c1c12032014007002507038550300030b040c240004d1069064501c0c0c00c109104405001407100c034100e10a00300024901590365800044201c0701d069040707220400100820200b603040c241c0c0c0e050510702c3e1014881c5031a81c00405003070718484000c941e00201c0402007040844c55039001203401c407080c4001014101c0c007000645050030044581300704250f004183e0f400308158108156544580040e2480b8150705000034000e005e480007804d81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 88279497 1250 88278247 88278251
    0x40602030a06030b0109020d06080106060e010513030b040f05060601020d0e040c1209060618020708031902090907030c020f0303010515030402011206080a03090b03100302091302030118111005030604 87
    0x1412224072580000701440c0c210001d40c2440da55000c250020350f201c1d0050140e000d0515400141c00501409503c0c2540c0741d5480f1201d0320802e10340111801d810820b5554421610ba840c0040410341001d0824010b6000e50340a0b6111201404c181c0d00c3e1076000b0300150304641c0040000c1d1107a5030300600c40c900904003101d011800000300300d8100c80601901041070442e83c509030a400803c0360541c800c1e0100e940a030107001c80300490301c920b1400c0707000b0800f000c0d004100801c0050511503140340200e100708650800142880c00660110703050710402c0ba00000820b55031041200070304e4041040b5801d10001900940c51981040d020641c1042c16004c00603202c1000701c0880c04680c060702000003501d07601d0904120880e80c6140e0315596600c092415008a1284c1402280f4031000d01f044a00c605001d051513800285158280a0400d50040540b8060315500c4120740050f0f40138050702c0c1b0311403e40c50b03240103003000d01e0801615007203040101d94490707664144200240d917003241c00d60340d100d00c0031a00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 88280747 1250 88279497 88279501
    0x807020c0a1a040302130b0405010602120307030c0c08161506030203070e06060c0d090510080108150a1104030305221206090c03140a06050c1623150f060301050f04060203 75
    0x1108400d003c1d81c1c00083d4060010f841d14030706007580741e0041500810444040c0b19592340d556003644c031a40d400c0da0140352181d040002800450190300044040c1031a8500144020307090740b80c15070190481403544200841503a06041030200741e05900203420040e4400304045440d42c4e0000380d540090b4441d01c00841c01031000911555204005c1c0c484508002e0700b40c500e000005c0100078090001303030065a108840111506403064840c904103416604654000c14050344001c06070380400300000c10030f0303201c16282c0347c801c105002041c006d440118426100c0715111007045054507020061254503100c5100c12500030425800c007408200340316500042c0000b0f040103d030801e81581210354102400c004001c04400081c0203000402621260080d84200300d80e840344100400140b00d5044800442a0150a41e1001c540c00d464401c5611408505050030301500340c40050628000c5469030320782c00b9841c0100520f5009040a040c0d0141c0110001c0180e446c210210b1071810b4000740c40a02400e0b40400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 88281997 1250 88280747 88280789
    0x1020c1b0409140708011812030504050f0102130e090a02031c0e0301090c0513090b011a0c1510090b06070f150f0b030120090907180801060302010807020c0a 69
    0x841002e0280d00610b03603000f0b194691840c2541c0314560f10584103d9841e0118221001400c6940e010f80d0a034030829148a08805e103001710041d050150042d42c46018440550300c00c400700744000c0281101302844802001cac40d000c640611004005c0c4140d00e560000202700005039400701d00e03c0e1580340e400b012280000d284000c1282c95500c01104141c1642c64901240144002501e0f1041110021120000000f004100880587d40c400000402c210955801031100445581e09a01c6c4104580c03c19405c0c8414119114075000c403038442c030b034500385969040c41710740001ca50180002c1c0410500500165003110040340c070030f1007809030107800810a0400407040211900403200d81c6008400107200319066100e1841c0240303151806035110750f19090582e803007580390500400c43c100a5080e6107050180c0c200c01d02c000b00d400140044104024031040074003200729030500c40041d11040c40002841d60551001500a14000d400b1900f0b43d80315507003030f05c543da44680103981995210350401d4201c0c58000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 88283247 1250 88281997 88282001
    0x907060f020f0115050f1207051e04050a050402120f030406030c110f01150503070e0103020402030405070512030c011103060d110102100906021e040302031b030a0f1209050301020c1b04 81
    0x4030b40b040300c0d5003480d25562000003826030901c20389004481c0042c00c003c0140820609241c05500066113412100041000b03280695501c1103269030b4007104a2103a580c1000201114030484200342d9040d511000d11065080c8260340c1d500350700c0b903e401003409000d4696626a80d000f01c0c400d0b88201b50301d420a1100c4188a095007522118102d002c0b6910140903402e10743c041e0407050701000c825410300a0004862400040f0030b005c903010081d10280903400d5400340000395000030025100c1e0f05c94100005107584030b000580c01c00111200240d621014000c42050030360b01ba400854550308020700900071141d5840316600d8080e030307208403410708007820701e0010303030074031a410300f669070703c01e01c0d165100c8148400c2d50010b0025030f0442800840d07030301c000303030008000e8007543c00080c0d0168002203010210480700c8030b80c0d90301400d0040c07c4440e5110f03031340d550219009040c0e6007211965024828000304a40006d410310260101310000d605044002459941e42c1540003d000d8084140458140040c2c03125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 88284497 1250 88283247 88283263
    0x408040504111206010311070326010f1517070f11030d1e0219080405120a0509010e090613022b0605010206090105060904080306030c040c0206150105030907060f02 72
    0x60070601c0b00b10619121406550021610b4103031040030900000d0f250b41c486c2c850424440c40792009681418481d84080301c0f1103100403001c00ca121000d01076091600421005c0500900004014820042c241800c4150761850360341c0c11400d1042c1995206641808001e20310b500080a1600281c01841c4400486500c2c2c040140b90700680070000c4e1914044d00c0c0703a00441004840074940b00405400305851104038410a0a8000000c0c2040d040740001e502c92282a90014040d0781101d40c82c90f500c0c034500c42d55500003651480441c1c03000410f20895600320010750100d020868502d1210300c0d00101040070b1703040e07801c0941c4010368000b40910900d0160102c44600440101c458010482c1034a0340c64001c218500480740503128201c00900c000078140589849168040c000f02c50303d84503a82c5410321900064101507142c0241c0d229880d460702c1c1d5108000801c002540100100e0030582c154103d500e044c10201c60411104008000248200180f6001140c01e00d141240c030040703500700b00b00d00301014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 88285747 1250 88284497 88284499
    0x90402180a1b0c0803010909030903080a0302030a06050f0f192102010305091209100302040305150103022106130c0503030c010905011a031902031e060405120306090f04080405 77
    0x800384207100c101da03030160415002c004039074079490302012800e44580018240082550108200512a0207041d410001c141c40c42400d100f1091620f0f40d036610119081f060186000a41c04800c2007895040350040310300070034054920038824040070000c110348000b04250580101094581800c4a00312041041c00a1002c6030010842c05154811000a0001004142d0002c0d090001050706240c000c00c0004942c05a0700c2424602001a4148415000ad40904c032060560030301000001c15000d011480c4a1005c080601e542981180304020083d5601f03035a241d0021100004107542100004800380c02c03120b0142c1403901c08109242c2048401d00c0c503004160580070104001003400d005402c0422044d100703000901010f4203181c840101c07050039005090313065100c07400d1301c034206040720183c81640b40080c0599519407001c0b00d61001490b49a1208105644003004001c20300030103010841006e490075101500d5410b00100040004030060f041c0b80d1076401181c081010400c0781002c850042030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 88286997 1250 88285747 88285789
    0x80c090406080703020907080f160c06060b0307020111090609121006060518010318080307090803160516050906120307050d090302040c080f0c0903010608010f0606020d0302041202090402 82
    0x20300c038440d040d11030030144130480c003940310f100200f510f440c0104c00d501c1c800c6c49c280d40c0410b071135602c03446603043c1d03003110002d100c00b0301104088003170105083e40914400341c03001090030342e924289684000c3c01c68a0b4580c01e8003001d000ae1041800300da848404a0f2a0f20300106d4200034188d003441c0181c1c0c1070118091203040380510b054000070b41690044c024018040000702c500f41e030700030082d00640031360b0540c10030744005501c19605100000d500c400515045100e80c80d00541c416110740c919072641d40103203183e5684902c0e5100c0541001001c00047c101d240711200b05688403464403001ca504540042c240b00d103d04d5403420040b40d040c60400030703148507640001c00c4030414014208060b000c105a40010b0780600d0030703c4a8808841d00503400580202c00c602c8c5c1841c015554513061103ca43c020415503503055484400010f0301010034000c03c2c0d5020000480000c0b294079051000e450880c1c82245182030500502c020411142160402c2e4500d5805941030040742c3e44030300c0050200d20620b07800f591440c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 88288247 1250 88286997 88286999
    0x10c0525050a0f030f0f21020c04150806161106010e060901080309150a21150807030302030a03020904020d020c0a0b010815061509090f220f03080c090406 68
    0x26040d2108281180c0c0241c9840c00307990784400000075900c0060201400494122541030300040c0121210700c4514005c4910300318012906c00c1c0d6000d2000302c00c48800040e400b0030708031740641c54103108021840c5004008010000c1c58480c000d501c908005016030301200040c00c551480f40d0040c01c0b2000350b116a0300580303090f50f0311031a2140c0b614000b03491182c0100550000030400350000400c03101d070903100a20541d5038041c0f944071048213a0006020604114008520380c103640300c142c80110161681000c0801d10484040da040b00140139580b064000fa80040810000720350007100310b50a078031451802607035078499007021a0180c810b02d488061154070001381480321407804242a8003ea00c00e040341a00c60340d840350007540c1c40c406220b042510b00300c00d001042d001e00d40640303400400a50304800c14223140c66140062222182118034810180742d034410400051341000080342e10b540803200c101228100303a1200452402c009a00500307014202e0046400c0c41c0320002503450140c0f00420074454a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 88289497 1250 88288247 88288303
    0xc030e07171213090617031c0e070b0c1504080f130509040302010905010c080c09091308070b0103060c0203270a080709020a030f0b060304030c03050702030105010f060f020a05030306010c05 83
    0x3505a0344296138400c0d140460100b42001c00c0814400d4030107501009600340a403031156881103100714108100d501e951108101e050b10018413524008200d00200591904020041c1d503061500c1100614900711002d0200000034030341c4c9050700e1048510000c0151520000740500f00322000c07542001e54480d008a0800042590541010000354481c000905c0b2900004034262000c0100b524034035100503050040489505113060007517406500048200f81209007070f111034420340d214450035103005a401005209000603801140c0c0715000c1c2c0d1008503d4482c0451000700101c80c5801c0c1ca84a04105405050895648010b141b010300f01c1d034810380b0b900d03a80c2c90b58400025030010407180086070429901031100c0c0246d00c0750270442880a05410301d50780e00e07550b04032898181070000302c041c060300b0700144015071000d1041d140130380555101d040149050480144c00c0c1410360720228210b6000402481c0000c10220a594100340700b801c0c82c80c02c0004c20f00d4200d040001100d1154401803203810302c2140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 88290747 1250 88289497 88289527
    0x302160e01060201140610030f060b070308010f081b06092205010602010f0501080c010507050a0602160309090e100b0d150506010f020a0b190b03030304060e010c030e071712 76
    0x480b0200c0d00208a00c1c040755501c1150040c0c2100d83e9688026040e18600401d4081d81080481c0c000d0014000340c40c5480e4121a0700d40e4011040c140c0001d15001c00622148842c684800c0241c41504000c244c80c4025001000081a1040c40c2d203001d400c0225001c4402d803100c410400780d072013180c403507000312800200b405070081809100e001f00660901012141d800141d210f180e05030707020500a0002d06501c0c00041d50b1035845081d0440f010302c1036002410218420b0f1002d850f5152490030703001961b4009050080074a10650800214246840c20603004d6550000740c900101c9000807000c242c48084400141628046c1000905103405003d002e210900c05580070612401c4c09882e000305000580038106d07500c8071190f40c020502500c090200c1d07089031028200461200c42c2d4600802c10700d003540d003ca803c542007a00c049800c59146c3c030351138510500a009900b1360003002d140403c10706844070403503a07179a0041c0c8070ba00850384031420a001040d0040c003006420105021005503101d80703002e00842c0b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 88291997 1250 88290747 88290749
    0x41409011e0b0604030b0405030405030a080a02010c210902041b0201021306080c0304110a120506060102060a0509030a05070f0605180f010c0914010207050a09060501080603030403020108130302160e01 88
    0x91011007694480e240391600c201c1d00e036414042c00003030400d420740e901c60190240160056403c0e200910002071240d074108400d00203544940d16043e140e29150f0b8000e03080d128a10015800d00c900103000c2010044006200d101c401c03d6138a020880d000103001080c001d100e402070311000e108150301007080d9660150010506012002050420155609c50450300c5820a451040000ba0f0800c08100400c2141d00e0070006d40c4001040f6440065950340511900c2c1c04105045407030b070b000902040700642e014810f040d40f01600a1090143e850155070140e01c3c2e210348a4410f0030301801207800814040040b0640c0b0f61070b0362103d0304004500b00040210300c2840d54035040c0c0b1440c458401360a03401101030181c00951800341e03c480759910304200581c1c4240500038401411840740c80800500c4ad5500240d0f00010130641c00009205414a400106805da00034501d03400b0390f00c01c00c800c200603607012449690285505140d00c0c184070140c40d04905180fa40e540e090301c2000d06d074078003060302e4581003203a80c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 88293247 1250 88291997 88292021
    0x312060605040e06040e030a050304140607110105090d0e060703020106030609051c050c150612060106080601020708070f0e10080d090e0a0b0904140111030a0b01090602070b041404140901 82
    0x46548007005c00c070070ba44841e02007404541090200d640c68501a0020310303081885200440c55039101d03c12010300e0b0079011281c00c0c000a80019800040d40001c2c850640c11003094005401c12001c00b020282c1084e20000070b840c084d1000094442c1418400c3d4003080c007070755100c0c800b482400006e04040703950b03c4542d061414400001540c80c1003090180046448032444040075001071484070000c0ba00701c610013014142c21440c40e00a54100c54030500485001e000741d0349410030b03107041c1031000914101d200d42120b50540e010000500440c0041824079088901c0c0172002c414a44d03408003102040189541302c00241e1242c04840003140b50070850320820b0b00c0780c9441c0310002d9600c0e190382030203441105503501d41200303202d004100840d0810b070009922a200c51300100f1a0030341d040304e10f801c95201300c6400000c00d56549000d43d035580e011149400612280c4010100b6504103a0106941d100381e11a04071000740f04501c030916a2100c1e0000d0283d041a0030941d40a81340c06090345000e031240c14051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 88294497 1250 88293247 88293269
    0xc0a081305060a0801030b060d02031009030810030f060506010302070f0302030d050a0228110a060b150301061706180a0506040b300307050106060f09090b010813031206060504 77
    0x20070641000020745411030ba0607a034100c0300341d00e140c8078001402c07c0a40082d4024820b10020000351318208a010204070406400080d103040314203004214800180003084840183c034010030104240803003c04244d80c011000117200d0f101c100060f0000d201e54440241010f4640c2d80d0b2805054010000d480d20906444007803000d42d6454034803104034403032441c0c16840045d000400582000140d009181b116240e8100300042c0030034401c3c0b0925000c46800704a9086450300815401410052100c0034401c0d00144980d046505150002e440032a041080320340c11010b14002852507914424800c88081841417503d01600746018014050b043c01c4840c54044e13070a00b4a06074040c200302004011301250b0b404038070707590f0100b01160352003242800e0840581d0b1100703021060100f0001e210341c50003407940380c61342c06158403901030103000c2c490724ad8481d42c000c0346171440801d600d0f40c0000c0600c1c2d000064044e86000001e16241c143d80d800ca102c541451214030300f00c1c001c51001d4201c1c005005880041c401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 88295747 1250 88294497 88294499
    0xc08031005150715020f0a03021305120a0c091a0108040f0206070b01090c090305070522020f072d0b131a010503010b04020310090905030408100207060506030c0109030201050f0c0a0813 81
    0x44c100360300c0f520450510034281048540b000a1003907001d004454080d00c0e0441046540d1400203034102180300402500344c0040704030f541002003009006006000c140f41c240a00300b1103442c9900031208201c5158140814107001500700410130b0b00a0007919402010302e81c40e54a5030800082140c0240601d1000c00d1500c501d040310540141c01513811258001c005014042c00d01081c4400401e00d5070141c1405400441030300c1c81813046001a210b01912500e899032501440c0c2000381028102d0b00c07941035000c80d51103c8120386038502d00b129181580103408400940c03a0750f186140281c40d0760320302070142101e6400c401c00e5003030b0040c0f46504a9004034000d001480e1140100400c80c40151146540b000c4120820401d81d030301030f0440c80429015500752410b007a90341980c20705014035104050142e40d4002003010401c4070f1446481e8110314260000d1201141010002e4030580290001a05103c404038540c020700d440802111003900c42d0b0401d0f138024a58514101080e6001128440140c041c000c0d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 88296997 1250 88295747 88295783
    0x209010f0206160e010504050301110304052104140612180715090e070c0b010b03040c12050a06050a061205070302130b09070f05300c0306010c080310051507 69
    0x1a2030760088901c1400755085081c0d418050710080c80b0320000c13a05000007444002034079902842202010703014840440d55a06c0c092a20500b0301015459a940c0301000b0108a170001460f84161801e07070325004101d1846206240000e640ca020b8951141c00050b60181040b000d09041c1c41e00511440c4401e04584040352030790350036400b180c000090a030000f45903010400c6088004c4c0c045039000491828503442a0902d5100ea02e4801000d030400d2003c01400400e000030841e000104600400ca0000c03118562407055032035948603944a035003c0c140d50303180c07004a10140595805440100603803446001494814507006440d46010b10080c2d2103440c04029001c0b180c100c0d4014913021050003000003a20b5a038070382003550210b40e9144c001d402c0040501a1201005281024019117601174151404a0031210072800741c00800600302c428008042c41030200907600502070240f4103901c1601c490b101c0c2d8500c00351280d1070341d45a004a50049090302803045202c8410000d0000d81d004000140c480002c0c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 88298247 1250 88296997 88297003
    0x711040b0603070f0e1309031706190b180a06030f0e0604170c0111040603050412020d1b05100603030c150b01091a1303080903010b0301090803010302061e030a0209010f02 75
    0x460754070200300b03e010441c65107441900d81140d03c5c1c0000340134000c50710b00800000210751245c0130450100c0c048004108880caa0b4442181c0d01c8401154051001a48240002400042407040100e10140481c014040e2030003d01900030f100406458805d22542c0c410004001c1c10950200081441c913043c1800c02500b004101d0620441d040320041c1d800c084000c1d510121030b4002e10483d0140d560383d15000b911005144020401420f455801007083d0034a03003805015604089100c0083d98442e13a200c1044941007050308020040c003690b982082e051b541001410321101201c0c0c080c020f464003078040700f055008000e030704205014107500240c03105030b45894dd003114800b010880c04545202c6041109921a03806107411010311003045042405140c80000d504025070012038030b030000403503a040b8a007402d00c1101211803045000b40a24000d03034a0700384c003034401030101900405000413601c1c0f28815510027140004000c580b481da403483c10300d00c54002500b1440c0c066000442824810380160303c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 88299497 1250 88298247 88298251
    0x3030a05030c19121d120a0212120f01050d050607180e010902031b0705070509060a1508040210180308070602090607030c06060b04061b05070513050103050f030f0f090112020711040b0603 82
    0x11100800044030786c095180c800d41c104410190071841500c0c40c51355007120341700c003a011304a06540c2c0380445040401c822682223105070070480c01452241c05002c0450b00010301c0e0b58100100c2e01701080b85a0360f46245c03a1450300640c101550500400300002540c403c107038000e51103001c0d480e241607a180010440d580241c414008050619400240b09010506e001954603070460b10082c540028680d54180d00c074034581440320142d010590318001c20095017440c000d5180d0403c91450214100800c01e150b40000d00c2207070001070300c40100400c40204024150381180c003a410005c05054803040300d460020b01e44400c9520031541c0d035041c458005481a1402c0544040e00d14580340c1c640210540304c17100c40f82c0618410181d40500c00c0c0100064107440d0618100c89118880c0004100766041d0308182c0e16240102030303c00c0c41503000308030121034290141c3c1650301c81030009200665580e0700f540100c03540c18808561a031120b100080b01020008010844032180100341d41c00d004030141c00c0100b003134a00007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 88300747 1250 88299497 88299551
    0x30408160305070e06010309150b01020c010306060f080901021209030c070e0708041b05130b01110a0201080103150b040c0e040b01090e0115090815071106040203030a05030c1912 78
    0x35001e04c14a59602006030b0301200615002481d58150f48607065200d14801d071321800b81d6502c0300e9a0029590500010203c4542130070240509450050010091000c11159404111a140124005031020340484959040140340418642000900551264010549074102e441001e2000442c0c05600b0b0f440c07480340920b41c4881e2000ea46e16101da00180b2050b0541d0498030b4100704000c00c456a83c03402d064200d41c200700c40000c01e101c1c1c410002d00a02e04003070841c0503603030000c1070710070040c0c0e409041c2d6410b482c2d10940d1642402c2440c0441805400d40800850740720381007642030b5044503840f0000b101820021603080c0007404240f001500c00c400d10b03000703056884070927400520010314080c0202c403024a1503e001004503584283c01030400d003664020843c0c00d00c0b030000340608590f01c1681555040f4008000d02068180b82e0700007540da208044d00042401004000181d8041402c400d4070b41380c0c03c400789020441d410314900200107818000103000300314540b40780e40300c11420142c950180303000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 88301997 1250 88300747 88300753
    0x1c090e0f011a07050106030813121509051006031b060806090703110705031b01050c04120213060b280c03020c04050606070c030b0f0a0e0c010e13020408030408160305 73
    0x100b40100040040000007011003184400c000741d0b0300007a424461a401580a04401394075200703040000c0d031089a16070302c01a0080c601240c1d81d004905900d01510994007a12800100240b262a1450074000a0700046003c40d251810000a21030f0030200301c0c0500c0d800c2c4a640611545031501640c80c0724003954050b40000f10350340080e4089000b5484031074021320200c1c01c035040c40099039500c6d145622901d000400141e007511041c12030142409407039040716036a0041802e0034105040654a0409004064810040320655900344103071540044058110300c50451303601d908180310080b04a114900310440130004101082145219140700000c040c2d02d9070242242c042204104009408040d140e0b90f0700910402a4400184030b0940e400001c41c0714180e5407040b85031000c0900f85482000342580304441c04e0031346070840480f000c900d9204060017400c10790895841580070984d01d00c90098081c111920004004c40c0310003001028100312080501240c09044410160781906001444000e20f940c1c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 88303247 1250 88301997 88301999
    0xe0c01051206220c05070204140105130b04090c080606190602070504020c011506020f010b06030408030610030b0418051209030307032109080406080703050c0d0b0301020c1c090e0f01 80
    0x4940a070030381c0b50100d601c0030300b0b007843c440089000c400c0342c1030b815120003c10300010742d40702141054020b07540440c4000c038895401d5071600780440c1c44001c071162003405442e40c40244040c199182c0d40311008854000e54110400307500c07030381400d075120b60a407001442126180d158004440411108100741ca142e64080c2c40c4040c54a001d0001039000540440525502c4440705040380c1d46503620b14008040c5580100300350280d00c04124212031348250b001d07000d50b000f08100000700d161101200e80295050310a004003880108003140100010022240c0c00303410210b0f4200c4802c400b000030900f6a015000359020605000d9404003644900c07240c6541580090013048042401880707e00d850000520821180d2507900040348201c80c0c201000700c41c03401000c1014800d10380e0021545601003800c0c2420030250508400b071080a0040091650b0040d0b100c048440c0d440e20290103650f5050701035001c4400880d540c00b1b43c04040c2400212400000306004000600f40c00201200b03401210b81c9182d0403016 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 88304497 1250 88303247 88303249
    0x30b09240d08070605070e0a06110c150c06010b0c0f06190e120309010204030605070c0c0e1005090114010f020a0807020118080607080702010c0c021e010903021002010e0c01051206 79
    0x450320030741940c9810080c4800c00200322940200f03071191403950f4820b41c1d4408080100070002005401c60b90400080c8200e1545005001401134800d0790b0860fa848a409510300015403140714607090f0700117900032480001520150703000a030401d6490340c000d039994840400d411907034420f421a040c0352140c00701c41a801c5101c496600c85007044541c041139800b01000c1c8055084135900648103254542c0d4005010810b00c200791082e01d800250381d00d4844c1d05612103032548003954034a401112a00400b1001058600c10108214401088040d01c0020749681d6413115001c3c00c601d0102c841d000c1407101c01501d010b0b82c8086040408164404030301420050750740c004584100000d00007482c046111940407403464000c000c603e03c260b90fa03a4420b0000d241c5000c0080c2900c4210060100388410306000d20016922400b41d440003600ba910410b100111204c01210310001c5940080c0d04a004591080405a810340202d10400c241000b2540b1080710000111481d208800440c1c0c081e2960002040c01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 88305747 1250 88304497 88304509
    0xc010f110a080406020c1207150b0d05060403080c040f060e130603020d0f03020102120a0b01020d020c03120f0d06121b0b030a0507180f0305070b070503040501050a0519030b0924 78
    0x2561b010340b0407164081d0040a40080d56400a40165500c1440c01d05000070499280113030404410103803100850340f100359581a41d5418007810045c1803102c0c0000180300858020195801003104039200a203d581c0c0300c6001e0150410800290b0003030891001060030380505024140860358050500e10702c03082d843e1600d40b800028404200c045540800005030302d10800e00000740112a44440029402032500000e4500281c00d01c0703140a64000381403e924640d07010484071561014551103036034030310804054040f030f0711840ca01c61a0140c50207001151031070070600501401c9105051100e049548050340029002482c401c840c10248104002a0f16003400d030031094214402341401c4981090555060f01200c00c070303421180b4102d516800410070302c10200005e80c0200014000c0b0b41c603092103512125240d116901034a070501000141142001c0e01c600c046070840e60081074052041036480f08001e000d080102103803031254501d1004508a010440e24680c0c3c940d11030305e0444800c01d01c08050140f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 88306997 1250 88305747 88305757
    0x5041505070b010e090d020a110402180a060c030f0206040807020607050a0f060c0311030c030403232d0c0a031202040b030f010911041a0f0408030c010f110a08040602 73
    0x41200c1480070310700080520155074041c2650074400241d51500c01030b01c1740343c00f100c4500c030310071540a5400745001c030f245015044c00c1d91105a50140e03803050038000100d000643c1504460f005003200a001400c16441441d00010320301c070740d4a48010701c005060483e07030707440300b80e6000d808030b8030030001d400040c5042002010354901c0303501903070f1100c1c28503100d20201410114060b140b040d25100441c180c20b5040c4a01e50812481826260039420030001840890100504c003d040c81060b090f161008010301810780450704081e20829a659010401c1620b0b03507000380d115020504001c02c800c3d1050f0002c2040e500003c4030032009024801950714116002d0b50401c1d42a0541ca40c20480817500c03903640c10080d4803a445220012046516000102003201d008800324082035105100502001440c0d0340080501d0b252031030740e40c0d00ca28001413400114400e41d40b010041344000516111a03000640001c1016018010b040001035000608003409110740511540000c07107000000700001c07c11f0380604 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 88308247 1250 88306997 88307039
    0x115020c010309381f0509090c0607050705090c09030a0312020c160e07170403030c0323090d11031b0c15040f081204030201080421051308010c0504 65
    0x1a13484e0190801d0000360411131070401c10100c48100c031001c1e01e42a1601c400d400c84166103401058507400780e4a10301003903540c004c140c8200d100c4000310300d080c4d01c2004200035191005007a296986a6031030503c0d40d031160380c0314060050513106d001540d05103e80040e61a082030160143c044040340307940444400e03028106030841c8507801e00004090200400401d0401e0401c082e4441c9240e00345008160f102c180108900c08004000c401c0705541e86034401095000759150601242072180140c0c1038010300310128080d281e0040070308040d10790403031190100307015107507001c241c408201e2484001c40d00032600104140b015481005084100078201c1d0400b4071000d5290150b07880020794000050f0050309488428075400e0000c6400d100701811195070704010304124000b0400d0300d48401400d9414040d81c030000c0e051004113800035040c03204003c843c00000c0302c00f480300821516500303005000ca81026581a45100c3c00050218021105204000155180340c032840d060603c0c1c50502581064503000c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 88309353 1106 88308247 88308263
    0x312010504270314120601030506010c0209010614190e03071203021519050901061e0e3405030601120c080402011107030f05010b03060115020c010309 66
    0x804000b1501c01d0314564624407504007582e40d001850340d1440e5040001070507010b0098410207852140f10309803800c120946803080115400008441d00a403c580e5000c0140003940c0210307412000c00581c081c55511b003400300340d0802d8004001951580c040b80596070211030720724060040c0006010703810120b0b00301e450340352030080d5200c4c42400302c102203041420104a2084888903d04184a0868000d100500700043c0450080c9090710444020b4440446494841c42c1d540c003900c1d0481e22041c490310b1a0b6140d00020724030410402e4400701124038481103200c419590072250340c100340d80f1900e0320741c1c40349850000940007202040e111610740b49021140c44241e41c002c204035030815020710380b625007049510b0486141205581003d884c01c0d000c0c0c180c020410905400480b5410410f4003a280c150f6a207988540c05418a075001030056004814088072a51003903000030180c0d4025111 = true := by decide +kernel

theorem cover : BRFrame.Cov 88129497 88309353 := by
  have h0 := BRFrame.cov_init 88129497
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 88129497 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 88129497 ≤ n) (h2 : n < 88309353) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
