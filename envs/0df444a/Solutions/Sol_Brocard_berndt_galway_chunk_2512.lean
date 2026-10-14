-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2512
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:49.164188+00:00
-- url     : https://prove2.me/submissions/b58d4a87-00ee-46ad-a6ee-6da56fdd7beb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 451618705 ≤ n < 451798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 451619955 1250 451618705 451618729
    0x1006480305180303090102120c010f050c1e180402090a030606031209060813140708030d2016020d0c0e0412020105070c17180a0e0603150f0105130b 65
    0x2503004103403424045480040950741010480045141c5401c1c5c100217910303150190f174146419078020031441800782003908886c02684205c5020070041c50020f2010300c14ad00701445030f00c1c1090704002070002410f0030788101c584800c000b00030316420070010800c1001a5000205030381d005040c0090000001c0c807d8080c00c2c010714814001c10a502c807080e400100440f82c19807100c0c0c01c1060600a000408400224000a068000000760b058080011207a032a200c8107070b201454070f20002940481c142c04580c0010070b81120152005d00d40d0001d402d55150901596501411068103101b8140052a0803003100200c18421542032a9a564a00c012680c020080f6010b544904007200d0841c6a558288140c3c3da0081240c100001c0211064a500f0140c4903408803c208052000884280507040c43c043c41c2c4101400600020941ea01e4100d0711550b070b241a2b440364064491640509a504480c1228500c580c074109544284e582c03a03c0c040140b10b814650040300d00b903a0f075089c2c4a13000d40300e001900074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 451621205 1250 451619955 451619957
    0x14071809030e0310060512010605100503060303070b0f180c0f0f15180418170901030605090109020c01110304030e01030b210f1c0e040506031606020610064803 70
    0x250702440d00c420300012200f84210207c0a92501d00c06018a980f480c03c0c0f03001001c10b80c6883c9403030f0b90300c1d200400c0c0345100380b040c0074000c181d02c0e104000c503002c24100035901c11a294202201600420090300d070740d6240c0c0c4501c540e80040c034902c0040c0c09043c0480380f02c40da00c40080401041d0001e001411055601c41a0500c82c405455018400103052034040e04024038200c00c03402400b0701c00b41d103424048410710070382558400c40004184100fa84079801020107844001c0116a070303540d407181c515000b07502080400b1403035400d00c065514007505a10a4038402e0b501502c0b4a0100c0c42c40f0f0300118004c0c4041c85c503090340104145000302d00c810078180706a480c07601040c001d182c00e8000784865894510542d15042c007001c007900310300c00c01d00d6000e01007102c40c0307030309031004601c40e12400002403c00c00c4c4801c03001240d5070407150000700c03a50300050550007003407070720191048242c40710411601610400090207554086c252056250f031003801c51030090010740c54142d90519102c2030300142114020600b54 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 451622455 1250 451621205 451621211
    0x201022b060f080a02010f110604060b040e070905040204150303080703020a020709110c0c0621040f02090408120108030a140c1e16090b0d0b1305160314071809030e0310 74
    0x82c4c2156000340e0004960802814035911208480c5815a920400200020302840d15040e032481c10742c07034a8020341c640101c1042a1040b0b141c07500802d1004223422502648241e080c00701d03500c0040c001a064506072a01035465075400c1c2e462203c250041d41c441c0b9407031011480b0310398000450142a11540c042d40e8108005a0754070706500080301c0c0740c007501d507901c5481290108000380202003544280342c86440c4030621a0000d0361241815008160325140180d00a280c45040004000c4468000c250030703d030341f66a904c19640c807a019159a400389404120119881d510650422032400000d084c45400510441e08240d9080031504410305415215828a61201e40103103141c5140d2141400548145c0c10100186280c3c07a000400d0660046d02c040e0149011402040034082c0e64448020035940040460b00c1d145192030a000984d02980b00c1601c0e480a914602220b01030041509822100c0034038801c0312604850030303200000d00080000310103018541403a000c00717843c1803000700800d601e200800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 451623705 1250 451622455 451622473
    0xa020409120807032901052208120a02030304060e1c030203010f06110706030c0c08031f0824070c0c0f08160609030f081b07050102010c0201022b060f08 67
    0x14007503502c0038107034409050910444015440c400030f0292040340310001d0441e10200d598005030341d24451030498444101c03504003480c00c8100d4a80c0410110380e1104100c03002c4407141d500d0301500e802070441820050f0020008640070a0403a00a41e251111050940b60254000c07403122000342244100322010a03008001040762810420036000180301e01c0c00d00c4400d94000c1406203884048500980092507130f900c03451010b09124a07241c646569114094507038a007010790442c056500c2062407020026128030010558003401b0404080000e86440485010a141c06040000d0316001304008100465007000c0d101048090300860010f01901500c0d03203015050018050400c02501c00012101803181d00070004298040c0320407007140e400c040c031310000c1035251906804603c540700548002c901c840300c61540724800803c042c0c04990302600204401e01004500741d0a0307010b0f035a038120060202c6030007100e5101c9220100500030400c0c90b0009191a1034600426005079984c01065041d8803060032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 451624955 1250 451623705 451623707
    0x30f151e0b01110109051504061d07290720030a0b060a05010f090b0a050706090303052e030204050402150310060807050403150c0c05030a0c020406050901050a06050c0a02040912 78
    0x441c03014000d1070f1009008012040d12a15902c1401c803101c0c015242d20b4030f00080600c440c0f03511260403d004e41d0220f000a210410403296502158007845207100a1a01d11496400f2040c07004030007541d140000c10b003040320302c0d280e00304e200d2030440394041a4458550300400070b40c0c4c28003031050321910802040e40b05c0c1c142241480420f40d1240c011a043c80580c00741c0004050b08450140201c1d0280c00c01c0e0380d50380c801684200c48a01440d0401004136050880181c10990141c011034803a8496203120101420720070f41030710500580d420b56070716010142c0010b002600346500320f00d03486070024041d50312118204601300c00560040391450443d600d80102404001d41c04120140c1250a03490410704003825519500485000401c00c220420f507a0407416070310718000c44152030495000310039039807100201d1601602074004100100e200c3c0303150100100b0540f920000303180c16100060290200c07a4104442581c0a0b409945080c403c5d108060017100182c6d02d5028041c4e030b003841480c0e40403144000084c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 451626205 1250 451624955 451624967
    0x90b1009050109020a170907180507020d03050103030905100e15031605070b0601030e1e07080f07030b07230711010807030203040b07050d021e0304120801030f151e0b01 74
    0x4000030144c010000c03e40003543c405010072100e0200480d106194680d511741c03d01e131141ca07038020701c0000303000c5905480c03000c010380c081031059111f6000c0c1c40d00180700d030004030b0480b002404010046440c04a0500c01030400c841001c486030010304080c2d40c14000240011b088501050001466020000812041034003007000c150b104041802e28030f04141e007990311210712140041442e81056034500c802001c0d038204001d0300d030124041001440d15082d00c141a103444031842c0c0160400b5104d101c00e0f466000c00000303810000c403034002c1300e1151a61164142142c2e0340325905242e010543d0f2031100001d02e090360900800c1d103140729540302040385402c8000500182e500406000a141c41842081b0120b003d417808554000322602e005036403220712003540002402600d002110409651070441e00c0101803030000e40c0030307078054400414070101a8000321100074090200604030310303591000f1400588140e030303000310420208001086405001c512196045003c001c01412543c0f00c1c00c0010307842d60480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 451627455 1250 451626205 451626209
    0x110f0d180305070b0a020f0a110105340c0c091a0f060d0e030d020c07030b011502030f250f14060c1e0706180506010618090b04090b10090501 62
    0x21031224000000380c0300038040d400b4514010b00140c24240c00a40c010f01298126280a801540e115840f1490250010441000400300354100d42c03804020030990041040307040368074650703042c40016403030300450000285041d641a1405004a02c800d85000410484181e006090f01c0b140000f88030b0801e0480f07440c1e01046155840c017800c000b50f5112050344079003080f501100111140800c0b02c0c600000320301d203980305190100c0341c3e840c40414800030030000421641d04403801003c0c40340d51a6212060181000301100700750700580d0040190f040300f802d0103c068102c0c070b4005441c1070012440440e20310070304602118200c458844070740400c1704000c1e000312045500e80e4104010b01252a1030440d1921512072003400d0360b41101240e02e190010400142154442903000d0405d000c60203044004180c41c40040804886d280240800031032a50320861101400d82c400001030071811b4a0b0440400c0100803805485400513200d540d500c001c104085c203003c0c040e095403000e5a562030300d086c900a08542c030603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 451628705 1250 451627455 451627481
    0x2d0a0b040b071106131e03020603090102181207050118030204021c0e0f07060e150c060f0702150c0705150708060103060501050c03070803091f0203040201091410030c03110f0d 77
    0x181701518103416100804000e503943c00258104e018154422005001280c0e84000c0d404a00081000704211040d00505894150741054036410b507480c0e820404c580c0600038150203942c0c408401001290701c100e809000300e070142c2001d007850a480e070b00030900b40e82c003d580710002156090b9180710f14400a200f0b4031540ca542d180904041d540d50000c0680700c1c141440b030082004100c001e1001e40360b40310502c0002003541c0c0741d070741c0350381d0103810711400d848120888140c407085010f80c000034001400804c1c401000400d42c61000591340d1101d100382c0075500010701c180c602e80300b4440c640c1024420070170401d000360020388422950b032500c540014155031030394008604028046c82814108000041910a0981e00c5000d294a80d030390820320504d410031868030020000c00090030400200d840340d00850099000380d8880a845440b840102c115101c14003085402403400d00407156014420f50080060401c2c0749408a0303c0c001c941c2010f08241c104030080038003940c00040c0541c4404442c03280900d04004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 451629955 1250 451628705 451628707
    0x209060c01110918060108042a080c0109060c0f03080a0f051314030a020312180304030323030403020334110a06090b0a0f03020906040e152d0a0b040b071106 69
    0x5c4000024002e40000d0801040b48040d26504811810382c442940102c80108014403241b50b99003400d15581c8007007144803130101b00c00c076901103090b6200d07841d000b52464105048081d204000d540440e400c0701c009100003901e6030b64000c42601c04280740501030080080100d40d409807112424008042240c0da0050340c0b00340c0c002c20000101d2a000700070384144891060f46882544c1c2d038a10009101c00c26540364035024040090003004050b00100108680b0380000001024007880c0d014030200ac1c0710940d8060056030062140d000101400f8030021140c541827181e0805140c2006188070310040340d41c000301c1341c0b11400719250707016080c0f60030340e980144158a0199495460500c0c1d1042a00c100c43c04030080120a40d01032032500d00030340403902c1100e4041c15503640c03030796142e42d481c1d0030100903110005081c0da41c80c2004010303c5d000c008131031b103800b40141d1041c0500c8030074101c0441c0c84041c540c40750030000705113000681207070f960b0240006080a02d0701d03d0740c500051074040f40c403103000c8221f9072090f0301c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 451631205 1250 451629955 451629961
    0x290109060e181e011701150302090109020901110106180b0303071101050703110601060f030b0d050601120c090203131401090302030901051c05010b180d02130209060c01110918 77
    0xa01e480070015007440030a0203603210b031108002500042ca02d030020b03070100c0140b5000000c4210840f1701d0028a0002c00000300004403066400c4841120140b201039030000e02c1000505c4070410f5640101803005c0c050400729090050328400b10b003901c1c40ca40c0007035215000c0000d203a44071a224081e44581c45821405145001d81d5a5120030000305225900c0e410418049103c908140c0a5424130210840f0b240468485607550035000300308181d402d8034400083e0810760b100640c0e0404a14040c1c0c0b141e84040600402d1382016040e445400c0b1005041e6005c0300103c9001407803140034401540134144040d03001c12055a83d041c0880e10403011240750103242e1520b01c562001c0b03980401514803c0009180c05c6960300300c001c50b45960701c0400f443e0180311038039240002410b42c148100400c0120302010300b507016000c1c020204400d1420300e00c1d0181d004035200e00a52036100d501e0303000b0050780c2c10080003030382040d00c80500c050856038030a0b10111403410000d0841410b10b40702c41c81c0107481e400452100f0b8149 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 451632455 1250 451631205 451631209
    0xf0901080706051c0212160305040b06040b0607020414100b0309030f0a031b091e060203070f020429030606040207020f0f0a121b0501050403081903290109060e 70
    0x30389100b01410000c0201c1ca210310000d40510000003c03030b008400359100c0c001c00584c00303100c4400303884041d40540c01c003400c4107040c0c0c02402130511507600003864250642da03000500c00503003e11410f050344213038100001d4005903200d00c14400c0250003c282d82942e844d102c80ca14450303010b9504519900c9005104208419100008031490448062140350321032010180036009403e00001c80410503800028614803558000a23002c11180c1040044500d80d5918403c519107150a000d45401a00b0421000021520103600f041e0a00d1010344002003803d0410f10000d800032880354031349800507100100459600d010405160441003c8800318504004e80d0f000540e0b0f0480042020300907c068001c09000755103150340d52004000173310141039007001502e0720300554090b1001243c4da09601e00e40118240d40301d10140e40540f503010812500d425840c05040410325100740300c40040640f0384c0205410580b103a00450044200a030801e20110240000580440d0746030304088200040007028108035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 451633705 1250 451632455 451632463
    0x6100e07121b0221031005091b0c060a0c020d1b050705060c010b010306080c0d15020405130e2a060d0b04051006020708060405060403140d090507050f090108 69
    0x141141c18600303150700c0d03000e04440c060051541c07224004000c014001c140c0a030007140c0e141c140d4000344100d04030440629845022804141d0765030051141c45842401581000004d080e04115440c80340c07501b20710f1501000c2120741c41906100f050341c008405200d007141c1c4600892040726824000f80a02c2010190300400c4405400b015020010f00070389141c2c14440c09212030381c0500b10243c2002e03a81d581c809070050107403800401050001c5e00c0c2240020740c04601065803440b4180060802c00700c603010b62140c140c0d100e04041070740070050b420400081c1a54581000c2c101e007505034030001c10640d44007034855003402c7d10b401000ca0100340b04000e4030b8624001c569071b0f240080e0b04981e07007510360129101c442c0003050780101a54119151a00744034003009006416402c8850765400c0351310403a11004802d440703000a44004040f68045008540064024121543c122609014003414540307514407810564003044c2041da0b9035003014600b0710041c203020740c16881d0140207840c518010f5251140495513 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 451634955 1250 451633705 451633711
    0x12110d050306061216090e1006050c030d0903231c111303060e0105010b0a0806210a2105130504020c0c18071d0d020f130c05040806100e 60
    0x2000800800640165a10010b1302c40c48020100d1560b00d901d0300f4400d000030000e01980c1c0e540030601e44000020582c0502101c503110308000c1c00c5a5400515102040d00c250b0400c031a105c0d00c1c1e0101707104081c0170700010301c540a200740c00781d50391000b412a400d45c4020900104c0303408400c40c45041000c0006107240201d20703110310401c001c0004050444580481a41c00386014048581f040341c0b800000f13118040c4c1110715984000e000070480350343d13507242c1c440d1244102e822107404111401c0c00940e40d840c01121892074400c03001c0194407029603617142c643c00c001d88440c080b902a9103078003180ba28110310072a81d5600e6001c605000d4506141c1030b60629411203d0f22a041c41241c00240c0c0d019108030502590303107c880050300c0202c00c000ca01030348a6a02400303d80c0240000c00c802600b5040000d0200d00100c451009081d00d42942002d0b003c0c0110442c02c0b00f007042d0044d10907001c500903840c13284140710f100c040645e40c154a0b60304010072a805c10401810301d040302c5140d0300d018017408a11b0416950 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 451636205 1250 451634955 451634957
    0x30f0f02061b13090615020303072102190201020304050c03060601120f0e0a1a0604150306020c0f0319030b0631050d0b01050f0915010f0c02060301090912110d 70
    0x42c80c00318041c003a03051886066050941900d1603803002540c104240c105206a80c4542d843d103001d4501c2d241e003280d0301d0004803082030008402c3c800c050240b00703000e801c02000c0b41050a001d442c00141441e422009040380704000010b0703500008000502c2010301a20b00003540c110013030411030600b00002085002ca092a0f1406036a9402d0f01d20038803505540701e002e11004007019034025400e541002580f0141d01ca200c5100b180101002512919040c8503940d082d81c9103149800b6182d01710380f940300c02034200303c1841d030881c03241101404040101f00007801c006098642c0003040780c092808001c0c151190f640850740140d00a00c0b89084000395845d03207031011000403203140b803040c00b8800e000d40400c0366948810b811003c0c0703050140500c0881d44200341607031010307a69041c4610b850820320521420440d4200d19140d11415008a03039845099001c00c4c031441850610744a049540000310240d000303034007080d5503d0340d403800c480c2009989014040e1045050030000030b0600090011500e4600482c2c80c48 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 451637455 1250 451636205 451636231
    0x5040512121903140103080301030b0a110a030903180f050a05040902090406181505010608160f08070c1709010207050607030203041a0c06070e1908150c12090604030f0f0206 76
    0x840e4a40c4698024988540600e4140d084c0d175030740e4144007400c2e500a000503a60741c002d4400181c00c0110b140100024104000c00700e0781f8101e00c1101c114001c0420440803000c00441022850721080351001407400f40424410302c01019241504210074100c0383e51040d40214200705291016948802c03420f5403150300810007140444020190407014202c403071009010150604034030740c4104540e03000b2416241c95850704590f9031134440f03002c507a01080c1c04041e13000650145010348154440c241c00d603004070071400c056114420f5965014040c0308640070380d070400400406c12000317648e41042194018403007610828030740304c59030b10000e4403031146000b01c22004aa51520110b0360f4808001c80d4500c8100d00241c2d841ca0411b034500400e44070b246000f56100c0d409200e50402d0508424504004690101009001c901290325031456500c0008080040c444401c0c020324801408001d80c10b480ac0300d1800c00b800980c031302484c01900c105507041c151400c1041c100440449290002812500700510300240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 451638705 1250 451637455 451637497
    0xc030c090411040b060703050901030f0b030c0103110904110c0d080103031b0503070b04082d1c060302030d02030c01050106170f13050d020106030510020c15250504051212 75
    0x3c00c010f03216420000703400c481d0000f4024141513008002d0103258900340c1e414401c000e551440c500543e081491056816082500001000e41c029400307442c440e103000c9941d501340070141c0d00003004c41c1e40d60003145840034000510141c00c40d4050002c0d402c2e1508505000c0b48035411602d00405441c8035110141d4940c03003000c2075000380041081684c120a40c00a0902c800b498a8600a40150030040c800c103c0c0c06405069441005e4106548289402900d200306081c8404410450701e00c0e80110342d100c061694814010000d62002c1c44900000c88654004642e2028009415802c68005a00180421440c034441d07a0b0144010240c05400c8030112032a6011900c6994081c020420700303550091141c810500c00350071003078040d04004100e81c060000c9d2200180c4000400040c7e02c50f030019400950000c0d2001e24003110046100d0390084401607000c81d980701c406058030000741142c01c107400440c50129040143d8900703088490841c0079000040e001a201582c4441c0341409110345011012040b41c0c2c1c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 451639955 1250 451638705 451638709
    0x3010e0c0f0f031017010b0609010507060b06070804150903150b2707020708011503060c02030417030310080a0506071b0204090c03021801060f080618090d020c030c090411 75
    0x54484140d00d070300b01e095403401c103200d9400940312688620302e40140e4203194a41e010300107105a05003000c019001c6442d055803000111010f500281c803c4904541e1250048040d448500240206a01c140d05d1255214200000030b00c014400c3c0410608000c40303008240001800c0ca8200f6106030110340011402d101014005909004c1c40c98091120880c071020340703501c8003200702c5202d000e8249602592146c5031514202400d13a039144005c803050852210f000c000003801640803050701056481607030b050036268581d90703c000c039211440c03030ae4981c03010041c03000c44c0e0320340b580290050001e8001410309a000e82d8036162070f0003008043c002408134580000042200c50138550440b1a4006c2c010480484203241c0411040154003040e80101094042203004c000c0c00c1c0e04039410b80d000c0d40c4801c0d4001000890443e152240141496005003046084c4805004440850740c0508080300140903d028282002888d0101c0e00b20140c0c441e6103c03c8045031242c4403c02101e40140c0c00c560ac030200c104203140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 451641205 1250 451639955 451639957
    0xe0105030c04180606090602010605090402090702030f0d02030106020d08010305060a0e0c040c11010f020301031707050102071a09060a060f0501110a0816140102071a04030c0c15110303010e0c0f 85
    0x31043c20310201c440c012001d03010403035111409030b80311600e030001307a10703180c06049007218094003406810a402501007405454840c91403036100c8103d104483c50002c20700342c0101260400c204e0540001c2d004401130001070380500c4844280005454000c443d0741c0b450b25856603400000d41203080d0721b9030b50555491400d00c02d106e0954501c0c8060000d00c1080400c40340100781d40c2009007202c040794680a180c0c2c05402860084a041b40e80007020180e444040d00f1000e0440c0e0f000500448503594204a40e900050f1024081d021a01d00446100024074040341c103136040c02c2d4000e094140440c40d000b0180032a07400e003605070068030030030720300440078041d0104900c0c900303a4020740181044401081ca500140d100c01541d20f030036846400c9903d80001c00450b1a03081c0c1c040e0100040061a43c18841c40f100c5210780100c50f840350103458000380301f02c1035840e13002040d10aa041030541c10b400c503411044207500000c0c1109644803038001189190300d00551590744410103881c0075028400003509641c148a800 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 451642455 1250 451641205 451641209
    0x40b040c080d0210050c030405031e07021e01110a031b050f0109060b0a0f0e04110f1305180c0a030b04020d060f15050415052b050105061f0e0105030c04 67
    0x190890300b1190400d50043e507944d107601c003182d0304582044009000820100e040d28091a4030800460928081e0801600301000021100404800911021000da03590b13211a0388645401c4145404e0256080001030106c100807210f201594420381420000a034450b04801c022185002070f00b9044403d45401d605140086591946941c200384004060100790384c0204281c007011a000303914550f0394412591007c070310344181e20300c0080103000a800b0400400d640c3c00301a00013401c0094076a0300100140c8040180e015005c4055039840c01c004804031030074038261020001070003c0c0061509640001c2c03808140740402015108503101280440d15980c0001c907a03a0360005040c0034a0a584001000070b100f0903030588943d11481d1800545800c0c10b00c1890148603807050001e0900d410281445420b42102d016280204544c0e42c402041e0400d8840c0d50440f1882900003050030704024003003121280081441020101ca448403c4042c5074002108036144603003820310039240d6940078180081c0e80100c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 451643705 1250 451642455 451642469
    0x509011e0903080f041e0303170c0d1d010501091802060d0e0a0b1e040506060f0105310902030c250f03050702090c0903070915080313150512040b040c 66
    0x2040080403214a00702800030780c0d4041144a04101b11140606a500038501c0041c001c6450081100812500903154507403110040002e00d1801c1d04124401341240c07042040d040c2e00a4418030207022402080c0121401046c050304107008044508c20f0802805160120003132040b03400040100b00e2944640021801015440c207880c411071880c10862000230084414841c00d0050240843c00040e0701c00b400c50085800c140200841e540e00003c2c044800304001425040c01001c1c0904810300503081022828446001e0004800d5042c80010004010f4940c1150011038018800c01150444d61001e90306000d10042c886d8075048100e2501c48800b6403100005044501403401030428035030881c0003041d1062003501c5003182d50b81d40341c10030040c41c06901f00b0b155160b000403001f0010170280b60005480c40c1585111154860368451000341b841c1c0c080900015003071500201080700e01e0440d41c807003541c94454103149150504c0b00c00c2d07070904c62800620040421609801040034004541600c0c2d001e0444 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 451644955 1250 451643705 451643707
    0x618151d0108010c08070c031d090705040f05100e090a020c011508150114010e0301060b040f03051203090705270703050a0606020c030c060703020f030d020d06060509011e090308 78
    0x80348660284403902401442001d60070250800301030391140c4200c80c1b02d140103669202d84401280e50031107075030340300c081c61006050704003410b64400c0d81c2e0310104a00849854850039522441c202c00507007403d0a82d48860310441610f8203024019400280040f9064000c0724064581c0c0d641d07030f20120090081414400301586409840598009452540800e4802e00c40440e0740454030b00502c104054000d0040465144000241c95565400364810301c0304008000d00100c1c440d500c94003283c0823038106074006102034200c85020010720006001e604210744152080c1450f40c80c002c0402030782e03082203120302c90007050610320041c0990300301c00c000101c1020b582c40240b801d080c0400018042c080589100c61120b04d41440040e06900000396010980c07800350103840d0240506080264941184106500754094046440e05c940d200340001c00400d02c040c84010780f03c1780c0604041e011609a50005030901408200010f2641c0c2c01c01c03240ba0b80c003440c60307104003450be800100460702503406074002082404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 451646205 1250 451644955 451644989
    0x30f060a0f030c030c05040e28050f010c08090d0f050a091203030506010815030709020309011b1e0807080a1d030f0715180609050a02100305090601050301061815 71
    0x7400507560782145d020304021507505843d501080704480021004280681c4500c8c0f004005e4080300c000c0e42d1402d80303910401c222458090b01e0301410040032945111083c1d544410403409290040b5206030070040620082020044448001e4190501300940405125010888105a62241c18548007a2000490010102c1c40318600940038240648042d408151074600065900700e001120700030040c0c00900030201d492034090725030000c1d880501000c185540f203001100084040d284c506030300d01c00703590b5030150078010341d41e401c01c0c0b8250150b0040100220703402440b01e020391103454a5000300741c00c80000b5050010343d0440760007480320104219940401b00d84084031720113203405030504500440c3c03c00c0746110b04030880011500c10811722401849501c0041d000b00303400c0e901030084241b0907812903040e05d405070002412400c410a00b4800280c581003000400c1400741300d82401420290002d000075810122107907242e20005d070380c0c202000e603141d108502d80014945108000c2070b55004003403241c0707 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 451647455 1250 451646205 451646213
    0x109050402031b130911011e050403080304020f0a0303022a0a06180e070c02040e0105010821070c090506011e0906050a030b1003020a09060e010e090403050913150812030f060a0f03 79
    0x46015140340d002c02c1e0010300240881c0411000e41003c0c150641d40c0a1405095a53302801504081e1044c0c0c1c002000c0580308100e030f280c240b40310f0040c500a400601e104501960766441d1800c0c020f5461040072060500008151150070860044c0c1307905040c5100d164442940307031900c8103029407000158130082014404800d8100300c1e035401081c004d55040c030000c10308481850030b8440a101c0d4030307070581c40303905051510608403a5444000580420040c5807070f86645503030180c0c8000d5000440003d80d81c9040c80100d682040d000c1c244100c4488003a69030030031078200a01640390320710410091000c0002c001c41c41c5480ba500c201c2000000414005240030200c0d8010003e4020303401150220f2441c0b85c0110344540200c0d4200c18a0005030340b43e004500340320b41030050b201c07406817045003405024003030169186e54000441e00c88410110b00016650301c01030503c00641c80d260300c800d0258002d004a844494004000c590380300c40b14030410b0700303a604c508000c1190000c4584c0001301602e000d042c04001c02c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 451648705 1250 451647455 451647473
    0x21606030506030d0c05030f070c0305060906011d06030d1407140a0201030507110604031b051005150a080a0609020a05090703060807050604080d0305040204110c150109050402031b1309 81
    0x18600541c2240c2241040c10070503031740200000800307001035000348015650084810010f203200340c841d001c50a20541c0d240c0c2c400e881c0c0742041e138001206800881c014094040040640c409801010314511a1400c0650109442c2d0590101d20310402c158541013000c1d080403141180d11240c2d00003806100e80b01110892501c801e6010000c900003810040400c0d1418840d80328000c072034810901070001500c40350303003d036603c9000020101200e0019401400411780c14806803080701800c1304041954a015081d1031944184580140c0c4102009481400312420000d031200c95a0f034030900020f0300b03901070300008043d080107600440d40a5907100800070301d65456080035007200e4a1400301d5055980310f03402c01c03d0071300903806407004039403001c0041c00080344603810a542003070015000140e003280c60f5044c031a0680c440704003d1071075030201d190b0100c0c046202d0341c0b003801001e002c01c081289091950001c1d850f071100c00d0819680e0108070090341c00390340e40c14480ca1000c01c0401e0781000001c0803032404a041d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 451649955 1250 451648705 451648711
    0x15041205010b100804023102030106050702150406050a050d0902091e0703091a04241401050402030705040b0a030e1009051b031c0e1002010608061302060d0902010216060305 76
    0x50b10385000c1440c00240140344d441e01442c0d0040007400920484640c144c0c0f000d40d24145484c981d203c00f81d40c03998005952000314080e04095840719501d9001d03005004403601c00b40e00e141c1003c1b50400007041010b901c541034805c24007461a210f540e0749000740c3c0b000c0140112020281d0310001010504c400e1051a4082c0c1c2a9582006d01c50b5412b50750307258080c3e0403281c0421018180b80010618901710b00700301c1c0d59060b1300500c034041c1c1401c2d40d2460000001d018644124424005940e241c0464444040a07007041c01414119425072941c0f0340080028a207000f02e12954900c100040782d01410356029030803040c0c88005d24011a4081150f0007a5203020704508a01510540604541c0303e0000e81341c00c0e90f0201100018006002c1c1d0000c00035801002c2200c0040401088841d41031234501c1d0b0760355414002c48103966800424003e041218042c00c07d0700240100300c1c4621000312420050b1200400c2d03440b400703480800001c2d290264001031b800c0ca501c8011941b150b454082e03001c103940e605a40b0483c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 451651205 1250 451649955 451649959
    0x20906070213060f230d021906050a170c071b090207030c020406080102030402030d11070e090307030207060815101403281503060c050f040e01061d090615041205010b 73
    0x4403485d50b954283c607100c12014510012008466541403550400307060340080a4405010310301001e00b00503c0c1d0b803642c0e0f2240c0004001900028284801c980e1180d10b0086000c079189900350981824544040c403481900e80040c004501b92a130613001e144900c00b043c0003410400c07415581c0388090710340140a15401e400803840b4514012002c2200001482a00e1040364090010100c40c00042070030340d050b1b4404082d1051912888002092000f0342ca540540a01204001152113410b0f80ca8043d0800250f5080300041044240820040101358130540303810100c20741b8110102c104000c01101c0d050390f40c0308045032030000002030104200680314440d901c2d003a680342011003d283c5890300c13002d807450380441804190781f80c1d10a01c04100e1b590300050314050307a810b1952602d071050018984641080e4440075040300701000400032250010180c90301c0160f018411960b032008100014610343e0f004c0c104c0c500505034818404030f14070720a401c48020b8007071400407134140c0f2080d00d4500e0191008210b080c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 451652455 1250 451651205 451651229
    0xf01060b04121403040503010204061d0907091a1b0a1703010b180423090f07062a051b030c090402030303041226010509130503040902090607021306 65
    0x35115200303105450a45040d030044460004079511101e003040100d64180304240000c04c400a01035500348000c00041c03007a522480f66841c00580d500312000c129181040c000d04481d8204048035500a1400301950300145182001100551801ca0740303009190310040e4240c80c11000788122040080c0c020740152080501c10b001d0300007244180c0c8640800e2003188440c201c144000e004081440a00706c10244002d000011903400c4031094815244580700e030b08101b202002c00f441028a8107101041c40400004000d250701480d020b402454040d48103044824400b00c503070902c00314603d031564444841d4002c4111081690000040b5507407200c0070070594480c1c41080084401c174109140140e200d260000c01035811951252035521582140140000401203600781034001c060807450321560f20702c0300e03000300e100e02e40c145401c2c402d07a172601078030811301c0781c60810340c1c031002402c004201c4043e2544d000d80941c071031203072001092803402911002940704034100c0c208040c00b202c0740e0000c41220302e910042 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 451653705 1250 451652455 451652459
    0x503131b0e0f0718060309050309031e0706090302090412020124090b0301060b041707030b0103110f0103021201170c03030d020a020105060a140409030905060c06060102010e2404170c0f0106 83
    0xd0f40c00314010075511204c1440c42c001000114000d5108085850203102035920b89240c0c140060b0a203100104810540c424400c81401c0e08001040300001402c030905183c1c807410b041d80c00090034030b600248018101d5012440d80d0001d40d00c00e401c942e17505451008551144004400c0002103040c0034000d00700c1061500c00505414901400707040c1c2221700d4402180d1038036007060940d0310241c9464071008114070032184004009000494018021409080341030b81c0c02050780204000c8542d03400d41e5504150050000c290b0a441030886181112a0b0314a12040391302d15401140c2444010003140703038140404500ca03903200300d041d0020000e01115500810290b601d502c1000008610f90003002c40c0644000f41103006030400382e00c1120654001d0504070340e450398030790002e402540908884442600907001f405071650302402503550594811000d01954403030341894802852018000d00c0700c080c10341020400740207240418841140130642195940c1e1210b6001d10b6840c0c00f158407200080d8649140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 451654955 1250 451653705 451653707
    0x27021c0b180a0c0203040b033420010615022d0a060b040207020402071401470a030f110409150911040f090201031b0503131b0e0f07 58
    0x684440d16070a01001c503551141074508004102410200082d0710041002280c1411104041e42c032525000384090181d00703644000910704090104040080604503030b04031211a00903900151f80400040b2a01c410201d0108076401b400080c0c0c00102c82c0300c0003941803040f565011802120400803070544100c1c1410a000c4040012440e0a04440e10703002001c0c044002021034002e0a04408010700141c1403500301c1d00020f04a07070203078108031400003600c0c05016098000380108603611288425032369440201c51031075002c01804e070f01c000802c054401a07410309601100b6880010b10409003013480b010f51a868455403140d60200c0035684449ca0140101c283c0ca8607028101020b98410a6042644e43c5404480d002e00700c0d1080480303159240348492900f40e01e50f4031403000041c1810002180000d414000502204d0388442548404940c0c44007498204d500201202d4025420181101c0b0008113410b09a8400840783c11350768295055500001d070a80d40618014010801c00c50b03189071686034020 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 451656205 1250 451654955 451654969
    0x210f030405150a03091514100302010912050a080f031e1306051305060f07120209030a081c0c090e060d0c030213060902040b04080c011827021c0b 64
    0xc41c0c1d640c00000300719440385a5540300c014002c000300700e00340451002c009a94110b42100540b0250088940e11002640e1940041502c030780c0040c0003c1540d40928110340000b0070800442c010242210300030001e032405c220080062801041c0c0043d0516125081901d1010150f03005403420100180703055401c080d4100b030746200c00e000e80340c0320942c0c2c103c4124030340ea80409003000802c2c1c03200f403541c215045004290305104c100d20911241e810960720745000200a8103c1c8004c01c02c07502014414041d0010545000441c0303000303550048506078640303814401e0109140d4003c1400c0389900e041100c801c141a8110305d4010940c1c0c4118104251a03698109000214004c80d501812421190380308001504008114003415100f4040c0441c0c3e05880d0206142607034420342c0300c801080e80005003000811814099851501000d207800c83ca0150003000c02080d50f0380a0113020988545640004024450940416880e04c4400015910307409035030b51404e91501c0b100100006681080300e801c1c5a860320034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 451657455 1250 451656205 451656209
    0xf100e0103200a0b040306090f050f0d030c020a0b0117030f1801080f0f0411030124030203161503020306040213031b0b0a02070e0a06120804031203060f050f040b210f0304 75
    0x70344c8504091031074940501600c03c0c441c0a465000b400071641000c64030030310580707c2d180c207184010140000c000c81c00400300d421f0348404c1c0c8119000000c5140001380b010400c03d04440117805158400147d40b0400c0b070451203043c454038020400010540d05054004441c007041440c04d8a542130b013075452038005566010200c07807080c07044844a00150028003142c0070054242c41c00303000042c09060303e1540781041d1500032501d0400f03002c002810011450200300700e100510100403118001e41c50204c41d02d10a0090641c68428076801100050964070742d40e044d10700c00a0800c100801c010358a04100500d40c0c0040d03da0600105c0d4241c000c07807031007020f008031400b03c0155801010380303d1a0600d100345500c005440101065240c0c41c001074080d18a420580c1801d010315a0940d43e00c1c0f030b5250520300d891022045500b81810710a00300000601c14242800700d9038141d8104868001480c00074009140700311240d0780c04442800e15400e00d54034070301a00180510f02044030ba00400808003666680114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 451658705 1250 451657455 451657469
    0x9012712031107080d0e1201060e0c07020a1508061c06110910030608060606070606121a100f050607080c060108030c0f0318060c07030503030c0a0e0d02090f100e0103200a 75
    0x2c2c0340d0101d4500b07141d20000707c0000c403c0d000003a81034907003503003090340303042a03a81c440c1075140400d807a81946400000000184a28403000c91003048040c00505121001000c07603103d180501504441d05122403601406207a005100300212024600c00034580d8108800490158030280200302409009110b21005e5a01d03d000421241d911a410496150f0110b00f00715441611030100185203a9402c00c10445181300348903d07605801d444282000d1780400501c40d903140c00788044100944000d8069100c1a55000d440f0b860390b81e102c0d400c041d99103108440d10b44c0c9580c814100009083c49010010340015034001c415280d5585011456590ba0700802c0700c41c150014041070f4441403454184001c201c2d0b43c4001c000e50b0400c2d0756076180c02d07003150804c0b580032028070800284850a00d0f4004008240b0b01411035811580000940205510a80043c0f0712019080e0090114031240246035090008021700107101203190b84070303c3c000d103040c2000e0400340c48518400d298405030786044088501690b0351 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 451659955 1250 451658705 451658717
    0xf050a0605060c0a06020c01060503010e0c030123070804230c0a09060303050d0b0a030519020a0e090a020f03030d1104150314071b0b010902090f0609012712031107080d 74
    0x1050702e4640081d0300c0104c4447d803542d42c91a0010b055102030148008840360503010b000c825503200245801e542c114220306c254024201d16032400001502c07030098001e421813514100344d64651800500381403e01000d00c00b03803012840c001e551864001080c11a039802079400c101d0442c0e4640c0d660082c1c070701600009010807800d001c00001d400040c0c0c00f0b501c1c0614001c080801440d9240c840500749402c83d440c0c201c0302c0880408104c02c0d42000740110000b410204a030885615050240302d841c0c0c40c402c2c174020710513000d440ca803140b16a410070984000409035581049600c1120004d0691940184200e00c01801020305000c5068003e00c03840900304003003000d1900716654144100c5103e0f824000d90074082160081160100c0e02c80220710703001e04000c01006a841000c1002c0201840d5032080340707803061004120186459900004800d9101c4440c008001d008820200c0349542401c145c2000094010f0304804906140e4440000140920f0a100307964007182c0364020152200c2c00e038220800442d403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 451661205 1250 451659955 451659973
    0x60a0501080613180c031203060501020304141c020402040609080609010606080f070512100819080a05160501050c070b01060f022109030706090501030c020105240a03060f050a0605060c 81
    0x41a08071031004443c0007400c3e01354507290303034960010102e542c10603070706400304201a101f016014400c000240000340025400c061800c440805015003003485a030083d00803500700c41240d42d03c016501070b255801031041d034942c0d407600002481d94041d07104503181c1e44541008a0741c4000103101d5401540e0305a5143d9080355914a0440070300c6202410741810003100700100c0618100020480340261003400501001d9072410711424649516103010003018480d40745010001260b96040b0b440d01c80f01801c0c802d03141c504017846800200c403c85000385c059400c02d8100801e100061006156280c861001e000f446c0e42c07104c5c0704482e0161010309a8000d64022880303480c0079007841003801c402d03480c2502c40307a00d0405c0000c007007810300501d5406040401c0b6200300a00480d81c0501503000d0b00c90052001704a91314040425980e00f000250080e010000340312041d8940b5261400c1c91806140c20110520500c5085425100104000c54025202628260700801d041c60b0a01c221034010000340d000b845200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 451662455 1250 451661205 451661239
    0x906281d090c1c02040303030b010f11061501051209161e050103050c07050f0d1416080c0f0601140312030c070b0a0b0a030609050d03020c150a0207020d0506060a05010806 75
    0x15100d6800c00d00f0301e242180d15040c00401a00090000d5486580d010440d440700c10300250441203c0d000403000d11208010020718104005042d40e2312145281c1038204441882c401a28540f0400240385109040c000422105410010711030540b44080f031444420103a45e1000902c0f00341202d0220034042d0500d0000708a203612980009800c58100e0507a1407601c100c55844900c1c0880b140e469101036017090040c1030009800c000380d03880e42106c0101c8103280240c0b0034619400849031010080034a0070204003c00404070030001c5408c500307c80341c101d4100e56102d1440d0100c940d0f91880e020700c6403040301e4668a0000d440c40c25240a091030100803818908241d0b40d4001d00c540c000c00c1b8040c1c0c144d550340c0c07c50042d0f50b9012800021402980c0000744107106007016800e200343c018021041c580100030512440e400010110441c5c841c00c8451030381078542019950292090700000303035110844074009010703c1004541c0600031002180c2461410384c1c0c070401540c0495045130029480012020b054041ca = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 451663705 1250 451662455 451662457
    0xb060301060503100b0a03090201030b040204060c0308041506060203030a0605180f150307060518030c0a03030c03021002130e06010309150e19030e090f011a0906281d090c 75
    0x4400101e1040c11300d5900d45000240c1c40d00840700383c0000a48a80c80e02080d5605489400700144040c2c41c00e61030103050030380c003400c40c60780520020208000c5030009401c0c8a161480c444c0030050103001488020782e20360000b59603070815030b58a143c45160180004981c600509103000e03607849030410402540d1807084406810600409a40c80d03c0d01c84a28a50203990601121004d0030b8140c039410744802c942c8150800126075554080d01a50012940480039074901c0c44000489900d4584500c4060a0b0b01d400c070b0809034000201c101490011030201490120085441c054901020b407031074050340e03244011015600714110103450b140c01d070034640081000319000710b40310b2148882160710508080c40c11205040c0c3c030410a60001e07220703649040d80d615260800036003050b40b401c03500340c880d410120352801c4200701046115250500003840c803000e480307040c103403451083c40044550070a24500545400308003080708050004450000320000e0390307040c0096014182e005020045030b583c4108082241d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 451664955 1250 451663705 451663711
    0x105092b0507060b090108100608150a0908071703040209161d010509060301090204080706020f370501060e07030e0c0607050106210b0705030705180105041806080f010b060301060503 80
    0xc2e10340c42e50b000000d25280c170840740703009002c80402866140018a150011640070740c00403000c641141e41d07031508140030485540c4c1c01c15000c1e8000034840b0032038074211070b8a1003820030080c1350b0a40e9612047c1021442409988114002e1b1415a02c035a103e540400810001c00310074800315203105650301c0044102600e00320b10013810704103546002c045400003021904241d005011103500000c080c000390348188943d00c001c22050008150050130a8445600e89002d450300d5480c2c4d41850407040c0c031000340034024104140a03a00f024251000da13040150280150f400b4607414401c000010400780b5120b40701d03214101e15410050050511003604020340d83e40441c80542c0c403036403602c0e000b08940e0b405681189411548002c2144040001c5c54042e0b0704400081140d01400390a0080204290304482141c0b56900303000e103408620a00d45006841d41e005682184a0341c0644203c0c0f606203c166502420550342c003841110700392507003d1440d9081e00e5140704000d8000c4c1e028001000b1460158000d150 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 451666205 1250 451664955 451664963
    0x1209030206040b0a11181201140a02091c1208070206012105031911100209010e130603080d0f050f0903040e07120c08070e150433020105092b0507 64
    0x1d059017200700e40460f683c004045070203450000d58a0021310b460080381d652030b2011120000c0c4002c0c140ca610505c0c05c028000c000e410740703e40000e528503065440e00c0c20582200300b00d17843c100f0b22003502e05020342c01000c03044040000c2420403001ca0f010030300000d852412610181d0010032401185160720000b0060890304807014070050000790380d64400c01c2d1007054001401e03616046c0304410905100c0c60408106000c1811500c10440490140d070301040c68102d14805480c0107000d40c41040050005005035440139000103c0411178854185554201f40b000f00354a2000307101544490114940d4803800355901d0100364001c01c01080038004202c0c690b5444420b07810046103070002e51800c001903912407400d05000505490070089069006400c5403d006000c0d100707101a28090780200e03046100c0c0d80101c104003401180d6041e031820002548101165041c50443c5880ca81d007840030340604815500c0c041540100d05003a0704010745680c0340e87d41030015080ea8500050303c490191502d41c02084252 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 451667455 1250 451666205 451666211
    0x6040b0f04080d0216090b090109020c0c210d0203030112020108090f0a0b04060501080a03170c130927080712050c01020c100c0c030e04020315030712031209030206040b0a 75
    0x1420780c4090122046603410f0ba0040c09403030800014221001c2255006142034034649140300c0103a1b101c1c59030583c1950400c8000690310700b10520500c0c0307481040152558420b07520841031844018000c400400098003030101c4103000d070300d018240d03101e010034040c82049283c01e04502c000356110704040342d004a030b08000d403054242d400840504044070950305862540542c000e00040200b131740305450050801c003003d0020801682c0c3e00511008114050303c090210200105410110b502d08481000b1041d5030390403001943d0b194110090210b41d0b8101806040b04107149905801c403041c4540031580c49644d8525081155541c0003000c699000208e08105040c45060741480b0248002c0400c03145c00d038010403501c01b1a856102c2a180e0400c12881000401640e07440029000602c46440748004c0300c0161700c0b90f4a55080e400d050701c3c0500b079641d2600c41e00d400061010b000d40c1e00c10303601c0b6020f542d41c0c3c034400c010140310200341d91090000a0050780b010000074045000b00740e000b50410f114113004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 451668705 1250 451667455 451667459
    0x130302060a080702070509250233060a06140f040e090c04050601020705060703110102130b03071b0b010303080402010c02130605010207091406090901110a051c060506040b0f04 77
    0x100305141c01204280011551540600030015010042d2100401d0121588280361810b10a859403468016110300348400c1c503c0d0340c907205240280507100c501055105038400110706800341d080d036482d0007844140d440105a010858605289250006039003a0b9102c41103540001e070795a6050741d20101d08852070f58428400407420503013010b01e80340070f010584010038000310640104421104007404403810340d4083d00c010059034843e03809a82e0307060341505010541d4842020894060b01c282d044010b101440020041501540c1201641c01003003160348160f90030024801010041d07c0c8042c003d49140c0301d0100400009226540b820360003403042c50200b05144070360740440c0301d03030580c1c0108002c0d1980f5000107200e2568104400c07401130811403424400386031201096200c002d009421507000380c0c2000000b0700c800da4250001c4c0c505c2121200e03095070320a1800002130103604035442141c4c11108200c10810b02001c24041c0c035082e900300810303103031800d442d006103500b045d400100d004c40c00721014400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 451669955 1250 451668705 451668709
    0x1b10020f0a03080f070c0b060d02180106020601150f0203070b0c0d15060e010c080909041403070c050406060f090603180203070801020c06220b0a090506070c061a090c130302 76
    0x1c4070614900c02c0c0c6a03100305042c22a140100300d44010051000c0201002c8400b000c62082c0c0d00d20f942180f810303240382c1403c4a440c0042020450880760b408500180c8500020b58a6800200d40d4101c0b04001c44c010003825200408681c070300004814680181c0c81448440c1c0850840411143c106046120103450541103074081c3c829141200402d0140c8145080c0c100710440e006040b40558a070246051000540f040c1e07100841d90148074901c0d0f004018090014041101e91001020240d6158088a88819561500c08800052401042d0299060050003e0a035014066000d401d000c01d841d4800c034a81882d000b02d008048100c0c80c8200f03034000c10700755805a10240215009172074400000359803049100300c1c1901e4600044c18040000f88080c1c189202c88286595500c180b0b648100030fa02c0b1503d502c01181c01a14031581c2c05000c81c0590018007407125048401c0d0140607100d52421300210040e18440b8000b501281d000d00c2e00424024001040007a200c4010100300394801040d40340300340c0342c1d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 451671205 1250 451669955 451669963
    0x30d150816090501050406050a030b10080312060102070b19080907050604060e1801080a110f040c0e010207081f020d11041217030606070f0606050301180201030e1b10020f 75
    0x1018041101d020310090044000a00038180503010584003404241c1c60b1802003400e18066100280100300884c0201d03d034080d0b10010503004020313300031a070700e80704440281e13446184140d48903405841140d400140460031002600d40001e0404a03481405d44c003000141e82c0c14030010621400f5002d807080c08280c42e43e036600500003412440c4d8400d900855420b09004041c103150060020074440b4200400500200003004a0340c10f60101d20030040250745c102140000096640c1c1d140e00c5070400402032403090f170042c0c4c0b112210000342d00701d54480c1d0b991007205481d130f49082d654804e241102020000f007108240c00402224030124400200441004d022907000d070400d81000340a40d00c88468103007444800e203103101440512042951850030001c2c0016098801c0040051001844500074018031840754007404c000c04019000744080a030096280b20568400d1108a003c80d04e068011035400800107410150794880e104034000901c2181d041008000d20b14030110114800c94001d8007084000748 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 451672455 1250 451671205 451671223
    0x9090a0c0b130504050615180402030f0603010b0904030f1805060f0a2307020d0f050615040e011406241306140c0c0111010603060908070c0f0305030d1508 68
    0x101d0815240d546100100e49502480d0f801144518202011301409030f803916400d844149900042e140d0307682c41201d00b00c600f140d401c40965801840441040f01d40441150054800e450840080020141103010011809410b0302c0140000e400c1034a0f614440303004004108000700e00c050030407122a683d81c006403540c1d20040600304400c00201c0da0344801e642001e07190144801c211201c40c0b4456900043c050113008007000688221140304d8503030240b00500c5090820160800262a91480c200317000b4141250018030315805039140400d4510049818800d01802d11040494203019403142010000800b2200304140d0256100c41c04a40c0c20013030301030040501721174004130441003520300480070306040701031001001c09040410004030000404908942180000d090044100c8240d0019500402103600014812440c000c01c42007408510009051628130808031090071030303218030703080f5501c4030b19101c000c00690082c80100001080c0703405c484070461204c00135542855440a01e18a00481d83e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 451673705 1250 451672455 451672469
    0x606130519060e01080c030705090f1e100c0c05040b0418060b0901050d050d141b01021804060308030f06040906051e100b0703050702060702150d050901050103080909090a0c 76
    0x200700c100100394018006803041c441c02d0818001034502452034410350311006041908000000800d403025a4035525004410320019018034501e0407070b0102e401c0b12654082c2098414180e940c1c2000c940c0b0310900c183d049160f44603d80440c414513100034440076010350111030303034040d488540b24200c140d000c0101c0301030381d40544404124104100240140250180c100030300510110400304041000052144a601450700e080030b00340d0151a501c000b5800382c6104013184c411090000b035084081500a403107000c81200300d041d2041d04500802c0112403580c800108407a0091000400b00c01043e0000d59010030080c10105250603d1303900c43c01103072001c84000c207051030241001401013031034440740c40d0720950749410510707890b040c0002440070740540d040003402c10000040010864803201e040d00e90080e0301a01d10010000c19a076400301e140c003d0400a420740c2d241c4000034803003c80500445040b0b81d04151454540580803040c00f11121004121139502c0c452000c0110009840590103001041c503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 451674955 1250 451673705 451673749
    0xc09090c0613031218030f050a15020d050901061a0a1809050f090a1e08120f18060402010e0108040602090a03200f090a0207140a0501090b01081506061305 68
    0xa625000c60104d1200d01120100046045a0400d0301102d031609025a608218200d020f00302c986840c615082048400038086d4164a0091400756400e40262008400b0031070140308603511000c4c024220f0b04140b04000006c0e10045003203039074603c0000180000d1100c4d250a0a00143d281020607920940fa80060981c81d500c80400903085400b14200381c0186c08240940141500c0387c4685010f00400c2d185a004026030503240802c108051048603560300307030484a000c043c41c26201c00f071850501203070818084460350380140312940000c50a244550b605855084085002c0f03001100e2440d0020700c110380c120360802007200669034841c001c100640c46028000301e078490314810750101366500b0b8100c034050b40165800d10f01c1a0b035641038595102c0d94490006843c0d803007504000c201034448070303158010340c0150719034102408019001480400d01601440f402c41e40d8035901145c8d149850000d9103080c1036440c0100b481464000000d0002a501c01c49400724203071200001000d18294040c40260540c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 451676205 1250 451674955 451674959
    0x901110a0506011a030411010f030b040504061d070b040b070204110c0a150b01120e011b051201060806061902030c01020f040906060302030403050d0f09210e04020406020c09090c0613 80
    0xe003102a084800c0ca80092810740c24a6030360b030500350409401c05818010041d0803112780e00d1083d03218400c880001003040c800381c02d050500d01e0080a04140b44040201018600c0090150000c3e80100b01e4030703001a0a482c251501d121701500350400c0340100c0e84961039410b4004540365440103001c0151106000c0c250709206464884500780c1c0c0e5009600c48241030a100c4280d03607801c010701028070550f40c14041100440e04140c5401441d03d48101f01c403480b18501012a50b5600c24040c0c11458800305201c40d071642c81d07260079105d00300c0c212551035200404010080492102080e1880c00322003900440b82800444c0721140c0c03d90b00254000b416512020804029810917801740000404480c00c045117113050548009103640f06400084418a8681006007410001903110401464002031310000840483c0720145a1709107484810001802d841d40c03090192606108440440d4801d070000c0512038005401c2c00940c203002800b443c80c0340038030002c403007880e200d02c00203040302c43e003025411081c01c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 451677455 1250 451676205 451676219
    0x50a14150705090a050418031d100801090b0108100302300109150e030403140a0b0c0d051b0318070b030a020909090601120209060d0f050c0a0e100303050901110a050601 74
    0x13840b03039100911480c180315a0100c20040100c1e5065000d0705072608076031f82034844912001c44ea1040721181d40024001092405803680718203020b041ea451464140008100e180c01158107042c10341e01b60707a01c802000700c00c2006152402d8440c060050480c0710072103500c5070400c03074216011418040141d99441d05000b0003040890390141440c817844210030403101001c40b51655982c00b55001c020702445160310302103982141000000000c070703403002081350b448c64204400071054014502480805080001140c01e05442e040c0111480b121207203580d0542c0d9496419010041e0001c003101c180c2e02400700e000c00c442a29600541c440d1030400c10141e82d8405840501041d58401030942c622500510010700039020000098032210b5011100040301d91529000200b42800702c00008218040004400080140214440002d032400f299000b0751140c0d80c140c282040c8d1812560042da0071038241080c80003a004402414220006161000c0c030703800507180c40713032800c028104155484e03400240100301ca1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 451678705 1250 451677455 451677469
    0x26010609081e0c010e0307120302030403060b031b0f13110a08090718020a140706050114060705031606091515090b1e130f0b0f030a050a1415070509 65
    0x10811100d8005101034102030380c0c4404081c5040c60400c0070081e080417059030f00304100d001404840807680da9020780f502d0040c0d80c0c1d60040c4002c0796814200900800d0a1401103040340c600b00450410310200221a4200f0488404410620307910042c4a55038644450716071092811030340c24401e40036a6410625406804003600810314a0968880102400300640560032003907028440301d005070302e814a02e10280c4044a00140303440d0540400300340d910500c41d1a030000741c1211803160100180f202c5010511500d44120345000c0c00c0341e84200700081c0951a124151040c8034040c0400003001000765079082d82c86500344000b201c0d200d40301c0c0c01c5030242d03030038144011006144400d07003000a040300001088449036401034101590040601007142034507200145010080341e004100b00d0b007000501120010504400b4490040d03220b900c200780c45043c00a211a0440d40000c0101104002a903501001c2d0100307600c0c0e00d02d07900918a482c50482d000d421464000d40d165110f6039260306041d8140542 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 451679955 1250 451678705 451678723
    0x9240a0c27031e05120304030201021e03180c030d08040221060403030c0305060901031b0b03010b04031b0b0f070309030611041508070f0e0312040e07080f0f01062601060908 76
    0x1e0000f4115400b0029500040405c00705810860b407a0302c1b50b949090a0703009000e86108824070404034943d820320304940c100158031459015580c0481d8800c80d5808036035901c500d807003554041d403160b6043c0113950b000342d40780e0b54070038801840c19510300810241c2c413090b2548005032885661060092004142c0c06000e082152107403450700f08424680840000d58080c01840040c28881c8039888040d24a01e080c900d03a8090481c1000030365503941e40306040c02e02070b0f00c60310042d1840301c600d441101001c0c0c20503002904990090075800e0030407101c40b50091343d560186070102d0a0000207000000040d009011300d05a9200c040006510345161000a0180843c604440410059603108001116401c0b11000b490b131165072500c0104925000003082c44c040c03070300c00e00368981103001c80c00150b10854140e1080c4507041c00da440b1501a00d507040050748001d421f42c2d80c002d6200042c3c0c010701141d4801d2a40c0241400a210121480c0d603501030855003082003a045500028078005007070108080401040031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 451681205 1250 451679955 451679993
    0x70803040608010e10090c02010228090e0c040618080718060509071709190807030e0102070803091c06020706051005031f05130506070809240a0c2703 66
    0x50f40d2030030b81e552402920046c0030303004505680e400c41c2c5000905c02d45c1569200341c1d541142112040043d00360701c0300c840e4011081c0c3c0028900700c101003801e00029049601400e81c840440d820242001c0c030540742c44082d400c85452914150314000303101541084000e00500109501a078520301011344c07503054450035004a401000310b82c050110381c540c40207401d14001400c20794800207845401200b810100c1e10444d10003034002c2c0307402540034480c0d95401404858402c0e1514903031004054016a210300c1b09110b1000660814800d10039542407005c0480d14102460442101117200d6942d183e080342c000400c2921001d54820400000c2c1039480d80d0000505005c0b8020014444002000050304a50381000c0101c45d072510003164044030800102c0d0f480d5640714099903003a14108070000d05404c1c0490349a6418490306000c1d02003c000c0c856036000c444811201c16400751354030a0204043c00f0030207246420071140c0110101c81e50360b2040c000c40c3e00c000c40703914071088030301e1802e09249501408130114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 451682455 1250 451681205 451681229
    0x8041104140f07090603020307210b040c021f05060102071a0f0f0703030608160902090301090f0812010b0313060525020109020102120c06060d060e0304060f0f080c090409050c0307080304060801 85
    0x2789558014480340c2940003030401d507105c080c01002c5148041c0a02c234200d00e4102c0d040a5072400501d40203c8c0e104e248800041c104462034003040c0001068035030075545580960040c1d0401d2240e05404c41103980c0000303070340c0c071168034000300c01d1b07030003102c40e4010000a1451200403a0480805515015403001408500010040b2000d910481c50721030302c05215542c14550300248107038440c0c8083d000050016080344443c040b060781c40c00c11f0103099101a1800d8158201c0320000702d030f003003008400d0307900900d1044003048144e5540d5450b000101030150010250b480c401500c3c080c0d0070340961409420815590001c9107a0b240e034400a494081929204540c45005100c00207800c0320000b2925804071040f200c0403420341150400d4401485500c25015040c003000070042181500519482a90101581c440001c5042038108840c120020344010000c1802080180b040d8a09a000b1329003581c0260700391070072405208002032415109078020321031908040340410040e900400c8081c010000e580b420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 451683705 1250 451682455 451682461
    0x41202060f13030c1d09070b0c01060302060a05040305060130140607090f06030b031c0903080c21070b0f1b0301030b10120b130c05060304030e0f0a050108041104140f070906030203 79
    0x55070700c607c1d2034000d04541303480c01f04882c42d0840d801d4110030000c50f00a402e0302c2c1e907500c203041c004202d07034024001540e1500c50103000040601812600f038407140c01d0400009014882c010002c2041184c05005503800e1080980c2804414402e210721401030103641ca4402d000f519122050b190101036074410400d1510300110080f080d200440c4240480484d001c5110444401040a4601c1d40407900060140030006c10705200c071000c00244441c0c401020300102000f81c1d402c081507141803080c69001400030f507406000c00c10091803100c1d01508410b80d6009607001c184001c100e0800c5d40c00c240d0040e100c0a0080c000c3c0196070280c04020f001400710103100244a201c140c60341445600081c0103503658078031450b040d005118034168a6405450700500340b542d60306103401c0003081c551600030414070449a01c0442c2601c1e207414076a03074080700c40603151038149a0790f507101c0e2400580c5407110650032907110011f251125240c050075034801c0c1e0740c10b13210411031300744a50000d2100e01140c0107001414410400c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 451684955 1250 451683705 451683721
    0x402040f2c073003030212010b0405040513110f03010b10091415120709051512010b0c0d0e03031911100c0e090a0b091317041202060f13030c1d 63
    0x14403c083c0709081c0d00010500802c0c07034120001e100d014003c50b901c01e80f090000ca00500000001d100b2500101c900348a5a141c0700e88089041da4149070003000c0b400c0f0000011142e040145401080c41801030000400c2c40c94880403505200506051300b000800b1500d0600850901c6210200c0ca450140c8410303801c6110020910598031030920000100766a03400000c80d140e03c90108440901800b070003c070f601d002040b5801c50340341c001a8000350302000241c00883c00f000c2030300540781002c1c1040020000050202000d40700708d8003001405400d40800c1049200c041003140036181031204540d5075a0440f40380320007103404c03c2e1325081107034101c0b824891a4418140c2c40325018103162002c85102c000d54591030100001001505030541c2c1004a000801c0010072038080c0060b0701a002e9040640080111540e80c00c10340314900039200a1a6450041c80141c1030007005001101c443c0a801480c124451211507103041c0c040e4400c40700802c11490601554a802c1c048a02e074003441c403400c01260500102e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 451686205 1250 451684955 451685009
    0x209010f050d0b060d290609010c0302070e090d08151e120a0308150a121b08010504052b0804031101021c051006080408030402040f2c07 60
    0x1010001c00401181c00440010668031680100b140100483d5640300c4207a10100504408591001040303481c10b405900403100c07401200c48400014000e030300d081129001552445002074007601140300b03603840407503044100301c9518001c204400c01007a4028044d40014840c8400905400341068008401c0169407540c1100180031a00c43c091480801020700c082072a230446804180039038420400101e0070f05030032a800c2e601a645281e648032404a0030800c2c4070680c6110f104100a14010305403a83c08a0703044d1000c101400d0241c040e5140c0242c1d01c02030b244c01d5543c21f580995264000e41d0605051112421075840e60340d1040c00c02d0b4908a0000710058080c2030010806810300107646552182000c003035045030fa0245051300603076050a5071440c14402050121614030b5520302e044404200c0c28042c0303e5841c0b103261b10108044c80c2d55640c0c0c1c01d11000d089108000c10a4a0306c0c0e41102d101d1440e100a1a030f041c05860a00340d41e15582d40750b010385024800d6120000c400d165821040d240c5400f00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 451687455 1250 451686205 451686227
    0xb1b0c100905210a0309140109050a090c05040503030c0601090f0e100504140d091503050103051e0a020603040b0a2007081315090305210d0c2307020310020901 70
    0x11050401c3c860728202c842c45086007600c1440880c080c001000d0304240c1c10000440940d076004030884d810340b04020044d42c22440a00a0551000109500301301c00c20054010142100f01890f042e4203240e6608080b0b46180c0104101e02050b0300f00c80c2c01405003014510885800c03140143d0300b03002100240414544940b01c0c180c0b20100541c65500050900186507642d041905140d030840d01201d406407001440350700940104403400390301a50305da00c054460b01035641a00e4002029003001290103840d175880c4801e403045004513000b0494150050f17900e40000d0352045004603000ba007585002040401195103214034401500340030340f00040010341a00a0300c0c60700da401041103032b40b0721011003840003588056015400c03421414480c2d0801e55400500002280d03c58070480b40101c5002031070402d117401940300701035590030a103c0302c14040d1194201c00d440310080d0900c0c01d1004003407142283d803a100c415042e8241c110003e03640b011400c04001e5000d480043c05070860800b910680000c0c4644c80036 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 451688705 1250 451687455 451687459
    0x105071d010903150902030715090e071809060509091609110904050103060e0f010912050a0302070c0602010606180e07180f0e0601030f050f01061101060b1b0c100905 73
    0x12900c0a000d507405442d034140550b41040c01c855034043d0b4040034001070804100101c1c000e001d80d0318000340180c3c08030741b114001c1810752104800581000f4902e0343c0c1c1f0700700800c48400c018144044001d8054018000b5000c0c0c00118400300d485403c0ca07045c40a40c0c0406002014140e1280303880b83d02c2e44801d0b003c0401900d802c00390102d00b004e15001c031080356006100060b54041d1402c0000000c100c0241e001d41d01c106000c100392160050910347c00303400c0b6224000080d2078002c1403600c203144144540300802201016050050074101c1c20b40300d8602c0e00d0242e4002d04050b1303641d440140001500240c00c2d069015055411030f00c0c103030510501d06030791040138180c3c1c8140040d0a8411841d400210440790240c04402c95130485250781c0c114074020004141d03000760100789011150044100180180b07445140442c56080e45a4078040c02150000302c45055103160b075603941400300f100200d41004100762003100e08e000c02c02010391541c080c00c00c41e80c000c000744555855103090030a00d800c00600001c484017 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 451689955 1250 451688705 451688747
    0x190c0c1214040302041b08071e0509040908070c030c090905031b030c03030c0706050a02070f0215160f0606080325030203070c0308071704052b0c0e01090c02010507 72
    0x2111000c4152030160340c100940c490304010701801b2007907900d441140c107462035541e460f803e9221b862041c0d80c0c1c4001290080c6007041101b000310181c0340110003c008c0410061320004103501c00d91220507094015000864241205d6081041404000120b0b600030340001e8608001100032076550b95540e100b200280800c0201022036541c070030001344143c8015030400d00c1501d07680d1500407144030700c03503100e00c408807005844d210200b207410b2440c6c402d54003010390001c07110840640359001c01100101c0a001401c0c102e00412031503058881c00e900c914142740c403804000c40401542e10302941600e00c56004007041e68010b000644030a020600400c0280c8084280d00b0044103040c03d049081d031280c8040074000514409000040081c007400030070502e400741c030780b200e0b04030032680c02c15040d44600e2142c1907000ca04a020f00d80201c41110390500c3c40f401c070010003100700301555907507842680190b2051203541c5040d8010854102d1030f000d80703202055944000c010514100b000940500240e00114400c100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 451691205 1250 451689955 451689977
    0x4080318190f23060115020d0c060b19060908151003030c08270310050103080906090402040906091401090e031204230d02010609020f180105070b190c0c12 68
    0x990b00d0039206a46103401c0203407001140003032020365035804c20f10031910740c0000b4a030b0f0510799a00c08180540f18603160b43c0d031070107032180c00d8070b070100175101d11075441d5400b170140e0108001d18070807905d0f14401480705854190b001490403900505109101c2c590f82640c2c0010002c00c2480718400c40e131308043c0c90340f600b0a15114400790401c0d5038107011381110440c4603c00d095040c03800006000180740d14041c02c600b01e5410a00404546081c3d0b4002c2c07000411001062203022041d02d0144045d000016010b4801410956104a00d03800d40c6c1d90f580c00030a203d681c510328001513120044401c1c2c01b502e8038900900c0282d48d01a03205940c1e00c60300c203403030300c110300210003090030070981d482030100c40c0c20040b40c0c521a505034515000e48408031384051102641c40c11000107002441030003592140c40c500c0b0209402d08010348074ac9200e1500713008800d030400404110440c00105034880f001d0050008084603208210029809411910364401c2001804407010301c8000248140c01e0100ea2080c43d0300c0d103180410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 451692455 1250 451691205 451691213
    0x815040512030a09140d090603020a05120f01030615030f02010e0f0d0c2c06060901030b03030403030c0606050603130f0c261c050d05070504090504080318190f 70
    0x411046201d00c810000100b44501c01c00b03290807040d2014020f040c1102940001034000741c1c1c0d5441140584045403041c00b080120724005c3c0e000d4005140c003414800d20304681840c80c00c00382071040b5007030880c400816005006002c014446d06e0342c114440d5041c1c10303089086481e40c2d074840341002d6000f030410015400f100419119a00c60745000d15028000c5640500b1600c0c2408041a141c00764038080740c020b941084c1c0c4852891501003020010032411007007510388105019403030344009141410303d52506080303046a2402c20082c00114000c1c0c1e503924407050b441c40c000040c0c61141d840f40348580760038000c0c07002040000d801c1029199114600c1421312031707030345001c0c840c00c00c2c207038003021049401c03445482c98080309002d8554000d41c2841030b20901d00c05008181c043c1003000012200040013805000c0001c16213501040c1c00c008141016400c09544040303a6040d50021141298540c2c4040300740400c44500402070401c40034020054641810b0403003544055024100c8050a900720361002e01040c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 451693705 1250 451692455 451692463
    0x625090e041707051c0e3007180e010623120601083a0c05030903060712150b0d0f0219080709061b080a0210060314010f050108150405 59
    0x20b10010701d202d4565485007045a100e01c9840c000c84100c10368207180e0b10b10288280e86109154400510b000303039a6460050020010320015000f03410586002c20780703544000204083e00c000d0040303040411494003000314403400e0325030f200b01018043c0c0c14804207010a011614088103201800c01c0521420b00740039001500018420b005203005000301d000105406002180540c44045099030400340701c1031112030851580300c0520b0302d80b100008032201c1c088503842800d240550600800c1201d040c0540e58001a06107003041d942d41002c00c2e0004c12810f0190898003461400d80c1c2e028041c108a00e04e040018540b910412503421a070540d41c1d208509003600d40c5d4192042146c2e1200462a034007141500541128001da80c4031012610140d80055482d1041801d03070086100954010300114441c3e613000000d8001100203019070042c59840381e031780d800610034040214001c0c4540241504100741d44c0e400c5512001c1c401481500b00401407101480c0003076011215004400d00c00741944c2c0c3d6003405424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 451694955 1250 451693705 451693733
    0xb0c0c0a0c090c140304020a0b07051e0601030b0a020a080403210929090309010f030905100501152303040f0804080d080a1a0d02031606020625090e04 66
    0x620110080462540201da00c00075003d0050748401c100c41482014a00c00b40c0011a0000d5120f00014014080104003001900308103202d13104803403240b1465824102c00303c0c40391100d100a076100b04010401d10459010141e000024491f00310720704a401c2c170008064800003003024060265000807994624900841009925403096040096103010f1074008a000401404000445080e00302a0320b070400501880303014082000c025882c00380b910005480c4025200307282c1081c903540740301d90070200710f0038401d044c40c841c20600c0c0081c1c07a604180c4289010600319500b0010403554640c03401d40c804c101c20b028554510741c4c28004c3d07266a19407410480000c1c0d4a400148880e0011600088008000420144c82c07021a26505055074030740e20340d0400c03107400d200d4134105103403c0100044141082c2c03070300000072130000d800d40d80e80c1c0d0301d80c01c04190810034543c04880103034000000c00200710b81c0c0d9000b584903090216601640c005480390001d010581500a06041d0341d1060080343c1081140024944 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 451696205 1250 451694955 451694963
    0x120304080f0109020f01170103031202071406041a0907030f170f070606060203090d20030303160e06070c1716030807151e0209120102070b06030709090b0c0c0a 70
    0x81e2811070464814064038400e002240100c00d0700b0016400b03076002d264250301c040306094041d2826880c685049451205600314004c103280d0800040b03003c111410b844910611400c1c00038802401c1c50b14203034042d9640100b01d0101c4003000010301a0701000400c143c0100c030741044000f00b040101c3d08040309500c0400d49882011140001d07042c18485034034019240003402a07804006955855800f039880e881480451039100c070088002030005186807100a40c0b40710207003c550b43c01c0301e40102013480c0d030b40181d03042c003030280200507030750740700395000190800d0240300342d401078280308442c0c0e10f07a000c5500c0c9015a032102130140505a04403541000071040e460002915203100d0350303036410030900f00d40c000c20701500c1d51001c0f00c00b058000e021500440307903000318805108000b681c0d0412108020f400140c44280d00c0241c0d08041d0380303808400d0015100440c01802000d0090504004040c5800e41a40c01070002508240c049004a010456000e40c800070445809070f4461202d6142d81c285500088020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 451697455 1250 451696205 451696213
    0x120c080604030c15020c19240f060503070b0a051b0a0821040f02010806060405041118090903162909012301120305070b0420091512030408 61
    0x4410b050740800e2000381503005040d02100d008a1040c0e0500b640f040c684031400c0b0364080700b071449030309115041c0151114040d12420141200b11581d02001e02108258044455220000b91584849920549004100403401014060700d0305c21004420300600352200244500410312074000c03500c480c1d142d1905900c2c41d00780c0d4103d011524215440340c01a00b1040c01d10400640d10f440c1c40030780001050300450300101c0c071f0b801d2504154011540c0032401049a03030070000038407000405445a00903041c05142c1c001900d51503000603c0e015004c000c007020440d10514440061080c9024044100d4040e0740c242403129000e115641030102c0132100d007580f245080d4003101342030114800c04001c214040c99003900280f04000c0e0303801c031321a80000c44104c40c200182e40705004001c582c84600303115018902c6030401038142403c41e11201c070908002ca0b801c0e04e1202c40308101120b1060810301030035600d8000c9030001250f003805d101a5074424207603407009000e81c20162190b68200300401c1914001c0a00104403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 451698705 1250 451697455 451697461
    0x40c140304020d170c010b041e111b01140906040224070b092104051e04110f0703020c0103061d04060b041d0709021e070c0302040c26010e01120c0806 66
    0x386055910050303c07201d49505e0702040d032507245487d00441c6000408148442510b440103027558001f081c5a00d076040b01e000c0100201409040b03041c2e45061f1800b10940000ba5018100b40b29503003141004081d140306800c541d041100503684d448441040c0b0b0940d981816440780c1d00500030810f8415244064030204280f0200801010300085481c10f01c400ea1060107543c01c40610b85000c0c500441c0522071703104800b03103102c1007038400480e1030300c0705001c0c01000424205c081d000864400d5015045184002c0c0340052000709168042000d0220100c0c20700c3c7c1088000c2c51300c0170f40c2d010340400b50b4412489002e0703407000c10144a03040d004480080700007001000250a10348a40c1c10298a000041d581c50190103000564ec0141780300b901c111645151500d100d032011240b10070516405a030007101c58401c08036000c80942c44030711400c0600e6900340c5412090380d04c4140d03941118061038520040810f401e20042c00324090f12004941110010782c1414100703103003458064580103542c0c0112100f0303c141020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 451699955 1250 451698705 451698743
    0x71d060d09060b0a03021f020c0603011212051e07051f050702010b0d0203070603270b01090605040c0c1121030a0e01020a051531060b040c140304020d 66
    0x40301d00c0d500e2140c01c04108030000d040c184210b4984512020354440400d14880000c02060058002c00001350300c140e5001340001800140150003c0e045801392000c20341c039100070004a02d4151031010b403581496414000440c1608001000a254000341e091022a900c4104001001110f0104206482024440890710404002032001b12020401982405110f030300c03d09040404000d0141c0280151907038504280080d00503000b40c640003210a50f8040140204010503500d1a840c14403600c4251055454040ca440545110350404c0340729500c4c0c802446015900008090821540b11007014510140400011011030300c0c9400d921282d25000254500d0b00008401081c40344480d8450130462035034217004a03600c000e13010004101d5400202c03810210007240192641c06032903606802e100c40190b0b84075414110003000342c0882c62003513010000400c2141c0c001c400621805580c104003100c80304100801120451001d101e0840000000c1000e40d1240740342501d0f032680182c0c0450900900c100c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 451701205 1250 451699955 451699961
    0x30f110904060f060f06090e040f020315060f1210050a060f060203040f09061a031b1204050d0311090d060608031c05010819060e0c0a180f0b0108071d060d 68
    0x9442803d007880c069000c10450024110202515065a5510010744c181a6890081d0b03902420036502540e5600b0080010380c0c2c00c00c025281d1040a100103043c5052102c00c0c0302c2c424207603a1600c1e00c0b5407045540d04d40d820740300044000050ba0419000f1907030f0b0301ca0b080400c004113510340107800a41c922403408295580c00000900441e0800380c01550b1003955001d42a084400e80d00414045000706064140c14030111000b940c2c20000c4001218540c00d04003240000c0ca9108031190500c90000004010900c0b00500c601450003940e401c0c284030107044d0807600003151252032070551160901c1c200305000d1081c183e05c40c001a0416800b1282d490403080158401c60074000024440306042500105801381c01040c490300c1c1d134201105055107140c4e607a451001a0140d0801048148903d03503a41300da0f9500c3d035000d01c0040c1740d0051604901c1c47da031a10365041d06d00d01140e03155103500b0b00509400b40c0e43e00c44132071036204144d468000240310404001c80300114a0034482603016201065907103000791968 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 451702455 1250 451701205 451701221
    0x91908073801080c0607032a0b0601030c030504050705040c020304030f050f06090a020f010806061201060f1206050a0b1308010f02090117071d040609061e05010903050601030f11090406 81
    0x801e02140caa98659500f555104005841da4208005000240010f0b000302c922400c00351003504003050380148403405201070250f10b4400d03180e50318007205200396960188241c5907441e64a1500703102d01d29050315001da41e40c0140c0b083c540590b1ba0341010403000780c400c0c02a10061a03010380e440341400020708116a54952003000c009175800b80c0c2c4e01040301c900c400140741504c1540501030031029004c0c40015a01003400502c0349400c42c10070042c8454a1040040c25406480d040d01e584070501c080b68001041c1c0100303e0014600685042c4040c485942c1300d01381d003011524040c90751651413900c6604940c030038040358407003107043d0309200c00844c0b03024a9801401004600380c2c0c03200c02c0185480d82180401d4029519200403d01c50b803030304c0708801005010704244600c00750000c02e2660f0344081c890b00300c2d405507100118540289080c40103126000d83e0004c001c081c2480c04c11451030642d140d06032034a0b41844001c2240c41e501c0400b40c2084010b0300103c2c00c4a40041860b0114600360500030058007401d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 451703705 1250 451702455 451702553
    0xd02040303031508060106080612010c110c01090806040b04050124080d05030708150111070303200c03060a0b030705090c070303050106020f030403081c060b0c010509190807 76
    0x2203c201d55440d0303848003c0d841158441c000801040e46005001c1d240704001810851304120b044c00130b42c0b0284030034003c14501c03c00d65611a42c0108120035280d040a001c10a000d0412040b00340411082c00000340b0b29400580164811981e07441d5482c1c414014192030130403548580c3c85040a4148052400ca19001ca07070400b81540d00d6100320440441c1e80d40b008680d144003140896000c101c4108015411a844c20018103003e15880c0001400502c0d0021036441240054444a500342540c40f81b80d07102c5102c03038100c50040013031b40d410781e0000745c0f0380100510006059945008405c601c2c1d9042089400610026000241e01c2c1402205016940d2144c0302c2035011070700302400040d229100080c010100403051000d52b08107425a51800c200fa800f101101c0304002183c000d0b034441001d40d100b14401001c0f07010119135251b1282401c58203403500106001e406810815550075a2411840c080902582c824080744d601d11251800402041980280d84039540d0804540403045550b00c81c2e004080340c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 451704955 1250 451703705 451703711
    0xc04120f0c0e0f1f0305061918050d08070e09010306230709120303020c01050f1906050f06211501170103110402070c080f07060327020f03010e030d0204030303 70
    0x182c0212410302201a5181c030103403640c040000350224500002100460204107040720b455a80780c4810703140c803809a0348607940e1103078078a801078111024070800301070090124000d01990026141d5030b4860840110040030f001082d000210340c94441c0701400e6440c1c1c1c1c02090302c0d0040d612424101c000340040c245580c0110104443d80c101c2842c0c8842080c0325400b00c1e66034040f01810b10883d801c0d44841e20703404800b03040d000c0c441c25481e0602800307007521405900600c615540703460350034008011104011503902c80d10f809801d106a895215041c42d4a039416214195035152003000074455940007041200c1b440301ea5001c2c00004101d03ca150511400300366240c40005010440807510000d00703102c01442c3c1c400050303903100700c0d09007078000d0400c50f400360b00c0300381c5100e83e0344005d103040040c506800c40e40317600911401d0182035010703c90b001c000d14503000520b110380c1c070061b10001d440c0c20428010b031144401c004071101075502500856202d40005013a251100254161603000e5042400210040381c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 451706205 1250 451704955 451704959
    0xc0605070e030a03031d060103060b0f22090309090e0c090603030a09140303160807021807020c01030f061a0702210607231204030f030c050a05030c04120f0c 69
    0x1c80364400d2661048010040c00c84400311399025401081d00010700510303030b46501d5026103181018020346008501030040440c0085280082119040503003c1884c8104603c0c1c00080c1035034604150008401d03071806000a03540d680342000d0302e040405520059050f401c0000c101c44890020411202860701921010801c0c6c650340c040640f85d0080c02c2c400c10000c0c078004400c100c2c2c059541c5810f0b8882502409580c500803042d580d0844c8841d10f11003d640d098400035201c0304500b002d802800040d29580c0d05800c450030802c1000b51184174000410781099201c035103403070302d0580703035401540100586918640e03005c40d425840c003942c0d040054181e2083c0b80c09038810b8001c00004214000350041c040280000b969100000e42e00c5007407205003104681d9030810300700f11007880100140350600044052030300318601850001d114610601c141c4c1c0c109418a0502191f00740c01c03000343d400c420b0302e034140103840b5a6440a0b44845003d07640c400104c900760020a001070100c200303995030f007a0340103042c100805c0e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 451707455 1250 451706205 451706207
    0x50720030d1a010c1e0606060206011703091c0c2304140f04080c0703121d010f02071a1903060e0c0f040b07060209090f0711160e060a080a030c060507 66
    0x90607040d00d10b010900e0322030010300040120b517910b0b003420f9800074402e8103c9966295481140c250760041009640440c00503c075003140d0000400650311400002d628000000012454100220b460075540606044260081014002c8520090b008a81d0070842000240a000480c01401c1035944e0085141007400f240c00e6285d80c1c2024858440c0c010a9a40c030b40700c0340d0303a000ca940d02000ca43e4000d801840703008000154441144014a045aa18420400503004074014480c5010751210305005610103a1a5844e4000c1134079001c40e0400f0364040421519041c6000d9107109580000b00d00d480742c00d00741d03d40d880e01640481c1c1506d0a64001a14903540c01c00d08201511031010212559001804200942c818040091000384d00c00ca0000d800d0040c1d040c0410301c0014240e481858401b400d02c100006543c0c0031900e646a002528020a840680009290110502401008000c039103580006e9199261102d10400519403a0112400440e05003402007540c2002c0204640050905020500362 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 451708705 1250 451707455 451707491
    0x51501110a050d0807050706140a1d1b01020a06090b1f1211130f090203100917090f0a0806070f0c0503121906030f05120c0d03050720030d 61
    0x282d10a0040c815140070902c1030b40e8890000300b468003000410410200040c915008807004902000c80094880c10b10b02501015213a042040c81c524102d00b03084100045000110303134403604a000d01044d03080c00c101300101d04001840c0c0c0d0151031242001c0700c200c10403040031062031007400c2e070320f400706c64003420300307121007940c41852066450008611850401023415207124404040004042c6051291441742c0c4100b0341d0541d80e071000005650b84694815400c060100307520442480703030100b00e403405035510141559001321190b012001c002c10401d40640740c64006544440c0000c02007414a83d503002c0032680d800c0100da514000075401c4600000c4e0340c0c0500c410f81707600d6500c0400340d401e0855440c0d01d40d4039454020074aca10302d8940040c00c880c20701c100d031140e403004d103000321038403a0180d48a04007246001014149001700000030000280b0010340418a080d283c003403444c01080707944940c1002c0380d40807402101c2d070089444d401c0466254160020081000c458103481c00d21841d003005144001d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 451709955 1250 451708705 451708723
    0xb220b250906110709050106050a09060e2101020d02030903180a0e01050415150906020613080702120f01050c090907090612150f0e1b0408150c07050105150111 70
    0x81101e0410a111590180d401800303400b03c90b0301111162a03551075824183c410a0703102d440810800030706102992343c070250b150054113590a022401c50b8120005c0364090001003800b0800381d2007a14900100c44080d0103c501e200f07810300081d5143d00388519259142d600000842c00030745105c4c0b6201d005810410103042c1141c01c41440d50219a10345001d00010340303041c01103822000034851000c25034100da1802841e00348001d0361803242d4542002e002034600a4060309040100d03164480700d40020702642c0c01c03209810f5060341e00c2d1003d20700030781200b4541180342407a141c031942403101b000811122000608010002100c680ba041c0d110500c0c1543c00f00748500402d00000c4822102d424180e080d90003100c440e80400380250304590360340003550400076054110821505024051007041717403170b034046042001800240b00c0c0c17402d482c1540c41503644210b12040105481c0450009801090400135079080380d410000038480c5140c41181d80001c1d04100b2002ca0100e03c034000c00c120450f2000842c452 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 451711205 1250 451709955 451709957
    0xb1b010e0c100509031b040c0203090907030c170c030f0a050402030615181e06090c1603030f1820010903200d0b0a0501090212040b220b25 61
    0x95070030089424000000e036103818460602800b08180c00380380d1420010310606103210707000058103180c00d8040109030751050790710504560081c0403d01c403559400210982242082c180041c0d80c0d05070784401d440303a10108841980c110020001c0218017211b9500452140d214028100c2072a691403001c0c104441080e01e0281d05613004e1000149444001d078010302007a440200140b81c048042401c1000c0b0001c121564280d00080041d59446e80014207031a40c0c1080b402c98054003a4a4500c8220250740a4000404100036011081c0020700d4001c0d0320003d05c40c20120070501c12031604510a400304070b03050340d0848503655620400300c6229420000c040e144013050b920f0b0310000d032551b156120b400c1c451780450f03942042c0560120003a941d130301042860281c4140010031040c0340c8096144101c81050f4080c803142c44c010020190112481c42941d81c2c0650b021001c03541c0f64031060400b80c0c0c0d031042c10300f4003055070b86030616030814841e9400c916032280c90110000c0c4440e50450070f910031141c0f0402e00082c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 451712455 1250 451711205 451711213
    0x1412210a0f11060402130e070306230405030a051e032401090f171c0801080118170d0b1201090c0915051c0209040c05030c100801050d030203070803010b1b010e 70
    0xd0062804c2c00d1210400580341b04045200810206141d040c04025401194000c4d0f945900500c4035422441c00c2899103001e0640d0344403440e144d26983c0c4c4a2050300d44800030400c0004419480d00e550920b10170714121070f603080c21b03124545180d0241c10300300c000405401c46601e000402d4403642c819098841a140d16000b4156070301e140918050150b86569481540750003038110410141401c0d801d03080c54803011759107102c4294506048507003180c035200c5480d59820104c1c440a0701062070941e03084200041ca180e61a503c0081d00450801880c2c50048281e00003541700d03940800d4041500001111805440e40d02d0f241691803140e0030480d501440410308003c20780300e00300401e00d40074100a800070341c5070242d51300042040e400643c0340c7c28211401c441c0050300c00344c24001401c007003000302c141c074800740c07410f80c0689000300c0f02400105052244511a046005091007003603c00d2080d152580d0307116100715141d50f112210352140d07420041001c004c010000000c0400310105024800200d81843d01030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 451713705 1250 451712455 451712461
    0x140f011a04020c010f0207060b100912030509040b0a060f020f032802030d050c040303030e0c090103140703081c0507051e07030c050d020109050d091412210a0f1106 72
    0x100c4043d4110590b88402c0f550b980c0484005103126000a00e41075116030030000c1d010304643c08110b031003800c4051581c00c01c00e6015060024202401040040c2034143c1005c54890134002d0000d4042e0080782900303030300310102c824000380c0ca98000340c050210f0350080d001d8030041900074090342ea60f40103c101e00d110200c0a5200c00141030321280128115200c0307803064038517001d40900d190094540c20b0b0740101c00d0001c00141003052503418800c51050700c07030320b40203088100c1014001900c0c84006000c09040c0f01e0710f1111070072a40d5010000b100007568170052032078465001d4121109280c0101a40e009414201030024007442e1048084400030310095000046005c40c0c1c9035a442035800c98081142403019482e202d002107a030811103c0c501140980c0003041181c0245030403803c3c20441c191180501000c1c0f0f106122604900690744050347d020340e8030503941c0388051801c924000e080211301356000480980d545202201000500c512041900c0e9000c00103000b040449000d03c08042c00c0409030000008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 451714955 1250 451713705 451713709
    0xa110102330c090d0f020f10080a11160602040e0c091e030111270f030c0d02060f0a08070906080408040e06040609020d0b0103150509160912140f011a 66
    0x80365000700c01a10900d00f080c500c4408555000c40318031095030201d1580352007104503d041001421a14400e5a085442940110000d0080741020308001540b40d1192811a940c3d951501038654400c03001a400e08000c0590030319400a5000380182c0e003900c50421f000500300145042103840034034010300741d1960903c460340480b1610704580e18445d4903540b04c17a01e100c088400e80c1e0140c070082c40c00203100050319551008080ca02030001036070034003801180740c102c005a5008121081e01d111705803804201d550950ac0020620710415011503880d4a01150400c400c903070004441d0300c180c1e130944034800c005494101c04d1b681004200c1d002482c05030200300500641d9400800d59401c484050000318206841d501400280d0300210840324425684076107017100b56916000740084c030050344020b000c09904003408a82030180040908000303110f40c1c1c2080840300d108603914401490201ca000d84443e2491600142c103d480d10105074140c42000030100103028103120b480e0106c040f905100c0701d0010700100b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 451716205 1250 451714955 451715053
    0x60903120c0a0804090501081603110613120c0806011202031902010c02030d0e0a06090b030601030b0a0e07030b100516110d062f0304080403061d0a110102 68
    0x200c0744120780945040c1000142d0f0110142001d00000d07040492035605080255140c5411884000310b0084102c404101040010148540420702030b43d215594841820034030300c5d0010b540c3e21400807441c0041c0b214050001c0746500308283c541c010f05031501e40c0d9903041160401c081d0b12001030341c0f54011040da010201e403084900d2601c2481810040c000c00f0494000904000d418200600070981a0005082510300320700901c01600c11820000311080c1081e105040d41d010040c0f0700e6040c1540e443c024213455a0708a110001041070300c040c0541841c068200501509000324444d000c1c43d00244080101402103080d0b40c0b40d462044a2518114100c4e2207000800c100c0700c4035190088110705c001c40125146006026418088a183d1a81c8a0040d00c0b4040b51000340e91030081740d80c6040c02800002a640412502101c0d0080d42c00b18484080401e4442000c00700461741c0190b124503044c0c142003020000601001c00801d80a850744540340e08100e64480329101c8400c9844c0c48003080c4d001e40f04540c20 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 451717455 1250 451716205 451716217
    0x5012322030209070c0302011113140102010902060f04140405090a23030703020c12031309090206090402032d15190f0b0c06090d0f0e0f03010606030902090606090312 73
    0x1101404210755030b0b80128003070002c19695400064800c00ca01020306809000e40d21414100748455460900f040482003064101405018000c50000701c034055035a100f5000440d0440c0c00901c0c5560300c44000100148980c800d1040065220402c1e000400c285001d202d401d02c130f019408050444440d0317503a20f002c0300000c4a010704098080c0d08800100d0210304002130000180b20760014020443c8520811060301d07680121015207a00800c00c001c200154060104101c23400031304003146101c0507200041e02c80c040d01a155401603c0032003000440d4801f6400c04080354125950f5041401025800690b003041c2201c00407201d01c0c400a0300402424034101246003d031044044101c10340e110410340b07103111010350003084903140104050200704014019950000301000080c90200e4060b24013900d0040303612941030034056009110115600c4401c1c2402442e04020000c01c284ca40b1100c02500600d07480000f0f87c00b0303d1815000940509291045507054035004000300450b03a03040250a540d40c0c440 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 451718705 1250 451717455 451717507
    0x3050f0615070f08160c05030d0504060c05150c0d230705071b090b01080702030405090c070f0b090607110111040909150c03051603050402090705030702010b09010807050123 76
    0x9115183c000c1504140030707144c0c01d05000d00312000d110707003810a80c03203802d42034008901c26004580c201c130400da0000704441c11200f0506110501010746d06085017000e1005482c060b1840c5803000b0031600349100002008490b0b21030500708082a142c40b030a040160001e84c82125541d03010000c502c1080c002d0000c1c081c0c0c14800d8145020640c101007000e40000c00c6170b88480344080c0c4890100c1250340c0c0000b851a03200c0b00034401541028941400206140740123030004251810026500082c0703d642081020005d0304004841040d080030442641d59a000f1560f1200241800ea901d80190301d0600a08800c0c1c0000460302c0e04244c2401140390080007503600c2128175102800d038040c1100c5e0f0314060924a9002d944000855280014414142096490741801007618080800006954141c1c01540000b000d1810945070390328100264010201c400b03115a0020901000081c51500014000113a86c0300307a072214142c10220305a1800021003503e5241514020b1200c0c005001c10210308241190031 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 451719955 1250 451718705 451718723
    0x9060c0f040315091a0f01140609040509062505040b0c071203050403030816170402191e170a06020a0203040909060b0a2c04020f030d050a03050f061507 67
    0x180756201240e50102c61a8041800e07120040241800301080604810041701151000d40349408401c50070041c105025030002c401c140e5a146509407283e40c161070a4180140080240782030101c040c5070f452208461008242040c9580c4104400c1a01d032104c0d10031000d41c41c1ca60400b814004200c5440d00501e104251070320a0003000500b5070b040586460b07542c1e000b5180e079030b580ca0960600800c0c1c0742000303080550802d00140f205043c00e600a01c0441d103000c000e0803010707154031584001411080210b00417104004e5109021880403004100740c105200c640703180100750b907641c05900310200c014400b04521600070b00a2139001c6410754004014145007441540d141c1510360306072808452602d20240c070b565555030070448180c20005119000f40900b074510040e09056801003016605101c5102480d4002c160086802c6442c0c5041c003517501c54000301510703844181100020318581014440a00203400c00011940d6500c0e210541c5001d550040c019803804402d51b030402c0030f140d1059104449401d6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 451721205 1250 451719955 451719959
    0x3120c0a0605130c060519020d051c060b0309100b1f080a09060507030506010e040e0d030902041d0a230601060507030e030105011710020f070b100b121b0309060c0f04 73
    0xb03130b440d040806004181c44054580c0d610480b140350002d4284048401d550000ba290304120f0303004010340c3e084000e103000381200c6208030b81e088005864030354450003403040048240111043c011039480c01c0091460420421810306508201001025a500040f94603098040328070b01c40c410a20700350702421442d408100c07402c0c1139481c18200d500481d174007030000b40d44000740b21083d0780c001c01d54288a4401c8500307200780c86c261080316032109041400e05060640d01e0600e1030440d00c85030010744000950400d130034003800035049840e845030703c0d6030801c594206104103400d0810104c00d400400319003c4000070450350303080400a030b8040e4042c480981c280702c804001504265000d020317442c00381006614400040e00440074481c0340080c14103803216420f006020410480c0102000d0300c1c6003a030003102032421a102c4081c684600001c0740c01501c485900080c50b002194440e20f9194022202ca00142000c0c0708100c03902062408252142109500a5408074000e60325000281031b8002621070040c3c81c0039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 451722455 1250 451721205 451721213
    0x19020306090412020f0307050d140310270212060a080a030801090c030e0609070801110f030a0b0406030c0b032a0702010c020f03070e040b010602060903121e0a020903120c0a060513 79
    0x604106001c07602c60b4050270004178400e600205d804107002e060480c0504608040d200001118032500403089030011403100110303580350200c5411501103100004550318600ca100315131005200310342140c00340394070000c0010070a40c00140c140880b6010794030001540d081c1130075000a001c1e000948010143c642e00d600307002031818400c041c0510303c1c2c1401400001c0c6003130180c82c01e403020840345009248042c0030b002c14071814031046070b91201a060300007d8015042d000100184416000540042c10503003001c129020036000440c00348541982a4181041803012403a4403d004110302d000f51200b80300d200015409503861145880c40100005c3e106484440401c0c5451410380c88419400107110a01c418403603101003090140c841d80c80540091301c0c0030310780c03650b0780c0c0708540b09410300400300b000103695098400255041c0041e84c102c1d69140e4100740c44008040d40110078024468003e00710b00c1403000403c8006c0707401e80d07100140600400d49030341d10740384004c04005041c0d07130350b0b10510b1032000b00007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 451723705 1250 451722455 451722457
    0x30813030c0b03090d08070207051c1209080c300106090e0a02010e0414061207080106060905030c010305040b06040b0619030207170406052a0a060519020306090412020f03 75
    0x9030a200b000ea5881e46410f81909141142d0401c00b1414400c0b4101484481d91340403e500017510707000d803900b00c0b040c030844a4103441900c550320090083e250041c280034002da4005055411100000116288000f00c00300300701003510314955105d241d0b41c00b8100001592801c0140d0240315000c8000003515030707030b00d85100040d01c86022518019402c00c2c18400110340e00020003110511059600b00000144031061040036032015086500c01d040302c0d4000307c90024204440800b4003034050007480404d581d090040c0001c895805014424015501c2c50b00565100c0c4c420188aa504280c806446407200b906000c000c0c2000321045400003010400264045103411107081e1030700c0d055500680c2d951483c1005080c580800350098503c030001c2008018848e442000c1c4c403040000c40f200210000007078114001c1700060141081c40380d01415281405000c45640610704c00c40c904141038080c00e02e0f003000d07941244021110541d004a00348040f0b004a080120030303240f1036083e0300441c0d1421034441b404600d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 451724955 1250 451723705 451723709
    0x5040e0a052d0303160e06070606060509010306090b15090117040f0b0121110a0312030608161a0c010b1914060306030d0e061b031e04050a030813030c 66
    0x2d0a203203a0b0444007400c480702c98651445020141d400d50a1201038485802d403240c030042d003000b604004841c0d81d0b540e0401111040e1b94401010404d069a405018005400807070245010900d40080001c1510050190748443c1030020500700700104da4810000f0a6007007845101d04000d100c0c2c41c500c85142c8070112407070080707004501d40e803028a428034042240e100141c001a142c00c510b001c1002881c0d00c812a90482160b100d00f4984828030081c0101d0f40380e074000e6002920b40107a64070004807035509948100165840c400940300031502c0721000150700c42d168424140c0345000c034100c40c4d01c48070110700030b012400c1c0324000118a041702040010b11402c0c000d030204d25803100c0075100f000306110f61107a00501309800c3c0e03680317404e620300600040c0c0ca0356450f00740f03a4103011080b10300342642d0b078900c411035803440000380c15001168003002010b6500d400007042150b40184041c2c2207450705006e4016202100c100801164032581540e581d660f5a4100e103a180d94071012402000c800a1410f6201c100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 451726205 1250 451724955 451724983
    0x30d080406020d0c02030409061706071b020402040e0402030d0f0207090f1401150e0102070b0d05070c0204020a09080c060702030d18080a06091a0f0109200429030705030105040e0a05 80
    0x241f21824080400304485450784154640400c0c0c007000e0303821030400f051a940c040414206007000d480b0103606040b50a0002100962203480010b01240341009065541d00490003942200ea510079410b206464048203407030b240c000359100000401035040d50342c001c42000c800700311001c5100d690b03112004c65008000c0c3c00070400c0001034520300d06201e90009030f49212034402d200501e03095150840c103c1c910721951030107a842c42e40f2a40041c2d40c45016002c1d40c41019400b8008540d83d1003400300040119215008450641c09000c07000501807a007001035a01c850b400a02906190008000507500c0f940c048004210010010100040303c00090090007803403801180080380301200d030300d070014100c42051004844c405c071880622160740c030514403603030659020344000584030b82c0d05082e403201d0032000d15800f242c911000401240c1100a003240d80070740340707283c0a42c03000450080c5000e500c0307000403a0a0400510144010000c0740381a8025154035401c100c1030326070001c2103072651801c001c07950641d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 451727455 1250 451726205 451726207
    0x3140403020a15110702101b14010c110303060405040c1805071e0c030e130204090e060105030d08040b1017010605130b010e040207020105090913020301110306030d080406020d0c0203 80
    0x814010350b09a0f148105140c82c40800029100e00640d407600e019072600030707000c0e0080300c20f03004c040c90058a803207070843c04400c80400c030f422036854503040030b90131090401a19420102c5030703402d6a0042c5101c3c105682c915000d1400c541d60003040c4070007040d0051040d9110440548001180301e100d04603d0410014045c0118581c9440702c0003424064171482443d00904c07807520f942072420303440340300408200d5051034184083d031281360010b24186003500c42c0d80951031001800082c00002540006ca50480d440d00b640c082c1d0b130f6610101038a8210074401c0c1d2001c00e928500040001e0851203c01d94000c014140d500106601c81325802402c010041c11064a60743d1148180041d14244202c0b801c20340d07480c04203008100e0210b0000b0400040741d440180115004526002160300440aa03501a0700c00390000e00c2e075150802411341803040710385050f80603510300703200c5103500008001100e21801000d0000c003840c0310007110460b11a01c000b441525032176030034860304041c03201c0390203540c01e1004164021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 451728705 1250 451727455 451727473
    0x3161506050603010b0d050112020f0907032c010506010503040c0e0402150703020a0c14030d0822120e011d0105031e071107080a210201020d0c03020a110d08160314040302 75
    0x1b0100c034810780040d0340510780c01111200580d23071054031816151064400703c0541e100c00d07505a0190101d11140f028085a88620f1042e048468010000c400070b500b009114544510740103540b144030903900a400e44500e46401c2c402c02101c0c01d08640c0061000d4500805142c40004608082d00154070860058000321038060074005e1b46d2904d0f4014220603584200302403d40b00c0001d603109110b01103081484141310000c0c44048000c050940c1320841d00c14900400e240c2403a22426620f800b100310b601189440d06d200c41154070036416841100080034107125202c100f900152000d0b08000c00542400450002c1034084451301c041282c010200c40c0c03680030b241c001500e03c45050108681018150354400031003080418081610201e000680c04000880280050707012400f9108410000240c0d1f8244640c0c12281d0398140e009084409860380d503001091705100425445520340d6060300001040318021079010b501180400741c00e147e180c00e0001c0c0820f0b040401140c0d4400444065000d07030024009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 451729955 1250 451728705 451728727
    0x90203040204150e1501020705030d08070906050403080a0e130f0e070506030411041e02030702101b0f141201080a020f0904030c120302040e100f060203161506050603010b 75
    0x24007541d880c200303040c0c3d201e00c80c107180040701e1112000300443c00c40704a0190100b010b90003880380a0103400007a0a44c1d610b112070703000c007505a0100350b8014000400e038500004030940720320300f41d6007501e92050b010b03803906a205200703c031401c140814a0741c0c044012000c81802c2901340c4100c49860300060000304036000514801c1e0304000842e40001d0144100b0420003002a1002400a01e1028103c500241020307034007455400c0d40103468039000c0c00c01c0c8000180301381c690b00001c1c06900b002880c0028002e100e80074103c525404901c49000000c0385040c200c1c000d1032409100d031100140b42602c440c2d0708003107240c40c00303581c0000203a200e0303040c070340040912005604081d01c012030b1000d001e8403148403500b8555401030481200c0341000d03220f0301c0b2556941d2100d40c1704c0d404030b60042c8007191400f0124200707240030400c2208140f2a091501e614104009069400481600c035109621b060240708410652154000800141c0b0032002c0d0951302c60000c5469640c0c07401540c040c10300072500075111240b10700c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 451731205 1250 451729955 451729961
    0x130503161206050702030903031803061012201305040614010e07030b0f0d03020133050d0813080703300513030b0c0c101401120309090204090203040204 67
    0x4010208060038050244030703201c880400702558000000030300c1c0d58030750354102d0460050f2000785915020004204400291100c500d6611035800c5056038042e031101c19818950b41c1c2540303e90641d8003a094a0341c0081184141c4901400c041403042050500710000000c090400361081c00000070b035540c0600c403e12009106143c03011700441c901100b59410001c40221402000340445c003015152140480d8545909202c601d05030000b03801e5102d061018034000c1e0180c0b203c0348444445480244490050a10b82684c800102d0944030f400500b59003007209201001812a6099698076400c0001030429940703c6c0404004059410243c42020305628000d281603500d984400b907111086403a4226403c00d4841a0109400d2424002e503035003010a849169030300c00d5400507010280b0366041000300b481c1c000041640c042c004054400c1042d4081e80030f0b0071070300320940c0041c071510300d0710050241030000c449101000e406400c000303802c25a50000d0506a91098000300503203a004020f2200314140741c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 451732455 1250 451731205 451731223
    0x50313080c0d11010203040503090d030215182b1805031509061509070804020d051c0e06120720030a020a1a0708280f020a0807080c04091d03130503 65
    0xf0084d840c2d410140c540031380d640100380a031071003051405800e0040500800c603090350303041030000d8018a85001c265035850400840c1030f4844d64000c5034003000720302d01c80146800401c1203d410303a40e520036145400300e808680e10032002000388004100400c19030740400c00d00c0b0f031013000041c600080d4a0010700d1182405400742400401c2a80500481c0a943c3c80b050398542c4864585846e90351a51240001209010b200f400a001401441c0c07845800c54140e04500910388460340b50484104040743c14451203102d20040162a03043c0c82001c5001030b8032400711a407154409244c01d2106590305030b1000e042d5440303141000701591124030400c0400a080030700c1c20710310941500d070083c2403401040103041407000504201401201c243d02c17051881407280c2100c18024104010404280c00b03000f180020750101101d07a02084001000411040c40b4207002885941148034240c00c041c5007040c071030003130501c0c42d20301751070980707041d08100840c0010800742c580201d540d10725110452500e000c2c1800d01503c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 451733705 1250 451732455 451732487
    0xf0706020601030308010312050702060a03060e070905091503160801061d040302151803040305010b0a05040b0117040602070f1112010203090d1206090213140307050d0201050313080c0d 81
    0x407000400100b0741000c80607044076088001102501442081224140b00e81d580c020350114010900a500740c0c1c1c103510403020b071a03101000c0c401d9500c41400540d051501449101c4d80b210783c2200050b00d4020811040d640c20704c000c0d044a19900400020100360400b68211102d540e640740020804568005007041d00314090044030031403402c050710000e454001880031100c10125040100e004a140d09102104215500055a4569480746800c90190418288140c401c800010b40400c1915142c4903400850505843d0400c441140501c0c81d2107001c8002d2040e10015424003201000c00e546203006a00c55109045220707055259104000340c02721026048100f0703a02c140204006d21000142c0c6218001c0c05042603030404514000320000350003141c21094000d070001c01c0490244056040326801c0d9108400a103030100c0302c00e4181582c3d60413034440c4c2c6d588200c00c01411000f5501071001580c12080c01001c81c007520a00d41c40c1e00306c441e4801101102d50358090b51300039041541c81800c0607164491 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 451734955 1250 451733705 451733713
    0xf1112100605090a0e04022e0315121709030307080309010e070303090b0d0f020a030504020109230603130f030e040c11210d0e100c030903080a0b030703060e0f070602 73
    0x4407001302d1820f840c1402800b940407001000b060955841100c00c0c0c56840200b00d0b100c07280c00641081c0c820038507100e81340101080c1840d05500503011060100d0080d14100c95181a414020340c41d08400701a500c05031a41d540b0003008080c415807814030003444164000e00380d1642c1c0b828041c00d9617007111008000100035802400d001d000280c0e02c0000c440480301c1c0d442000b0f4654000b51800d030001d00840400302e1005100007043c42815030145c101c0c62140307000340c8070722030b11660710204085c440e902c02000e075000180c0c030f0f1103602c81c910f40100550340041d200d58507855a00c1496940c0b05d80300900e8642500860000c2e1480c0340b040ca403030301418248421074038100c1484081094415175400d0365401c1e400350304640003850410084000b050f515003680703c180510600801e829182e888881e0403483c0400c580c1002c1d417202000c0d00034018220200d5155441300100e56543d140030f401800004541035150180070000004a645e9015500c1008014005000031a1440c0103081c0740203201e41c015015504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 451736205 1250 451734955 451734967
    0x50a0902070f02060906130f0501082401050d09050d02151b1207030b1809011a102109140106090c170702011103090a0c0b0c0703060f1112100605 64
    0xa03403100030351035855040c2c0f40142c4650040001a1b140e01034000c140d0020310190744002802910b603d4076408135002a00c46c82401c0d12040d44070f021110f00403404210114a804504185512441c000c21100c80341d0380c00001c01c1100341e641c3d50300700303440024060b005078405941d400710640039401141d0001c04401c82d42e001d550200a0f04483e90040e0511041c22403000c00008100038040d41040c4c0c58043c000b0002818500b00781d000f800003c00a4680205a41c43e0004a1443d4550303200011446480188410fa258003910300841d00400da00240c111011078600801d09580703614041ea111042c801e10380131030701c0d40f500341d2074600312540d03980300d40d00b124100f00c0c04081032608080340306003814410014030003903600c600e42680546002c0300642d91500c400000c011948502061164030144541c0c504454140d0300c0c4500f1115000c1d0103c0102d00307422a1100f080001e410764414040440d03c000007052424100c3d2240f14076030880321012642003425400c2100c0020a9085c41c0060490b41c00e025007401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 451737455 1250 451736205 451736213
    0x6030c0307090b0616050a140114060d0302011b02010f1b090512030f03010b0904150305030a050a210b010801080a0807060522030e0406060816140c0d0504050a090207 73
    0x100c1c2500c1510035560f60b41000584540302c24044420050f05c1e03400600503480c107841d000b81d40c2c0b0b0584000340ca075080442043c5020980601950060f47d80d403904594264036464200158078004481c2142590b69809902c500700c15415070040c82c6600c250000100f81032842071000c10b5408507588102d402c1614004ad600158000002006440003510003a040301640c0070b95a107103104801d60906c50303480c0440001018035142d0f0081039000c10580c0e080c465141004a00e60601c4401d02004113560018890701d651144120040c3c0071000c0285004200b804180c40900e02182c0d0750b01d000010b5a44415501d525540c01c00c02860040c00c2d4180200300581c80d40d212450103000c2c1d568000c0a050319480400d00b0020201034640f015208146540d07074484032445c0151070b001010046030f0046040c1320000070490300400002e407242101480c40c1d04224181601198603140448006442e65010711024910903410050030701c1004054a0702c0b43c2ea5400c207802c00820803250707030100c030b007860041005000103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 451738705 1250 451737455 451737463
    0x15011b0b150303131a04030803040b0403030e0a02010f05180d150507021c0507060b13090615180b04060f0b0a08010f03051b032814010225020a090c0503090606030c03 73
    0x12017110f03608894050800d0551080c1d407149070320103801900044240818081d4200806001c0c51081d00c08120005501070556202d140c1d5260190101d0b04041084000600403802012070501141c1121801da405d280001e4002c1c000c044203036203030300c60410742141e208404d22480d0b4104645000a003244030042908240e00c400d6038000d1010000c000c0340c3e40d0100b0100c1d4000c5210110020600624451030754000700c0181050711065410300d003000e084003801d41100100300151404801502c140c6640a80400041c0c2094200d144d002a62040300290651910707000b07001400021010030340d82c19102000070006641030704586094a4040c50400c00204006541c58071490180d040501000d6030f1700010303081c52034010050b600c05c181001c801883d544160021603030300d4810f004c00c1c80c4400601d8413440c00c03401061012400c0d04015135901c0c1c032854110f04024800d51005120600c160f442e080c8140903502c5807034036040410408018020140c005001032a4040b13030580c010085203075030000182d0f036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 451739955 1250 451738705 451738709
    0x305061503070f17030409060b0c16050114030c0708030103120f02010501060c02042c07030614040c050d06020c0d0c0b1e011a04050406080304060906030e0615011b0b15030313 77
    0x2611102141d0201104c9090090310000d10420004002655a0313030101d0080d0791001341d0000150041000d01107100c03200058039000d8a1041e955002407000c2c1c060707003a0032a440a481149101001c3c00088005031039000110b004e1407061161100c946800940680032588211001095905202c014010340da4000c00d503000b660340403a40456038002101d22a241220a4200040040f42640c80698804000203060044030b100e0306007009086140ca03200c5017140010341c7c00030200743c6035000c208510302d07040400400480c0100001850078040106a625280308400144003207206c10302e40006100c0003a102d40d51112043c129452030b415042802c00081505006445140c03401064540038070030024140c0300901030240c000c1213210307101d000013a074039000340c820700d07001640c441c1d00443c020b48240140f5030b058007418000c0120303032281c122078541c01c160800928104901d809140144091860020007500d00491008400b418042031300000e194010007818001e038010001020817072110001038003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 451741205 1250 451739955 451739969
    0x103020f0d020d0b04241515020f03160b090105090a150b0901090504120f020327190906081605100c05060106021b0d0510150b040305061503070f 64
    0x40310907061000401904500380c010b4002100362007084204130760a41c00d1681c204a014150140086002c001000d885094500030500307884450208040190801c4004c011513090060ba070944040c0b51000e03165400020407172071000800d030041000c2c845075040301c68000f0180d80c002d00c841c1c6032030960960303207088100000740810303c0140300e411903543c5070380034601d01c0c1001850b00d6030380e5a450b00c4503000303400306890070748922582c860b0740b5403d14040c0740818000b130603580185040481050052000f01d0100c0300742d101c250b104440d040c1c2d45d0342e15080c003510013031004445180c3c3d89003401c0707068084038141d800040c940d600035800d0400d0b28100903222030440718102c50780c4502041220080300d8400c5d0380c00004020380f04031000450480e0f0041522850620303840000500600071108024070130760702c20006401904040020069601e26810031114100d030a451012441d50f643c1d0b415031b41da8842d40c8291400d4110300b09100780c08804151142400c8003c41c020000d00f070814200003246c0c440381c42002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 451742455 1250 451741205 451741219
    0x5040e0613080c0f06040c0e10031205130306020c0609010501050a0e10053307031e031b020102070501050a09080910030f0f270b1f0302030609240103020f 68
    0x1000c2120b41e1003211000084102619998694205215950b510550341280c500030588004120046c8041031244207104010301001c9051442c0c464444405e103860801c020003400304514500d580300c60941d0b03402988100c4c00180d4940c018440329051080c05000ea01c12a41000c00400a5540342d00c803002c1603450004124005441c0c101c0b808600d002c00f50301c00350f0854a0ba121320114844212506084002c102401c0b80c1c0400c0d01c0a00b258051042010040109401d0504035403200407850351456102624100082d0781d01421621580f5411032403602d0006039000500740c0c003001800c0c0203081d00004a99400d00c41c1c0300303081c0e072249031500070703000b03458003641070300c804020f045201e13410580b2003a0000108201c0c0c4440640c3d0200541000c0c03c1c0c1c0c4010b8059030075044103030f0080e032007592030040d0800340120302174444e828003021090300ba8942101c3c1481c40400800135030341c180a5980114804001001c0c202448124207009a00c0f604840e011120302000400250b1034140500c101a04110342030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 451743705 1250 451742455 451742491
    0x31d060f1308060109092108180a0b0c030108010b0a050f0409030203040e04080414030c0d24020c0d0306170c130e0a0309140d02030a1b0e07050d0605040e06 69
    0x6150902807a408000b82d48900303000000d05a107142e020020343c9000350503850340d00041071200a84e5850380c0c809440050302d00c0c0006400035840703210004110340d84006440001080b522000307081c1c1070a85101d0000180000100300d540000d100e0082c000006558041900745404001803d48010000240c01a1346901e0100c0802d882402120007403d4602c06000a034205410010402c4c0c116008030000040c4000c918091450000380c0001411002012580000034030340d0344041100d4140144075540d030480001e00056911800034050942403400103040e00b140e0004020705480182e884200035121001c440308580d680491010340e071280c03d803016140e003450194100000c11440c0b0540c0c0c480d0080040040826031310070300709d0040f6042080440703aa80a0038003001180c00300d2100082d4180d202120b650002041c00d030703413003100c2412002c0d418042603503850450550700d03003203a80c3d4002660008000103952440c0c840c08024200a613410080200300a0640c0e90b601001740482d0051421403020b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 451744955 1250 451743705 451743727
    0x12050702071203020c0f040603020609040f06151206170307080307020a0c0608070206010501110a14030c060708091903090509190218120d09150207030b13031d060f 72
    0x100d10092144800b01042820907050003074496480d0b40455210754068000e004151600d070085609907a00180004c1c54802c5540802006040c281c03d00c481003a2190400155900b50350f1010108a000e0380b182148403d0b9401c00e04201c42054018a81c04040b103510007658042c00070941d0344c242e50000591350740b40c8821005902c1c11000000c000d00c0c1524030040442c05951084070130340103084c15006c0710040d0362101c0064130070b94520309011000e54040383c403035408583d91250030100d0401050907a880d00b85440c3c3d00307500700322044680c000890000c0c000d12912040401940d0921440c001d28440340140359a801018401c01c3d110300c6205424600110309c0da00001c070030030703035030056407030700440d91010340540850080342030f004914411001c040000030509004950005084030755981c281c0558100380700c520151480b2440740003140310308440407000445d44c41150f40904940d911083c59900b2618000344094100004032121150510030b8130740c26205c00082e6111072222610403500ca00c801c0d14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 451746205 1250 451744955 451744963
    0x807021e03060103060207150e0d050f070209090106060206010603020a0f11191b051507230601090603110d0b0c1c110409151d04082704061512050702 66
    0x10005601d401030400010400149078014044103100e40454841403046091207021544420309000c0e507901f15007400030f4018880d90040c4401e0400c01c0304030b410b11246801060610004840c000441d81d0360b03000510869804004103401070070140b03020f510704003075040b0060007810590301d01400c0c0096052203c019580c2071100320036100c0d0b1541ca0004020b0107040442c210311580c0f48000d00d0382c40411000c1442d04005e14884030390404100c0c480e242c00031980c2c9500b08a002c4030001940c80022082540003110288074842c020300c107242e004991107065040c0343d103030840743c90301003446000a001d20100161000e0240d41e841200c002c031700c0392911400050303901c100e074604030464501032504007401c3d25440408040d10544100050401c800c10610003400c010701072600510401149034001c5c55107580f001301016501607c2051002d0030f09a01860000b441b00840181509800580c10b141500341020b102d108001e04801450344205040c1080161040c000300c1c7c2030401040d11603000501c0c10703000300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 451747455 1250 451746205 451746259
    0x3030902090a0506010f090b0316030207080408070527060d0813030c1a0705060a0203190f0f14100b09030a0c0602030d23340509030c0904080702 64
    0x160054620745048629640100004c945241c0400d4031191070066075071040010205440c2d4111819245032100081020140e903041c200ea810141c00b0014000062400c60180000380064401004007909102c20410b00360180c101443c03100d0890481014285250344000303400000548260710340071410f0908003824484c6400c01d44a101c89848008100800e0319040c0c0f0482d910070840114440124140342c201d4070034254040c00300d80c041d50209008040c1580207503005000481c0e1120310102040c8950107481c5241c01c42e03c1419922010300548400f50f010703d000c83c0c158101c0c400c07003904c0c040c40c1c584132380b111b01e001da1080b00070040b44c109040d480130003a000c0d24542004281b04c1c0725581d04802940d80d0300003000c081480741040c01000c48898100000805c0240e1209d4021650b0384001c800f030050032800c0c1c4e10000b0300041c100c074015500b0080078404610400c0742e80d890395551800092520f03142c00c1105041c0602e03444420400811003503c143c690b01c590403941114000380c0c40a002c858907640d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 451748705 1250 451747455 451747459
    0x40c0506042c090303180705040c0905010807020a08040b18060c0604051b031203090321092e0213080d0206160806090103022106040507060207150509090403030902 72
    0x1602041d04458810028415450302440512410440e6640c81200b101901d04200eaa801407012035006444016944d05140d407000443d840719644400140c03d44100265400200b034606909001a5070711000c0390364001c1580c0020b004903562030355490520300c0380d842030024410b4042a690742c1844951141c02c1d008000074005519402c085140a807202400d41c0e040b81c0c0b500c0344202e0004900c40c81001da06007500001d0140445000b400c83c0c00c04540d0000b0f11400540c001004040c036608510320b41e6070704914804038014a9444c250700303582d250181417904c1da80c404041100302a114036041c518406a07c2d900c01c030140e1035421816200501d05025040600c2d58050303030a49166036680002d880703100d40078801d020007160440000075900d40d1425980650003840c40c1c0300500160070300718660320661400e940c82c80505410402e285041602c1580d0894480c0c01072482044074030b50400c0300c0c5004e000c0e4050b00d81c030030181c0b005015005201e034402d1140500e550a0000d018107000e070303200030b81c182c0d00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 451749955 1250 451748705 451748707
    0x51c0b0102120c070504051b04092316090b1201090930081602060a0b0307050312210603030a0c03030b10120509190206070f020607080307090e1b03040c0506 69
    0x42080d01c0301007a0217840e0099207001c0004120500b601c0300d2014151500360032500d0503007070001e42c070301800c96400c000650345c652800c43c817490070300030107042d01c10000700c8450000d144000304000c10114a60340500d45c02030381407010003045031043ca20b507811a0141c050008001011380b0b04045005070184041da280690703c0e03030445400c41002551541980e49541e460050b6588a100d0300d8041c0d8250752020069004000145142ca0300c3d034420304407000020110707940e5582da040042e18080840c64119115070380480c08001010111420401180c0381700c0d012503507441d00390007190f900d0180903580340c01c0019500010003130501a5011210b803002c0501a10f04407010b80e40c0107010880800d001c104200c0c5048006090b000e00441e04408404441c03e0b20304d60881140c0802410f80c01000058500081040b2500d005a4492004010003403140e195640c5a28010310040e00700203a6070b00201101c1c15500400640100000c0032000c0c0c0c903900341d80161030740c8031401c080d0589030040e08801d030080c0d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 451751205 1250 451749955 451749967
    0xf010e07021506180708090d02070b090d0309030204020f0a1202070201020604080307050c100501080d030504031b0503040906030516171f0b030a050705040605010309110402070212010f0c030606051c0b010212 91
    0x146c0b00d0f103c3c034403940701c20007180e000c6601c6000490360303018103104200d00c01c041407140e540702d890080c4502100b00c4c001e14100c10800e0320ba4001030101d0f03001c001c4003445403d0014213100d8050300311640358200c45050f0360860034201c294002030b440700c100800040080000000092105005030140c5003844010421a40104821003044004010a0040138442c0c414406004c0340c0c14844d002d81842585e0568841c00510400c518031f401c02613004804072000e002c24000841c4070003072840303180001d40c00350703005000f0103801310062a000e171800d41059144445c001c0e0301c450411400291040900009402d030300000c0ca565603114000c0203065105a40743c0646c0a441e01440701c00610602616400c840c01c110030396503040190304070f072004100109000705170b1140076480d10f802e178054081e150018100a1a80c00306029050840e4004141003d4060f9207100d1020419403510a0f60044d1800c0d04001d403401b080b500302c500e80315030580000e020320390300c52100c0c5015034400d01810031400510500d886c1c89007 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 451752455 1250 451751205 451751207
    0x31c020d0801080a0c050f06041205060a0605061306140702030f07060807052d0712031b050f0702102a1101091a03070306050d06050f010e070215061807 67
    0x14421020000141c510030010441900202e10342c120143c0c02031803005010720345001c1c04013400c40009282e90102080c03000207528040c41140c42180c0c0c0c45440a4215440d004214500b12001a0031142c01050305000201401c00324000712826540c4c1030510040f00c04100c3c100a41501c20303404025018003c05000e940c0038080043c06806580954031501c11a6450f41c20846a0b0b02501d600605200f9086100c1e83c410b079118402204c1e8142580d80d01454003109884a0080b03026a00c1c1d0314002036a541000000f80e859404203c0520701e5500c0c15500d0714110221311005409a2070010b8840d00604d04004070a502071200201c0000554807281291441e0000030405400baa4070180c0b402c56130100303142601e600c00c02c06581070302c8141562400709c2c5580c811106483d00700806150605580d18004559a40c494040c005100e11900700402c0c02e00e0802e0303001d090404182c6c41120318181d03031002d02001c2500407660200c0e00980100c00805552081c0005259032030740c060f5840b0382160801400065 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 451753705 1250 451752455 451752463
    0xe1510050d0f0c031b080618040203070e07020703031202030c0304200a06030c08090d08010e04060e330f0a0c051e090a0605090a0b030c09041103100e15040902031c02 73
    0x5d00c1c482d080c0a03900c1c1250000644200504558940e03010310114540c2043c207c061031115003050026044404168840b84142641607040d541c09000d603021b84810800c140d4801c103550207030003d605007582141460303016817426020180004141c102045800d03042003d94002c4480c145100511150416584410140080030860054000070386420002028601d0000341c92221029641d2000881c0e81791541400c25260017910440b0070980b10f0985100d034160404c070003e21405400b980c449602c1410303040041201018042c03400300300030070042100c4603505181c002e074030080701342000c9280f02d000082140c091190f411003484e078240d010b841d22a252910000381030705200071f847e80d5034215103810054070940282ca1701503612080000061200014090285800500100d9581d0400d0035000009040c1c5406042035944603002200300108801e4104804008100f020341401c85424114690320035412400b81c182d010740c2d150203044046480c10016401c0701c40e062000241d02c4d0300301c1e000081d11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 451754955 1250 451753705 451753721
    0x3142209024308040312090e010603050f1f0f0e0a06051c0206180306040f150b03070909030c0803010b030105011409060d0e03090301020c0105010e1510050d0f0c03 72
    0x211040c1c808144494480748421004045a800b00005214411602524021480368085960040034000000010350102c2884000d2030b454070b41e44403050030241012101001640701808050401c800d00810080003414141c00009050142558004001d50030821103040e030b0280344181007e00001a0640750741070b00b18041e003070f1040203000c00760383c07201003008601891214820003665607a0781d000618180c030062170a484046920031409141c00c000a08098044805945600c05040103804004001e11108100e403840354007002011507900100c1d54916490140c0940d103070352030032181c060501030010004903684c4184529602d41c2c5031810b0143e607400070720485d40031913840000c1041004100040d140420300140c241d508213000c981a080c050012600c60030f20a0008201e080401c3e02d00b0f00092140541c90f2001107240d51508450b0b190912009201e900f0034203600d804024a9990801d91120300000ea16025484044c43c2c130110008003841f42c1742c0c0d20020b19004013040103640503004200 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 451756205 1250 451754955 451754977
    0x9180504020f0a050109090e010f0c080f10060507170904090305040602060105010f12021b101a03070806010303121814060a0b0f060c0307060204120b01060c0314220902 74
    0x20000d0315000503c115000d50780a600e001c284546014070080740646d20540600d03003c50004101c0680843c01c2108944060304903c000071003c80401c4509411040041d801043c400300c01c003425850800001d02c0b038041c14100070102881101a1040399148000fa038889090040040100c44120314018000d0740c054850400907000c1e842c000175582d07000b03c003000d41f60b072000e4803034400204030701c40510025880960421000300310381c43c2c5500c1524040290303c07640060401c00049a80d01e46001c1140001c1070381186110358404c0314207100c2681c02140035070440340d143c14003000d0280d458400901400400c101d05041e158400d84100c00d12400710503001006002d0419642c0c1c94480250100c10b507070303401e40706941104800038004a80d0800b480107081070245d0005481c108002540c4181c181e900c00d9000213000c0d9940d4522405011031064000d006202c6410b003440503501940d03003d8400d00f005000c802c00b030344000c42c1c09a100c0c521040c2410383c20000c5d2040c9a00d0f40d8546e40da6070000c1d000508884 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 451757455 1250 451756205 451756219
    0x301050108010e0603030307030b030a053301050f010c14060c130501020a02030703030809070b03090a030201140906070c0309031a0114010201110702130204030c0f050112020403210918050402 84
    0x7080c1ca8480e003c01d0003000050042c5255a640f03032800d0b006030800c0d4000540611500040f9008a0340c18000ca2041c0c0a8407a6080e5001d5000d4401601c2d1070035184180f250541910010800c40e99103007840d0307140e06d80c2802c148160070140e0600b602c0c00c0000310940ca05501983c01080422280e04004107001600355102d0f41d0000e483c0c100499899004110081d050b038400b2000307001107402107030865403007090f92040f1100c0702d40b03801188103560815664040540e01c241e0b94101015020f00900c41310f0281890a450303a403a06801c3c4566840005c1c02c030034244900d64030020103042c420150b42700516003169040b0040c0200c0300f0082d6516a00f4481c0b44504211025400d900750301c18080c0c400c6881c119499641000b08a408005000240c08240c03942d01c1c0d03080000200103185490606e00406054a000c0340e4149000005000b41c0200508103000d02d00c108018400241d03800a4210321121070081450101c0c0d4400341511180e845400006100040400e8000e00d068140c0141c0c3c411403003a01c8403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 451758705 1250 451757455 451757459
    0x6050415090506070819061d062d03010204090905300a05090f030d080403030c0c0c03060b01111b0f0414010b03070201140705180907081302010e15030105010801 71
    0x400d04a91032040e000300359030801000b00700c0091195200c107401c84107401d5084a5416192620000ca44071f03540b10b1004803000c031507021507101d00c0700450340e40400c05440c590300b100007050f0307007105d0240c0c2802d000c3c045103505c04c0b01000e00d03182581a00c01800f020001002107084c08e04200d5590458000401200b03c80218002c1748141008020611100d41103109418802645000c0d078454000c00c6100d038000d512102158084e56081241c02d400c0c200c141c82d903a440703003018207004042c0c85080640805002c0f602284500261648103d681180d801c42d000080000742e44c001201c0f0100ea28400030810320618089010840c2010551402a8011680e180c0c1e41c062080c144410f4440c1c01402902c2c0500a0004110b032041c03034002164045014800014040991580340c41e10104c2954031000140e00810700944444e030400798190480b1040350000014509580018042400107003030b8109280d50001041c11640681c02e81002c0010051617a0f142041200c00405550024426280003036101000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 451759955 1250 451758705 451758743
    0x20706060608011e050102030d0f14040c1a03040312020306011209080903101506030506150a020c1512070311070b09030d0c09080606060702150a090503010c0509032512060504 77
    0x149804071750044e0081c500348a02165034000629044007114400d58580c84c410900454a6400603c00c6d03209031059038842d411b00509400c0100f1601483c0a003240802c24000825009224a000000c00a0b800342c2d49a071903000481b0800038a10511244c0360410f1070b9a010031419501628401750290105d078003007208441c0c541c045d260003180460500400480500010b403194104581c807180c084d10a00980a130900030204a03131000708840010b0300116400c0216142004003406c030407403160155400c059000c030068002003c0500500f05150f0742e48404a0590b00c902c042d42c00440d00020422510328004103034580320b910828403000007601d0403080d510328a01501c50281607880131802468540e075a6070900000f0b920410090b81e0000725000300d058a1072215008090011160340e0b142400752130f20062609427003803c4405400d0110a11500a003603c00007040401070314000503003884208607801d5030240820b160800108050752034002401d015181d00a035001d14402c41c6180081855101c1d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 451761205 1250 451759955 451760009
    0x30906030e010c050706230a020306040b010c2a08070602100b011103030f19020a020d0806121908090402070f2a17160f18020310031502070606060801 66
    0x3000d90100b00c00b80800d20108060390b003c0c41c102071f000e443c2c080503803040304950045003a00b10303201d40c106600001009880d04090003540b803841020f003000c0106030395940d01e902a1628080e1034081c5540360760341548103603520036814001080c40405940e10a03807540c000a44564444030501c180a0070414011640d52064602a40340280840a0f60950b00c407640c010744d01e510081d0180407480240b00c2e000010a1142c07004100c490b03001e0700180320b051001600038091340301c0207100754400c070044c0c4030305c05000c41c0100c0c00f24511005d0410540e03030840e051810f020740d80981c1891642080c404100070003013011801400443e1400360368450401021041030125100041d41400300c601810101004407c1c90203000752400b01c0000141c031021500082401c102d030304035a114540562520104001e07611580f906140c03032602040043d440d601d00041c000c89010051321000b03001055903401156080065415070340c45586c480410301103e503403500f00a0410a082c022904130b081c50f0007118503080d00c185c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 451762455 1250 451761205 451761221
    0x1080a020105220b0d02030906090c0102030405012001020403030302120a09030507021e03010504060605100309020a0b07021801060e04060e0601141b011d0d021f0f020c0307030906030e01 82
    0x1945452902e020425007848014035802d000f426071030f5440001c40c00d05640c0028103003200010320b0042c3c1703d103880c2503d80d282078805014604142c210021560050740c1c04421903042e42c40078209400708081c11210030001d030302c0440c1100d07800e500c042408010035505800405500340054075464458135804860400c503100000010042002084500014184140c003668207201c0b040191603421000c20100e425904100d40c216411641e40d1800e20440c40c107640c1d403d104184ca4502000f80e1002c80d40865108402406462a21240815900115a100440c142c8603e8440e201002e16507036400000d0a14a503030140b491203107040000100b40c0c401c9608082c1d2040505a44a00401960a502110544c044180808140580c10700c00000e907409018528210b0240004514011041044e26040551702c0c100c5a003107400030581c00a40d06c080414015482408503400144105080c483e1402449450301802c814003003c1450f00c207041c0c0090800c011074403030742c50501a0418140c0000d088074101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 451763705 1250 451762455 451762457
    0x1090302070e1311011116050301060f0f30030e0f011d010e150f0706060503060c0414061902100e030a23090405010e04110a0302090f13150f0501080a0201 68
    0x300403080109016105960013514103045c820b030180352030b00301039042c03038506d1503480d0315600c0b5400d003006281000d205000090403c034115400f45410070183d5100d8407418420b2805402100c49103000c22151030310f110041c0406000c0c08a0255072500c4c2c00741c6043d82000c4040d10400310300c0b1940191754011106c400e89130303c090702a1552107100d0340c0150782000302a60000d405c02444060140002e1a041c028040d8415000081341c88090074074060003614015000903000350442c0c0144988082c0c01000d0364181d4168292a001c42104040801d900e4003031410a801e181c420300071802000d980104825590380e540880074440c030f0801200c0743d950b910403d040d5a000401441c14100003c110319603841c1814440c0540b5464265410001010f84800780c00442c0b0248010050008020076511000700d00c5d041075501c00c280702d1079600000c3c0c0c4a4402881c0c00000c009100016140c0010714098a080d03683c000368141d44002d025615000911000107242140e52500d0004508a03400144c141c4100d581 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 451764955 1250 451763705 451763731
    0x1106040803061009080304181d0307030804060b0301020f19021b131b030608070603050708150d0b07110d020c0303040314030d05091c05092b1401090302070e 69
    0x10b50401c0c04035808004480804109641c07038082001207040c40100001c04d042c01c600104440006a094100c801c504a15804410f05102ca04042e08001c41610801074150404001507a03550a005016240f0101010f9165200090b00d034079181d020000b42001c0c0e508911a601241c01c0c100c001da9454143c0b042040340c80c0e2609c003000b400c42ca04603c10743c7c904c188040340440c1036100c1c0400d81507182401d225050109498000502281c1000c04c030401c01001103140511003030a1456001d00f241030064000e1481c030899424010507500d848a1014000b0303441042c3c0e0946140c1200d0040075a40c000c40c40c10f07018000d0703800e072152891000071000c0000600502551070b0910355540e10920882419540809000a00c04d107841100e0798400c103846540c003440a8012020b001ca0013030356485e608580d6906106040c0590051500e074140007400007601e401015880307680700c608026440d209020f00a2100035501400d60b12100190070a0b460284281c08507a46241c8a4034241c0d102001140e0048011075 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 451766205 1250 451764955 451764961
    0x50d080f04022209061d060907060509040b280e0603010e03030a05180a1104060f140103090611040f0e0709120b04020a12060905060106030b010512040213021303031106040803 77
    0x35040d903e921140d114072400089001c9160355200c29150f0b000d00349442da0902034002c0d0304c41402400903c0d84034800c0005010098200607000e0807a002c0e41242900a55655144001c80d459510711146204000307400700390140710260f14950800f41038040e01010703a40d0301d0b007c80c0345e40c203050240c0c40c00c2c6070030f010107035003180d560008203c01090004c000104401551241603243c010510007000c2041c041c080a9072064509801d02054501550100d0111074442c801080b6400c45d441c0c4a48280c2c0007480c2c046140030560500c08007a052011002030703164000240003e00028110903081103e01e428103184071907803088070a840840051203480c0200d20703c003440b500003a020000f1a07030301c144000e2486501e580c440e900d40000403106c041c1200e1303040d52411044180308040240e54014007507803405101c0d04241e40002007541c0642e0140300384c844580800b03c1c045680301c40c0e04000d880002c84003151202d20424402c60401c40138031041d40400e5140c2000414028081000c52007280c2204441d40f45403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 451767455 1250 451766205 451766239
    0x1e03200f0d0e0c06070803060a051801060e01080708010e0a060320011803020a050d0510090b090c0a05150c03191701080a0c12110d0b0612070305061803040f03050d080f0402 76
    0x640300400083d8002c00d511004543c6a176024021081080bd2941d0361500303605100000e4121011124001d05100d001d2040100d11a0300c10704450658034a8034001e0903a46490000340c3c09880b80340c01c01410b0ba126042c481880c855200740e0821f0545c426603c03482400229018010130071076130300010750000b24510b810320550408840e9409600d2041040782c440145064240045410703010003100c46903912020712102c20300c10400c80c040d981c8110366240e0910701d4a8001046441d41d05100380d4800b0002c603001484002c24000c0d101042d10145d07410700c91119565008150248111040215150780800418420310024203144c440e0b90290519458504012030404d1041d1101c8046849170420704c41501c09441d49035191940901c543c40700c040b24100344040015112110200030001e034480b96003000410000500309030069019600c2c0301c01c1e6401a40240d003907100341d800480c500444440c1c000101f00c000504c0c01d550500d40ea40707240c100c0c2c40320050115511020740303020350300c001d4042d0789003044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 451768705 1250 451767455 451767457
    0x50606090c040f080706030e0616031509060305100c05040b0304020105070606051e040501060509061b0a0b07090e0601050c1b03100e031206011e03200f0d0e0c060708 73
    0x2501000040c10aa9141e071500921102608100030302e8205e002d0030840c140d00340c0602c00c0e02403d4100680042e00e483d09902d1540355200403044c04045d04e0305d80e120043d03808000600d001d404091010702c40c3c02d840c0d041c035a40d2244184201c4952900d8070058a00da00d1144c0d05442c250380025221901e142c40c0c5400440b840d4020320400c0e0340c803650762180000c5550b01c248102401c104030000e00300c01842c641d4100421124140d0040c814004d00f041980429901d0404540e100e000307444551040201c0c00d82d12900e00403108900500000e40482807000d41604026078078101c0b501c00d0404040c650b01c0c58011106030045a40348030b42640a014601d54200713440e0fa54102600014048508094400304c00c10165098012114119003000903c0d11040561032000c40d4070200c01e003003804920036025140c541c0e03811501e11300c10400d42e49130400b00d9a55880300d01d40314600c0d080c0340e1a540b01c01c01071340302003069805001d12907a05480c1c0f1900b0542d811002c03c115164403002400e0328140302c1f0b2a1118552 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 451769955 1250 451768705 451768711
    0x807050306011206080d0e030c01050a1d0405010e18070f0b030a1103180f010501030201050f0c100c0302090f0d03050301060f18150f11060402010f021e0f15010305060609 75
    0x18810210f603920000d0540d40710718001060100014170303d0407205400a0459030b444101280a504400c48503609a600a011034542005502e02400c004840000384032020070300c1c512007035110b81002c0001030042d1580360464012070b200f00e015800710200140e555500c04c0c20b0b203c2c3c60300c0140b0000c8100810800c0d4000b9680c02151008042401c20341a0034040480c1e000715002040e05031602c07521a4514020042c02e0700c00a40c182c0208030550554001038660b00038030300c4000c1c001c0300c0000e0302e82c41144240441a24040800d0b01401000e89088028029421240a9038050396026840050510f001c0005c5040340c0d4043d181d0600d142d090001c11070b001c04081c84448107010918840000ea003040500140084c515844480c1c154078142d44003c10351170715410184104400707030140b82895040481c0302500158242401e41c080440f903142030742044122005002e0840350f20b9103041e0807040105884a45d400c4584c2599101804941444084030082c000a0203a0b446400012401c0c1019082ca5130 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 451771205 1250 451769955 451769957
    0x1c02030906040f0206160c06090815040809060c15061305060f0105031b0d02130b1e0315090901060302041b08040f03110304080f12070305030a1d100e0d02070303080705030601 77
    0x2141c0b0845048402d40c171840541c0072500e81f540610f08106050340500040040d005e000d001d40040b48011140c1040c15801030030181030104001040c01d00faa0300c0904403104811380300d045e5100441c9140240031901c034200d03040d83c000c1088500202104010344101c510841c0010401a0b808510a00446840e00b00402d1160854007118001020812030800b4088ae800001c10241c3d80b06508900d81000d0346469225456000f418808400b114140044294041048515958a0380e450441082d5140c0c0c00b0460603402c4010941800100403040d0090030950380250780506c040700d40c0284c04210030b07124008010004851070040340014880c003042ca40450b00a240c502c168030300d070303105c0c00d03065a0150b40402800d40c0008259013003d034040c0b00d00ca84d61800440da441c2022500e84014190348401061511000c1e41e8003107624080c80c0c2e0442500000e0142001c442c030607001c25503460014412545641568815103404450039031001503c2001e0340d50681d2002c11303d8603550015156508058a554 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 451772455 1250 451771205 451771207
    0x6043207060f09080a15060b0403081c0c09030803040606090207060f0b030c130f02070206030708070206090a0f030f14040807060e1f0c150c2001060f06120b151c02030906040f0206 79
    0x70b100e01646009c5d101130740c090050a9a94082c092111920509070f43d900700449040c1096484a581c100d000e0500702e9400040f25030340c07943d139403514000400d447d41296400c02d101141d60005c2c81820340c091543c03039098100030018440d541c01050347d01c00390407021991058221420711480c008075000908008084000941800e907240e00040c0d598004598440019118500300700c002c0354100103054216a0240140414400a8403030b00d515000540c005001c1c0060070950801e420301c5003a52503583c0d80000103603905c035078458036800d849882d40e01c01d2034006034000c14a0740051070701940310391000c2c804014802240d5003408043d5020250483c040e501c2c5c5658101d080080c0c2094084c4030300c5411a1758a8171b04205e2202541c5880d5070404032a524268900703042404200d1212103100280e0348241014803074035801080443c080c00140c0000d942180c107a0130a071030700c0700c1900054900003401c232425803000241512400201d001c1201c040c09540d0080c4041000724106080d40c0400c2400a030043e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 451773705 1250 451772455 451772459
    0x5061b0a1d03190210031b20060703022101080c040509070b0409060e0a02070b0a0b03030c07030804060807142205030a0b040b0601050c06043207060f09080a1506 71
    0x103800c003141e800c08403c0f21846220404210b00c0e00b00c2400e02000540c3c00c0c00c01412440f441e8130101542c9454040003841000502d00e0746204102040c17103541400101113415500c1c0543e0300401039005412408004404403c040c082141c00c40800c0307050f01c00c12001410180341c0903082001804000e81601e140c3e004410f40810704a4a50b80104003810903144007188240c038001e1408060710000344405000c03841400090009000242103e81101200c1030220b003682c411400070f42140300701407070300c00d00c1d2050140010400c00d0300405401102c00c251524501c5986811090741e00410000b00c601c0a601b08001e00540c144404100242c42d01e10003152150341d58840c808a46001d2a901069844a1181041200704000c5904a985c44907003840c0603410842100300b05a0384400240005200515002100411010304420b28040c11140010002c805180700c0c9400e0701c0707043c17a00a8000040141b001002c0307440c001c000140403604004000c0c4045099602c480150030354405c030102e02c2c0ca41310140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 451774955 1250 451773705 451773709
    0x3070b150d050c010923090712020d1b020c01080117070b040305010b1315090905160f0602060708070e0f12030f04050a12051c030e060103080705061b0a1d 68
    0x15601c2014403038402000300784807600c00503000c078115901c03c21050002c9019082ca40340040b4803100070080030342c1c4003070f860b4665400c01c0d0761540c10003582c1e299481c03022403002400d0183c2e411050040b40110454128035000040c02ca0b26018510b600c0d9010819940041004a00c07894080303020519030004d84900c65100c801a1a482c0d0099209443c00da44810a0034440e290411247c42d038104d45840400410390b0403003a510f280a034a10540d66135542e60b620304024080144aa0325458038a805654400c0c3e0700c40760110404003850040d480107125400005280c54002d041d9580982c405480300140c1188100030445050b01c04d50545400c40c90555100e0b9504008001030b210320107114680c1912203040c1414003599241d181c1c803903900381c102c1007602c03c086100421030170102510390a0013444c1881e07080042d80500260300701c800161203004000014020380e80081c0900600c510140e82440d00d440340c20b003400b4014150344244c1200100700b8a40d074a405801c2c00c9080942c514400502d45200c040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 451776205 1250 451774955 451774969
    0x13110d080a05071103101d0616050a0207051809060c0c21070b0c0a020f0c130207140f07231e03010905010e03030a15060909020906120717011703070b15 67
    0x1000c0700e1000d0301c85d807480c0b1241010703e0002092007c40401000b0031328003182101540b40e500b001440c1404070002e5a49122032081c46040e026042c0581a003041081d200207204007900100d030541c10a0103010046281072410030201d035144408540103080111241e5500b96145444a80b00c0f050f1341002c00100780000e01003109588203090312031034035441d00d01c80240a03052465080f003a0080313401c02c00030342d03c0300e940303103402168400b08041d00180c0b500018035080d42c1c0c19031001e10200781440380d25200040c2810000d03808058440c0454140891007004242030424498a180c256008001c00c98100e803041400c0020030007030302e008001040301626a15600d084a0f100380102c44150000400c0001000241c01074941c0d41c001d101e04c2090107403070540001d15403910b41c0a01c0842a400040540f030b90755030101601e1a091640f4400300c00b5003011003001e800004544032140d80503c907900000307002c09440d078124486d0314031000034601d810300550762600010f400810540100300b03184066411611380c00e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 451777455 1250 451776205 451776223
    0x11120a14011a040b0906090a080109050706050309030703030902060d0e0a020f060309030d09060b09010e0402150913050603071a12010e070c0f020301090b13110d080a05071103 77
    0x800010301900e03041046200d00030140c0064041c0c5a0181100624945100868044401e80352800d501c1d01000f01c00561588120034a00d40e00544200001c00d04000662014540d540b0810403603144d03035600c40c3c0541e154042180c015415410600481010034003c0d002a0180d41c40140040c0c42d000c0c03418a03103030885400d28a60741e801d0303000380b15040440c1401d02e24818003000442c1e81c0c50652a20700140c83da288038100003202c0705038460ba081020085150013906180b40010315440c115038480d0f820701c415144c2200c0903881118104440700c0c0d040e80c058120750a45030040c005a100d0b00d50500010042c0c4405405c10750076102d044400070f446504141c1c0703c0c55028030f008625554240070030314881480c2040c1c003d42400f80c040001e1101e5281c00a041c0304405501558075503005102e0300019005299000c00a4200502c8204010060840c40030a00003d4492040200462281c2040c05800c0150440c010001c400400c0881015400740c00035106d142d101c4e078030b5094950004404682030110030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 451778705 1250 451777455 451777471
    0x112061a0703030605040e061b09031515041e110f190224151216090c020109050d030914100c110c031005070201060f0b0c060105090709091112 63
    0x100d080020954913001e80360040c1000c40f005d121503016a207900d9181c0c40090300416800068415640c00070216070150b0341c0710940281941c80c10000422402141641282c1d40d40b070034512181032a085103014031528800d8175900304071451617070490b4500002003880c00741c0518005028000072402c01040c1005054400e0860320f0f0240140d4421000b91030203805803081d29140c40000d4070310030803055051100d9400000076605660446000c07010460504100c444a40c40780a10114025a480d6111008044407030b900010441c0c4030407241c00300d00322214600001d1090700300084600d031082c07084c3c02ca40e01090141c44089d1041040c4030095140c40700000000079455154810241c3e882d400c50302d03e091000c07151014024211110002030f071a008030300c0042813083d82c0e0f44040782100d4800d5000700083c02c4504004258161150881855a003140744c40450502c104000443d4500308a1000c0c2c2c024001c0382c994038482400e2071092070140c1200b86034840706640900295401d0000154901e0255200e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 451779955 1250 451778705 451778707
    0x20c011e061d010b0702011d031014090a0309050d1a461a030d18090c0203030117030f0703080901050c0f0d05090f0a0b07030506011803020112061a 65
    0x10b450004991085424a00c001010b4814010418898818111030a0f20380c2480c04509040d0f100c60000c850300303613280095404d803040b4442c2c140d4942c1640c0c00714100100b01e00d5200c1d203d42d2201002965040044002000030300f0700081000142019040c1d011110b1080f00203981d614926008001c0b185011942004c2203440e59001c414000d907440400ea102c00780da2500d03204215020080c411144095010b8490902e581d110020070a071002c0c1c00880c0302f404006d003a2046c900e00c69500070040e10310400343c000103240000c4000f80d403030030601c6107184e031500711340141d400c0da0b00e041c280503a14010303604000300500003000580039442c007000003015035078465110f050f40350500300f0485003103900090000600080420080c80040c2c0350205860380e140c0001700120766596030020881c1802004003940100748102e42c84c0400b04071864102c0381c400c0c0b0a5035000c00540e51118011a200441c0c1584941d100380c601800b80b025500c1080071098007d4132003c04a0426a600b0500444140c02140301d901e60f98 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 451781205 1250 451779955 451779959
    0x70309060e060702100807030b09070302120a09020d02130603050d050703030e060c090f0307181d0c0d03030f0213140a080321100b0304081b060403090306020c011e06 73
    0x107085034000612410903200c840c100709099021440f451100102c407010700482d1800102c10034400d07005000347e400c010348401c0090800c03500140c081d4001c002501455011140010289801c81c4580c05076950000d103800b1200c4840e400744108a045880107141040c0c41e84004800311b007013002441c08410301950b400303075101000d050003400c40c3c000e078a6140712508440188a10141c80c0401c0c2c030f4070800300316042000b010340c1d81c00091400005500601c2000f41c0d8804690072003020707501c0310b040c0c05040220030303500000868445440d40842e400035540210034110801c0440d03c41e5000c1d03403144080000040c41c3c00d8440c01d649494a400ea4846128a40c09250152050400c03010103030003030031550000d40c10405c11034150070000e1420441c066080d00e84100149110402c1c0d14040014580010b507180d0b01d08042c107080200d6401304081038500d6100c02030b0340d0446800024000d01c215007540e1000411411036232407134041e50040f000518107640340e4924403200b03a101d500c07414085224180002e05d884c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 451782455 1250 451781205 451781207
    0x60501080601170a170901030b0406092c1c110f1608161211060d090203070f0803030f04110307060315050d0309030f0804090906090302070b130303111207030906 71
    0x180500d5001c12a40e0803402c54400080d991108500300d00b24212005511b4500c00c000490040800d12035140d4040d040c101c00060303400c1594000005190250080c5600c540f881c0066600b240704040c51621139404801459034220000041d001c92a85616084c02e203804241c001700c4c45c1c50808200c407100c5130014908402010368241000d40206080805009104060050200000718601c24140700f04801d100c0a400c22501800d018a2074200404060b200c2400802c503a00411440c00121301030311a410700826017008011541701256411070046107543d84000d04a1880c14000e88206c0b803000c03816200030805d640c14000f20028000560703001802400f9a40c2000d000768590b4865400b500400e000319010907440700c240c1007642d4100c01041303103030b44061030603d0061040758042e01c5490b18001184e0208807480d0010f00140d8001d0342240c0001761102000c00750361207100d95544000c0508102000040d0042d86c14001c1c849009050755040c089121b2441c2c000d9105400032000908010014030850b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 451783705 1250 451782455 451782479
    0x60617060708011505030901110301080304031203110a1d120f010f090b2a04120302061608061e0d03050a0f08060112020c030903071404200d0207030c060501080601 72
    0x10845141c9061694074001c0b11220444d48604581c04100002000880d00d240c250010510b141400039096920741e0754217200d41c1c0700d8105000858002e44d90408260301c180c400e0050f40b8001c640c1e60340d41c1d03213003c01078541641c1284519030581501c1103808890516551a50406440a101c000107400c0500d03e0f007603e07a0841d851001003980441c5480f10300c0c0e01242c61642c0c0264040000e007a098080d0300d9126601040d0403035441c50070900400040c000c204182011a1100030754402c2d004c0b00c1c03445c1c50f0f91044d00ca83c800c0034035804c80094410300002ea45850b01c0412245c0032440344000c50540d14a10022031b00100c50600103070040b45000440303101e403980c40650189001098a840006400c03d100001c0403040e03035501860001c0d401040304030380c1d000c081c011078222210081c11260f07020f540b07821010b8407040e0b10710010302c620703d40b41000041d018200140311404482c10195483c00c5402140341000350451041541086181c6001c0d1000956038440c85020308080703001002c140d8544509450302d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 451784955 1250 451783705 451783711
    0x10e090a050717100504021b0a050c10020c030628061403210909070905060c0a0302060c04032a05150706050c070203034e0703020403080301180906061706 68
    0x81c20b100d640130020412203012058051340c01c1280c025030796441c44100c030401480e420381956544d000b405119010014009100d4401240c10366640b5075000f03031441c00740c0e10344001701075103038040d007100c000070700a020071624500d080000c84850304002040000c0c000226406504000500440f1945c0c00741c2c6458100a100100c0f4925070304400381c201a003c01101c1802aa404140a5a01c510104507600d0281c020f90025100240041352208220001e03250796800402080e00503014020104084008280894080c2c83c0c10999900d19200c0321021100403a903210446012140301160100d1243d40f4100183d60001500c3d01e216180d21303490610f1011980040c0500981a90420075040141c4003c800c0d2412100608010040d40c2c0942c90441c031140241070030441c600e010380c824440880344005508041d50350340b024201c280d0340c440f40245d08034461800003414186040c4010000c484022043c80d4a0030024a404548c5108036641c447c262a0385030081c58060700c0c440c0002075640010000c280d4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 451786205 1250 451784955 451784987
    0x50d180803040b042102180604090b0c0318070803070f1403130e0901090c050904060b100201020d0e061e070507020607080a120b240702120a0c32010e090a0507 70
    0x200014aa03400a0400c7d8601c1d0000c180d1140400c002a440340d890740e00901c1c03181e41100c1c08081d5864012101c40003640100c410b40c078204035424048454220001e000070550b440c42c0021483c0c0021034aa8101e2880391800c1243e2151013210241c2c160368050000c1c1a4010b0400700780d00000d0b007041d05400e81c00d40010a07108088c0e260a5040b00810042d40c80c403811103000781c4620141e038a4604080c000740c01002030684e00310f13880c00e2800c1e40003035056004014440d000390701007050220546802e9220b00c01940c3c00c0c54100d03030044100c56031140f0404c070340d0303007007082c134282980703000459070104107150459030060310031090110708006903a40003100d140030a801c2d102c003000070502c2c0d41d00145000b41a071a6180c0c0340d2100c004071540004030f02044400c030a030001c0c08008001404680b80307990b0101c08804403030844c0c01d0400000d10b0240c0103286440300400c00107502d8002054103100328620b0184200504000b1030000c01511604c40380b002e01d000714480500800c0c83d24021802a00c001707034201482e6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 451787455 1250 451786205 451786259
    0x13031e03110318012105072a110f030a120504030b010506090d060507120212220f0b040f02090a0e060106020712120e060301060203090102011503050d180803040b04 72
    0x35007406001d540803d8642c100f42440c80c0d41110b20351840e800b1200c2d0165201e02c1615100500c006d0b13640144254284151a8807014013000040e06819842c104102004103242c0a5a0b5071140514101c10401034a15014080307820301c0d10b00d80c071420401d42901c103100001c500005401d000380050310f50403502528060f075089241c1400c41010561704081c900001d00302c5d6a0311804075280d24440d150007041e4912141c401d5483d40c8580c1000085030400303644040790040340f00c44144403428401c0c040740d8203580007403049002d24281e854603080b406004008807031485030000c5a00041c0d5841c0c8145004426800002407244000060240b510006800110035580020f104001c4010080c508081c0d556001450740e1000d8445a002c0e80c50840c1404040d82c440b0012001180540c0c4c0040a480b401c14264000d1007401d80d511000d40380380350b03070380009899a00910100902140034000c8203e0003075000d031072a1000c0c1ea4498034241960050303088030780d84520004007000801d003980e091600119020b40b480c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 451788705 1250 451787455 451787467
    0x9030f0301170709050c1902010608160f050301051b07050102120406020d050f090d050c010b33030112030518060409140f07051204050c0312030a1d07050613031e031103 74
    0x22a20500509035080c0740781175203105900c0824230030340101004094080842d491821284601c0c0d41c82c0c11640075a81c1c40c407811000000d81403905005035070044005441d454408903c002d1956a1903105a4003900d840d0b4003000151070402c02c680d680b6100b0b07401000010303140c07100720000c00d0559030701400d0741c0d4881d000002070180014000c220072001c50140d003002c3d07503030740c00c0c5401440c094511052455840490f5460014070a007200d08400302c0760321481c0f4030a0a8031036a03016000340d40400c0c044c010300c205030740d0364420000e03002d8801844203428080c5481e104928203c00500c4a501942089000c1c0d51642141e1070580c542444407078001c5a0725500300d40314a01303018018101d0160b0240108028800320116080c40340501c00c00e040030b000603082d50b098608142078206554819288211850700c1d101c600e0490806100781d450f0400e140902a104a61500081140a40150000b01c0c006400c0510000015000200d030b00031310395074540c20303ca1a01090601030103210000d442d000c41c1d07400c04c1200c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 451789955 1250 451788705 451788721
    0xa0509161809060905070803030103030813030512060609091906090b0d120504080114071202120a110c0a060603050f0601081504150c0c0606050303130b0309030f030117070905 77
    0x741080c607100040000d0042250600702c002c0d041544000c0e001e03028070500801c902d0b0001c4000c6042c0c0c1c1c029121203402c0c0c2c031031010000d1020380307464000c1d00141040c0a412100800340705940e400500c024407041c01c0107620703000114130310b4058a08425143c50309c100400c0104c010300441d070040c15414402c000c08000d1380045401c060105030000c1c005410004940250350042c01070b1400340030b441b0002c001801c050340d035003810701c9000c1e254200890b4a4000e0300e40d404c18507000b140c43c0301d14804141903464440a01880140ca1005200410b0460501a00c00c0d083ca0030801030081e10301658011601501e94144075050010401011445410401c014896074400040ca180d2400085940703041c5030b612402c0820284148080c5144214200743ca44c00e0203903803002001f003c15010b0042002000e40e504101696845030001e94250311100c05420000304a4040141da4811403401c1a40e2401d11034001303840f078945c4260070a400350f89040117405003a00d001c00c81c03070010701408070f800c001030b00700404 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 451791205 1250 451789955 451789979
    0x70e010e060903190f030905060a230f070812060a15121503110a061e110703060603080d0608070b070809010909060602030a0201051b03041211060a050916 68
    0x80c0c10350192900051403800c0361002c2268012010040201641c82c866038034040c000f20200380c1c029400644008000310f080d16000c400c66003005640d0311000581100c0c2c941030f03052000c001000b01400343c1c0c00d02c080d01c903158044d4014240c40b0b11405d03c41755100300c07500f907500003d400a849203014400e01d940510968000303108607002010641490705c08040c050207000040c0c102c122180f44801010340000081114080c020001484220ba8800c84140c40b04003c07585980007050001a000c14202924092030048048546c030924071416103010586a40f01c03002074540c0707940200e61485000940c188040003500c5840090903048010b80303025031034800c440126009801c030160400c14006101c0c0496030181220a00400394401b00b8880c042d51340c0000794480c0c2095200070095403d040004d00320310305600300da41c1d100e9401c240303440c00c6486d280c4550340340600148c504001d00c10040b02104410f101007164a103e0500d000000c030f0356103090442d050400750ac152121406407080c0c2c0040c02003242081c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 451792455 1250 451791205 451791227
    0xe0d0221040506070b04020f040c08060d032601050306070f020a03121410081605031c121127090c032d0412090f030305030424090b070e01 61
    0x18646440c428445505160340c403903940070035030080000030800d00f08600c1c0210039220f01e00031101011002c4529042c8015106492030500000d4102c000103031803031400b61095620940030340342c64040c0c0c92203c80c0040700c502e8080380349041070200c0401005640340800035254404001d107412411000a84406540c1e400d01c0f0320010b0034400c50110b1141150b00a42c0600101c80441d1803103561420420300a1a00100a001c1d000c014000c006802e12400204d8180307004584003d001081e04040810344030004c618243d020204202001b507900086084d24018181a070040309802070395111241c4582e10b480740b03446a44080000901801a119a50064020b901020600c00b061743c0c0d41c1d035a00f0031040b03404070002c2000302c1004014001c01d000b6114601c9445944294441100d0b142010f1055803084840d03c0381c00019101d030403052000078480e10213035801c64072840100450103070401d1055040e00f103200c4500c1c0c9a940d0b80030a03105004182802030781000c0681071528802010000003003d1203840 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 451793705 1250 451792455 451792483
    0x1c0308010e07260901061a09130902060415020d031b18050a030602040306050907150339170621030c03030414010507140d0b01030b030706020a060e0d02 67
    0x80c40005068a00844810030f19400182040c00030107490071030064106400d96103281158640040450b9925000307804c40c1229441050081c100b400303130006c00c1381102c070006010310019103540c01c110040e26904040d1000d0f22186034000618880040001c1c504003500000004050406c00c103408903107051249101848001d20302282c13803d04485100b680b052041d841103400903507511000050180503400b13001540c2c0320320020b00182d11000c0c10a0741d01e019900a0805440e003403200060923a0180c1e201e021030801e0411400003405803c1c807224601c0b41403409d1980b0a01001c10080306841e4089061002c0039501061710403241883d1000c039001814009036590356100c0b0800002d1580d00420039076250381c119004481d1b03030b49003e2400e01c0c540084004506203075820400415069030048070702e031107240b1458110a0800d2000c0c80710354050048080c2040c140f541d5080e03800c0c03607074505105020292160780c00400e24607125281c140200d40750510004210b400c441030841c0219400300742c00185000c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 451794955 1250 451793705 451793729
    0x16060213081908030117070305101e02070506010b07171305040c11060106050c100f061d0f150f121c03050402060d1e05010306060612020307080c0a03140a0203061c030801 75
    0x103000e00b586051041e4001620a116640c845011858680c001200d210450032f620701c0340e421143e2a4005034024214010000d41100c40140310850b4041c0243c42640d00540c14002a5064240d903401660712480d50840d4007120601e040c021401d00b8040e504030800380780b4000118101e94107145482d40c0c0c0600909080110014444029a0040207990300310039610030100103940000d64002c0040c10706100d1420b204c0c8608114100155458411a03c2055103112420740341d0b84140c3e1181d0110b20b900c0d801644014a00ca0484003629920505000c0c0054a401402070351170300d80c9002c0910700e4000c41c04040506140412005032078010030384544844060b808100c50b1391201280d5070380240b405031860b0f0a841c3c030b0000028402c9941041084400c0c0fa181c00318413400d004585422791000704d03009000300b4000c40124040003102c000524034128a40780000321380c06980212041500300b40c070000c00c80c5801109216103891302d0400340f2040d44403410207807114502d6035000b03450a001445180001e0724 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 451796205 1250 451794955 451794989
    0x5010804120f020a05030c0a020f09010b0d0b061c0501061202280c1b0f0e270708070e060f0a12081e0a020a0c05040c050d02160602130819080301 64
    0x2000f000aa113820341e208040e240c6407102840c41c1c0b40da80c00c00300403c0e1302c580184021595542802c50040381a502c07030400b03151070b0011021044010340381c90200150001c4040200d00e43c040010040d0b40402c0844d048003017055494120002c002460182c0c00454451040005100722004001070041200506520741d2030600c0d00c103019a003c801803000039003200c10209442c0c40715481c0102100940d544620380450700391312803003001c0940d5400ca407483c002030000f07050446843d42c0100340e503c0300a4240704a888094032001214288440d50f440b064401502009004551800038214040180140c90300c1840c54680181040c00c4500844c0280c650b00000070b0790080e8440d104808420380c4060f90f03c4594a8110b01002540d0302201141511451344281d4041142d01e028052030f0034005503640c0b05401c10a40703094040088d0301c0300034550050655414903a00258040c000341c995041d080340c0152120340740c02c0005041040e0889072a1081011503e00c9000640345000c0e05c0c10340c2d2070340c85030b900c14071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 451797455 1250 451796205 451796207
    0x40501150912170a020a0302061e010e040609080f0405010912030801052b081206031b0114090904081e031b070204021b061005030a0812071e02030706050105010804120f 74
    0x64990010ba0109043c0058001241a00000e9034215107110b0b600301c80e92039540b19034449400041a66142c9000d207a140104880e184204040381c2003402030100141c40c042c1943d44000c0d40d80043d0784009480c00c0420100107540e0040312540080105580c0e000c82410310b980c00600304401401128844c4482d0710f104207200b0004046001280a9100443c08018103800c0941c030310341040400041061981e00001c403141000303d0101061220441d800c0081c5140340b00640b4000011030700d120303421500740242c0c510703a40d03090740880c081c5010302d003010b0b50341d41d00f07480022010140d041c052421541c10010300046106041c0e04103200d070107000301d15840b50164030018003e03204009124415100100c002d800f00d44020503454014540e042d04600c40907034980505460300b140000144c5a49400e000c807c101c90071600d00990b001071a07240c03100c52404c0212034102c0100b0091000e03401680042480410414144900d502401d02401e00c40c1c00f9140903a1071040104103da017003010028141180003c00b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 451798561 1106 451797455 451797473
    0x705060109020901050c010615080f1003020d150203041401050106020123100f0303091d090a1401020f0403050c0418080a0e06090d11040501150912 65
    0xea282454100094020100280c14403008006900142d00d0138071403c00501061880740003000c104c06401800b4660017403040320f41a014000303120494401c0120f100c212a0b04852004c0e040301c1c546005803141c0f05010203080307610700100030300081045c40c01c003032408036003140000c010036039881c442242680d00410044121440d10030113100c140032048151075010000c154100b0324681c0d1101d01542c100f5481d4010760009411138018010352001292480c0201d0104841040c20705111121a0711086c54201c020503200b801c8001840c03030319003034054409034580d20074004e84480e9603007081034503907880c0b1280b6031060f46000141d60301d0f0030060a113000e8443d0455030060910103100d000761210005a045903500c08824051005103030780d80762152100303d00ca0320074a10101000d405000c255170068008034654000014980c2c401588448240c040300c616500c64808038009040a0000f = true := by decide +kernel

theorem cover : BRFrame.Cov 451618705 451798561 := by
  have h0 := BRFrame.cov_init 451618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 451618705 ≤ n) (h2 : n < 451798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
