-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3377
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:29:42.656238+00:00
-- url     : https://prove2.me/submissions/ea86d0df-f8e5-44f0-a4d2-62266c0d0cfa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 607194244 ≤ n < 607374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 607195494 1250 607194244 607194281
    0x2070819030f060f06080903030f2e030809131b11010b13050106110f0a020f031911010314161b08031e010b21150a03140c100804020d0312 61
    0x20025400022503035111040002440c27541c41c0a402030151003602401c00b800c0f600302d0301c0f2074003565039a41c02260302c20910700012001199591501291319841308013020700035900c84e003840320041131500031540681040d4005030380c80400c0d20404c40d06d001d842c46100341559216841004c440d01d42004c0f5034081c844c0030201040d03542c10100050811244034080e183c00394002292841c1d0601e01140c004062941103600c00c000302c4d072040002e450f20813400802c110242100301903400300600070200c1000c1c2a03080c1c0303050100d469a10a91480345204032a200d50a09a07100046582c901c14680c41840c0030b080c0c40d00d82c47c08a13441c4c842139030702d0b04116a80c0c4402c56036801402d0034a03060f8001d00c0e0050050600f4a46068040c8804000c40c91221703908140000392140170484446001c0700002d941c1001820348032780242c3e0f904000700340210307046444086000d42d02c1000817074204050002c0040419440b85c8030300d6112a1b01380000e030980303900280d041041e2100034054000080c000c0040300c1c0d8402d03000d072 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 607196744 1250 607195494 607195499
    0x5060c150901020a021c020a03050f040b030907051c0c0b0703020a1b0e130210030b030319050904060e131e080309060601091e09020706020c01020c0a031202070819030f060f 76
    0x10741b03059110000c14414000c001d00d021644e56002506448840c0c3c545400f43c0c80e0710118000c200740703029541050140d200040204020000002849030489030121107061045000042d40d040c4e0607102640900034000307070042405034000c003c0041c05007a109204070303190112651112268010300c0404100c5858403940200050424170180a13040307698500404860300a0f03500240140209043c40d100b41038031012101c6041c0e40900070f1325484003140340c801000c541410002080c81e4042c41000b0311503480d141c1d0103e1003106004060f031240190401641c194401c1b030704d41460000007170341e1030041c1400030913082000a508402860050740c003040101941d0030071400141140b0010303042440041391072001c0c80036045c1960502c000700c4600220050341c4908030f04040003e8401c0940a954a40c000100c2036480c2800095014019019035502c4d40300c0d05940140d1f8040e4881d10b48040c10b1501c080c0004000c64a400300c24030700c40340190600188502e400720308401900c409a1088614215a503400c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 607197994 1250 607196744 607196747
    0x23030a050a1506080c060702190b0f07051603170304170f0307031d060112080910170c040501090e15030706030b040b060c060403080405150c1806120105060c150901020a 74
    0x4020160100c48042d2038078501c0303480070406c20300034108064803441655581d1001c600790546084090100b02310000e54480c0c01c9030b01040701e54003212044403940700d881c12488a260440f000101500c0e409280000c19000040c10b0b5500c9400161060741d0050483c400c07074420b0109003005041082050044036200d1404d0b0002400b161043c1401c403140c0040c403400c0224022022841c50305450501400d28031640c101d0805a40078040d280f511074001c1c800c5100582810307000032059000440201e88042103984407102d0003041d000c2c522609020075103a0f40240004081118404c3d800109141140e031340a1003040002d203002d04c0e59000c400802e503104c401290310f0826000341722980c41c043e83c1b070300d00d0319072881d0410350707200801071000c3c0c1082158004201041400c0c400341009030881c04900703099050400030b00020764048600b49002e0f8901040c50302450810700c040c3e9080c0240600210800e07880d040c01e1001035449103a5105082c051140f10810307881c0505c9c81103002d00701d410300060302d50704c007104c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 607199244 1250 607197994 607198001
    0x60a2a0c0e1005090c1b1005010f030803160e0414040303051008190201034a0d030507050c01090c210506070f0903020907050c011523030a050a15 64
    0x100035840e00040c00c01c00300540510708001221415100c3c81440d0b03841c075060720050f001b2200790303000c50546c1c800010000c50300010b40100031000c000c41000180d9a880d198880e00c0c801340f100a109040900001e1a007009605c000c41c841d04107400c00c5040178101100080c115284019040c2c0c042100d1801c1c0401e1580c148949940a61901040c0e462103045c0300304150b4440c080000c881c840036580d0030340f100310391194020702881240c106401d200310f21480c26031110600c6004c411040d20101c5200045510303800c1d078488a01d0b10b5408003601c5038000f4072200b02c02806000b0624001d100c0c2c1000030000400c824844c8009281c051400d401801381025143c680f40e4041140309480ca206010140c40455400f040709074114140d0709001107960359003c1c0c25501e001e0654006540a243e4504201c0d0722608a80105404400b600c000c002c2e075410b100d00f40355007074580d01440c1c802400d40400c11900c07895485680e001404000d049030320354031607580c8031843e08414038812140c070f6200d50300c0740440444500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 607200494 1250 607199244 607199249
    0x1206060e250c320102030601050906030613020f07051b060a180e01080c0108060d02091f082b09060207060c050f060705040f06170613090b0103060209240702060a2a0c 73
    0x3d00a620350300f08000020309a000380480c43d4030802d00040402e900795150940b03007810500ea10000e42d200c0b520343d2000344a58100c50030513202e5000706035800790800200d40003804000c00040c4000d0038500a904100d42c05005000c0901c100c5d504500045119241c81d484c0c2802001e5050082c1540300c92000018013005014001502a408100c01000180d440e203240650007406180c5402001e0910b0004907000c1d000c5522801031405031140b440e1065107820102a41c042e01440d807124a040851001c44040d00035124043c0107801c0084240001c81c0700343c01c2c540c4024000c42c1101c0c031580b02003580900b400c00580d0400d004c00c10006080005050900c07440d0b0041415081a14000300c09541809110b10003c0c0303083e10444a051000105004940c001141c0603040583c032401d540e107924084000303511074068076200301d04c8e152298072403070360110740c0c5504d82d80b80003907150134812281c0c01d1207002d0704101c40000a00c10400700000d40030f041c140c1302d0380d000e000788503000511066509050342482ca403034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 607201744 1250 607200494 607200593
    0x315030a3206040303110403140c100509090402040b010528021203040c0e1902030a14062d0f0d0b06010306090501050d2a1206060e250c 60
    0x2510326070761444003085040e48a909814003142c00600704128900c5c1e8411504000d0040707400c5c4078481c0c0210400607014010707800903a1201c03034104200788180c2d6140034038683d840c0c0c0700c51110009001403c098000c03020030041818000d003442141229103846030f50103e650b2616003c1180314a00440d4108004200d00c3c1001e81428903500701a215511311040c280581071010a240d0085404c1003400d4a90b1014600d901e04115100e05000f5400710107402c140c01c0088012005101050007460f2907120300604240c0c4140e4082841e0940c110320b00c0005282071500e0740141d044056080b551180c801c41d0210a100e0032000540381360140000d01101c04540001801c54500030050115449215299107029001458410031540381c47c2445900a160a280d590101e5441000540f5107142040f4220191150350705210a43d12840e103c580c0403800c55a60003c10071404540541c01049454039042e44903514129202c0041038881e8000a10314a213201000c00c16911415003058021310040d41100302e4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 607202994 1250 607201744 607201823
    0x120c0302390d0308040609170406050a021606020d14160506090f0105070f0818010204150e04141305030c241f1701060905040302070512071a0315030a 66
    0x1510f0041441200800041c0f10795a148589805e0100c0994460300e8240301c2a45d030744d82c56444600050113a00143c084401511454000d20359600c0d1aa81010070f407882c1758003c1108401d00441224006410304490a006c00c04002e84000940e03031800e2100c6140c002d070000c0c01f00d03003000ba83c85441e0404180b8000b4a40c2d1404041c48085030303204c055544203040c20300d051640c0d6100c1e034600b00b01c0500012020041980f00240004141d02042d030001c07650011900c0d044650482c20f018401510404a00d44001090750390000c2d003108035400c1040b0340c99000d4822a4200582003034450324004925009c074180c41c41d007190301110703e005c149500341e110034600c2103042e040a540800c400d03555580d004400501d5198456a80000003d601a20083c04000428042d80c103180c20080c0d2a4401402120300424801c0640a0a00d000040d18821a9079440c0c00c01f0384000480b808035499080039007201c240e50402c5c684940c00380d03001c001034502035000b0010192140003107140d0305403100359088414401c00d0f0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 607204244 1250 607202994 607203019
    0x306081203041e060518060c090108040816030804201302210103081218070302010f03090602180405061002060a051302030706050a020601060c120c030239 68
    0x1040140c1016031905240e40c4984032403420a020b000c58030030001040000118040034001290002402031401d030701d900b68008148450980c44410071101e118481d42d0800c5104059403042540c5940302d4020b42a00d1305000540a1401046500d41c0b401d6001411040a0009000711100c40682110341d802c140340d0207440e20004510b440d0700400844880c43e40c0496001240c501214050a0307a1203840d42e0800b40307603102c0c54080300c02c1c1c01005003412100c141c40000b55100c20840b035072900400804006000481c5550300448440400340010002c05031503114800c0001d210380042c0111110340d900a10a2000034001e1001321342d03000300322501c10356043d8940c003641c64010a401d500710b1101e000205030359840c268000800d4820400080d050300c658600000c540b036000000d0140580d2950a60b000c0b41d0340c9040444486084a0010300500d500d0a411989240110607010045110b4019140034813a0080051480300b10050703c07010380b0802d43c080040c04401807440b101d44000864240f500082d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 607205494 1250 607204244 607204259
    0x41419050c0d14070801020d0c020f06130204020f031503010b01030b01050a03240e040b0a0606050409021b071203020c1009030f06020904110c300a27030507060306 72
    0x40d5218540c1e000d044880c09100510820740f04900c0c403061a641110320300e90780e420010f8000d5102c0d40307021482ca032410351003052203880419000b0310b034000000144029160019a8010009c0600f800c9030302607420080c3d600511400ca010314460390008003011608841c0ea020716081d80c244403c40c03810103141c503084501030380e0441c09640d2198560b10300054a00442e20340b9403c2c005071481072200008244200203051451030b642c0c148254480d00140c9a40d85425000e14142d5404c1d020701d0000c2801480b007801030300c802e503010b81050023200c40c25444808003952614201081a000703001c4566540c0d100d4410b054040002c01310002c400e5824081d4222040c50080015045020080c865540955410284065034050b943d01078401002000301d13031100e127180100c0d60301c039041d5205039000c1c20004400003660700d0000e603408205c00760000040602e02c003440951382d002480900521480d01800103200b0b20032540c040482121118940c003050840c1000742c582050303030740420101401e0100030b22620 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 607206744 1250 607205494 607205503
    0x30c050a03050325060c03050f10061b0201090f290702061806071a07030c0206090d0c03021005070c0b010501020604030806040b01140c160f1a0703031d011505010e030a0b0402031504141905 83
    0xb040500364001d810503241c4010fd80d501015030240300c0040910602013107440c0c1d401c0402d4500c07500d8445a1f060644524114403030307030180313480103540050240070703078401c0c12890803a40d0311030070307000b0001d41c504030840c1e1b54010002d28010005101380c40b075a0401194a416119030703500c9c8205400181114038100c0305065980891010000c1000400d0082d00101402000880fa000c1c1e41c845003400140b505480c02000341898550550b0361040c1d1200000b519400401c3c004c0c0101e825076600c0b0060760b946030510000d41180e80400c0d04200c820718400300c1841240019003143d40d404009090341e12407803d01611030031515081603000a6103803800300140d1401c80d00c00782e942d00d0400e81c1d0b15165a100d00f419002800c42416041c40403800e4440f41c4d41446040d401250000040c0b00000074150b15034004540340032610740c0e8650540c1c04032091501240040b88003503402032004048a40c2500404440601ca000a440455500d04403100c82c103030b012010b000100303100060036412142d031104c54480079500c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 607207994 1250 607206744 607206767
    0x60a030b1308041802030415020705032b061202040c0801050a0314030d020304050c010306270f09050a03181a071101111204030c050a03050325060c03050f1006 70
    0x3041070701c102400400142100351001819194540c1c096600540c100c83c0195004480440e812401c40c00c0c903003001c2d0014070980d444582c20500850a0610020b24032504411542582c004845506900c00308000640280000340407c1d800700004400144103000c00e4521201c607090a0101c0c400040c80a9155142c10804580d0020500c0c5141340c0400c940c981144941c220b041c085d140000100028080001000b0076060420390302008401d40d200080e1400144282039111448080100c010550320300c1c0d0081d02e90381c1e400c180005100e65066441d12301e0028510000c50204060040c1c401e1040ca41c1c001c0310000303240110454400043d811640d110714460342c1d00041028404202002181e4070582c0b20050049585041707403420500007100c401c1c0d50b0410311040b5074560010f41d01059900340201d004d003c480d400f034019400c0228801c110b2080d0140c1102c015001580c003220700b00807500707030b003e211200549c5442c0010b41d8100100e03a0710081344000c084a0001041140400c41c042c0d116402050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 607209244 1250 607207994 607208011
    0x30a0203151005030a030507050f0c130e0f1b031c051b010b18090c0303090a060302070312060b0304020a060c0f061a090901050f060d120509040221040b060a030b 71
    0xc81d540c0140c0d89040b03020a42116415200340815103007010342100003403031014001c008542c6000801e00500e980c504038480b0590300070007409651071100c07050307400411284001405079034130000c800041910717020300718600c1248000700601d159114202441007075203c4040400407406840310b5000908036100301d414840f03886030700b10002100010f00f0b6000c0e40084400074201300400060340d4070f0119205080d195910a4003070340111440d64a0004201c0d02d003080060175280015103885401d500175002550240c0a0200b4445610f55008803881440c000d8a4443c19450b120f0820340140280a40b40b50040028044524071100103d17242c0240320000507441000443c00500e001d00c0003c150000e5440b00d504003404005108025406400280c411580c07083c181e106a9591020482034260381c4801a040e00403080710354101c280b194000b440c00d0b9101070300151a08043c0400b0314444501c107546480c2d00306140c01880f08002050203402c0d00200211889151541562100d982000c00078020310b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 607210494 1250 607209244 607209283
    0xc0703050310030818030f0d091e0f090c1d061602150c010902030c0118090f092a050103200903010905030309061503010204030b0c07170d0c0e030a0203 67
    0x12840c0c6042e5000001850b48500016107450020506110f01122130207964803a000e842a031100880c40000c2040b8810007070b948581c3c09504d41400c0041000117011000400c40d4070a10200780d100342894014000c10004000080e00d070303180003000b0002481c03408000c052281140700c441c00703580d424040e9a011400705214000c0e120403440080c40c8642c004c4a001070002c808a81074030021810352141c0d11f8a0300950a440040756184011101d894004592100e030041c118070600c400740c850703442039030a40c0c80c2c01030029840e42c0f04c5e118016448510a00c400307494044000c940340c407001e25444440148001e00b0280300035002d000ba0180380b41a0070071a58203400e008958030485a90941018200340c2d0010140c1b0303070b2030803c107003d592a09412900510500105000c80002d42014030071582183d800031030002c05516101000c5090783e0042c4000e450780e030341c110a6101c0d88500c0360000c146140103600d0000b49007500180c040e29114001d00001d1282c1c1084202c8000341c0c5002c40c418441d0f506081400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 607211744 1250 607210494 607210501
    0xf0c0303020c0a0b101d01030f150b0312031e04030e0427060903020f0a02090f0402031e010c0e03010b03060a1e020a020307031e0207060809120f040911030c07030503 73
    0x2586001400d20015124560316014005c044504150035010b64003862051102c032030603c49000055a02031000815240f030800600d0003145c00756601d46041180741c0301c04a0500252000a0b06d07040c09100d4448080b0000400e000755507076a4403051640c004041115a441c0c40d050b200078200030b10803c0c2d060302454030f0705400600320201000c424040680c0c1414102c0c80e4989090107001030a92200c12000f40c81814022501d0410000c1c0c059103c030350080000489507594200c40706e14180250040360140b045009401e11900ca0380110f64030901c1100000072041483d100060048054007040c81c0281d01d00581c880b401c0c0c50200e51140e100b1244003010809650070031140c1852000407146d01300315032001c240003004513800304c02464410b0280d60741590000301d070a02e11101030001c0404001691101604011a40c0511000b0381c0c04a62541940c1c40c07080304039001481c0798044800440002d60000d01404603011a200c1c2200300c000c800701d010f0031461320061440244c451500050f05014011000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 607212994 1250 607211744 607211767
    0x90509090d200f01240f03060b0103110c0c0a14060301030602250602091809030d05090c030a0b01050a060201090309090b0303090409030e1311070f021c1a070f0c030302 74
    0x220001204600122000414000f11944c000e00340c008480c0340c4100c1079482a20f030030301d00042c42800e54585000e03042e4941c1c51540d0b12002455001ca4a6040c5900c0f008520b460004c0701d0b0141045941e841b0242121030b000d407042286605540e04100c84c040c0441911041584800341900d0640c1c3d032004006980b20010f800c5840c28070880d9034503078040c01c1e80c4c1c0703400020043c04d230f0040c1268003c04e9a8009a14201c41d07415105c4180481c0c2103801a441449421030102130350308486e400425442c19220142c4188006c40d042800c000001c1c0c402c1c0507228010807607400e080800800a05681c03008000e110a02c2d40c004095002c688100b050352910740c1c02d0104940d4052080722490701300280301b0414000c942c90701902c0c007500e03c0036982c400c001c0700c00d0f1720484003000c0c041d071031054240d955190b18000c2e90351384a10401000040590700301e07182d61203070522804000868010b040c0543c0e00303803201213800080011024070040c805d104100c0d648641c0b624417504503600754030241e8542805611080168031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 607214244 1250 607212994 607213037
    0x1101140f1303120c050d080103020f09130b0a0c09080105090604140c091801050a0e0c190b162a0e04080c070f081009020f0411120f07090509090d 64
    0xb600e102c0300364040030f442c183c212851204861203031050307500d0941c401d42e090b0b410860920000e0342010214940448500c0c1011485601020f0b14900820780d00b11a114000320795011603020840a0740c2d0400d441c441500040010001c0801c48001e01c240d2424100d13042e00e070320300504001c0030311b21518100840b0b0707581404059000e00010748110080d01c0d2040c260750035104074000b01a15940713400041900f1710994014040ad03100351070014290b880f580d005001081034500000b08280c0c41c0c191010402c091190002c11000001403582c003111900760030200c100c030840880a4581034004100c1210410842c040da000302c40d031241407812035079914241440d09200c0e0114101041c011039402240944e911000c40c000e85a0755011100100d03c80d540c1d000446088100296100d0401304c150b5009207007540103006e0381880c0300310b01401c0c8510303118007051805041d14481c1e015028541002070b010380c04840c002c0102421100540d0b0360a2070750b00380d0b44410301c20006204002400c45049a203a50450 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 607215494 1250 607214244 607214249
    0x20011101050a0507030c0206070c17070c120b0606030f01050f0103021c0504050c01021f0b03150901020301050f0406120314041706180705061b071d041101140f13 71
    0x2000340014a0180203100041c00d01315103040205c1d00d04000440c08900c0003424500c41d52841d12451026645501d034684060010040900912000c010007070000d5281729907640100300c58440340e01008090b10700001d6208004011781d001ea841481001100b0000840d1a8115039094410901e980401b01c012006403181c0a00301171681000c1d40396003442c0c0c845510140c0b00b28016400c0d21034414244004a0325113079400500d407001c041203289200014500d034806580035000504940c0d4176090000c000d01a580219650401c2da5030201c0100076600700800e4002000004840c200181410503520309006001d004004d03042240c282d000b41a010800c8086030080c1541200c10a004840c80108541d20034003150340c100b170f6104a1040140c0c00a000032000c054400042c034031030a1211748003003278061004020760301c072103031040e54400038030241c2d0200800c11080602d11000c8842c40c040c148040000c040e2000681000000e00c2d140d00805400400c1e0389459241d10600b50755880c1c01c45104440d20810f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 607216744 1250 607215494 607215527
    0x40807200406180c14040519090c080703200d0507200c040b0607210c0b0a0f0c090b0a05070c05060307031b020a0f080309011e021309092001 62
    0x80400f00e44004900b005500e50b90310741030103200451400c0f80c00c88204062280100c4807100502040c4401e18040003e05840d170717441181d2414690b52202182e003503c07840d00040303020071550802e120a843c1d050250b042d1841c07405803600b16050180c1407000e400e200d60004005031654030400702d103040703102d5030bd070105103600c12050303900817400000d1068441c0c00d00034002d84034515040385e5910b2402d1210a071860160003800d034900e86941010006400000540c0c42c10801032014249400103d24141c0180581020040082d190700d0f02040d031811106140c40da502400340c441d80c10468000108202da45e40c81d19884e1498807000a803401045030702c026008994803403404010000059810762058407008a02e550f01114161010300c1a170b1560900030b00034040c90b0240b201c80011032101d100464211220000000e40300e03541c00c10303d80c4001a80102a01c10540000e00b03801d4059540d07044070050084080200302e0f40ca0a595441960745a884010f9100003480c2c240c10344580c0140c04003580309180 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 607217994 1250 607216744 607216751
    0x12706030b01080d0e06041203020f0a0b010e0a02030f0106050c0a05241b030c07030e031b010810080613140703080403200306131e080d140408072004 66
    0x881c644498440000d025040700351241c500403010a610400035891040005801c1a01e86810054884402401c0a038190b055220305000c68180c49410420403041d81c0c0103901c01580c6506042e80c0d40c40440c1e0260080f03008500510a101413481031221450440f22542002da0383e442441207464100003045078041c0182c06516010240540c6030749030549411074030300d030320b03412550b664040312110102c10302040c85203c014800035074004540f50007081003d0082c00d00010814400c00001e241140a60013554204500680e01c00d4551308140119000060010300a12540c100f02c0c0581c2e072254000c0a1050060382003400c8130501c464260790b01d0030740e0710705029114025140d0404d00b509520511007221302d4250f010805482c1e8411061424607000010080c00282d00c4640d00d02c0300d0b5184101080d074481c950a120b5921650008a1442c179942c40b4590302626008601c0560f01200c04031030040800740805420080040c00f15012114003591002c8054601c0f42c2d0f04840e0000c1042510340c07560410f24 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 607219244 1250 607217994 607217999
    0x1905191a0a0b0315010c0f06050705040f1205010c09081906090c0b040f08010203040c0303080603010b03030d1e111b071e0503010b01090501081902070f032c030303012706 75
    0x190085100392081201ca021301c21820004450999a400c409003800c48149071182c002401a04042e420980754a030060030030303442e4407000d00402c082e80d1108810219a1200340200315082c000c440c619020b90070721900b03482c608410140c80e800c0c02240d510050310740c1a82182040659888250117903002655007440644810303c42e00550300034000c5c00c40030f030800e030400a890001402128400c45d40080c0d500d800318915541520912000b401141e4555210299184c0648042010785400e1420800209403a4000e4105800b1840da43c241c0c030f440d0700d060004a4445480d1201100c0d04402070300a40314648580040c0d903420142e90f5005440c0c1c4a9840101030701c0506000c1c0410103588044000f003040340704220041d0342d1001c15101c4d840c0031030401c2c80051030f0026019510240200c42100162410916580f40c8504402c42232044000c605550140305624091900000b80c1604c810056011115540300283c8c0c2c03404144501c141d41070300a460710b100b070101442c3c54800318106080030300034540c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 607220494 1250 607219244 607219259
    0x306010c290402090112081b0f0115050420092101180303050c03060906040c0504090f09050c0108130206090d2f0604060512090102071a1905191a0a 65
    0x100c0582d401c2e4441e0340310100200d0001a0307000104660740d4040d09003441e050b107a40c80010f10132804204150980616485e1407800c001c01e0180e0503200c0607008030b8191141c100002c1104988134000c030014952046400ca45503036481d001142c8075041c003241c00819800c10345c4a0560700d81e540704000c2e001542414400c40c90404441412181244030303480a001d00c3d80c45454003545c2d804102c51559200c1e441202150132400c003544541445182d80c40c0c06494103440d01d0f501400e4802881e0390000595a0b0003400e8203114040c010082d25010910300b00f91513003040c01040c02d18110514010b4898000041c51160b141d40b0300c0f00b108445079001f40c01712200d4000e010b0070182d103400100d03c841101c2e286810001c80d49844402c860603901c0382e840300f900b044502250032550a000a008030691340d8200715078000f00d19100d01002c90035040d62021903682c540300034110103560801003403280c01801d000c01c0c049801c074000c00c28240058440c03000142c056550541c0400001300c60041c0b500208844008201b10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 607221744 1250 607220494 607220573
    0x2250807021e031509100e0304140306010f0b03061f05030a050a0c02120708040b03100f06030507081828110d030221130909060b090c0306010c 63
    0x203500840d000e50701e140c1006112840c42c490400780590640100c43e50040522a00c0003050300315064030115201d40d542c03034400310211007090301d0400d115800803800300100030344044090011382050740a44000c0d45402900341070712096001d15068040d0100020301c1a8980491048442044500c000c441048400014049a006442e1000414100380004032050960f0040540090265004040009101280110541010340b04031284801080001060a0b54401a5000b504000c1e03e0440701d41c43c0540300321680c821075000f03405050030841001041034110074242d5024107581024981c00348961003003410076403001d000200002c042c01c0580c050308a00d402d4860110f1060140081c95941710040080d032075902800200180c1c04140711103074141e04809c81010b0302041904007030404582e01d03040060400c0981201120390780c0d072038911050052602034504240740c02e03984150306040121000440b0300c4014841414000c03215100401c00903a0350a88040c0083c110076002201c20280048002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 607222994 1250 607221744 607221757
    0x503040f0816062315040f1b021c0f110f150604060807261203071d1e0603070909060905070e01021506041a030109050d1409030a06022508 61
    0xc05140640d40c2415984101c0784c1038040303444490181007940c440c240414000c1e43d08800303541064850301c50310181c00786d50085201c1c84806076054180d6020350a002484c04802c03c0c0540c3d4042d46100d2801c0440d034100d0102901101c003464421440074038001c4c01d51078240c414034076801a21602c400003442e400c06a83c4503008076400c940c00d000751a641d103400d41d9180300a0094500458180d4403076010403062101c01e41d000341412060310300078100a038042d40705410031034a020100300c100841411003902600c01018000701204c22060070060a941802c40e1208010b403a80902d0000000c00c021501403d0001c0041c0032010b024000306844a4001c400380c08299500c00c0811401c608184556001107a00e038041c42210a4405a903030b03901d400c20024051690703041c8015a09003400f500303e43c03801e0185050250040d070040c404902c03d5400200312501e50b40d0404d158103400e0007140c03020341d008908001d034150003030409a102c19520f000740690424110040d000c0c945034620060130002d5030340c06000e0303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 607224244 1250 607222994 607223003
    0x30d060512030406080112140604030809060709030b061302160f0b010e01270f020d0207030212090a030308060619091a030103150e0115080c03060a060e070503040f0816 74
    0x840c10000507800e0b500d0041d03002e20000300d030b20350300107210520701c2c000c682d00c3da54000c0c014070003c8013007900c0c035a003031060581e03050f000560490704118811004000b110303000107880c946160a503155848880c031150015105034420300461003000d0440c5050703015034900100c005d2980f0510b004603d0981d040701c08940e8115001c3c10034000014400904400d054101c0e89090f80c102907001078000d08112000c03240c82a502480ea17030b0f1409c0c0300400c12501c013a02c0324800d181c000691310b02d035906006c0d142030510030000c0c040040070020180b03203494580c0200c0031030358581420f80c50f54441400040d203d00038070041c407800751400400f501125510030741980403150b01c0413002ca00c26a20080c1005644024040544141401e03100c1c844001c2e010341c4496031004a1a00000e24000c2d42040941140394a80c883c0310581d01500d107400a0746000c0c000a5080484000c08108451901521000150303004003076406001e004000901407003c0f083c5801030300c40e840301c0c0c020783d41ca4060303a1050704548640c1c0c0c140e5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 607225494 1250 607224244 607224259
    0xe120706020f15090c1203040902070c090f0e0c060d11070b0403090801092f04141b03040c050f01051b06100602211305041109030f0a030c0213020c030d0605 69
    0x2030b0380302d41003e00d1a010391000005801104040b5042c4800b0708201098405070b44070400000980384060320141148500c0b844184500360700d440300c50b500b5140411495605c007450710b400700da11441c0008007488400002e84ac134540312601d01c5110710041246145a2580f0b800020703480d0708100c0038000d031612440c460384032080c64030b803240001400c1700c2d08080b00900303e0041400003180c08907221600711a03e41031340c224956041c05030001c1000c5d6801e220074007512145031001e0001400e000d4852844001c0c00c3c600306c50640c9400c2e21003507041105c038442e2a02843c90781e01c4084099102d02e080b990305452030091100b1041203c41d8032990b80c6401c99541081d1030340031030003240d82440824044032100700540c21842c00d5040c854108100c0d4014070110b050b003000301c0800203413922140551602503040d018216140c426040926041c01c2c510b40c0c50282300d400c003041040010360031520740c3e03000c41d405681900156a044800a0081c480d54a00590320721010544520a05498220700d055440c01d0b50580c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 607226744 1250 607225494 607225513
    0x60207050a050d02060f0c1b0d09050a05010f1211120708011401090b0a030c0e0d0503030f1f030f030e041406030c061801080628030611070b010302010e120706020f 72
    0x2c0b6152030003540c07481d5005101c6008161031f01e070410050401510a105810002c0d0300c104c4040c2d1034488000c1500c030204a046208005928208504d0b42c0104030a00f01581301e07801e2580003d10f02203a015004001540d01c41c4844454085031003600d041400400c480c0910381040034028254540910800d010308642d401c003400070b54814552141102e54606003d8102000da078400d0300501440703203d24041044c41004203185588813000c0c420b06a008401030365482c1058001c184503000c00400c04282c5001603162034126064148046c0c5c112a000a24082c00c0000c1d072504071040070f080b5640070b5200e0704284006001d998090f003410b0084800310101d403a0480100148541d41c040c0c407001122000c4040c050b43e906501806529506c48002010700041c401c0001090325084914800d04440300c42000041c400c004243c41440c1407400e02001750b0741882019076941240d000140002070400c015031010b2600b0303882e803017052500014402d060307400c1c4036110750009542f4904c069000d11a4407401162 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 607227994 1250 607226744 607226747
    0x1b030c0d060f09200a0b070206071403030c1804020c0705060d0b0904080a110a0209060d140a06021306020a150906140c0c010f060509060111100f1a0306090d1b060207050a050d 77
    0xc2c17904442250380018141919502000a0f0707070030040080e00c40e402d40344040003803600d040c402940f0503010032809503201d5100c0e805a03001075410004c072030701440c41040341085a982c0080c008003203420868040f5501d4440c0b5440c94040e00e031200700550060306140500c000c001c0044003400c9003010300d98941c0416101c0c1800c840c0d5072602c038000a0b401c007560101280c85030401c00503144013940660454a15590406411840c0220f60b54050324442e6010800965070381c00d106010300240241d10040c1240b000d244c481c07003156810004044000c0f5602d640744020419507420400a2016500f4060b806251440d00c0c8412903000a0b43c8240552921b1501c8075001d489101d1034041ea42c002c0c141d24072654a0100540b052102401501c81c0d911504245220340c030b03014041c036114100c1d51400443e8800315041e000e003918808001c554880c1d040701d01005022600007543e0b28110311a0302d0800141c0e640b4060810345d4403040e0070040c14280c00004d48100748480001c00e440124454800c07643d078248858030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 607229244 1250 607227994 607228009
    0xf060f0e04090b1605090d200303030c030c090a03080c0d031503151d0a0302011b08040b0f07030e010e070e0a020a05040e10050d12021b030c0d060f0920 67
    0x400824180515000c00d0042e441c104079130103661500d041c030302d14124044000441c11700c85444100d45800307503ca40150300090500c240c85041e10181e0085d4150708242182c94201c1c0001040c0b61911040841e04071155501c00d1100002981c0128400d0340c0c0382c9001c0d20590f100c41c50035003070001290078041d80b041a52454001101120303040700152030800505d10100000d041c04094030300c5009503030401b0381c1d940441032103142101e620980000403e80490185a6504105091580d0a0002140c1000301041d08191902e900c84100d001004060703854400c281c00a052001e8242d03503d62a0034039051390520001581c00a44410304442c20080c0ea404400e10142c1c41040c501000285040c0420407250703040c0030750242c000c2c41400b20842d800b0340712400b103034040e1100002507030101c1c2e079003c031203408a030140070b40084802d043c1055060740500b8400700e9610124103e68a000c0c0135000070840900c07030290f0210241d99640401406203c2c980e081c9642c03110144e1030341506550361700310301806c1407405c0381 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 607230494 1250 607229244 607229261
    0xf060b2d0f0a05010809010f020c10050601030c051801020708030c070e1f15050c10050115020d020c010e121b010207060c050d080a020d1b02151512070f060f0e04 71
    0x10300300b41426061200454568030068440358039992920324501c03c100d541e002900048039200d004003c10f290090100e82130300c40250616040c140f5144c0000d94a541c00b0003107640a03030700421208140d40c62000103d01e8810241d0021401d40004550355822450118218046807a24140b0795003540f25a54118443e80c1c0c40075601d06083c00002e810403031802c00c03403030401c030700300b900c3c02c0140c10082000d031064100710315030100c0281e1503070784d070018080c00c90812950850741185e4401000e03c8030700c60001950b01e5044415241c144420424000c4c841d5448082101d90034a900c429100d821071502d417040e41c00348600702e0143c0036004406000c1050340c81030034804461030304030000b0041c20445880a42e51600050300d200005a000c10401c0c484c400d403802041000543c01c22108100d8940c20750081c140700f9051950036848040d02c06204440f0b2005155246170b000488a03039880310702c859401032030f00056500a101942080d4400500580c003e00d0a18005009484071704d14a01020100411154203c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 607231744 1250 607230494 607230499
    0x6090c150801030807032d1416140a06020418060b090a03061109182a03340207050405010f030f1203060e090706090e06090a150f0f150f0c0f060b2d0f 66
    0x49c2c00b80c2c041440d42101c1501c41c6040825101d018809464000030f0703a12940000001303000d141d50182d188131540c45214010107034a5051801e21400e0800110503a1451002400f89038490843d0100820700c002110f40d001002000d482c0f541c01192895001040c040781d07070804200c01c540ba81c030100c141e20420340885c008c403015443d20356950340b08010801c0d0040380c100502d141081a08030302406d180d40f10100c201c0110307002004001d140104000981c2c00503000b00c0c9410303484041c10800034021480d0b590000d81d116507070000c0003102100450041007140d000f007981400c6c820911528580c0030400009071201942e0b6810303466150354196000e0002529403603003000001d00010f14882d0141d2000b041d03460036412641001d5a144045080210070b50802c100b80c4103507200400096607082000c006254a0b8104256140070805024000d40795646020300b40d01e8007075051001700300b03c40d0301082c0403c400520741e110090140c00442030000f10305004020141d001c4a001080d898007000e80520401c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 607232994 1250 607231744 607231777
    0xf03021029030c1c0f0614060f120a06091109010303050d0b0f0d260d020901030e010911090a0e030412021e030c040c05130306090c150801030807032d14 67
    0x504c54000c20740000c14080d44c060450701092800110117008402e40044000000c04490402504100300d0440d04484c00d81328080c0341e0003480f88000d0210344204442c1c0c0183e030003d14881c403400e00015a12070801c881740d20500c49000407082682200140c9541c80c500c10040128580c410140088244103524032503202d032003030300844005949103209a45485e07400720f204280c01148170407110343d034102c030301c00c01d0600da000b140d040c0c419681441070701d101100c158002d018403042512020202c0740c000f8040390255800d000000ca211502e5005100c1a0641e6400c1302d80d610356601c0f03008036000c0000e00032032007055982402081038920200034403a81e04020082c02c080c5e1149004c0000030041e01200d4800d1100a02126a80040800707000e002113016041c08a524903040ca0500c500031640d4000201940040400c01803c83d440b4a5260559074080350807a9108098282a40c0701c62402802d03072034112100703c1c403818450045003510841d03001074440540088070110300a00e00e0103055032160f00301c0d08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 607234244 1250 607232994 607233019
    0x5190216060c0203090301050a0501150203040f05010804080412050c040b031c080603010b0d0f0201200a0201140d05041112070812090406121406010608070c0f03021029030c 76
    0x8980d1151020b0002401207134a800c4000c40424203482c0202d5114001130b6175540108820400445080d1030030096101031498076040505038003455266009150420074200002402c001119007124080d11010209180b9061189481560303240781c0c541c0c09000354240202410b003030400098250f80020046c5400640c100700382d00813101110018020b65042d0740351403090086442d0781408007102c03402040c0100c410340440c0005465210100642441802e000140914968011465005060782440c148c0a280110b03c42041076000d060b680700c5045207030006200030410740078000c001043c800d507400c0c9848402c007402107440759051300c504d024030303040910380c0c0020110302c000512242c0070007040003540b19240d0408040d803c05184049400a04510b0f088485840130040d150041038030b0315140390f40b89040c0034000e0004001c0e04005144030184420881054004c1c003c000051100754010014000c0380710740810a40310a0f000e00c01321a00080d50000c0070704000c5480b1a2400b80039104001d01d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 607235494 1250 607234244 607234253
    0x1005041d150a09051f030201020616140c01051801051b03060d0b0c031821071a130201030f14180703020d0b2e061101150905190216 58
    0x300184010210801d101191840d81d444100c03010141c10042000246031401c6035039000404500140080300721000c4504000513039000071525841103489070301c80c00041186030245c2c0c50350000c000d02040140f004c03486042d0303031105500c81c81c86145144a92400c18204440c0142282d900f6a0220540207600803041d50306440c1100464000030003400c50307004090b050325a02c4000105840c0c3e410418400024000f880054210068180321018094071200e375042c00101c0c280b509440c8006208903000c501142445142d61a405110b604c4440300da10a240030444524202c1407490300f2804a460300c18016007a40c0a03208601011001100400300d503201c607100e00d540c00c40c2d404500080b0b480740d05008001a1a41e400102843d88640d10700003850402e8000142500b0380d0700d0341c0903545c1c3c1e040c0d420b4403d160b00210f4050100c0b41c8a043c0b90345c009400ca0312903405003c00095036100e041000701c0010b00150a5444148190f244290028038012240580c0701a4880c40e6901ca4071900304040d8070003c00e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 607236744 1250 607235494 607235549
    0x31e020c10020c0409030f0809150a05040f020d110301201b0a0510022a0d0509030705120a0501050907060e01030b0a030b340206150f0307080705100504 67
    0x26400c50040700c3e0044803075400901621601c25085001906e11b41c0a2518140c01800d0b242d0000c01150141034a004406440d084010300240000603194640c0040b40501400a88a807845d40e00602040840b14003414081182c12030050868001d41c03030300e107100c12660204e16a044846442c1c0c500c140c60100f100142445540003556064464000e40c851440015020042d40c80c40c40e40c06800580c0300d10038600b02150060b819802c4900c18030b9000c00c2c21003c010007042030340144c02c0c00c4c2012529012034402091038140640c2000d90001880010081295070020f088900c0760b1242000f44040d544200d80c1c0c5485100720310451340864026a202c0c00c456021390040c003003031311006d00a001c455940e910b56685141c800d441c0311043c003000100f1590b489514684100780340c1c4240c0001c52140c00340d960020740e01c2030001c01c1c40da00140803e104910550312510b00c5500444d0050854034169280e035640b07500e40d4400d1095610602c0c98080940209010f5000e0310700700d49080c000305825100704d04010018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 607237994 1250 607236744 607236769
    0x1020a1202030c07081b3001060503100212060a030206040603020c10020f0d050603060c0f0d09020303070b0f090a0b18070506040b0403020102210f2101030f031e020c 73
    0x560000f0300009040d0401040340c41d000b80300a80c020070000b801035515a641000e0380174494040c2d404003481c40315007124010754610700e03000420390840010890b146c1500411507904281e03454061601036030704014141e006003080c192007180300420340c1c403070004001000701d09110081d00040c00b4001003088501030381c050b010346000ca005a42505941c2c186034000ca07884020444c0710305070046a04a4034100c035110f007603449035080d00145a02d04241520100501a808036030080700000900e8440160094004c14416039001d0100d98a89080d0314080d00d001c60100d850541d01c41074100042d2614800003a002a41504114804010f03111030f450103c101c0110080e8641d617125040e000035031616180020002020b202e000c03141c03514114800242408002d103840d0a03541c828112070803034990701004840800e80842d44441ea81c4c1d51052000300f001c4c038000c2c2c80310354600050340000248902249411601482a510001c440d0080b0f65440d07084402e000c000401039008244022241c100030385403803079 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 607239244 1250 607237994 607237997
    0x6050a12060204050a03150c0305240105090915030d0c030f0c061b0201230c0414150304080d06080f07092301140108130809130207050a060917040501020a12 69
    0x3d042d4540c0b0200703501e85020750048464207902c2540c051031046038865082ca80710f2615040c003250502948552120718400042442c005240d01e000d10542c0c01207040301d030b030568090150407451034200b8100700420305240140d40071340540c802501d5403e109004c55100264540c0b00d144c5044c20303900e8201e665280c50700c070803035130307a0b0b510780c0d1000011030000040500c24580b60700212310329407201282418804a94039100b005400c00040c40840c90007003040c6c8042c1d640c01046660030f100c080001606204c0c4c81d40c00c9040c6c0310000800d0105003c0a80000c0c80c001c207280506010082d59109015030f2080e01840400aa403c418000d200d004c4890300716042c40300302c01440b621480004007600b80c41890a0740301d01c0100300c041c0041c0403a035030070260043c2c2c007101d401c40b001c040b90080d45904405200f00c0310000e114103107001810403103028550550301c00d240c0040840b2685010303450024010a9181425140c0e903ca201e09080c03080b40c45806c0f10217560040e07003e1f01001ca01c0c1d030f0314000b0003c03100003110f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 607240494 1250 607239244 607239247
    0x20d050d0209061210060216030b04170301090b1e0f0904020102011e0506040b030d080106050a180306020a1218080705030f0307090f060306060816020a05030d0b0f0406050a120602 79
    0x2c80395580c6005481221851180d64496007440c1c03075950b98140050344504199000f06502402d0a51101a21000c8940001d00d0240c0c07a03940b031034098140f00b144501494007000102c000308085540307601c0102070030000c1c0d038181c80589036810140400600a1074540e4019141c10b2041e15504103d501d1981103481070001041c2081529948a9417644640010010503501c1c000c03c044e907d40703405201d1070200145c01a244912503041c00901c1082d05000303031000c0c080000349a50281c0d104810b0b03082c1130f00c840310402d17450b241c403441d144000c1d51040c0f00250000c3d071034400c820040c00f443e00c22034110400c021446007110741c181d51120429001403000307550501050108070742d000300304801541f24031480d9036808041400c0810a03261085503807c01c50800d0300c3c1000901a0f540c12505594121100ea81c806040c400900300880c90f02100c500004c0c0301d4000070030f68200c1d01080303400c0305201c80401c03141100b41c03404400c18002114010320566510104c0c122007003103404c2d04690011034040c020714016 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 607241744 1250 607240494 607240507
    0x105090a090312051918030e060a020f150a0b03062401030207021207080601140d030305130f12020c0103020c0a03233016051b01141b0a020d050d02 65
    0x4a045410481d04902100201d1000c4c0c40d084034117104010b81c402d00c68000340c0307499504d607c00a0420020584040c010701000a8040d580390003000729010703a002a2040b5819041d41458030250104280d0380345a404e410321486462910380455402d10171a01c0402a244400089020741b2036909009190b40c14181d08002c42800368803141003a1222004500040040501c0c1545891403c04140d10420349030500440286003541e5440101c0341050f010300e40404c0d240c40d40b0340d942c45049600ba2000340001c00320ba10f10404c0000400700e03070710810304a400740c0340e41c0b03d40440190260b101c2d0030b407c00c2554008030b41c07103000a402440c1c130074800f1003422585401c02c1110b02c0f100c600340d40520541c48016100b1620786070701200c80c410750400f03501e04804001d02800e1202005501814200c0c404042c40f601080901c9900c40a0b040c000714100141f000f07000e0341e614544142e01c1d1400c251070488288500c45901c0c9002c50154086940d000300b076a005040b40b03a00004102c6032a02300840a5203026000c010300e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 607242994 1250 607241744 607241777
    0x204020d0e061302030f0a03050d0c030f050a0e010c0c08030c0c01090f06020c0111070503070b1b1b1504150218101d1009091814030403030f02060105090a0903 70
    0x1d10302c00d0703d48800307032a54640a0b004040c58060321400c2c101355540a03031012400070307030712405072840e489182ca00490a0b201c20a800d60141c9240031201c1d03003082c644001c1110714034464110389084940c102c000c0114400031903040781c40300400c041c0588801020804124428000310041c1440c00300c0c0800065116015036030b43c541c000e04860143c4406030040b46007803a02d070080c81000c540303500720f4a00c680f074070516683c0d01c0d481f0300403000064a559508800681130080c4083c0d9614010914410281d0b2a10b20311205420324040042c0c54609104082505800c1c10020010600440c4c100c5505284100707200c1401d00a507111600c900300440082011032056140c10414200c00021500d031a150115603500700504c0f0001c02030700e030b4440c400d007001900555070800e0414060b154000d002251000320540c031048494144070006020701111140a6603003840800a0402d80740300790341d0341041418180017284d40341c5003809000e034042d6100d0003195480c14958050740c1c400d03100742004620b00268912 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 607244244 1250 607242994 607243003
    0x120106080303040b15010207061b030905040618110a0801030f0302031201030605011809120e0a051f020609011a01110a0c060815040204080c0130140112020d0204020d0e 74
    0x18104c403010110000e11403d180340398540051a5030a1000300400c500d0000700409a101c60408038901282203a0002c05061040140340c01410002d4820f001169407030541d400750b007080401c042e00031071070714032602803490380c50341142c0c0114455903418000d80d0070350b103e80760b030142c1c0080d046003036100030041d913550111902e642c1c0b4001e5000d1000003410707600d04001c0044014402807220105031414018100042c1c00c244038004440141c0340000300540c81401054484580b5005954000b0171543c90000c041085a04800100602c0d803d0342e040b41c1710f0300605070981d0030703500350b40141e042441e0350526294815012600400440002c071090a0202d0f1035112400b02181c11840008114000300700e1405140102d1126000e419601149030502e0b1000c0a512072000340c10250401030050100680000c54030018101e820040e581125a82c601d5584a0000c1c04490b40714131010961000009100585030f801090b0a13801802045c4050140d41c00c0200a42c0802043c501c1c840d46c0d000c03c0300e54a0420070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 607245494 1250 607244244 607244251
    0x614090f13290606090310050604020f0c0d181503021809070807081b0417030c0f01021201090b0631121401110f0702010311390c120106080303 63
    0x728041802c8402c21190351448400900c01400b495040000c0c40c0c0945000418541c1c049646400041030f441d0000010040d2040e803142401145012884450110001c10540401c80d240d45854815030214001e50900ca200780c4544200c5039800000588440c2c0aa0000d000000110809003003140c070f25000180154019a0300303500051202c1e00b004600c03500500115003108000700da4400c104110140e04856100740d001e04003a110341070035428800442081a10414400c04003601c5c080f02c5540c2c0e03418002d4001c000498041a9560700000b50741d05903104292148202a0406141c0580f1984000d0306120040f01401c0019000341400f000c40e59409014004d0300c034000700280c6081e40d908009900e00c034900c582140a9250010540100c081d0200300d03111181c2a600a946600c2540010380042004450b00200703001300180e80504c05603030400080742100c0070b04401800003208070011a000320604541d4903241e1022880c0213151401003840c00101e00004004200386855200140c2560800d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 607246744 1250 607245494 607245533
    0x3090d120e060c0c12030409020a020f06060a03020f061804020a0207030b060613150c050d12150f120c08031605100b010c02040903110d0f030614090f13 67
    0xc900312840740d01840741003240380101c64071401c02025418503034883e5a01c42d4502d1003405801150380d558a0305109460080c89203030300840d240c0307404010103511125489010b070814051640001c8207803070004038903001c0e250041d00341900f4411003c00d0051660180203880300c0b1040140241c2c1560741c4900060441b50003076800760443e949140f516103086480034000ca0300c5842b040c41040c0071103007490b080808403944100c00784559004a042910b00c10000140603051707009242c44840340d150010310042c00e07815100c0040100e60b070702c05d50a100459250041136405d8005d0038040101c0740c00010051000303402a1000700945907620800c4d40355034004842217030320845500900c818080103000380312189450b07810600142c180b420008245115180009100e255600c080c0c3e418180f040c2041034405100c44101c5202421484010384110328042e40400000d04204020900d04001031040c081030b9070140c1010425240d28508290060b4018456083c4252224204000c1000c4d00141c41c0c200803c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 607247994 1250 607246744 607246763
    0x9030f071712120a0506150304030f091502070915120f020901050a080d0818060709170114040f05190303060914010b090904020f13050a150b0a08040503090d 69
    0x406084508028091158030b2018a003404040403c52201c0c0c0100c3e13002c00700c840000307855a9107100040142071030028042c0d01c0710005c010003041580000e038818448100b40c680d81184c81c3c1d140f174001c10b884204401540107801c280e504101201c059007088491048006014054940780e0003014509001048192181c111812101c2c042d41003a07401940507060960f0042c45282c02d007002280e0701c1e10302905200400504800043d001401c1d60302c00040701076030790261261400c113110010550760803070050741d80b095900c00c0c2405c0c61071014402c034050050b80c0200c1c1c113099a07607600c542c0d0180b1609030060315140905c01014000c1080000c44544440c4a40ca000036403d041100e2102290346214100107007204080051201d504404259101c050007142c17008202d035110320110302034280816120ba00080d40380c07034981603080789030480b6200d00030b102c50401103d100300c18010704c00e50040c800d2007402c1500f0003c41103614031960381d640d442030155003144d24140c1604085548851003400a5604103003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 607249244 1250 607247994 607248029
    0xa0f140d0203130503070608070807050d05010e09010c030204050d030507051227060306010813140f100e0c0604030f030e0d030e01080f0103020915011202030903090a15080c09030f07 80
    0x3c4003200c0600016401011800d0601c4006444010f02400031b074103000c006c0001072011442241202c2074401525001c0c03000b56915100c0f0650031205030342d900c4040d402c0200d41c0300014424400d0f50100e580003009180d900300240c41c1907545500c0010103541034068110400417220481009260180c082c42c0800303281003469015001380903043c20114400d207000c100344080c42e070b071007205242c010702c46550101c607849440c9003506084218507481001401807924a121001c4003061940c03440c48001002d0010050714441d00d5281d41455030080d82c0b14406100520104451400c02c8171a24824203107881800c40b81400584807030151102100012802061509207503849845590801c00006100405504503030001d0403803c0010b0000e00310701316a00009420b07a2241c017640c809422540030840d664100480700c0d980b030358407240c01240600502007000401c0d1780011601e030285581d654610368580c80340c40910320954412128158503110348138040c84000400e10440000303049045c5883c1c003024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 607250494 1250 607249244 607249267
    0x1802030d080c09060d021b010b12070f06080709030b1003031d0d030e03070b0318070e0c0906161a01151d0909070b0301170105180a0f140d0203 63
    0x28540003220341004200d030188030403204003000703480e4040412074035551a15540380700c2100901501e000e0f01e41c0c209a84081c0c044244045d40701000b401401c0d01da80c0380000ca080d01807541c07801c217845608000700300b6070001c000075446003100a070841c5862900e600201e071740b0740321a072072504140d800498078a400b0000300b08044e0450040d505400c264010344040d18581c4002941003441980e0207401e1020301202c4404550b018012a0301400355211940e0704c038282029003403410082c1c1d01c0f0306622842400004281440d071190744900c107a000e00803541c80c0c01424000d102054100304040703855803003a41404000506941c404440640c10380b1800e0174a5898601080300350307500b000c012801e1103020100001c000d00481c1302c245c110318066075104600e4071801d01d001d01d030440ba64420450444040004140028001d0480140301d4101000340550f4580300c0981c04030b06699800380703071240d00c4a050500090780343c0110456141c09030004208200d50030028a0401c20750041c01c2d070041e0000a41e00b030080c2d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 607251744 1250 607250494 607250503
    0x2190b12060108060d110613180f0e0303131109070302070201030b09090709051f060908010e0c0901140f03030c030a1b0b1b04050a0308042606010b07110301180203 72
    0x1d9003d00c0c042031103040000c00b04a40f000c01c2074020b000e0105445911000740c40b800b040b6010340d0403608088003501e0344d681c3c2903a9804801008048458140880598660942e005400101d440d10703020f145591641e200003c410030383d65004a0b90a901e5191040a5964000c1500e125111544005d070703664003107100041c111481f12001c544030700e8811040c080c00d4500080c0c01c000343d0302e10300d5001600c0d0315000940310007d00c03903403801506181800004995541e0005107402100d42110003445142d68403144903442d10030081e40d05800800410040101c10301003448404c0080c40a010202180d8040300480d041d50322510140207035500014004d00c0e0540d1000c1c031003401094085514056091554401e44e450030003078402200e00c0301041c040419240524121030081100500004480d5030ba450400c080340c10511030300c64200c80d038003c044080680c00e51500000d0807118054a5203a00740100c0320749503000484180c0340f6090580544217152024414440801c180c0490071010038154810180303007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 607252994 1250 607251744 607251751
    0xb070b0c0d06090c030507030b181f09060f030203070b0306010212180415050a170309041508060f01031a04030c03050a0c061d01050601050a0203190c060c031a061608030402190b12 79
    0x3500181c540d0396074080d11700f404290000401c0d001d00080c9410b549100bc50042607810001406191503000151005115140d8044a1080d01500e640ca680c82c4140c0081d808100c0c1c203a80982c00480b4000c00744242c50000704060034681e004034483c42c14081c0414100c1d1300160a402481c1e000702c0b018031180c40c03c01c90340e200608801012450088041c8602600d03402802d42c168061030701c4182d80c80e180d44a031401500507200d58021030b000c03440d051000d185da4107001c2c0300c15100c40090940285c00c41c5000140c0341d10560300342e1210420000b00e590210785603071046940390108060300c240400062070b03900a50780413042c00066413180310440413509003100c1005e8080c0c1e052000402c1206201d40c0c000c41a1980345c82110080c00402d41c4280058603503030782c20140240800c0ca4040303601c00c6240c0540c02000e8003a90300170a286488503c1d0107100786845281b03010a440202c4a440c800015007060007158054800340444d80d01d400c820039000307030381d26407038200744088640130682c58000882c00310215070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 607254244 1250 607252994 607252999
    0x20618031c090507053d0828060305100c050909221505040b150d060522030203030406050a0504240e0f0c0a0b070b0c0d06090c030507030b 61
    0x500a600d0607454400e101c1080305059207500c80e52034a0600405006900c0104000b0302909000c00c01c104600c0040c0030600b0014520074204030020380c1042c420391b90304200c1401d6480c0c1100030f40711903144110312542e21141781c100381800c1310401c0a428040c0036a900461044c0000d00324a10108001317404d0b50b414981a0080100600904132540e07035142525402014483c44201d083e07200c800511030301000c030340018050301040548541d010754141d000d58801c0f406102c5400c2c10382c480c4130b030007004450030f0a05203510007490101b18001c030349158400c0b60000040c424080f000040c000ca4a84031070100c032800d401580022041009001507401070950000d0110020059450031b581c8903031408038190a4081d40030518241d40c0e0501e4401d50040010700c604404880c44c2103da040d000da90b500049030841d001e084549400130703000c408041510311095100452882ca940c490881c6061500444042c8803e82d4440d0400680b1100c14407907070010b91103a94000c241458214006815580140362250 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 607255494 1250 607254244 607254247
    0x152c06090624090106050702240a0f0c0f050106030b01140a06080c120f09010b01020613030809030f04081b0117040b0a090803010f080c0a150f0302040305010c02061803 74
    0x195500030590075400500d40c0100148800150202d90928620051803500140c548001140181d0080c01420f20309100f00c4811021b010310381c0034010920307944000780c4220748043c818440e495000c0e5140101e00c086618090015041648511600580c960002e032116590303803d05005000344441c2c0b0501510711000e095481001c00008200502080c1c8100000c01c80090041070b04020702404540c1c109440040559141c106800410300f502002c0d1a00000c940c40c04240e204194008115a0310030490303012001000e007010b840079240d505000b4007070400b07800b00b001301e1900c2c504503002a101401d600d400910782e1500c1d000300b1407100b01c1d568221506101c07502c0d15014507503101c4608682d00c560302041c0b22000d9221983d2040141402d880f0003402d0160200000c140d520f507a8031300a0888422008413160318043c00c0502180c040140141803501c8445a0301c001d000c0e0268505100040451900618043d52900d40600311400240c045005812403030038400889080160b503901e08100f44082c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 607256744 1250 607255494 607255501
    0xb011107030c05010c03110109050d09060f05040515120a050403030c0c05100e030409021c0c030b1503060102030d14040c050a0b31151101020a0c02010c152c06 70
    0x24205203492088504124010385c100741010702c5100b200110890040c000c2c0800801e41c80c003075495180d21180e1900103104042d0025400d841113400e211904402c0e1545031600f0b052409101c40d000310840180451a41006000c800514800100c0c2c4200b2840c00001210b04042c41d001341500c0d9099401c104000382c4c1e07481d800205001103170030000f95003480d2001440b40919084d00342540299806407859520124105501c5100585540921004004104562003011000b90226003400649941203016500c002e5001000d00d001103801140500440c0e01f868041c0011400340e07180c000340301d64100010380c20301041088003604500600b108a42c6c410513030b0300340208664607000b20420926400409003070b00301e02c224000e10040d448181d010041c020680c440103107510207800d565070400020380e4103410614042062081e18110081e940d02d4000d4118241c00468111482c8041500c007121090805050b000d80b138070605004d403000000f0301780481c10141caa15003510080c0e001500702d0b001801003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 607257994 1250 607256744 607256753
    0x20904090512030103200f04090f1205070606080f030708210a0c0e0111062e06050405120706170604021b0705100c02030c060c120f072907030e031c0b01110703 70
    0x140d01e4041b03048e9070000300e10096081c4000084581c20000d000c00007503401c3c0d40c0e80240d0040007064443d01407101030110a5542c0503981e568080d03260070710ba5941080c440703040044ca018009113070140f91800401d8041e46840d0000780b900d142640c4600b2803c0d9921828178240e5005500e5071b2800d0b034242080d9071140c2c2e2030109a626404005e01210758054129485000b09400c00360a030741c40312074000350b040e403d5101d02024140c1d038800d006007403007003910301135107e4203090004582041c0c03400e59549148685180b18400c2c0d801030082d2070541e01c15002c0c007001001c000c3d21002c4903c0709a00c81d0041c15000d01d044180204081c450180ad010030013541d64441c00758038005106124a103055903201e030740c0d2510282007814100c0b080420382da490300018400310350f900200060a1680c1c02440c0384c429403200d40d011b442e0402d19900e0140004108800040c44150280e40900411514441aa45004000c540c04500c044180007010300240c0d46000c10521964440c01518410f00c42d48000e0080d241191034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 607259244 1250 607257994 607258009
    0x10c0201090306050c07050f010e07051909050601050f0a020c1003200a0318030908060f1e041b030f0c050d08040314101d062802090409051203010320 66
    0x6050f054588010aa82c403101c001250341040e0801c040d02d8081c100c0c1d01e01e842c060100b80906696501ca07603070303021426260524154010082d002c031800307040c0e407a290800026010090940b0305020040c0103400508910500402025a9030f0303020380400000c1300204841d0010102e001e5040610b44080041c5000310342d240192070709004400142c994484400c01c6000d4600f4261860001c920483c1c80410983c011002c0820f0310b02c8241071324074030b03030300d402440c1c504080864680ca50300e102101014030000b002d9442d6600b00b0b008501c03405d980500780301d0118140c4182da000712601031001c00c0003c00d1003c1110350001a0008864400f0343d0046e6880e461001d00840c00060329090305429002c1460a00304510003403c51920010b100b211180c1c400d0600401d001c0c0000701c818040c00f4000b507000b000d418500440e0300703c151556104c000e12414000002e402803090940c00c140d807a02180c3c00706504100c241107007002400000d03600d40c1189021f034a604600c180f181c002c1400010a5601a0307601310 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 607260494 1250 607259244 607259249
    0x10b09010c11151c0509010227030f01020c100e070602030316030b1507051005100b0c0a1b030309090203060105030f1e010b3a090503190207060806010c020109 70
    0x1410740b818032074203400152800b00003054000181d000081d9581030b00d511900440d0107000025801c102030781e41c00710b6036803d034464410682c0e581164401c4603200a05a007007050b01c101c1c0b01400b1500b6101780d01c0001800c90b40040c150190f0f81d400b090002038200300500179003800d0b118210280010601e40300d0b01941d04c1c04083c045003040c50050542ca040a88258048001020000c0c0950402460040d0440e120742c014201542c0d58065401d50175510200350083d81d00440d0480c0039002064030f88083c000481e0000c08441000740510380d4200c011400c440112030101080302c5443c0703085455450701130301d900020f9002e1030340c1500501c200b0240d82c1e04803094030380c05904c50500c0f001c6079a51118205100c011121100b4002407004000319100c1503010190400030303608166164100f01c0d240c1d0b40700490007214208000040500000d603441000c1703401440045214a00302d904100c58122110086041a80d291005034040c0300c040280b40d501c003d040790403100030b0825807008080c0e500003c03c10403450 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 607261744 1250 607260494 607260503
    0xa08071d060111030712122a110106030b06030607080114101b050c040f0207020f1302040509130b18031e0d0c05031005090601080406150b04030f0b010b09010c 70
    0x140010740c40c2d034015618125018200c4060b02d0395804c41d46014400165020030020009803901520340180c141c51140d102d00544911148040381c0d8034041250704038071861804000c000e80c030090a070700d8031000d0042402640c0b003050030702c42c0741c9030840038545014070040030340003004440001002a1201e084840f0b00e240c50641e40129070442041c020350300403102c5a4003604e11b40f00780c03121406004002c00c1200c100b44040b20300303101c0000503030b12a0313080e030046c11006035100385858240741140c680010210100d00060b44094101903407040043c0000a08032501e40d140fa00d0740784d8a804008124007455805007401640031340c8801d058032003c1e940c0c028898204481c56400c405850080c01d10416914181c2d0003d0017032201ca0048840242140c01c1507511440c44901286c0114051403c030b858144150010b96a0203e182e440ea1552000303445025007804000500242c0803aa141d42c000042000e1400791101c00306143e16481d0407031a80d04140d00402c0c1900050001c80d041d40e0b444498a03680c01d410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 607262994 1250 607261744 607261799
    0x13020d2003220804090c0f02120a030b240d11190507030201060305030a0c170c0d081815060906010c020a051201271406070c200405070207050a0807 65
    0x10181d800c2030620442d000a40600004035001461180d180c1181240982d1681d0303603c0c0700d2440c034a06a0b07507910900129643d1050600046807018400da00c1070ba0034000080108a0526280c181c1c800200c40c0209442c90460f07000038030103501e02e11402446401d0828402003890700700d0420000329030034007203541041040000291001418402d4014102943d00442600c0c0d41d449440da02900701c08180d4000ca40c40ea0b60414007103403980d054802c0d12804070110300681a81e1050340404ca80142004045c1c0c0745a0b500c00220192840c2d081214400300c4039203200c0d2250b141440c40070003641041c018031444c1003140040803400140c5038210304000300d80c41a140408001c1c0d1074040c0c1405040d41c8441000c4425049018012011007409107182d0a40590710031755140701003240064503580211910004628a103035610001031f0818401c0085800017503170101640c1003600040d06a8205071002c50069000301000c1c012483c0511284005210a00082c5000b40c604505044003d0151040d003054900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 607264244 1250 607262994 607263031
    0x503060103030f0e03070e01150306080c0103020903030403320604410d09060206070503010521060a3c0f1103090d03050a0519050703020913020d2003 66
    0x280415078060380c00a05a0b06c225803a219a0036901000744641000d040a0007802e0804a00034030541c02038520301000b424803c110b0200540280d8009000b05405210412000010035641d40940290202803071000d07240580140d0038031050981c4151111003500030905100024030702c900b08200c5803140091003107484207134031031a240c0b824140e0750b68a2400b1040c07031040c40c15000416040c0e0194041c0d21010100c5489000c126650b607005c840e6440071071810401400503142003045000003945400f0080840c0040303510386401c008041d0b0b150f8808a40300c65640c001d03114107070307a26080b03e4030b00049241c000003002050104814000d070f081c5865a82d03220080700900c126007102c8030b0b904252440580da0308000c0c00840e80d94840c0c5c0314120001e80380001055a40361540a504d0003160203600d403800c85001d20301100b0051002400003c1815820002c1c907000c1e0b01d480c00b1079182c0034440307c80162214004c400034029a5801480e100c0c000d0715060010302194440340c03d0340d0f0058079074407036600e5454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 607265494 1250 607264244 607264247
    0x14010f0c06060906030809030105070f02491e0c0f06060f030b1509010b040308032a09011106040c0314190609050f0c151620010807090503060103030f 66
    0x1820f800000405040c600301005004400f0010b243d4a10b080e03008001550303c0d0314045031503042031002d000060300720000005091030010507001c4008000d42981c11241c42070f0b5044149050ba00f081d88480c00c803000f013000d2100c0e4001c0031071040241d20744509054141d0394000108040c4000074001c0440440300294018400c00e640024003414481e12021521601c0b4144024050340c101d900401000042810712164101000c246040704d01ca45003a509080c259628010a600010a030441e001300002c48003041200051400c41419240b00540e0b590780c1d110400107003180906038440c0700310f61241061100003040d60510300d00700e0360044c2c1e07528182091605058200349440b03140307280b4280c50b0740314901803100075030295104908c560204c0b0660149000d540d5102c01452001d82d030b110011004070f610b00c0c0304103401020a6000c00b54031044840072075035413000c210030070340314100b02c10303114404000c403075821030a6190080c2040c2410b021041c60000060b603070300c80501008003009500c03a404180c96 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 607266744 1250 607265494 607265501
    0x303080906010e070f2102040e22020d02060d06061e05040f0303030b0a0308030712181a06031e07140108011a0901030b0d050a03031b021504030c0f030e03010614010f0c06 75
    0x4200020a0740246c5c112450070007a4010740641d807036200d2420302040d07180e00842c081e010a00590790400404002c03540800c08510074000050740c1241d0108500c21340e1003440d200b00005403003d62112890b0704482c180781c802d0201274090000510004106c18080003c100d1050b1040742e6041c5004680b4401c02c9010400c242034640c4003c0c1004404024411007941194003140000c00759181002040355031011030b6035900c01400007034540231100005136604090b04020590101c0090116018414598450300c0070418101e10300c007440c0c014900602c00f00c0400c05820b19044c10034a480c00c51941002202c60000501641d03040c001800011083e01d1071340242c200300d0b04070344028200003640c612400c00c60740350560f074002280041e10f045003403403032800d80c64158680124661f00a00151240c01c045640e0740e02e0180040d400c2c4041c01c004103000500c0c000781d5050300d511036550102d0003008081418250fa0b40c0ba04020311055102d50a4149a607206000f07140c44915803800b121403507c10304084004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 607267994 1250 607266744 607266767
    0x1061a090a0314030a120c081305010e0f0604051504081209011118010f021605090405150915010b07080706020d1d010c120608071217130303080906010e070f 69
    0x181c21402c0f0652500920100140c043c00e4040d4980180c00001c101d07040f0102c0c0c0d403480c04c65021544c00d8021441c0551350300031a01c0700314810000000c00e16104507001d45010880c4404049035448201000304005007889072100e080020740f440100c07400d059880300c031030f4010b0841c2d01c0514a514000214521401d4010448840e80f0100381070b9504049800040781074400003036140030900b40c00312020f2191002840c0c422507011303940ba100d1071504240820a015030054020b550504c0741140144c807107400c80003c40e0180c08040020000000100c2c00b4090040051b40854002c40c0140714940102d5902c008540751168000d40c01a940c250006c004001841e00b4100c7c10407000342000601421041540020040c0c41c0d00c0d11110071080c0003e482c2e800303072103045c02480c1050f084000200140c0c15220420f112040c1300e12000c2841c908402038035a81900184804403000551000400c10f25400c5803540383c12409e1400980115030600780b00000710600078000c6400c004580e4074000307500740309840981c0f1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 607269244 1250 607267994 607268003
    0x80a06180c2d0617071d01030b0307080d030902100206040203060703050601170a020c0705040203040804060309020a0b160b070503130b0c040e191d0d0c08040b03190e01061a090a03 79
    0x24181c0f1410f006000800a002c48102000a6000700d0a218012002050b4841e000c40d80740d0b0500e903603000110007031301c1c10080150b01885400f00100d40c001e42400100c10207003c03554005502c4146004120610f18441e801c0c0c020340d089001071101607140810328030b500c242242004034050701c50800481d6131241c0060801031080c00a0f0a110180119030010418142c2620494041940b11000c01c001c81c0b00640e4000c1c106542080100007007402070f00724a05880c002000142d480c0e075100050703c01d07940294030340d6042405200f880010000c492080700d400004a1410303030704614280d00004200741c40002c0250091074000300007450380c031041c42143c004c0c4c01c440c0700baa061410810b0841c07a0188005042002c00ba040016040035881000312036005d5854580c01000c2d2040081c0c1c1c10350305c3c210f4800b0195001c003020403000c200e0342d9160000314011264108040c401040d0001514121500210305107a1039051050412890152140307403811580080c0515544200550004511b040c26510041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 607270494 1250 607269244 607269329
    0x1306090b0a0522060e01021c1b0c080d0908090301020f04030605061504181d061902160605180a030c1b30050601080a06180c 55
    0x1020000c000110038000c81d072608060000e0b446840041d05004001c904103400805542c5a05011a4442d0040700107025001c0006103000c0c1350010445c1046815012001c846032510503005c40030b14040e0784101c80f07040e20320f8803543c81451580c1e098654802d84510056080c3c0303590501d0240182c50f411107009840050086585042200d0040e4258005d84000da03000d0749442e00180e00d509040500c030a055002d241c0c51841c00e400d045a80c082c141000c22502400c6648007040c802d520461061003402c3d407401c0b0000c04c4249004a640140c00066014000f1a40d00600240c0c2d010906410090036003607200d0780208407070b500c4035100590100560784025a030300c1284004020305411850121b00391340243c50f240000c40d03d201100032100c0540c032401c0880243c00c0e007400450b0101c055520b200140c0c00c03051030401829074540529040003a00404450742110003410104005803041090401410700b45400c0c05a490700c07480040d0345544034100f0100303881007244a001010002e0b050180f804810800c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 607271744 1250 607270494 607270511
    0xd111009031401110a0810030b10080c031b040c020a022e050309030901111f050601021011071119091b0804050a021c20010216060f081306 61
    0x10000d255a210595282c094500c0c084098801805510646103070490130034170f4681c101d082105d03c034100a00d0480c2000604c0400300c002403107280040e01038543c076080005224181810a4206494a8000da00c00d5102941980130b4040d9901e4414074610100d0b800104148440420380c20900d00c41c000075401103a0344210500306514400311421304c20340c45030b00d1007080c8a1034429140352100340c40c030075400c0c0c0c030510000c03074550320840d1030440602d003001c00ea4860f0009001151541034000030449042e544a20400516590402038002040700030b0000380012900310305108014483c0500150510710810b0003a072540c0c84059404101c507142008403515966101d18035801802d4030f041c80c8101d516040c22001985200705000d9000f20381010292803500041d03400c01412854104198040502039040a40424610142850030140c4e100c58070340441441400281020610008200103054945040c080f556201408441e0044039051410302c984449084040c049107200000300600c0c141740c8407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 607272994 1250 607271744 607271747
    0x3080315030a0609050708030f160c030b04030c030e0a06050708090301150803070c0b0c060609272107120e0319051e030a050922140f0a020307050301050d1110 70
    0x4400d402c3c005e0041e200025201e00045071284182d100d40142c4040501070310001c840c0015451080300d10400030440190b6032961402c1e12032404031030650109070302d9040c4805150704a2480301451000301e900d203800303906101000d0b09a0203a400b01a003110750110b034450158a0075840104881052010303850070b5036881800e599643d00400080781c0c2c9200d910000601d81b000c010544010201c1240508403550f503c206100204500401d007001e4002400ca444080e1400015040c04090103e8081d01c030510b82c1c26111134400030012603110110104000104c04608800c80c6903410307040c41d140000c0d101540a00280c40c00d055000070140f001d00045603001048400200750030002108000d40503001c0d005d01e03a444d241c0c00b43d000c0e2000800c04c01c001c048140e01d00352481c0d50b0300c00d4261110441d001048503480c0d04072102c40700052a090029410302c807000044203409540310590a40a500c4c615104d01d004055002c1840b5a500400910200c9801c100c0c80440b142d4020310080c2003411100c000000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 607274244 1250 607272994 607273001
    0x30a0b030304170c030a020132213907240e0c061c0609020309031c050618040f06051f06020c0306060f0319060b0907030507020703080315030a06 64
    0x100f80a2040c1c1d00007500030b00b404911014503c1e0161540d03048030b10f0030089508000041401481c030040402c952521041f80b01002c0c0140405950b031592007180c11003072042900e00050a0071615088010760f0b0754810b10b07040420f813000408000314522550740841d4403800d0f40120b901c014140c0d070203941c04131540c11804210002d50340d1104024807490b014038541c50f403541203000540b03800c400200023140c02002c002501e644400290300002a51079960103041040360030545424446400000350f040c81948004440300301c15882d031804100342d00b01100081e101c02d8070f411010800861010009041c8440b00303410070640e82d04a0000e12580c54001421020003a030601a56942c96460784d010950303500c0040c0c400031550f40600104010b40380d8000b00420100c04001003685881050301e0709064003518080e85281910640c400700752285c4160403c2044a8010701903002c06141c282085905c41e0b00040500c101c0ea00400000d64a46911651002d0481c00c0d000507070700341c4115000201008190760 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 607275494 1250 607274244 607274279
    0x703030b0d0c1703070c0906060305071409091b19020d09140d06110406020127050a06090203010b0a0602030c060a0204060f0e180408070c2108030a0b030304 69
    0x1942006908410010440082900745001e0410301c8a01000e100f04240c801c0500c80c8070b040c0e403044038240010780e070750b41400c5440c0742c10958a01c1c1d21645d082000907058006d03c6d0300501c05d418980d0b0110300da502e41c45010f000300035400344240502e0020031499a00201c014640b400c01c074111325600c40018030086a1100285c2c2500010312800d11ba01080c18480d11060064801612104403003240c8481006840000e00c8003c1e81c41ea561108c48030103c07400c200c0180700800d5a500085400d9516400c0145200c0100540003081448402084c1c000364003c192055036070b6022a00040c1300045001090040c2082c001c0b039034200441440c04a642500040508003403c07040044984950f00c41043d0740c01d070300651080c04081032a0b0b0540c158501e0141c03024449001e809012015141004a0705031444c800503142500c59050018071203041c8802c08d20411701902c000b06030002001e64000550380030000290001c1c04440010001c1940001e0715003002445110040449840e5a00e4a4050180d00d803000c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 607276744 1250 607275494 607275497
    0xf130b040816050603090a0303090c0509011d0703180b0a14151c21051c020405040e1f0e031303060b011106060603060405040303021e0a0210051003020d080c010c050703 74
    0x40000f4803450104200d07486440b14001511200b140c683d416000fa1071109001c480410440c00046595150040507600034106072442d0315500640950300c4070703255005072400003018140b40303455412525000c3c5d4000515407049000000b07596660b207032402022038210301c0c410140c02c0020701640b807440602d030b41c0c01c155040300c4285141c0c00b4101d190b03c8810072034000404140209030145081b034580044114640010304045140032031b00b0701107401000300c2c03141140c80b0070b0380402d060205041500c0703052200580c6000808100085115800d8440780700380003a1300713803621003a01ea50b0403802070003655540d01051340c200c0c11700341d22445e01502070603210b00c405002607226030f42601c001c080002c0c51802520301a040c6032442e00c5807014071029203001401a028180c08028201840c110003403070148042c41042c0c000e46070800003100034200024140c504880714100f03000c1c0110030005140341c004030b0f0741c12202405541e16900d032509942c09003c98011065181a642240c0641c010b0020001c0c00e109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 607277994 1250 607276744 607276783
    0x609080309010b09100b030601050f04080a030e0402030702060a0f0605030105152b080918040b0a0e010b06040b090114120f060405041a04020a0b0a0c0b0705040b0f130b0408 76
    0x5030041c0034140a045450001c590785170711040200c190000021504404107150851803d011520103590560080d4040440b5a010400f03070707424507038000000302082c00e040b40c05500d10b0a001f00000c1d03561201520070000b95030b848402d8180f84601d0f9000340011700d0064001d00842c5880c2c02c91720f100c10780700c3d0121809100021034480d02450034241e00e000703030552000d08850030490381d290170074260000009640c010149903920703130f04d01d6090380c0c009103c2c603c5010406094074250101105540316260110100d81c10150a2101503440703105a03029502d4044081da15104254012a105001400034110101d40007900e12007210503010858418507440c03a40080303940f1502c05000449404881c007802440c1c1200d1444607445e002611544c00a00042451040546800350105c846c1d000d011a10f0204888001c1101000f208981156111800c0d051050900703140c42d40d0507106104009880a801700f002030a20300c0f0384e142050400c05003032001c5140b92600c3c0c0715514a5a40c8030480c5428104480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 607279244 1250 607277994 607278011
    0x180a0b2a070803100314011b020303060a050d050a060c020d0f14031801110c0a02030606090906130515010906080114250314042906030304140d060908030901 69
    0x10103040849100442094041c5000115101c00e0810b030000351400416040c614800404500c0c8000e8688100d4100ca00004850211000d402c030241502850241503403c1030082102030369880d0300c4001202c50585201680405500e0014103040b6800c50081405140494284161b9800198031411140f640c88411000000050580d90001103803000d040e10501000050110400d0070784081506403c42c00108001090499100d81c98003c0740115000754004601c5400b5441d080045507007204050300c0036910742c10324a02c0d09488850040c99040808100c94000c001c00000704006042c0785440d4070b078241156120082c0001800c080e10a480c41e031740c2449082540c006047c484035005180814000c411003841c03a074009a2402828600403d141c1c0c2c4000405e600b030084206203220380d101e100510301c088111071075805c100c112006495a1b0280f0101000402d84001049509807172641011042850250b0006641e015a05c1d00003448a402c00309031404001c4007030082e600840302c802c002d119500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 607280494 1250 607279244 607279291
    0xc031502180103091104060801150e0c0304060b03240106080702011a040b040f090b160504060e01030902220e0613030e04050a0b0604030f0314030c0d05180a0b 70
    0x242601440825001400d010707440d0301940c00708540b28862859040c15018440000307085542551158545035100e002c10450600d540700320074098a95a01e00305038174101115030071458000103000900a95503107400010980d420400006010702000c01001e0b051000c19039804034150a01c551400f1400c1400410070840c01801110054a400460800441841230400c000740620b020401c2d080340d42e480d50300e9800d45080c090010003a001d000450580d090010703031855261100840351041043c14071041c0400e562082c05403001c00c209180c0441d00c11600e000240c1d140c0184041c140c03018904420308006014150419200048503009803865640d583e4044200d1191481c40213000882e1144c00300c4840ca050761110b50070a80e01507001a1103000c01010403079a50054100340c9910301e80090000426a1005c070f030b03420b1400c80c2800142541001906c06035980a182c1607680000c1e160000240396203004e01616040842550032030307000003000d060a088100d0169116440300c01c5c541080c4c403150 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 607281744 1250 607280494 607280497
    0x115020d030b010f08060a08030c0a0c05040c09350a120206010518100f0f08070b09091810021c0b0906010503010b0c0a1704140d050c011103160c031502 67
    0x240030684503c454130391a21411954950020610b660080c01d00f03401140f200c004002801c1e03003c18602c0141542819414060768076052076011510503801c04410f8115180d01a043c1c03001ca4500380c4004c0c907e840c0b4044c0c818142d01c10030400c41032044460307014421a10340022000b801d00c0c0284a8405806000001240c4645090042c0c0e070b0070400340f1403850f0708003041c03000f050b90240e41805110140d0303843e00032a042d000401c0d8401103c007a0b240c1402c0c00b1240c0103014420080401510b038918065145012400b003030030007050148050714110b414100150f05002800c038550006034110740c0c5002d08498550303850728000b83d21070107a00c0c0030540102130a055480b41d0182c0f605031100c0d81140e192010240c9160301051007203a181c01000e101c080042c2c10010701550310000e0700582922182481001007001c0b403500840c0d8410a034a030300d561302089003c213035040b1000007840c0011035954500b00c65880c0d44a401e50610580b49095480400e00c2007101008003900e20940c202194113448d0050305069 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 607282994 1250 607281744 607281761
    0xd0c17010f060c0c05120703020306011d040f261c0908030408070f0c091d01150635090c011106010e071106240a0812071a0115020d03 59
    0x10075a003003401d014640c0a182044000b5201e0700c03504190325121408203800c0c800700700c04400d0980c002d0006008520b814040c1901420204440c151092480d400710490800f010307002070800080445c480c014007405403001e080c1c480ba10000207a50720b6680603207071519444690003c207050407181003800148914020f01d00a96041032030a030031900c1d1500c071070700c240c0d10010045a03111030b505030040001d00313040180401007101e42c0001034120440b24400f07111041c040400a65a4541403481010041c4002c00c041074130190300d410203110503104207440780e40013012816480c41e92040400c41102401034204ca00c1501e89005841400c0e0b5000015104a61541851003007900450010b20100d04901e01d0598050103503d083c0c21090010844903081c01c400369182e00d88984040001040e03500c641003034003000070040d0340c54241280752140154039540028a802803480c80014581c0030b00000c000070311071041208040242c9540c0d10410801c4840341c1c08041c9026009094010b5203040c001e00c03954a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 607284244 1250 607282994 607283009
    0x30302060103060506030a0f06020c07060c0203060f070e041109120c060301091107080a0215010e0c0a110a1b06020d0e0a060e03010f02030702150105030607020d0c050109080d0c1701 80
    0x2416421943ca400141400401e010742510a103100d034008184108011030180340500c01c01a503c0321142101030030f08000b6008078040c01841c030f040c0001614001103003544420702d00404401915000d5003190604020300b081548030f030829450402140410b0014208484121103084a4a01404031141c032003101c04841540b0100910041021511075080300d0400a010a082c1e403a001042da106101a00f058010f480140c0c0322101c6050081d2842071040d015200c0d0301142c529514103070100d811988138044008007008600e112000251008000c0302031195442044441c1004010841922913101da108100051182034400d00c003180c0200000b40c02d908010b81108881c43c100b48080c0d0711543c0d0010000c0c2c240d960b412181305024580d10265008032500d1b405080c5042c1c503d91410040001a04400c0c4260009400c0c408096000200260701c1c1c1c05034200800f80c038400f818010b0041c0110f200140c00310200043c1502c240007590300144080e0300d01e40301d80300002101741760102210400d006040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 607285494 1250 607284244 607284253
    0x91810150302010f0201020c0105070908100e03030610090b070813140a0905041a0c030a0e060c04060c030c05030a0203030604050115020c28080703061404120f0519090618030302 78
    0x2d54458480700c0e07030003110f03030001616007218140040d08407402102d00d040040c203040070900114509020000911844070300070700050fa00d00000035124071026141e18450303104021000700e01402101c401006094100c0784a4032000c0398145050036078003203100c079004120450030120f40d041c0707521010422180702414040a00c0d05104c44070000744806032043d2010800b203950740450b04500b10f0003d210b190343c281401e8036400d14030600001c0d00c0c031503840400c590700100104410291900305030780c00c4030700740d145c11140c0c03c565040a490f00302200d04064140d000000303107040526000030047d4064070f4151400c001c01d0382c0c4c0720480e00c2c2d1407845441000050704031550403603071460440c400004030744641c1022025026202d40044c1101c04550140506800ca11030030421700000340304003d00304034050440c40701407405565004d10303220050540c4d024000245000080984100203549103407024903003440c41c2022859014000c1c02c20f511524001500e004080b01d0b040e58000c58401c105c0c0d51680050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 607286744 1250 607285494 607285499
    0xe01120204020a0509100f020616050f1e0703091e0303121a131a01080f040b09010213060206150619030e0102070c0303090f090b1503090c09181015 65
    0x2002e580140b192108203c424803084849584500100d003050741c1a03191001d14036808040039082c58001040d880900043c840300595141c0c1100413980f540701300101a6030380e0185521440d281044240400050010120300300c405c26030002d10301d0f03040d200f400201e040365014410075002d504041e400010002031030900103c0340b039520354100072007100305002c0550640442030040f031461a07405801c21190368032007201e010008a200040000381400703280000107860141207102c8003100c0900300900c016498000a0040c1e502036040d00c40d26000486074018280d030f01e12000303560791421364030303000d01102c40b6004a0091400c0c400316894000c500d10350b8101c20314400d000780c00500710300e0101d1900303540800207800040c401c0d603407130006544661078500b02e072428600c00310101040d40d00405251032902002c4005541c0c0d5442c011044100c00d100c4942d660345013413106007400703241d5690303a030131020a200303025088400703041619842d00e24400302d40c031102106840300e081d64411400b01e04000040c4070103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 607287994 1250 607286744 607286749
    0xf1c02040501050a0e011e02010f0509030928090510030b0915070c0503130b121f03060b0402090d05011a01021506060f07120302070606050603060f0f0406170a0209010e011202 77
    0x81703500c10380c05041c0303861240b014070098075403918007445100c01070750b403805100841040781c4212500010100c4c02107007840d1014000c200344505003c00e01032800240c2d4944544145060680c0002d402618001d2055081c68030424009100c1070000b152402100000200106000602500c107580452100500f584a400068a00a052403015070700b41c00204658000842c0100301e2400a110b400e00281c0c3d2003c00e08218022030307002500c50b000d070041030803500c1902c0014801c5001641c0d0080000102c45030848002402407243c15082c80c2c020102c0400141400030651007411014400080100303180080b100498403034016030782c203d00210024000c110281040d5000d440d035040341505052410318113888684502280c1c401201c0080c1d000120101000428000c800003402d040c1c13001801c6003003d00c0001d241c003a41560050295008003010040741c1d03071f960030250040c4100306601140100074102103481e8034010344140e00030007550000040920013440014101c824801400d01c001c404c1c1c0d400c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 607289244 1250 607287994 607288007
    0xe031b0609150f040504050c0c060c03070903060f050105030607030608070b030402010c020603360303060f010324031703040203030a0518100f080c04080a060906020c030f1c02040501050a 82
    0x30926088045000b68103054050038000304200d000281c1031903100c528010800041d140d000380b001e00441810b1194026801c400540240c100041000c02503c950303d4402c00c8500c0e088a61000d0001d0342002c0f486440010030351f0015050310016820354170b5507034800c0c0702601640c07802e2040c402c11303034090f47c41007044140d070704042c540251052400305034081e4683c00042c000d40081c1c031090220000c0c21031054055901d81c00c0b201c1c4401c85e01c5980301a0119848403242c91340002041c0e0340c0a20088960401541e10030b6120100c0300750040240b50003101c42d0f00c80e03008010003900044440d508190074590000c03a01c4002e881c8500e50040040d07203410030340d40c0122640d80042110220344902c3d007900d40d015640d010040c07a8502c850b5584c4044465880000030b0942c4000340082e000408100300a0049110208440b050144c004e100403606411381d1034914000d1103440b00180d080d010200303c00045032004c5004003005410b0045070103010241110707d004a1040380716460115108001500c0c0083c011003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 607290494 1250 607289244 607289257
    0x30702120102091203270a0603180c080106050405061903020112090203010c1d092707080609060106140c030406030e0a021f0210064b0302010e031b06 66
    0x40c00075040a0016011500d4001c01c00c03444021a000411801c0504039062413075038070940610013030403000700004041009079a05000d13000070541c4031064101040c20460b08960895409249204856503079003005000b04101d0181034881c9040c00d010075418541558810b21240d500183c0100c5c03e45541d00669030740c010f15150070a4103484490603030159600788120407802c4129292205410849410400500e601c1000340d032040c1c03448001e00c000c1c1c80394052007802171038034040000500b0607203215051512003c0d51182c0b10030700c1600b080110045000c1070590480c1c8075502d60850b0b000c80094001d0032401058581c160550042c8000c000e903520075006a11803031410b9040d903103003a045030081500c900c1544004484c6580381d01022011550400cd030000a800b4403c0800001d8106182c8081800099551501c40d0850441d403010f80003456468540c043d8940b81d026200f140e45518880c400c0f00301d84010307404a48914074205460801042c0f64a00300e00f044840c0306000009810060181c2240 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 607291744 1250 607290494 607290529
    0x706020619021e0d06030b0f16030f11030a150609080d030506010c1b06260a050901060e070f0f1e0c030e100c0606080d051c14010e0a140108030702 65
    0x107103c14007a02031070300c0003041032007004c0d0004a800740c103504250741441c50140c0842e204120707440c100520900701e620302a0142541c0c0c0380106408104454075009090b0070401003d40840000500c0151030f001d03880b21101c0500100d0000010b5a121401e82c4e5032841031040d00c0c0c25820032003e0541e061311a910240d4045c4050420501c1c1e0400c60311400c01303582c10300c13850300d59000000d2020300c5140e41090452026200340225901082b01800e282e0b403201b81c5c054020b43c0d80c592106c012800c903801c01e401010280641007800000c0e4070b42804003c08a13a14107008001198003a0b81449000348107800c2038142c02c00010300d0301c10303c45803808111403c4c54013050035400c1101321041400e49a540e400c5030001c00c0081d40d640c0503031244074181801103500561102c4130603485501800382441c0c000b02540c80040c00c0c0b0b680240c84800811040010348042d25080d81d40201000c00843c050030304004040c0552001c81040042d60405206841d55000a0007107400980c003e000000051a003c0031001c5550002c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 607292994 1250 607291744 607291777
    0x7050a11010c06020a0f0801152a0b0403120b0a03020d0201050d0e07180e010507210e01020304080d150503031e0c061018090c090f0e0607020c03070602061902 70
    0x1a80f1940d04030380010403510001014460403800240e8840750140c007403d80680740000403140242c000d80240c103640c1114100080c01e16901c14070001c0c00301c5289a0340d07000010a00c107031504d031a00500c5104610221070f1454a4449504603900b4041c1d0007030103903070340a4201803515240342c0040d9255008039041450b117035214244906020700a00108004202901101401158070400729090300e040e882040e031140e1410007000b230815402140844034040c000c0340400c3e2808084410f41c0903003408414a5642e6000200780001c100c4000024059100352802c108106007806003c0034041025124aa030300d41e00c03d000758075018001c080b10002400c1644041468140380802c19030070640c0458015114130b920890030080c01c3d5489056098800d074034501040342090540d204102e06107a800750540c040d5840324900100c482650205a10845000413107403a032916500007942c9030030075060140a40202100010300b50300009070580503140c5c1340c4058118100701d016040094000010911440c0075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 607294244 1250 607292994 607293017
    0x903032a1b210409050a1e0b010f0518120f0d0c03031b0905060f07050601080d030e120711012105100f21050a12050406030b0609010203090f150408010b0f0607050a1101 74
    0x8081685100c1d4680700c0c4000c01c41d41d8035023002400032000c0d80801001d100303082240c144200c40b0341030403101e10002101ca4010181c08604014540321490440c1c030514420245000101500310070000101c91099034144005100072064001703a6480024003004122074902c244038503d0304401501c00301000c40c807910304012031901c8051400c442a0320030006504140d2503034160f913030306000341d244d05c0402e2001414095604001440076204903100a0000c07850b50344000300981c4911154021501c100c1c0d0461102c0410401d007000800b03003942d41e00000215810009020103040c40302608035070018a04042c44240d488400c602c40211942c202c4003070081c84881c400103420220000d8820426079105ca841e5410018054103ca20090100384181d07001d0010b08950380e800011036071641420707501000c2485141c0085043d0030f0700780e20841558407012030b0102e0f612105511100185034111703842000e00107007006004441c4604000980035810a0100c032010a03500040580c4510061409410b040c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 607295494 1250 607294244 607294271
    0x51506090f130f02130e060103050f0f09030d020f031008060105030307080c01090b0c0703090f0e0610091701021305040612080a05070b0a0903020d080903032a1b210409050a 76
    0xf40480c803c0c0108031842170b010b02000d283c0440451340b011003803d003007104d0704140760b01440d0023000600090103000983c0c00249861001e00076900f0714004a80190740354510820121800d40044411400c2840c0c40d6100241c10740e000a192390403258007401452401030551510140eaa0003415008401d42d02c440020001810300c02d25684a280318420994640d43c5d28a0010300144440d8000b5465603181103050011f601c0400c030054101b5805c03204c05a40040304503066802031721551000d0816017030410308164107503041d0001d1a481e2100e00004114549074000c0104a8201d80120251980420103e0f40003600460041c42c8008081c1422410130095540c1c600e205502114256915a16101c10004043e010441c11100421b00c0c01e00b0f1b8014988072009a56a0100a22290f20003202602d814250a1100d04072805e1554203540179a84e0380030501c0e54225520f2100402006100341644c142a50710b007a0f802e01c449501c000182c0b0315143c580300396a4003908000c1c200d1881f1551790f50740d400c0c40d00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 607296744 1250 607295494 607295497
    0xd0804060c0f021f090b040302010e131b0f020d1407031404090501030303151203080601050a031103090304170703120e1c060b09010b0a0e09130203030d051506090f130f02 75
    0x203620502c00c4d14588030301c100700240ba00c81164410314009070240b101b400181c0c0c00090500030000255186190485014131100140002000050b02d451070840c41c5c031503559104080f0041c219840c0c08803440745038102403c03140c034042501c504107408410700400000070f20a500c60310790719004440b00d5003050345420b01c10f4129142a0710460202c0d50300d134000d0801600400e4103000404130300002404d402010b49000e00a85402845035040080c0094152080d502913072094108810794401c154903841c0074a61140d0f80e072304c5805005629000755040c100c444100083d0348059a60001041a2058042d01c090750654200329902e980000c40b000581d04218182500d2151319004041c0824404030780010f1003090101a001543e00d958100458540560809640c1350041c1064031040859030303134241c41c42d07014054900000d5142c007000620500030320040e04103a0203140c00040c188010400c100400004d40325170b80300241c10502d4110180d640e0310b0300841240701d19019030400b04180c0c0740911104220b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 607297994 1250 607296744 607296769
    0x90f1b030906100e28060b07082113030305090c060304081e0a09050909010e0d0503010905011203090905070309141015031106070f0f200d0804060c0f02 67
    0xe40d100e9020000a65641904a4001c0c10310340c035402c40905100c116003051456401d60403107510110070010b0a90642640f11b5402001010200e070b071518201d10700680103910040404402d03000d260411008070080d43e4145004161450101a4521480e0780503009444001c0c1844500d0080034400c1c08503448000c015131141c1e1003005256500c1106040e002c3e242901056840c18410050000c1c40082e5009840c517801d81e00e0488032440c0343c0e0342e4403814a0140041107900040380c0282603846441a800c45c0256050310400002402036070380b036040300c01d40b2204100002d000a480160104440c07070003640b140f50070002c580f0b004180d501d440e8954015880c074030040030f06140d010f1041907422981521484180019100064040a2440d00c0c1e1441d07410440c803410b8815400083d0050420680c12405010b183c0e201a01500203d60340c2000300d100e8101e020301e2042700070300505e107400c40d10745103500303041c0d060b03000c0c0c0b0190400b4248941200e030704608000483d100304080d45444c2c0942e81e402d2a42c1c14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 607299244 1250 607297994 607298011
    0xf1521050a0807060c0806100c0c1d090706111203040f02090c0d0b0f0312090d06051303030501060c050a03180e150a0605160204050c0f0705070303020606010e090f1b03 74
    0x9640f903691500c00100d8071542c00c4038042005003404e00c6141c1c5d8404070104030168851515100c80b41032400e20355405001070307000303a03a00710110844404480c02032041c584a41002c8050b141000c1e40c3d01420f803900c0310390481034031454209143e2800c50420780c10185401c02e010b09150810886181c1c04105061820780d07c4690842010030007482c0d00f030440c041c0c0c2c1715029041d541c4d049482c05010220b9900e840f40503e0600807000854030b07003181d89035801c42001d62900010140a141803003c80d016102c070020200303800003401c11001207103a501681c2c040b11a103900c24000c018a6005840844004c0400510315030000314031070b000540e4401d10500c66001d1003191984260340e004d031104212141000d45d20510038003505201601c800682498004200c41e0181e4011860355101c006200651280800f010161100800e9050034408006442801c1e20700c650210358044e1140401507540c240400c001660000401000965029615050980103d44500340318903c030303011b01c0d94800e20707041226401c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 607300494 1250 607299244 607299247
    0xf040506210f16020a02010903020d06020f03150a06050a0c060e0106080307050319230d0f0905010203040506010f05100c020609060408060f070c030806060702030c130b040f1521050a08 81
    0x403403c02039420f0078000160f5000500d940c03801680040d0040c183c910000e03100e8202c107d01601800720940454032400000010140d89107480d5140041c03041d00103e040780505054000821098000c1c411200d20446a460752034024007645c2c0c0d6900505065040e5042a5417a0580000d40b007504001070140c0c00d1180000d181c030b480c0d07100340b00c40004200c2a04002082004540c1503034400c8041c109194114010443c5582c801003841c0f4840030f40a040550030515140403600418802c06601442c020f42c4a031041c2c03185642d8a04a640003442d49026680d4400980107050210601900c105000300e03101034032090418844400144540c0c10076407042a050300880f0800ca088181c1007046a031040d00760030298854156074a00800c048801001140681400111075040d940c0401a42000c59402070807420001034090000000e029200034541c011030074210107140e003007807500504141010a940f4801c85520b00038082c0454042111166150b801d00b061400100701c080c0401c1c51004c0c06200e000303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 607301744 1250 607300494 607300501
    0x102030705070611030f070f0c05061e06090402011b020102070e01030809090f190522060f0c0c0209040f081213020108090c090103030e061b06040501060b0f040506210f 74
    0x10542d8030704003544244902c1081004004410700c1155031f048000c84c504441c1d1540d201c541a038030800c001c88050443d1040c03104001c03090303488095401d0160380c00d680740c15140c1c80b100c05006a10609407030081c00318510000300100c0d40da54500d15100340303005104603a072655403a410314203003030000c1c1c00036195a100024000014100030722001d401001c165a04076451404210742d0b40d0381c4040340c41181626403a080443c020500c005005e20664800c44800d0803038400ca440e12000424001d113000186a04040d04494103501980c41300da2004d4018001d110159560340d5214020780600e0400c83c0d1480f0b050103001351202130a8201da118695081003140521428000940400c00062030841c81d33620400c6448840c1c2c81e0210300c94112941030800c0c02d0369103580700025210340079112002d004040030b4140925050700001d0998043c600a2008020b42c50300d916810529100380c01d00b4800d5144100020041400e03c0300c014010300381d161010482400400d50302c03c6040c0c2c019a00386020b84801c8062 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 607302994 1250 607301744 607301753
    0x180a0311150f03010302060307030b031501090c09030305030f0c07080c0c01172202060903100603020a1205071802040306022a010e0706081905070909061a0d1805010203070507 77
    0x800800c4151040c14140748444801e841070f440f0501000340100c07000700104e00100d0107504160000603009040c0c401e200800b4144000343e14007441805141400c01c4480415240108910000c2e41d0305540c0d9a440d540c0d47d00c0e5520340307915014091140550041020601280723504000d0030385008040d01038a140c103203440005060300d50100f69081c0c50f820240602268514152840d1119003000e021714403405001c0c00020528050511425090f00988408c4018200b1a0b0301c0181a240b01f254000e800644400c603a031908142810014201c1c0d010440610110000b12949000d00038604030252400c2d490703a44020580c4c02020701c1c28040c200080d682c8251403191254010000d503034100810840121491440d984d030898803407201440000000714116003d4481c11102d2400d0100040c40141000352005289403d01c1c07003900c10041c9050801300750f900c0c12a02114401404c1480241003260101da100006c3c0160024030042070011101b01c0002202800a1840b031245070301c2c0c060700c50405040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 607304244 1250 607302994 607303009
    0x30906030c02010c090e040507033c0201090509221202060901140703020a0306090c05030f2a030901021902011b090e0a05040f051b0a0e090d05180a0311 67
    0x7400c00959040141503c44994020050b004542c903c0d00ea0300001c0d1101c0c104039060616642000d445c6401d555034003241d00c2c02e048031662072050721440082c54196030801e03840391401c1180e0000c5c0041d10004081250789080c054540d007280c00038401c0c3c40814a07660507100c030340240c5401100d034440c043d2032021326150103001d20b0364090070360402030240d603071340000300580520002e200101345940803a01c1c14641d07120341c0c0088080c1298410811801c1e8080300003600c81e070400c42d2940e2052550200051b68241246203070308410004103810755085914074403540484d00000c1060309299401c2c084000c00003c3d1024500310b22140e600005036541500d120002c0d07400c0d000c444082031140d00c01e000c000108284044550005606200050030f071110702d858440c84092100107866482003a1043c2c100c0103074010a580c071140c040301c402d00c4a81d41e520b652500000d0446541640d6001540c0d06600305010310001c0404081041d6180921142880001d84031021030b003040c1d0b005e00034040070345d01ba4140103c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 607305494 1250 607304244 607304261
    0x7030b0711060705030a020c030c1b121b0f191a1e0904090f1b05041b0f020f1212090309090a240e1009051501030b0a050a0303090603 59
    0x2500c110300001c0c2421690b642c1c07001528400c200300c0000005031041000303074107071095800403400781ca07500c024403a5600d560b030744649c400302c00ca05000004680245031000400441c01161030107000c0040070842d00001000c48242c0c4184c0100f20502c2900d810b41d240c541080b00a8001100c0e0b403646420440b403100d54442401c0141d20040c020400811191082031710383c0c010003c4441001e039140302400c0070a02820440400510b6501101c00c00c00400800c03844c5044182481c454903411542d1302c07000c210540f025000350403044001020310120541c400d058051210641d80100c1c2d60500c80c2c000007520300408103941c0c3d414140e001c100300070030070799041000b600b100300c800082d424586400c00184003201c01902c1c1c4d003601c6a881405194945c9182003658451416684080303489031340b142000340b42074003210708413001011103901003444070f1070b84aa94000d04405551100549180d030042d0010b181000a15078080180c20000903940d5440315102c000e075110b030344d80c180e040e80740460140507520300b031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 607306744 1250 607305494 607305497
    0x60222080111070b1b0403080a02010c180b3402041103100509100b0328060b0d09050a301b020d21020304060e0a0b16022107030b07 58
    0x40449640300b006a4140c81c40c40350040403601d241e49420034142241c5100d01c040504094000c503001081c480d0490140c046203000e500284060070304410215a40c1030a58272850300b90201d200280030721144c03400607182d0344800b8242015800ba11300c811005112140c03115803400500c030500d0000f1401c16014400140001444260450400c1021440311040754099030340950350210018290755828603090000f481500c003003a40d6800c020703a400c403000f0418428142052414848041150b0760780c800d410440f03403641c1909050400021400340a415080d6041d03c03940b058540923004101e403042c2c0c14640214100c0f540d003081c02d580543c0002c035400b1141032400c1c451104a40c035511001207600c89040340d4120380204081e1902c1c505001c01c00080c1c0c81c0b2080c8280c00328a800c0c25150004000c1041e61601e4036200c0b18240c4c4841001b81f544924041c641060600f407101c1c5d400b0350b03104906580703c0c501c001c000c140c268540080c0308015550900d828212588001c10800900070314030412a001806da = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 607307994 1250 607306744 607306751
    0x1305070e0d0602030901061a0915280e22020a0c0c090506010e0604030f110406031b06030e1603172203021305060603040b1503070603090501050105010c020a090c0207030602220801 79
    0x6000601080727003d030b080b00c5401075806404250310441d01201f11031a14103a647d6800c00320104280500841e40c400c4000380200c0c0c00c061800c805464004402c60309c00038222055a10304031100008800394100b800324034184036491000b02e00080301c1442e9503010b4034881e01c00254610344800010114100c0130b0340c0e0303805541c04210500114148001c0f2440c050780141110300c551038000301050003000e280d40040c10380a00780b9085195848805500030403070301160340500c40489614012500c814041d40e400c003a64924a0703041001803d001460490880c80f1000542003e1242c031420100c0c90180f806a0303601c10211605008606e0149890003100b104c0c0001004145441000705159100182005e0030aa02480000c0d44c545550507000f41d404001900380c85d042d03070740d0340e5018001d0a03000350100e4440d4280323030001c903180d417040c41d400c21103540003031112001920303011070b14000785000940300045000da1f50f00400810b80070300080c1000300110461580700b00c090201c030800400b042e08031000c107904 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 607309244 1250 607307994 607308029
    0x5210c160b070f03050f0f03060f010801120b101e03050f06060901031e0c060309020a090903050a0c05031312030305070c020f13020405040c03090b01141305070e0d060203090106 78
    0x80405464619521407a030301d03c0000301d810180c8150080c42030403000a070f00080c1c10448038406101440c0145400d980e10690300c54104019124040709014059050700112255008285203100640e0464802424034030041d48400488408000c015114410441512800c00c01c00c5410464205909044000b0f412203080090008416040c1840080e00810039003145000301d54080d204203029680c4204221716150b62603d0140c050121442c0aa10501480b0130003e007081b01d40c002d41d890300360300d591071510345100c2d20400d407083c641400381a58148820b0040880807204c010240003e800d024800b04010500351400505544000784680e080286030451040161955007000403000f008580040400d048040124024000c941c0043d5100e401e0001010450341c0580c80814098000c190030328440c4c0e2585400100251603003c0c1ca03070050001c00311000c0107691a40823036080996860118041d01d01da42c00240042412041501c4a50b40042885040c5100b40701d400010401c2c1060442e0004 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 607310494 1250 607309244 607309259
    0x9020a050f0a050c06040c17070302030c100c05060147160506040f1a04030206161103070c06020106080106080a0204020315130204060e060711010c05210c16 69
    0x428205031440040850080c4002d8000d001380e5141020070400c441c00d900d403505142c000b00b40b00e07120319000402d03d40c290503a010740c0030a06000390b90f0082d00401c03524800f031003403108600036908175400300200551036600050040c8242030081070071038030380f07603000d030704010315190359580360342c14100c11090308114044080c503494400c807441c103014202e241c07544a440b29414803944081002401c901602003040304101000d0b007060701d428080c01900d40c0c4814801110445454181ca000c0e001d640194000f0301d031003c49000303c410401081c0341c201200c003058a00c592035078000d4201101c4007858160b00b8048650309100305c00082241700003e2204501e0020000d460b182090390280c00b40c3e8001000480e01d00500140d0004200c1c082d01e080a448945103060f0025000360140c800021802c001094803841c01354140c8842e035401c2058144404d106900566208122100031100d81c00707008241d4041d8503810352015a0442500c8030141d6030b0140c02030060800b01c07031709007250118698800610550 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 607311744 1250 607310494 607310497
    0x20a0806060a080402130f0606030905160f140f0402040b0d0f1104032a0b0715050105090105090a09291f0303080703020403080a110606040b090601030f09060501061809020a05 77
    0xe85c040c0c94100519460f0328900d0041c0000c100200816410504001034540e4180e11081010b0f0240068400c8042c03014408130542c041481780c00791031701e4010400d010f0540182d00540c40c011008019102090303610000c5400d90b089580551400f980116100411400ba8001d15248800300d41d8100a49103d2299007500b03801103002c007901e0000320246954029424510303041c280d46110320700c1c8140e66982d4400c0c807032591083c50121065108802c081a000c215401a94182d8800600440442e800e02007030045455000703000714082a1100040070115a4420140301d002d05407041806034a100e0710701d80801e00314041d00e00b10f150702c102c02903124940c81c100c81d030788240c99140ca403102a940310628110060b0045803c00740030020002a03840c18280c00100025140e034242003a44e41c1030751000c0412084950800b0000c6c3c203c8100030009005601c603901541c0d00700440700c000118034019440b20790890700c3c0dd03000200442d507401c01389520544a5281e1000910003c5425072400c001114001d016 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 607312994 1250 607311744 607311751
    0x1b01030b1009060f2a05070b0306091303020c13050105030c060702090a020903150a0606030627200706050f1f03060c0912120e030d0918140109020a0806060a08 70
    0x2c00070f4034548000c515100e1342c0c405202c421a0304180900326210381d01003c08810f804170860701072107803440c0002c41101d584117403032240c0001082c00c0c0003659a2819424a03014086040302140201c5109042d15a0b0303c0b0311110101801d504000755541c10b00c4107040c07a026042d0300042c45001c0c18042800107030b581c464040d0380040300d50400740c1c40f60683c50100b0b25040ca000c4180d04c00d000440100001201c3c83d0303000c407003140c03401e40c0d0901840c0ea840a46441d04024200101502428030000100a5030140c0020800124241191503c820031100d00d50040d00321480860741c0c151110280700021082c416102e40040c15201251004841444c400c1750000403444014001c58030788011480d158007901050000302241d10500709881076900c0d000d04a210090a60404107100f0151080c0d903060001d0701500400007074680b0441242043c2092810f070320398039040e08166403203154803140303501c510840300d000340009100941c0b5142820f8002d05041e000a0019000b50010b001a030850359024140c40c1d007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 607314244 1250 607312994 607312997
    0x1030213060e18211c02040f06020c030d090e04260a0201240b03130317070305180304050d11150703020706231b0a06020c07050f09070816030605031b01030b100906 72
    0x81780c11340d180400001c0d0282c0d44c490841d00c2c0b19007a00181583d00882c0c07000801c0003c409030f42400342103031801c1d10010310760b018107580341c500c80c0c000400048280344480350511a410740b510756030004e03005503001c45c0e00448014005035102d000360007003032800b03c103091403e14036103510100300742c1412001d81050000400001c0d140010740400c0080c140502d8105000c002000c014500c1480c107054094050700080e10641c4d04054000d4000d8034584010091724140c2d0350080803980b0700e151581708c440303890004000d588e500103002c2c2d540b00e1201004a0090104070302c00c1c3c014190790380c50550098800305420b01c03130940d0a00031300c10a0108a00582c111501034090203503130080d170000900d45620b840034650009149510000d0100c14600000401c8003c480e01242c0802203c18800c01340003e290007600c21402040f1840042a0383c0752407407003220701c0407159280000c0c02950313440000e407800c640b214031640c1c2009000c8100c02a96854060440c3c030010a4030760440201d4400c1d00100800007601c9005d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 607315494 1250 607314244 607314277
    0x240f01060c031d0a0303270e06010c02040b060301092403030c0303091b0e061c0c1403031e19030e1b0a180203070e0d050601030213060e1821 62
    0x12500700340000f00c02015000d0011131030a07072245801350507018022100b200d56107181c42c000440c1450404158251120303250f0041140d01c9200040d0390b80d0070248001c0341d20075180c505110a584072500550300170305c11508045004100e2890144400741e0b40e58004c5e0245105c100140b002c00d4124a004808582c50f240018104200b8180b0b845009850100314149050250002601c1c0c600d900c4114000c2c10221803458040700300c00115201c04000260003000260f0246040001e25000c08450314040d5000d000e036860061009d031105e200c4803102c4554003c22401160050303400c00c00180742c864841003401d0401100591308240e503525018a0003402201c2c040901140c55a20340404c10001010301c20301c2c2640c007234a0100c03401d021b500308554240000303108040559291806050700304040344c021001e8505a400d603001e22000780f0b0041102c204c400d44909001501c004e1031b1250728410601d1101c11a03c84040595003030030700c0c030016080044402da83d42141030402074101296103200c42e004000d07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 607316744 1250 607315494 607315517
    0x207080307031805030a0606090e010902091303050408120301150e01022a0301020a0207030203150f0a090809270a020c0d0513050d0318080102030403080610030608240f01060c03 78
    0x84a140e0444c1c0c101c0340d018007030f00700d4440800220750440c100380c1e4400c180c1441604d005840e100d003203d007800d001a40c4144071502240c8102e00020890380007a0091401174074158441110314a4801c42a13804201200700200400484055000b101c42403c558034040411000700c0313000035640c062b810540082820030b5100d119400e8a5124500240c4401130000d64803201ea881000e5122449844164002d01482080c01c06001001c00514030401c5e13004d080c200310b40ca0300d11002004004840084400c60401c0010340a6651039500b58001d103602c49031241140d503212002805030810241c0300048060050110481150000c516511544000c2c03428680762202c42c40c0c400b41c00a680d42c00b4a8221820404440905902c0a07910500e420704007105038071540d0300c411082c201e21080758060006100f51012410030b10b4071081d9201c0d1000030b0301d00800c00740d482d00306640c01d01c41499440c90903941440d401000c02e04409454550009410300a07624030340c5403400140050101d014010104000d84180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 607317994 1250 607316744 607316777
    0x30601090e0108010c1b020d1b0b03010306052703041707090509010509071a03130f0b011401020c0603060901030b07050d060e0a0f09050c0111031213060606020708030703 75
    0x12402070005100301c4219595440d0214003c0c0040605940020039008900c0c0c41410b04c001e240a00c07a41c007501034001340246403101903004100788180c030710480c464540011000c001c000514042c5020302c03000195420420801c08400d85c03d906c11880300310509044010500300801175030202c0c1d002070310007000c0c0030380381800c9410a0400d82201c1d525a2415050002e160700540c0070520511b0580c00721410a51108800c02c0c2a0354080e0300d020a81c142003000413441d400321450804014441c4005007160401e41c0e98001140c0003d8021403102901d01a1020b0070390b904000900b444403003500c203203140d401c02d0750105007943c10500000d0708035810b5002003100030f8071901c100e0b00001e1144d002006480c2d12190807020016040d01d00700182410940803122003101340c40f4003000b0b5644400202550051800191030320000b0204500c0203000c14002c80200c00c20101c1c00511822100c0107040c4a40503528154084030703501e4006a0440d03019810902c081e1600004544880d5090b081c10410b6180142d00f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 607319244 1250 607317994 607318007
    0x10c0914041808030709050604080a1b17010b040515030a0609141005100504050f0f040510020d02031008030f030f040804050d240b10110a08070f1e02090a02030601 72
    0x102600480102d55a2034240030b01440518040e00b16952000b50380d55552041080360f0150340244101074020030620b81c00500c5a80a0810911b400030b00c006810f50303280c0900720400c1050b0021440c0781d4565100440625242c40384642c07040400209012001034080400e960742c1031054000c0c0140c1e51003140308203103c850100c0c41001c0c0c045c0070803114588011685080945029561062540d00303891000c2468075060023454464640101c011000c1c0d50f9102600c08456806070041d1010b01861041d00d4035803a0b240020410807007024409682ea050101c50750402e104240c0c03000350a50028443d4620b05044c08084982007100340358452207907115030500301e00314855070340401ea1022680f458403007000483c480440d2098910740c1c060300c11926000e40308060702c0b6283c0c20581d00040646403000c216000c0c00031104001d40032406c5412040e4141c3d928040f690100300705079003c0040801070000c0044a55150070700d08d0008444801c1c8540581c0484d1031040013410380d0621540100002300d05903c502c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 607320494 1250 607319244 607319261
    0x120706120b06131802270a0503030c01140901020708030105150f1204060e0a050705010f0903120822020603040f0f0b24030c0a090207051e010b01080603010c091404 72
    0xb806a6a40d10310600d80304540c407524898441c10506096035070800c02104e209039a809004c840c0b040d11612035002c0c616042c40c0c01842c0d05503000c602c01002041c1d42c0c408001400b941034005000042102c41c12080c0003400340c5c0101032521580c0104a0b0900159860051303e044030003d0310501c88012072081d000002d401244000b02c0101c4021a480c900c844502c07420300d005074021001005a10024194681ca808002a001d00b42c0d42c8005801c001c154803400092800145a00d00012003540742da60300100f07040c03503482000015401c0000e20005120940382c65512943c420400704146a941d4003103126404000e001a050400061958003030090906564a04130340c052100c00340c900d454070448100f8100a0310903482d40c042d00b98001843e090000340c2d40105403005003034a40d900e1404440c48060b5100e043c04561500030341540c2c2c0e81240a0740305030f9006282c08800403c951000c0400104041c1c00100042d00c04e03810410f8548a5540000003030060320000504000c0a0000d4004100030f8595031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 607321744 1250 607320494 607320499
    0x3190323070f142e0c03150302010f170f0609060a1805060d050a050a0c05040e0c06090102030403120503011e0e160e031014060103050103080f071e03030e0c120706120b 74
    0x11314880328010304468040001549103200700905d80c6103250480407035074411916841c9004c038007024000b56004040d50f8441c24503038a0002c0507601101c00d040c031068000d40303070118000100c009000c030318502460003603840007083c0d8096a02c585800c807600751441e9460542d0220503503590216006840b0750400c115515041012161441410b2901580c3d807100040709480800030640301051a2a050080b44c0c4c0491180e00207050b0080840c08204182d0b120000c0329040d0300c010440007002481c00c4001e841303281c1d4a5104c46441e507140130132030740d00160040c4481610b06100c0301d00b4050122820400f81e0801c0e800b070002890040e00380b400b0b031941d04d54425103e51501c520804078034035403643e170080581c0048401048140c2d403103950054081c1c400030301000300994020303c01032944581c40c101030424103020300c00800500341d8030451140c1401200d041900042c0d01c81900d40782d0302d03008110600c85014180c854a21700c0100c26900350715044ca40c0120740801c04241f412584503529074220303c0425000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 607322994 1250 607321744 607321783
    0xf030103060c02150405061008120406080c0c01060e0702010e060402010f0503040510020c0705211509030f040303051209060103020a0b0a0e0a0f06080a02180402030603190323070f14 80
    0x11b007490760751000f0403140c5102d404010200841c004030301140c3c4d9410a03010743c2501c0d090508201081e58aa0001400e501403242d0a21520f60205002d0007190000e0200401c01500350805d03a00090035651220389071407a179482403040c000180d910401601641e4105d240041d1280c8541c580541051a001194103081d0f00100e25200246408101c00080f10800c90312a050410860900060030200300542c2da600d41103c4862030f0783c1b5131580401a403120b020300c156031900c0007260b16150980c005410540020f200802d06421881512000a800c40228402000f0035031560340042d4440b944c5008200301c407c8049001e0340000d0151200c0350000800800464909840c0c08681020988900c1408009042c44d030108901d14002c0c400c6807c0c80e1400c10000030000b08640500010f0340c8040c140541500c204810340e80c0c40b0502c1c0400c3d01e05c580c07180e507800c0425140d011160b0008528080710320038501f41005008006003805183c5000694800002410f030351136544840e04080302111703403941030b506 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 607324244 1250 607322994 607323001
    0x402010314091c0305010f060302160c26011415040b030609030d150b180f0405182e09051906020d0c050c0d120b0d0c1a0f030103060c0215 61
    0x32a640310000f030040b5049404010101c03044040c0c600c280300300c04850480c0d80e42485a2403003900103045a01c1d032040c00030350030061960b403589a1030240d1302c00309800c1d0055800a401012140d410324610304840000d00007a0406c2008904102001e48190f4a544044440d024075480ba80c006076851a00101076850354a04040d410fa103d40c0320180303440388245000506d1030450403100143d070a0700d00e240710050a102e44407506501c002d03402c0203c980d01c8a10060740c40b0b0341d66918000d45100740741d0780e9918000344200002aa21305101340c0741140986541400c0c0710301515488041100d008490303200030500b814142852030612103182040307000164180380403000e00000343c0042100c8920003408118072000400101c41034007a00d6000c0003682c100440413044103100f91108114200840c000080c41c48501000416008000104480081c9040c104000003040c8c3c3c00d20f044400c1806031041e1901c601804e8070403091005020007890f8560382e176a041c544c28420412007001c4441c02074103203407604 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 607325494 1250 607324244 607324261
    0x31e090312150302090a0e0d1202040905090307020f0609011d06040f0e1504090c050607110901140a0b0703141605030706020909100f060f1101090609120c11090402010314 75
    0x40b030600042e4003a00a900c0868150800c0e48035248010b250030002c3c2c0b00342e1502000c11207028a0b0160108109030702031001143c0c940c0d445c49501c0c02890b0400046650b548584180a409006614558440c40381804070a110380d0700003485006155104d1056510742007840001881401035800c24011011484408656002c82c2c4818500407600801d01c441d41030b040c101000300f5100d01c2800103200d903006070740400250921102800340903104104210320160104003140c070b200400d83c00034041082c000d05201c1c440c103013802602e02400848803264600142da0320041c2c2030f002d5400e03130961b00071700001d1280c402c84801002100700c41d07805401d507070741d0790001c0c00c0500103504040280303480340c01001c2c00710710b066240000d194200c822a407944966186407840580b46400390302002400d10003404020702c5580001e1162250b258814100001c00c84918201070900d000405404024022455942404503040560307c1240007070817602c00c607084c0d5451004070003928004040b000c40303a01070400d100111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 607326744 1250 607325494 607325531
    0x5010603090c0e07050f03040218070819110a2106091d0309030d05090102010b031911120c040507120e0a060e0a020109030209090a0f060b030d031e090312 68
    0xa40c01090b5800d04079031140d400c0450002c003034032001301146003042407110800862002d154080d00081401e82200020020700d405004102d41410014143d00204440720700741c400c07426a0305000103400c119030309551000402c24860106c0750000e00c9844a4040070040000411130a946021901070140ca90340351074000282c1118889600491101c144020800e00b000060b0341d4a0340d0001c0040c0700400e81a40103a41c0e070384c00840a941155244e44280d080358804021007041d003038035005080c144903000c0c01c0c0314100030f507034190480c4501c4c00e44d1f09903808241e000850703440200003154002201d031607000e001d80c0d080100c5403051058a08040c44041c0d9080082001c5580ca402080180900040784034415240c000000c002404510089414005400c010200b0307a44200c81c0300031500b80c044903440d0785e4481c030003160007141e5140d11901c66001e6400d0a00607086102020b04003400460700c0846000400041d8010240015039030305001070505100b01203c03801c0b105d4034501080352900c216080c01c1039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 607327994 1250 607326744 607326761
    0xd0204110d1514060919170f0c01091a0c0c0405070f091a070618052d07060c03210c020d140301140d061b0c14010501030b0a0f0f05010603 61
    0x1121000c000000c0c80c0700e0010200110f108002d004a213080c0c440c03410802c2d80005a003821280c1e4421003404129400b210341c40c0207110302d01900600e01d035420200080e00d01a1782e00166410070004000402204504110040c1d242c444159041c1d2600c2c24528454a401c00c412480e581c010704110500042d15005000c840d004400d40ea1014086500c4228034000c4020705440101c00d42c8003001580301040650b4040d400d056007200b202c1320b2000c1e841d00d9251414a455403000b0b00090f0341d0030b602c03a01c41d69079090408500044000740120501c1c000000e014298040c0015041c0042a0800000000c190341400c4140404090800c8010640d441c000d507113409903c9030710b02040e02c0716408841101440c054034100d65402a081c288086010240260220001e004039200ca0305c900300020f40b65280c050340d241003a066540d5010300300e4581030642c0140c1c1d101004084503454140180042071040900603480500b1020120790903441e80c00c0d81008000d00d41240e81a00c0c80c2800103d07850b40d058110030344 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 607329244 1250 607327994 607328021
    0xa091a130f1a040507090e0a0b3d0801080d030e0a020a03031e03020408370605061f080621030414150a08010302010804030302090d121404030309050d0204110d 70
    0x1255a40c5e40098030003100d10300500d03c802c02c0070350001d200d5031040d4110503034600010f00100352441800f180301143c406119801c1d000c5402c6201c68080782034071001c0f1b0390035100091500700e419500d00080d46450720219603005081685803040700ba01880e0030007024003c150301400950070f65a072418000c1200030200d030b182c280d0b0720318a42003403441c510038000e60302a07950403405484000c001ea040301d800c12201c0d50509030401d01549890301c0b011016100c0c000132a0241c003012919141c0a001c000048220022401d2004048221a060103510150280e4020b00c10f4441007500d50009101140740f0b40d002c40c1c0102075100c0000d0120ba2646488103450751401c082d03900a1030465524045c94140c01620b00003000203420303400400140d03118040781500203019040040c9401081008916a03480c001003d50301c50901c2c3c1020441c0c50b0340b0007006a800b801001c0c2050406045a50081c422103441c0f21b900e100f0442c000001c0301f9951b035940030540d003c200b030b4101503896050801540150800900012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 607330494 1250 607329244 607329251
    0x4030b040f0204201c0b09011815180522050109140a02062b02040b0a08180c040e03160b0702071e0b0705011b09050a091a130f1a04 58
    0x8403419140b0304e4032400c041c0c0440303901e82010010001041c03410045c200c41c00e03226840d002c10111030b8580e4605039028000307400003030000030750504041c1c042d5032400219481003000c00408106507080a031b0b0041042d28401030218454940b25203400e00b1282004061440c85400c2d094481000750551080d00b81a102d080186500d03138a080805032200765140c80603400c0001085031103038101e901d04000c1107a001420380c3c2d03400d0340c1d0410441c0c0c0c05c9070829000310030b0341c200002e03d880b065038110020039070105484800c0305207146085a001c1c2c0b214a4076017030170b0090792034050400da402001c1c400d55412001c204004550082942824035411000381c480700c001d405031060220750741a2000359a0941400300e072002042c10703d07000c0194800d50000b002600c641d50f80308010844220300e03103910f0710340d00c41d06e80c4c4218601c1e04240c00c00050701c00950112182900d0300e00710803403009900d00c5481c45650100c804003e201400d184e103101601e0441c0307141d0190307441d1080c01e22180c0707540d001c1500e10b14002d48041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 607331744 1250 607330494 607330511
    0x51e090c0304080703300923070911070602181f0f110a120e010315080c0108040318030f03030509010207020f0f0604090203010b0403060c080f041704030b040f0204 72
    0xc0184825580580402010080709010078051401005c052a0f250400410b0341e1141e072209200d51054032603045050b0300c408070141400819003580c0c2c001c405082a0726643c1c003840d0021669055248034041040e40c8450305a0fa80314401010703914029041031040d503a90030318004180101c000102581e119110b5031204540140d107048000d107a00d0b64a440311035044607059802e071110b5086218540192092219250008652030701c03424051007540c580500d030700310300c60014040e1021075203108800d042c20242000031020000e030302c4d03804420a0030302d0b00c400c0d00c0742e08040310403026110540f142c15000c60070010410198083c218402402541d08001a41742c00c0d400d54242d2050110280d0710401c412846101454117010815504200030040e40c03078555a441e030f070000d0342c000341c0c090541d027400446d041040c00181d000c0c166400d002407030200c045d03140c5100840000e40d805480500300700e02e100104642508880101d81c0a15013081d09424140f4162800140109640b00304034003c07030810141 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 607332994 1250 607331744 607331761
    0xc21020405040513030c0b13021008040c051008041106070c060e03060a050108030703030b1309060e0616050a031e050405060402120601060210050627040506102706051e09 75
    0xc1340c131020b0341aa101080710b00b01e1f072140718035108040d00e1440350324296009440160366000c0301c0020403107103446040c101c2c64242060640b0141c154002c50203a0700b81a890441e85501148007940700d584090f007034601d99014400700303089008802005000d0500300030082505a0000bc803e00c9d01c1004034101d43c4a031b554004180103450083c400c02c41d170366009226031000607009402c00600d000e0043c105000368048a02c1903000e030303006c0c02d03420741d00305a4a5a104010b00c030107120a030f42c003035105e82c1d8018480307d00003402010f0b8419410054100340d42d508554107903a1100e40f048401e180800003d00c0542054148180c582d24259022840390110b5018140b280802048540c100c3e0003980141c01442040c0c41c00e60090400100040c1c2d02c014045c44440103000c00001181040c00041082d05044c07a0600c0d2240c5400005000c020300c034144154100052090420341e10303101c1c8100303841e100245a8125001014080540089a000215040500078500c2100c44002015011038001509031a02c40306d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 607334244 1250 607332994 607333021
    0x1905071a011205120f0d053105010b03120403020114040911041e0b030c090a08030301030506091b03120a0c0510051608160c020a0b0f0310080c0a03060c210204050405 73
    0x1081d011a03a082c006c02d4035000181d48040da00503042c2d40b00515510030080050381d030650351840e4043c9680114090380910209200b012180c52065009122020400c20b070b6140c1b0340528440281040300b00f80c061042000c020056400a0103405824480c00310944001c40d6140c210380290703100341c1000c0104081070504d11550b54202e601c0d10740c00301d255441d003803c9221541e1101c01603d40000c4c0e5900002010402080114021401307100034000508051540c503080a1202a045101c1d0316500b4588102c0e59020484400e260200e139802e550710140e0707050070b0301c0c2001001da01400d2406035440140d0903a6444c2c100ea8400d44202000f41840b0500c5441905c01c198103540190f00640144400c0e02c1c0316000354241020180005d2889144654445c03843c0e09650028843d1114940040244000d010714502c92001901c080d001410152420201113081d180461001901c56038941c0ca020b1035160160040e0000705152100c0452407400600800e00694898030640d4016440c4c000080c00c038405492 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 607335494 1250 607334244 607334257
    0x9090606130e180f0f160815041401020d050f0c070305030c032509090b0a080c0d0303021306020708280f1109040605060907051905071a01120512 64
    0x204034540c0300782403504440700e80c04010003402990700343e215121080c003410014405009a01001071915100c0c0002e5281020100500601302c43d514010901ca406004100480d5122201d0328002d080c0e0707107a00b410314280c0e4910f80940a01d501c0004d15500c10f954907088540300c2c40d440142501d042d2076400010000d80300f46000074000410034804988400c4480c0025a00001652590403041240151480c2e804282c80b0205012600e410400c01092009004036814410101e41c01d51485183c0b2503025250f02600045a201d03200c03900325581014040d44c142d4001c41407940007401000d481e19806941c8441c41c2c02807400611035101907010b1444c0e8100c0c00b2030716400c07410490100352480d82d1101750100c2e44582c226510010340e201480162645820300740f00e81e0090f00b022401d81008010301c280f224018044004001c001c1141c2d048041d014520558010014130f082d565604841c1055024035070400c1d00201c0c0d00c10b056000045110f81c80b007981c04c85c4c50140003525038071410010316040a11604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 607336744 1250 607335494 607335517
    0x111030310090513050d080f090d0e06310914090705061605061017060103080924070605180a0c0501050c0f060424092a0305011109090606 61
    0x122003400b2840725a00041d420640b250342c1d00c0e100300c0d110f40e00c443c1060b5502178a100082c90440c00c000c0c0031034081098540041461000d04250145410300802400d0b007a580d0302c0c081c000014610011541a41c00101c0d070095132542d944031454410f0032204e40320520700c19540010b08040e85081c000c25000f15a5000304900002480120b240c0001d00c5110380020b2503042c0d00c0ba01096000020440c18001c007403040c02c0d040c00311200c4600340f901050003419101d2030220340d0390203c801400001d43d00340889105c2c200855003800c202c802410b1400d80d02c0380748450030488200c01b08152003007000320342065001e1ba040c0c180d04140d0f1402d8141c0e4564031030603090040c00d81c0e0303030010003003109502440017400c00d215007605840148405280c11841e013078007544c00700d403021104258815680d1220305040100046001c00340090280754490b001d0300320790302c11220015502d16040f10300110080c0c40001c0190762000090001107045018070265822258025004051400c000350451528504803054620340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 607337994 1250 607336744 607336771
    0x2d0a02010c021306080a0c0e04051e010f0e03070c0518010519050409110a21080904060f1701060e0f1f1206020309010b220207020a0e0c070201110303 66
    0x568004565140c1004001d0740c100c000000e10310516490303030207030001410ba010000c041e030040da03190640070741410b94044400b49480b002444005034010910003208820038000b504545800c07174500e40100211402098101d00d07110419001c05004406401d800f0301400740444003c0c4d440303042c41100d4802414072056040c42c940144194606041001100400b19000f91000346c0c580d8007103801c0b00c201c2603054075403050701681201e041c501031100c04080c200490042d000800310100b40800c642031084010184d82c00400d40207095103503540488001d11210110030582555003034000c003090752010604c41c4d59400e1000c08a8a49140b032443c40c010a008040b03003a05607a1210b00302095120319045e0307059041103213000244020244164050580241001652410714401040c02c4895141d803d41c00b500301d480c440d00050000104d4a00d1446040c031000d65105100d10004060311780e075811605d49505024244245509414050034050b40b007a2513403407859460301c034415500d02049038510300da100f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 607339244 1250 607337994 607338013
    0x10330c03082202060a020102070b06040c0f11010e070e01090e01020922090c060e090a051e100909061a01020a08030610020c0301140405071205100522052d 68
    0x241c1c03224088082c0c080c4040b81039841c000d0790004a465010180380d500503034021641d40207118001910b01d070440ca04807810828404403510244c0205600a032503410320852208800c241e590070b41190f0b128105030006e41302e80305d403200007101c04a0020302038010350500e80805081a00414030844000b601d005101c040594601c0040c802e100580c406040741d02030f1160703040000142c02c01c81680160129840b821890543c11043c410484001400f00d1101c600700301c207102030130740c000401c03006508090f0b5a480c1e01d540d6441100800030519400210413501d841600000c3c803a0341d501041d20030760b89011001040c01008012a41c500c1c000c071000d0f03c00c1c00104003040703e03440d1590099401c2c20450040e41e14690050f000242100d400720300c0b80500c544031038100001c114082c01610040c01c031040c8c0000300c4a0040d141c4a513540c028428010184c0e40d0b520204140312060a000c02c0242c495030080000041c07245030054903000d0302840807280100a080c400d54440f0b4800078045920302c1003000304201c80 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 607340494 1250 607339244 607339261
    0xf0906071b03020f010e0102030a1812030209120706021e01200a020709020409020408010e07080613020a0321020f07120f0206070b010b0408211210330c0308 69
    0x900e4000c02c0b070940c4184001100001006e001d00d13000341c03060304001600c07894030200000c103580600c0b0540d10002422411007001901440007401d0500c003034640186c8035480b0b540841c200304155041080d291003240c40c001046c03580016103542e444001c0c4032011031007100c041d403e800ea54100c00c17101e0b03850200250244101411a014001c41c08180c411035101c3c0c4d0f0707240a54812030b0312607005100603580004003440350f07810034006c0c0c40308900c80da001024800d141c92500c9444100240c505003010f041c0448100940d9680003444016540011a0b001d80521280c40e00c2c0c000c0300c0c101d8445015005583d0100d000d540d01007000805c40707061a104182540c007075a00d001d036000702c5260480c1d001e181401540c022403003d21015001e030150503d440d07920b03401c01d0303119403500e0174080320f548015000c244800d036841040c4007130302c1b110921144411600e071203100041041d000b850300044540200d20108201000c040d10000903038070300c190b038580169a050041140d01143e045400b034003064030040030990740c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 607341744 1250 607340494 607340537
    0x9030324011b2a03060c08011203030209040605120a060b0103050106091a040905130c120f081602060a031406030607080f100f0e0103030e18130302030706060e0f090607 74
    0x480c4110303540c03030104100f0660404211200c10300e4074008025540c0c00d2080010b00c0c03044100f100440d00700b0020b10344c075085014488035101d0f00300808040d000315141c00181c41e1a0405005494002c02039031031005d8419501d0350307981403080251225424a2480c1c0000d500a100740d038160b664560f5141c1010b428a21242400b400e04014008544003c01000407103d0461142c0d9020304e624503c03d0758860300070300740a0750139410354000400032001e55040c0e00000b039803040c3c6600104e0340b00e8141c0ea00d40b21010021304280400701000b941144000650520395545603000640c02078074811000000e07103560040c1555004101c0d29a00880c0462000c0b440c08000c640542e81c0c4013007959a0006200e455880d00c0c120f802c40c0307a221421032080c800041c004c0540003403020145c0c08096603030fa540c803291108680050303100541100d890b0540e921000091506c02e100303d44e61150040814803030569200c1840014170301c00c442a41d41407640c0c0008c91034000300418464080d000b5030341c038010304c1c42d03d20000d501e90 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 607342994 1250 607341744 607341797
    0xf19060b091513060804020a0e09030306100522150c020f0613120c0f080a0c03020609010306050d050c040c050c030d0b0d021801080c030102090a120611030903032401 73
    0x51002802104a0000310600d441d025121359a100c00341401e01d4070500c0403446203034000ca4200100d540c20402a103000006a07944504121a625240c0003c210151100d03c0350a59441d4020818034556299000110f0160304071503601a02d0b1600e8207844130200d910076401d06001b50722554000405040b4a03021000d4400d07c10440f40800d005ca99031f0351140d041c6c100141e0b003100d00100070881004100d0401d0851402881c10001800180c2d450395149181030303006e800000e1140b940440e45081d9a440b86e48143c000d002e0103040c2803c1036460f400c00d20ba4804589400c640300302d0a0100380e840480c4104107071816002400000c5082c06071031b865010103400d640f401950003036140c15014015a59494003445011201000340e030b01e550400e000541008a2040e80b1808be80c010000d5070701d1601c0300e00003802101d081c030703514419500c10351400201a002441c043c0b001e00c00c0110900c004a0b10100045000d11200002e41240307040d51644800d199a00325401c0707003c55002c108000e4050054040b1404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 607344244 1250 607342994 607343029
    0x61506040b0706050702010c0f0215070e1c0c14130207030201090210030c0305090313060509030102040b070503120a110301210c060932010c0f0b0f19060b09 69
    0x61a40301c00d81c1005035041a0000d4070010b8031074040c8001d058080c89044181c81c014684203001c202c003020041d503500c50305014a1082400040041c40b0036102d0181c110380c0640c000c04221140041000b40351800c0519070b420748041030b2010300022903a0230321400090840016100d00250540c0300b14010007500240f40540a6540700c4010100690342c40c41071100990803030b20000380c88440800000c08441c4000c207122010361007048800b2141c4901403503c0100c404a182c29551690101c2c0482d02a0059034048072032000c02040c081d04003c404809002e4402c03030300680c107200340d4941e40030500b52a03404014a40402e400c000611081203490702c02e425543e5504c0c510514103070550346001188513694010070024903100300501104403402d0900800120f000b0000ca84101288400203070b2511042106041c400c801240c401048218800e40c0e400c0b6420000c41c202900d003000c02e0340228041120a5103101607481e42e182c1d610001440362009644c2825162400c001c81d4405000c440b8114400580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 607345494 1250 607344244 607344247
    0x20304082b20030a171602031602030a0803040507060f081302062d0309010c03090c050121050a0b010306051906080606040909060b01080906010608070c02220501051c05061506 77
    0x2d6646404000038840701d920f41d40c8002c15581d281800700008100a45801c0c6414503682c01c1100c150ba001054031141c0040c901c08041080d814400a480c04900384802040c2100c04002c00c401d05c0000718049040b600b8545484c40c0e00d081d8810100da641100315800ca038902001c4032100e01508048003e05201030645803028070000400e070401401c0d4061800040c1074080000400290020a028490190246050a1203d1400d581c0c401681e2081e034041d050400c0a590b031901960444141c8204813250b403107804000600305026120041d28094080c07a0200303052110000d40783c01c060301c5542d01900c2055844000506003c0d0858000d0000b5003819449034040c0300108145145108808140303125240c0007520b07122440c00908400c10003806070150303401c5400100805078015040c60742c0b0801134903081d016007940b84001544503c50b0b040f00b0500e0000d4a0300b0b0309a40c5003542c001c03816030f0000c0351f10344401103485410061602107a02c00421a41090000c03c60800e0312147c0c040301c04c94004c0c1a20b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 607346744 1250 607345494 607345547
    0x412060f050901090309090b0904080306031e0a020a060f0c110609040609020309060106090f17030d0204090e060901051b09030106030807262b0e010c020304082b 71
    0x51060301c000380c4500c40340b0b0b5950b603005010150082146802040b10070428802200003e00013511940002c002625000c0e0000001e416641c05020042e840c50b12280ca6041d24466800c5d0300369500344d0032404900580e0b4504000c5005e5000d034455281425895031040309a40869440a0100d2103001d5481e03005a800e01c40d500e050f507960b0040e2005058001c0d001601c0f41b42101d00c99141060690140e03040c0701600d00d060240d2090002c0300700035a80c54003040702d0341c600c52002007455403054418000e0301d1440480c1c00f180d68046500300c500b10381107807801c559841d203901040a089400a407109000903c140c03046000c2c041204000c1c0520780d200400000304155207480c0c680e803560199604a69070f000f03181c070003030303115905122b0070750600e02c103e900605260100d8501003010302182040d20701a00d4a642d6003d00c51045c1e000200103668480080c44860740070540a592900103000307100072130050340047c10218665445000a100d05040c85c13501d205002d20040e12140c50071080e400214001300c010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 607347994 1250 607346744 607346771
    0xc0f0703030627060504151518030602030402040f0b0f0f03030f0408160f08060105090c0702031c023307140f0901110303040b0a0e0a170304061d03041206 68
    0x40d014610034850242c0340540c043c4a1081c00c42d0266040706120301e140010301e13800b10540398813000648000810380e0210307091080c810340d1176031341e50700750004240420007000c4104074443c0c020b1030245109503018001c40140c042080e0503109061030030b41c1c12041c40d000320021403030803010b145064180a419686000100750854815510582060000d0f51242000d00c40b4400e480500d240148041540c2e0f1101c00d040203400b54171a20103110340c42c1f00c0c50100010130300b17845842045070f200030f60003804c40d080712050844100022150001c824054000c40441e0811454404e242d0188400403260352400382d40100501c6c0030600c4060448070400c5620b600800744895541c0c010f19030203c1049901d1340351618000010720510f100341c1c40500a030024410f0000282e940305980b034021422010100b13280381e19900d01444c103208480c0c00703481145141c0d004144070003924011805207000e02e400740604050902075080c00c9003910380c20f240d01e9008000c1003020303084d03402c03180d10740d5032184101091019200c9007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 607349244 1250 607347994 607348019
    0x30705071e020a0b070305030a15080a030806130218100c020303120609060a03081b0f01020a03090b16050d0902030312071205010608060d02011b2301140c0f07030306 73
    0x20807075419038034070096029490f01a0f492401000c40c0715105207400c00c941d0b00248a0700020b021700354101d8480021601500f050b04140020303001c103108403800e4011a081c000c210351403d0310342c42d02403903803119040380b038013494021107241d400f150420621100b104010b02074500010f081e0b1034204030501c8070b8030780140d40610061001d104100380b110080d08001013000b03115407010b0078691094034046810400134948405032580301d060742d0f140014a444c030341010780c24000e441c682c6005c29480021800016501544030840107401182030140950350b040d8000401e0101c102c0b80d10214400b400111034506254000303400c2c0600c080c00782c9080400c1000d96000d0f000083e82e8810110350100992a008071071846014010041407074584c2080c102180815003400c1d507200d000c0d0411130031140001042010340c620410050b480302108420140c0c890340c560205a104404240700c1d400e001108143c0d4580b281f281d0300910ba10001145000400300701d00391981d05c103860031010315032140300000340c941c140d0f071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 607350494 1250 607349244 607349273
    0x3090d050d020c0603070c021c020406090f050c0703020309130906050f01230a18060b131e0b0d0b03010f0501080c0a23010c03110d02100b060307080c03070507 70
    0x1001401a00e1070640007030f05006041d8020307030043d041801042142c90303000150aa481d60142c4010034140e80e49400700c84410760030480a50064101500000d1189959201c514035004000b01008140c5400d030700901188603040d0042c2c0140d0050260041526100b01600880900c00350009021402ca07a1541c00f5564112160240242c0c2c1600400c07212510000000d060301800d001640e485110700d0000344010705a0049120400b610300031362056003816031110001c1d084010031140c94110755800000410382038021303040f041c013820304488101d18205c0402d6064400030103140c1e0602149079014401410500c42481d813541d00d89042001c4502c43d446514040c02105016280c521014000c2c4824511150720100380c4450501c200300200b9000285041002d4092a1580c0d0050040c2011201e0302c60f8004034107903a0003042806650035400060806607080d07a2407050000d4a610800c008550204803042004500714100007160b8500350740c02980c0c0400c1a08002e424080c0c2910350240c041c8000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 607351744 1250 607350494 607350503
    0xc090102160506430b0a02031003080307030b1e120d1d04020706050a0b193b090706030615020d1211040e0933090c10201908090303090d 60
    0x465040c4c1400070408103160301c91030707040040d46182065020507240090a01c030141c031700503003c8045103035503220f0303007041c862002c0003000541604803a40d48c0300002c40071100054031601056070074201d80382020405104d1740d1701c680c0b245411090a414224030030301d52b0b50700e1198815401c1103c0d40c0007903030b54800e00e4000d08a03850006000601e81c028005921408103a91203444581d900c1000940c030704a040e540072001c0c1034408002e980303140b0301c0707091071030032035170144580c90003150030020140c9000800303400310b400c255001c0c03003410341d504140c00d40c6000131103040c03006800c400000400f29010710050418403101000c001405803a045074001c06810541000c042d40c080c0310180110b110040100c040e420030701844480303200d4091400300703654207a90b82010680078045000950824030a1042040719503000d8a518000d11203540700600511004080c02e514400c01c903c849140c43d000922180d4010308032980317150311034003626035a50f47c0e040f40d05070310b5145c801008100f109460b16121101c229100c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 607352994 1250 607351744 607351867
    0x22031206180b2b060b04090b1b0307090e1f0803070201031a061b070803030f04024b13060806010603020315120c03060c090102160506 59
    0x41e018105036042c10b41c5180c840c0c04a0b0b4041e00c0318240d9030071448040c42c11810b862641c401d143c07070500d000e05003521007a13511500d4401c1400a111611400c41d00c1503900c2e03030440c103649440c10b8400489010503240c00d000640c06003014088030380000c80c500e401c400440900d032084440e0f00b40810b00240d2581110752a60000309800b011540c260068101d4501d03210ba280704e0410b4040c020542a014010030b8140d5554008001c4052071014000c0b58044d210031000e5aa0f24608142e0303041421905550880c01080c040c08918070aa01c0c12450340100f490203400c01d030700b10614440c03103404184003030665030a051881d4440900c990f41c0001410b892a28264042841480d0050403414800d05038000001d1600400411440e41900c507d841703161007049404021061880110301d16149280340400d415100d858280500311003164090009040242d00300c0d0048600300c0d82030003481140340b140d240c1000050241c90321401c05070807140c1655412300a0308000c420503143e80d40c591901e040c1400b20b003504 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 607354244 1250 607352994 607353029
    0x120527010f09052d0c01080709090509010b090c030f010605090604120b0117160612020d09030e032a13230f0c0f070b0a020d06170f0622031206 63
    0xc680c4c024146807888007111003441d00760790300313658440c4044900315041200403000510340d94040c90000c40034000000d0100000d02d131a03d0310758000c1000301c00032403140070504001044c4a9034081201d00c201004000c0c1c4026902c0c2402c1a1425008440c001c3e40c0302006200120706108040020a00c09010b080c5018555141c80300c48000d00d01d640030b11000c0c41e0080009045800c8482ca031282c00c44005242c00c030300309000400000000c0c0a5000000c1c981c41c140100201855844091106080401ca084e21034211150b105010000104941c00c2103003064940000398038500244480e000d410356a50103c0d09240254108220342201801010301f1805101405440c0006400c0b140d40701c0c102c5580503207401030000301d0b00240d000d1007100908404081c00000e40506043e016075404040010050002c0354640100c1003a5403000101c1d0426882950003401031041d00066090213680d10300c01000079501000300900303804819441c2a4180684041160881d00c4e0b140f00e40c60080032032010301040000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 607355494 1250 607354244 607354273
    0x91e110409090309260a030e03030d06061e03020a0c0b0604021323090f0c071113020a021203060d080703090b030a05060906010806090a0f1503080a120527010f0905 72
    0x303104949144060017111160312205030018419210300d42505000d401d1246074000246180b04000404c2c000b2030a0074400905a038201042811a00080c9521030b0641400034045089014082031600061160034012002c50401791071036800c980080c00142c980000464607a0000020364009680d403404843d560b24001c0b0320140d2802c01c60000c0f588030815080c00505502d105c0406815220805000a0002c041003992528000444000341a1031515074808503450000d4021422960160149100a17048110b500d01164030905008154411504480d00e6101c1d0f503401107401142403101d292408984400c641c00550b03c2000c822101280f00e02c0c000080c49807070940a000203052100c1d400a101450307540d0301c0d071386034002c025520000c0c040341645c480350701400240400000203141040040140304146008081399203035502c5880d103416580d00340404490003114801810510080c580a071442c1001d0041e0701c16075210300108448901001d2101101e0410304112a04d5106440029420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 607356744 1250 607355494 607355519
    0x1080a020306010503070f1106040302030d14060904060b0111150105100201020a020c2704050a0c0812070303090f1e0308150303041518060810091e110409090309 71
    0x1040100040d4114200705001078440d000c040c083c0740a00186044503900c041c850342d036224403505013100b15100360038a0b0401a4903035001c10000300004d23080c0315401001c150300c08161030160b000504840780316512500e41800520036403101c1c038100020b00c100e05012003810494254041c0c200804c4141c15450042082080c04c00b5207144810b5900500804a2454005c103074902c1401094418840440f4555203103507082c410f040e14001000211001e010034040000b9000d807256101722800301c072203078560100c280e80b0950058020810f020800120300020b101c2d0700500f105a201c3c4607080c0101082c2d685001c00310140d0f100c2044e884648101c2c0d20300b0f040d840b41809800a45008030203001350103a00210742c591046000c0c0c0305541e5940b140c64020720b0700c01d524840b00810725407900c0c081c044c5c90342c3c00100140000d4807080070880300c201f00421404514410007042a0220706090f01010307900717a02c600034000c19800320344254030038000010358007441d02851001c13500c2a9030b088015070800740d12110f00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 607357994 1250 607356744 607356751
    0x8010b1804020f0a0513050a1503120302070312050711010c030218040b0f06070305070606060923030a050f0307021c0803040807110d0606080c0d1707050307080708090108 75
    0xa61004030030040000003220590340194064400182111022001c034050182507400203402001115544201c0385482d880300e8041d0b0b4404800344441c203602e52040c4138040480c00007528042c5880c0451030071502079401411041c0c464209440e40e59038019039142110421074600000c220b6100345071400400a11400c0c2c5c044183c7c0c201142040c01d1009540c400380e041c2c541c482d009980e26007500640f9551136607101c0984100600980d920240c2c1d140c003c005802c01c0c442240c1050410030041903950080b0400c400b0381e40509104042c002e0300140100f011725040708800d0701800b03455600c4010030014020400925030000045d40d591125205102c14035a0030329048104005481829000414400440b90025080034115469210908001c08111800d02e07213590b20000b1794411404000d03c03034001d403080b9880c040943d544114180180004902e001c80c0c014880228070240e440b80d809098050035600b4000c20459007001444c3c0c1e00c86881d580190b509468540001c10401c040d5030348066942ea0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 607359244 1250 607357994 607357999
    0x10e01081e250e09150a0b030a06050a02070c0f081009060905070b0a0905150a0e0316090c0f020c210c040204171c02030f070201120216021203070c171c080108010b 72
    0x1c2203645c02c00c120400041c0500610031503625240c0000046e50204403c200741e9802180c100542d0401c4001d04000354003010702182c101070406000078a0039014a4040c0c211400880500f241012040610004002e004c0c0300304e400a03036440030540403400420058019001c221401559100e80440240a15007242c0c08a44103143d6488001c92125040042e1221002103003001c0c07440b2380700c02c0b001900b84908044036900e60a0701040004d029842d0b90000030047d0b42c3c90302d03024080200600100c2e110710b20405036030303002040404c00340d410321502c1000c000792180c43c10954030550342440001d0140c0c0c0c803560040e02c90115002081030b040d20113000312040d15140740c840c21746510f00c1e03a001940740d000c0c410001c0710380d5a0200302c030025640550311200b05008001c40865a940d00381054101c02141c0c004160b008009408024040c0c2c00d0000c1200e04041d0030668a1044610b88924041c504400400340d00c083d0203650554012184120783e14050440c2544450015604020800b0300b1510607100c03aa1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 607360494 1250 607359244 607359253
    0xc030715060f051c0602090303030405031207030b06031315021b010606051e0d06170607090f080c06031909050d1404060f0f0e0303030c070b010e01081e250e09 70
    0x21a50b0784d440304030742c2444040d402420070a020306105000780510940d00ba01400004200002c005001c0000c00c0e04625940b403031034603601c4804040b8101d519aa002540043d01040420010a07001240e100650300c69031505801c480840124001d0381c0000ca005041c4240400303c400c02d5000c203006900103003419260107801c00080040302e00704c0701c04484824000360000190300202400c40e8001d2000f0301821100c03074044c03a81c41d846140e52202d0448512001031015540490100e000100d141c0450b83c024006108000302001085075035072000d0a024000c00c04110075502400060080c80381007030151002d030940c020120340240015030b030007640038440041000b041c001c10b5000407d14412070410714083c0c0c00c00241d040280d820fa8100442103516200100070000d42008450050400b44c0c400e4040c902c1301d03681d0322803c220078a801e00031024a90020b06802202400e080204248042c16400301d8141070301c100303101c2400c000c42c0c40542c00d0034040d03088180498405071030304c250010703003040080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 607361744 1250 607360494 607360499
    0x105160c08030a091707060b041109061303021e180c16030513080f010b01090f030605040c17010506091609050f040905010f02280c170c030715060f 65
    0xc01524120400401c000e8012022035105001540005121503100d40b41c00b00401030f800c0c80d01003503000154110f5085042101c0100c1504090040744483e0f54203400c01810030818600300881c0760064891500c100405100c004056514034840c43c0c9403002503070203800001070a000b40420740b0034010302100110390000502001718010b0040301d1020f00c00e040b01c5054140c1070700d0102d46030b200c0c0c4d00d489100c0c500400f2002c030310614089400110070500d20300800c64071010b04010740e0a081c2c0c511403032011030320b15002040032a016812080c0d120b84204035035140300b511011a00001642e090310950b1981d0b4880800c4200d007010303c0060b40100964a000311f08001540c030090600c2d183c1c1c01a41c3c005c1c8220301020580da01c03180c0041a21a03480b000901c1601c0d0503140c000020b42141520520440103540c41a50b40442818500c82740303602c0342d49181d083c140d03684480044c5c00c22141d0801c203903802001702c100444400d01c054550355200e41c0c04240808a0056124146d84245d044015a410200ca04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 607362994 1250 607361744 607361747
    0x60807031e03030e030307020d0f09050901030b0c0415030902011803050c010c111e10110303070806150c01151a120c04030203010903080711030405060d0e010f06090905010516 77
    0xc01c1c00d8100030403001680c000c81d4a81100644002455481d1600c0040140031503540c01042035145c03400380d0380d00c410340e43d1000ca008403142c40b62071103a190000404001803001c100c812a602e9030181c0400d40e074a10701541c841c4190240607160101c07100280c0d4850340d5004640e444489155108000721410342c18500b035460b01502c880e900c01c500b9041c051707107418503010008055200384010344020591004407070802ca0116540609400301c621414002011000450081d4000d0401d060030000440c256900e848065456290150995510686245000c02042902c90060018508800c0041100003400c00310042480c0d103a082400d091941591000e4100240c90a8ad040300410400c1d414081e210141c1c521a02d1244d604040d40550070400c4d039009054010403003501036140b50b40c4607000c11220203141901c0707020743d004042d070202c41005507449610854104003540d00007e4000200031540e29a140102c81c0c0c45c1d8031211480c0c0d02c6010110900400388112540f040d4845040d82e10900e14010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 607364244 1250 607362994 607363013
    0xc05040b01050a0e0a0f1206061203080f04080d050a0e0118030806010c1412070203100b0a05060904020d050114030c120304090e030412030c12170412050c0303010f03020406080703 79
    0x48840801a04c0e035800650350b500e2502c0c04d8000e00c0742c952200d001d1500c41c40c1500400003405021f65615081c10000918460a58080c11600d40c165032980c440740c540d2028106100c10142c425030300b541c02031200601c0c0c0802442141d020f854001cbc0c00060400002c07034a2425079a5003d42011900048440200820380002d81907901c10000d00c0d003640013000b50b01d0302c40c10011041c0d0300300100744114441902414043d4005202c828021004c841c9100c40b80340031013042c0d4502807442a04100716a10401185c00c00c0009401c0c095002071000d03041c0140c6d15502c03405c60740240d000383c40036110008003051030300f000d0040c3c48c59020306440200050503480765440d5203105611510000d281d8038020703114268000d205036406010b00c0e411840c642001404e00500410203000141c2e01410070701d008405c44d078001e14600500c0e80d40ca400040d02d582e910788801c6d84503055a00c601d000d0000404c8500407990051008601802c42d07030240015030741c11030051004840d440c1c0c01000c56a07001400c1440480e0780e91a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 607365494 1250 607364244 607364257
    0x206090a0809010306080a0b04020429010806010c050d090303090801060b1903060807030b061504030f0b0601052514031303080c21070b28020c011b05070c05040b0105 73
    0x700026912103841004a000349195800300c5014000c0098400400c0403109086001d54000c84083c050104d8440702130114003140000c4000004030b040f07201d1410b50103610790903070000c0f050601070300451031501c80c00d0a01202c074005a0005050b03840502c10150445045000307004000300070000035042c400b082040d4441c0d0146804141c141c041e0b001041031081d00300d00040c044580940b80380c00d036a491320035092101a114988a00120707140c1c0311146403240141c0f401c41c0c1d0046120840707540c03640c54110040d040a450241000402c103c0303003000d40401c840407000a5001c01d11160444014106200c844207115442c44140e001040141110400c1c1c40790300003500d070002c144a0b903800c8000350244c600000201000d0010300c040681c0541080c2081c003600085020740601c4c1003513a600100940004090811075504041c03841c981d00c0120140c0e4060300d4120152400007442d10041007802114810500c0240006000001d51500b000400310006008040a5030140f20409d80340c40064131502454 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 607366744 1250 607365494 607365503
    0x50703050c0a0809160f14030a030c02010e0a05040516020c040203070f0807020312180d140406180e01081e0d090b0f160c06020c06030606070f0c090c080a0c0206090a 73
    0x260f02080c000030003070060414030b06508880800855035040c0d04441c0d07000c41c0c492041c039507505c0c0d200080c00f030402141c038142c999419560700c409076015a0042d1002c8000c0107032a9040340c103c400101b42a180e912619004c0c440000400700c8040d47c0c0070009142c070000c003810f9401503005100b8085c840d904585c4801200f0b81904103140181e035031903002c9103540925000808048024000d010355403030122901404038803841d05851000c150710704181c503603160040d102c080c0104100301c20004580b00e04000905c09091114113102c00740e0340c100c1985003107801c0e0005c0b0301036008130003008402d12001c84174003100343c5014080c0159001c02c8501812190462103100309401002a10018200003401280c9401818042065422505013865810891540074030005407013001f40c6050175241c6207041d00d01c100001001e00e40707030201136a111075240400f82c804a5000765507140200e801c014a019070b6401c01c0c007071f545045080c50048004400d0381d01d6101c1c00c40554220701d00b0b010741710401240010b0001c0c0c02 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 607367994 1250 607366744 607366757
    0x151c0506030a05070311010e04231503010905010f0b190e0411031e0d0e0d0822090207020910050607060507110307051c08010b04090c090e010b030a050703050c0a 71
    0x4100c003107414450b030440028181e028000c0b01104001100b500410209000e0360780b00c041140003418082244d00400c42d414950304183d04402d04000c3c11001f050b8000441035141c03030340100c0940400d003540e00d002e0f012500b694491003803240030700c013520800c980d03088100c0c0c90f40d80110b20171603641e645240341c1c01000d42c2600c0c0000060180441141290f600c420054111001c2084580052201c603900e51002242400f0f14645500003c0c420510f0310440c2c08020610002128642c1c2c5070101d65000d491980130a00c0d441d1b55a00854a02410b00c80003001425005a03031500b10b4030401003040c00003401003120441081040c4103a072a40c40c141e40f42c00b07a100c940020070361200312090750702402000d01000c6a100004100741040004507a404140141600b41502c603660f0410a551444090084440702c0c40c003800f00304140e01140c2c2141a4081c00340c100101c6151302d83c902d07100510400d8000320241d1200106000c0040a9881003e6021400b4501008613040869400c016842800222003c0044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 607369244 1250 607367994 607368001
    0x1e080108061f0e060a0b0301031401050c0306150705100e03040602010606050717280522030b0f10080d0e0123090607020102031b060601170f0a050a090606030809151c05 74
    0x441a24010240c00d240c2d5011f82c0783d43c0e4a141c101d401c0d440b501d0303042c00c0310f500300004a9201014a0180c1b8001c00000301344800607440300d031412200d5040070405031880c1c0700d164401c21541581e403283c1503500305100050350745c40e41001c1e0060309584450b80b00000301715003044a180881c1030b031060040e004462448a036520650895500c401520656994400041c0506083c41454019004081c843d20941c00440440400900114003014902c006000080b1441c001140f603014500c03850761010080c541030406940b5081d6141c5010583c103104400704e460040750640c9981c02420705400d1848885402010a1130320390b0703811141c0200d0006d54010700c40442d41d04110780c002e10940d2158000e25014445011104900c15503400702581e04034042a10303900c04508009500100e584114000c038103810b02a2940c1046900800c40104400e04056071341a048000030074600481c40210302400303a50307413120304400401c0026510010007010104081200003250358102c0141540c01000c04070025086e40c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 607370494 1250 607369244 607369249
    0x1804061e2c151e040b0405040b0403180e090601030b09030310030212071806031e030c110d05060a1a011d0f0105070b09030403170a02060f071e080108061f0e06 70
    0x40c50b44141e41d8441440307140f4581d0300040307074407841003504116818404203c442e42030204483c0107079000741003601231000160100b40110039074505049030f50303442e041c1c0743d07034a0b03410482002065400007895001440100240304404020a400c055410051891410954508a03000005110080c081c5044100c900761100040c4082801000006441c070113211400c80300000400080c0000c8a0803020380c00200c1000c06070241c00250707554141c6a85154140588441118811000400391311100403021740703001940c14012240254850440441d05181401200601500040e541410000120010484508405280c800444040d90080001e0355088012a8144600328000d031000b41700d00d082c007006d400008010700c100c0c0d0044085140708032107910303520060f1044540d07802c0180c1c09200440d854560b17115089401c2001401c12000d295640144007180c1c003601c007000307000b04175400d00401242c40103020843e031049073380c80c150840395010305030740030717081c109004400c2540401400544643c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 607371744 1250 607370494 607370521
    0x180414060d02061b160f050109060522170615011407050304050904031805220b0d06110a08130b04140a02031221011a1804061e2c 57
    0x5210300d5203228400f01c50740aa596404014035000074602c0a0000021001489a0006c054800c160f4035420440c2c640b04c4104d8040d04400454548424074240b002c0c40a05403041b800020300c201202da80042c40d6180e14242060b00c002c100d0380d420083c44011a44584e80003001c004da0511401540d611a038180c18440e1031402a13800003608201141c0902052641220241c99800284801000240d45850a1000c050002240c90903640a040c41e488200c1940b07820a40c141c42c03000c0c120311a0292191180000d448400329144c0d44a0b500081d80448e5951110003070f54400b10b950b00c440d480513019640c054031481c00404c06810180785050301c2000d4078060000351503094006048420302810400d03e4121a0300000d1240301c40340c182034011820003d0304811904881c0c03960380340e0803101c0210082031070990280c41c40c1032400408900510084d5520706c07402000d1712209022050130102601000300f801c406401c00c00a50003004c81d418080030008070380c91022541c4624010854403800e841c507101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 607372994 1250 607371744 607371757
    0x9020703050c0d1806030e0607030902030a3002030f070f051608060109140702070b0a030f09060902040608031314010c021e09130b060f06160503180414060d0206 71
    0x94042c43e240c08491070360000301c000401e140c01142100044e030760b10b42078044898200d00008960051400151a903001ea03012001650015007a40d03101c030820fa940d541c017480211414050341400e04c043c5024458610340c801c400d880d0b03a000070b520f05802d401c05428940282240109140c0101d07940008101003802060302c000b09900d220441a40c0300e10816807560024003501104d24a000c400380500341c11880528050095600a030040c0c608210f04d03402079038400c017030650a00d40c690100d10980929442071800c17150040c14002401141c604c1000141c0c0e602e688003812a50043c0591012002081d000004880c1c0301151100049290801612403070b0758100003940c00440f200045075140211001c03904c0d60b40c000c80702d03074040b030342c85601080c1207025035440601080001c2c00094014141201182d00c441e100419071814162070741850014101a10380449041e08045541008860b40e1081074210410440d01400082c040b0760010b620f041c0002c04482c8140070284800c0d042d5114001183c0700c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 607374100 1106 607372994 607373017
    0x706020d1401180e070b0a021c05070b150a031401090b060118060509030703020a18140114090414010216051509030a0507080408011b030506090106090902070305 71
    0x2131070580010010f52055030300115000004201804642d003030f07503005058130100b10900e107a43c0c440d091400e5007800000c1c0300080008505820300c0e41e10111460155084407482c800061a07500580d00c05070220103045c0d00e080390315a06421030241a401108032241079251500111205203030003525030000000440f051100078402c200600303019070001c0840b0400d0b912900000d002055550004182448a00911180e48041c2c05812400d00700d09005900d5503261072404168404c1307407460140b140c150708000a04000126081024140443c3c00864880408100c1100c1e10138592030240d806104580d41c012000300810a51446841148080c60408194a0080c3d6a03600b040c0022a10441c043c0400306100c0b80c2440307500c02000030130b42500000e03124880c01a007150b02c054080d41c0120070316001801142e0300280c0314001c84410038001a66400c850a0454950061001c03004 = true := by decide +kernel

theorem cover : BRFrame.Cov 607194244 607374100 := by
  have h0 := BRFrame.cov_init 607194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 607194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 607194244 ≤ n) (h2 : n < 607374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
