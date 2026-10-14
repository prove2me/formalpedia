-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2747
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:37:37.056676+00:00
-- url     : https://prove2.me/submissions/5a8ae9e2-a5e8-4f31-84f4-92e174f2a278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 493884892 ≤ n < 494064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 493886142 1250 493884892 493884913
    0x706050106080106210c110a231606030218060c0a020102061807030809031516090803040b040e090109050f010c02070504050f01060809190f110301140109090510021614 74
    0x2000910091291400703551150201c0c1c1e80c6d40d0189441e40031100340081a6410130f145414400c1c1100c0802d80980c9060010010070b80840d08046601009664021140e0001a280c0348088029410458120044056400182c025641e410b0000c2c0f02042c10071000d0b006030329a600000e81000c50003440702c650031a00c4588515040c1e40482d0f804140e90703210361007a45a60200c070100b480c2c20101041d07540e25403008000d02009408500c0d004441750856510782e0156511088800e0b101d002d14820060410300c10321080c450a40c0f01241c1c1540b0191200c00000e044031143ca0b01460302006813002555a59168100b20071240e0600c180400340100740e034188054200861200096401442040201f20400c00458206142448210422446243c50705031286050401a080080702002203840c1e002d000d02400642c00c0c103000b20710400c41d400b1348600d0301e40c0c40c18910f4030140c605290704a41b10b000704441500c08000c0352002d0004081511904130f80108640343c8000041c4041c844500954800349106 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 493887392 1250 493886142 493886177
    0x506030117011103070c051603080a05030c070203070e010906080703202e2007031103030f0304060207020405010b0c0c0f0d0210120f180b060d080706050106080106 72
    0x140c0c1118100c400c2580c800204807152030060030700700c0350034880882c00424012415403042004003032a01400c117462114803040c4510080078420f00c0006e012540500407030903070318054000f45610a03030503403e061400c0421707400030b4100b1020740c020811290b4000010300c00f5804074807440001d88809002403407600d01715280c24103007400e2030b99001c243c00003030403949045444041c100d14548240b0040d030030101040091002d0b00c003400d12040400551003031180c40c980e00109840300c0d0004805c502401c60755081d5221500103c107201c07580c81d0184020041070707156807144801544030ba4004c84c6c0050700c0d0000d900c104010f5035410380c08140050700510602c03070b03080310209201159a81c100c85010150107042d010070103844607414040c0d0310950240a0300100c980000008455074880c1404100d40f4220804280c22602c00c0b40720240310003803800d00103000400c446000c54100708000c04d103a1300501261744801903030f8000041102e040d51202c004100305500303c444140503001c01c7c24004000c000f545401c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 493888642 1250 493887392 493887397
    0x8101b0c080d09080909070302040302010311070b071125031202010908030106180510020604051c09060c0c0506070311070b03042d0203030d09050c120303161b060507030b0a0506 78
    0x1008440d0380d0f075803d40400c00142e00210b40b103010740038020302010700d0190300181c025045440240d0209052900302c54074a8940803c442d0ba240c0e000080350002d407640b40c01140c0c55403103885060801d200b151039949089024003014400345840060584110f1708502d4240229030308040301e80190ba042813601000075480809481c1902d00601d0180d5911000114031075070f4007074560141d60041039407001d01c50010f502050300c80c4107600400071100311414000d20803203148502d4210345d0010350240f4080c040c45105400c01640726024100f04800c07907403640000780241d03020180840100d0480401c00c90901c82c00d115542c0181650402c9030304500c1d142d217500450300404103920194048920004000c5200c000203500256005002c80303855001c0a20010010701c04036609940c1403203140b404140c54946022801005200030000e1803c2d503d503880103141701400c0e8640300c001d00c0940034909120142080c0024001d501524001c5483d04144c04041c013140d00f640c10700d600a00c41e40e007050103540c803282e04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 493889892 1250 493888642 493888657
    0x80709020f1b07030b311e0c0801060b13061b06020702011e050c0c0f0f010309050f0303040804030303111314030a020414060f060304210908101b0c08 66
    0x500e0007050302a204050f00340310311904020203440c90141031149141c00380911515205201c40000d040301c02c00320707038107040c46110f0f0001000c00305402d00c0e03026a600e00c0043c0030344052043c0c050b2044c4079214200142502c441d038220400b07548001c5000507903298038004010060480e07042c641da1400381c03140c5514020200e0741000d00758a03000100402164404c070a110084502e811401a0290051400a29070f0380f1202004550780701c8c1c04000f2980346816420003010f18001042c000c072001d00e880c019005828042d000341c0e014000c0e040c00d46444181400254804e902c0b40d00c00903038550461070041c0448014882c0d00c0c04105061000c14074403641505143d0507501182d201c824804105400a0315000300040000d411074280110aa40242083d54450240c001140c10340345d42084071042c0410750104941c00303044a01400e000c0c2c100310030701d2082c1210329192881e020358070540f074450186c038042c111800c3d50f032940d0361841030641c2065044a801901d45903450b01d034060700180d466409042c019282c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 493891142 1250 493889892 493889917
    0x50f040c0b090a0e0708010602010f0605030c151e0a090f061704150915050108030a05190c061d010b0603010b180d021801030501060f03020a0303080403030b060d06080709020f 77
    0x142d00c0100d42d4a442c048801030134400301915462514410043c0004070a100740c01c0950b003404d50500044d01d45025040944002600805031660703003c0030044411058903c140c2da40c4010084005a0b606290700080b001d8115210305030764510022004154001c0d6520000d81c2c5100c1030360038000d041e480301c0038102180d8180112031140d00da0f0306054a1401010211525080c500942d60f010013003c0b0000b2144801c503140204001c0c2e90f50010300342c4a2040010b64030020320100f00b107440d9482410b086001c04526032030072903580072150392030345d04a8407500b032900c40d4a0500b4040901c10b400074043c444115030241c03104d50855241000c000524003d056201a015a003036098444940b0f0303461544001c2900100300b608105103050381c02400040a0100340c5041d402d00e030001c1400415002041c08481d0f001c0c00c17059500d851602c0c210b54645e40900201c0030992210482d82c560b45d9502e001d001c070742c0780d0b4110000b03d031480d114049280011540c03054601d00d0050104684000404082d00d841b49403ca = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 493892392 1250 493891142 493891147
    0x18031214010909020a2402011d070627090b0f0d11011b0b041b0609080d0e0d0b0c130e270f0a05010f0c17072619050f040c0b 55
    0xd1001600e85515900304601400c0d86503090400700700c10b851340842c1c88121f0b8000f00514080c4072903803101c0d0034a0500250b415401010100803d500c2180c401c035003001c01c0786009074101440caa8090800d426a40b0031900f45d80c442c1c4000015107000c0c2e484a41821044072060540b100d10398a101c1c0d052840791b0403d040c00b070840e50b249078241c08403204421580d40303c0b986070245d143c5450162038401070400905102400710b00d000c55090f000d0300c2e0500a40728404014001181d01c06003c0314502c4c2c20004141d003003401e0480c5040000c8015075024080c20100429945460b4520300324551072146c0d50114034214010001e2080e1120a044000a886403800368844030720380082030369180c8904580140c1c454441d1030507110902c00c044d8132081c40c090300740c4014230101014140841c0c52024018500c0c04403044900800c20050044401054118a946180410072904e01c1803044000044030040d00c0381c0702c40850312400c1d1155102d100d074010b100c0c4028071400c0c1171580718405501e013107024406111030300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 493893642 1250 493892392 493892411
    0x30a180f031209050102070f0303060609120b040c17010c08130f020918060a09020a0f08030a08090c061605011128021c030b0a0504021e030c070501180312140109 71
    0x90f401000159401c84025542c03515540b0302900d4510003a10280d00080c139200c40424018410b0041d201190b600507070010001c4030540b02c00081d00006041140d100101d503000003400304240b01101d00b44076041000050000b61014003902c140e1000300003610b91107040d40c03800c0014034134220380100c4980640d1003400c559946002450206620070310700110340f10708010404001031640040654500c282c0b00e94500c40c1d901e8442c0c0440e80003a000b0004581c00c24006000d48511902d18180e000d489001190a403211000201b2402d078003041203081241251282e0314144002405002264110050b03506d240c075940c10002014441c03032a01803482411050031a04400340308002d00b400c6816610f4118015811038a0003400605040c0e000c0307409800d9035800007805140510a9603101001250a000c0440c981c120400f810b900003000710661807000e00c10040450400d04c51040d100200c480e61417031100711403c3c050b18512580f0840e0360100c0c10401094803000c000000141114854000800d22002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 493894892 1250 493893642 493893677
    0x111321080d0605150c0c010302041d0a11131d060114030901020d0510030302010c030b0108070e060c06040503040e090d0f1d0301050f01170106050906010f0207080f0102030a180f03 79
    0x265900c40c55010041c40007244c1040760a0000348205003190044a43c0c0d000940019400c1c3e0066201d4071402146402c1c04440403011201000d1707121980c2c0c28009406c1d41c215100820f1a0440702c409031412080450a0008003a80039000c01d1400041140302c0c801d14010300000c04441d60710110954011011020480c0c4201c2501500c08400c1103110074400b42c500100480300004052105900640c240b422240b8424068802c2260100c4103039184075950740e030710906807202800c41c07a40903003040c4208045000c81c4c0041c044240110311407005543d80f149413105c005190980a0301c02e01c080e8001201d4000500d03000f070b546003114a040e041c445883c00002c03011200d04a46482e01d141c140d4200404c0140c1503400d0f1500038140c1d0742142401034003404c03881c0500d00b260302d540200c50300249940040340140d03008901080304031085204a03844144c03075204250500c0411581101c40342c0d0040705000e2443c045009503500a102410882c000a40c03e481308500c07076518050240c00d011b0307014020f510344c01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 493896142 1250 493894892 493894901
    0x1030b03150a2c011505041a10020a060f02040816082109060a02010903140f09040f1104030f020a0518060108180a050c0405011a0301090c0c06111321080d 68
    0x401c081c0e2880820f82c03011101070180141420b502e503510b4003200c011070580f1b0507125440111400c0c1c074441482e54452018050b00551a02d13076941903200700d44111000400e5400b030030b40d400e03000740c6001d6215850701081510b044800000e9195445035003005010342400080d500241c90041c049104039911040106100c901c2015400c40d04844000303a14034030190150019841584650b40780e008580e1100c0c2000180e0051802c8547d001c0d004101010807450a50030003040307a80e00040019030000d001012004681c170503881252a464131003005005c0d071429181e01c45c010f010503507440300300c2400040144004040100218103021000c0d0101d2006401c040c0c074000f41c15860f104a5040d1042c03030030065030700c0000002007031103070742800d00101d4123400b14038210400707610400c01c45081d80d09040891000d08850b8022404101c403aa00e031402040301c0d406a01d44010700c0300209983c071418944181d442241170f4120502040c10a610083d200b1705840d503510740c0c00c0c2c2008a890301e031041c0c1c01140001c2d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 493897392 1250 493896142 493896191
    0x30e03180f060a110c010e0d020609030102130f0f05040506011704051608100b040b030606010f0512071e0e0a15090b03100609061b1707060f0b01030b03150a 69
    0x10030302040301c07180300384c000211501d01034201d01202c4040c9000b00045400440d100011070300000809610030060a2503030140c40302d200000c3c00542800d03001c8454100c00009580010249000c501c0300304140c4603c8000d031400f034072058a052007185032032400030b46051825030b04400c7d516042700002d0148401401042c034010000f0084001c503503a82d41c0002c2d40e800200010b050801d241c0485100540b400e48203100c1054406405444141d58000c01911085080c580b050184001081188102d61626412511418035600c0e00c40b4040f0362100d1140b405920a05040709200c40211340c0c669a5640c1100740044400ba031158210b80000c0000484440c481980305441c03040011042c003004402d5030300580207603034465480c000e090342c0e200c5d403c4070310810a0740c01c880031001d00040d20303000c00c8522043d040300450856403240f038150b069591400312811a01c074480d0070b07640c880b0f081c40150f84c1401030380c070040c004400801850311450643c07a4240c802401c02e4181a694003410f5000c86800010315a50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 493898642 1250 493897392 493897399
    0x1a040b0f07210909060605031b031807082109031f1413050d0206040c0b07060e030705061f1d04030201060302030f0a02040c0305010602031c151d07030e03180f 70
    0x3102a80c56014000c0d0b15213000e406010750500101241542c86801560310800640e0103030b07005040d030442400305581c4090001010701c0004d11091041000801c40e20b8000c00c04a00240a039800c89201c40340c2700028004c03101310099003001a07080780e540020301711106011048080112000c0303041e03504002e00d940f480007881c0080c1e070810003000c1c2d03450b41800107105014506640000280398802c98541800b160010b10348024440141b04031300580000d03144151054000103010b0341c141c4511803440e0444801141c10354444400c00502c080b02c40d048403000ca85104e01003085c00d044c0503514003002043c2000107084000e060002c0d044c14800d4021500954014050b6003041c40c003c9821511421550340aa00403401c0c983d2000103a0b101e4882e917412070760790340d014509110080014400103010240c2d441c214a0300e500110354410358440c14080209034826141d051a001c100d10000c0b03040300202080103152900da001e4520940101c1103600882c02c04e000c0344181281d1400040e120080c401c00141c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 493899892 1250 493898642 493898693
    0xc0d0f020c1b06040905090a06020d0b010908030f0a0806060904090302030a0314060906060304051509010902011803020306010509130b0703050702060a0603030225050d08041a040b0f07 81
    0x842009600030000900c070203068540300030001c002c608140420414998000c08100000c00c01101154402034001e030305001507551844a5440d0303c07040e44c00926001100c01e580701000e024035078000200500502070800550308200c03008405001901640c210300041c0101080015200d41d94481103500c648001402001200c007642070013940c98004401c00b8004c00e20f03248030ba001060305030010606c5440010b10301056603441c0014030205030800f0308100d401d03100d8411001c90070442006454810b0b120300b0000580d5824034000100b41c00348072910a42e00345410401400940c03000b0601c81d041d0f0f2415280356074903440300800a200c501c4404000342c004840d40703043c002c40c181c0c1904800d0003081280d089600e161110500c10741190340501c8010050fa100002c42200d140c0c54100e0303000d8030300d40c40b03205160b0a540e42c000309145130703c100e03011101c071100001c0074800e890002e40282c050341881034607503007402c1c10054101c146202d0510414140403012a0003802c1042d031400010510840d813a0480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 493901142 1250 493899892 493899911
    0x19150503070603050f1e0103030c2102010e0709050f1317070302031c05090703120e1e150c030315060708120907120302250f06020d080c04060c03080c0d 67
    0xf40102419203000c0382c1c0c80b00ea6800315550099103e400020404041c112281b00e0f443c5540030750764000340c108220740c01344101d100848590045145100d420459800106100c40600d04403418500d440d0040601d60745482c091000d080300c9900c3e055880900308680d0700c00103096007003400186000102d20440c903000044e40808240d40440a444007000345005018080031a60044051f03034412a50100c190340001c0c01003001c00c0c015450282600f156040161604104101280980b071160301042c808502c804c40468481c01c14000d46d5440082180c00b4500b0715003200b61140d01c0380300c041c111130504210f00101120a54074902240d401aa02c104540d94408421118414411049035021f0103800707007210000741441aa400b40256640c10790240c580346405030f01c0b01d40415080e4104004041e400d0314003250402100030a07001502440d0000d21828150341130044c8041001059404454014001004a581c00003c400b005d144d150411100d40d42c1d902090800718040d114446548904240e52031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 493902392 1250 493901142 493901147
    0x9090f0a05210405010e09150a0803031803090a030305071718030d080907030f060f0203042a030c06031e02130f050f15030a0f090c060e0108191505030706 68
    0xc259021414038160201c8010b80e20954901941c841c840c0820400038000046103410b0381c64660004202006405045601000c2003218480d0b07000040326a00020500100c1d0200c568a000d800220b040218038142d218000300b4130f13110540c4002024000045141c10810001d40c448000710304c684030009456010f0403441412a1070030422a600034002c2c0141d42c1011842a4a094440d06020005102c4030345550340d00321281941517070a1301e0726136903042071301030040107400214061402610030540c03144462200943d1403088044000c281640e2890402c002003901170b4050450740340d030034005240100211902031401c00f118044981c5031000403140e0001032200404010780c2c0c10a0340780d00209480d0800d1050600e510403407a544001d038020700248840c19000255231011280101180030313400c4600d038bc0d040d43c070400d0003100c031400144000e008045d4007500c0381c0c9100000b4a080f502c0d905024400281c0b50b42c0d603e10b102d074400c1d26012824a00c04c0f40065104c0240006000c699a269448100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 493903642 1250 493902392 493902403
    0x918090312041a0609040c0512010b030d0509011101140a09060e0d020709060806012d0306110315010305060d0b130b010810050115091e09050a06080c01020d0c0209090f0a05 76
    0x800c0d50842e446408a0313642d003083c0011600c41c6030700004c4090b50324107010400c40e2980c1010164601c540d200e800360180e0b40c07401d000514000c40300d034a982da1580400c20000d0601d03c0c0d041d1071180340ea07140a02008214a4900000e41c008145042c00074001110b42001805800c10319281d42240c071071081c0d9089015400030f41c81d822140b5403a0100051500c5590054407400c0a100d50520010782100c0c42041503d00f01c982d240744902d0000d1401880e0f90381d40c940f010b940d003680b030920a070706000c02040408140c6009502000c40c2c2468200304520f0848000307072500520410250802204000096140c0c9060b10441c080c1d41c0c001403041c0340c560351a003009030303102140f4a0cd004074508200c000601c285010840d607460b021542c96180791142050107403950401042c042c03c9180015000c0025008403a108a5026911001c000b144003401c2460300c0d440c01100320b140e1070444d4031064250000302c1d881250074555682c1100e0100355512505a05481c0c09906044800c10780100e1a4200c03c200e00040d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 493904892 1250 493903642 493903673
    0x306100311061204021002030c06010b07050d052b1e0902031605090a110412060c020f030405061c0b10120b011b0803090703080a1d06091809031204 65
    0x1081058400000c144200c1d0f000340b000d076009182c000c002003401842c0070b44000820901345c0c0b040307900b00350140640b213107080c4c1d00b03a01585910000003038800900605000c0b0b07107030300c1e512410064508200c50b0202419035925030001c5008808814010b8036041007604003003012516000300c45110321903000352500400203524120b1203845001c0110f030720326615004910032a40010030090f45503540742002c0015104010314082a41802c00002c5000c2d5844d0502952075805451300007100b29180d10081d240c980c032050380090550040c0803c0203a59149011a0030118404181030403a8044071100c5024204540d5240d42c4142c00941030000300b9800341441928412400060014101c07010040d2803c0400a018601d525041c1220402141c070b25801550003540c040c0032a41c02c503999454070012a040440f043c800118480010f402c0441d03d140ca090412008079816854200210000781e0403a20090101d021500942c00017182d0f1003061060b0740480a2148101c40c1c03501d020700d07040e00040f56104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 493906142 1250 493904892 493904903
    0x912030c090f08030415091221030e03030a0c020c030a06230402011b020120060a060504060b04030611041e05010f020a05061f0504021206040501120b040b100503061003 74
    0x7040080c0500340c103880c14044800b107801071441d09061041a002c4910080031904c10700803915030000f0801e58009641e6911800303071100c40d461103240d900f8030072030010070b43d00f4104160901940720485a80030040300c0d00489555000100b1041a40c4161705021550301e507240c1c10301031072400c102800515005803600c8804000748100d0130241d90340020501500352006800503c0c881d4100f081c1850a1810740c0c220341c014103200105840c501d0045045075200c03410004260014014001c048525000704e4002e05412142805141d0400d51801c901c0c0c0140d11002c0c008544134038a0603d4400390030100e40142c0f007c0c0d000501c81080c800b00590400c1c3d024401c0e80d000425036210052032510105007e015294044054440d54440d03c40040c1c0442da0042d100301e05010441002545548030320013480e405082d8000c9206a00c2d014080004030b440c140e0001d001107800d0364012000881d008065648594030038a09a5181c0f0b13108d000480c1d003482a000260540309120a0000c41c150a5125404480c8110b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 493907392 1250 493906142 493906157
    0x140c1801020d12110c06190c0c15091109090c09100308070b040501112208060106020307030f2a12050405060d180b0708090609010606120f0912030c 65
    0x2001280d0300c0c84240100700000f00b030800000b280d0b03000343d004911080c0b103030040c00341004110580d0f141800c030150b880b05100c5084041c00480b12449010b43c1c2c032414401e050001030013003944c480d039509000d1070540b006101d0340e80d5040000c10992003c540070403400034024001c0e03403030045902ca42c0e44004240d01c41c0b01740240d5000071010075003414140f0940307501c800400d05000c110380c0ca0052040e006841181c540d500d03a0786003041001007034094040f4200b61041c44002000c102613078a69024150400001b80e0010401440b44a40000440780344560624042d23070440c0001200301c40340080306007104c00560240e1550340e0041220043c2142050052208a81114030f049040e10309102c2c0f03105040e040042841503007495082d56100c461540c10342c0c0d108a5401d5061343c1c0f1000a13039412528000443c0748001840603541c010424240d2000d0504001c1000c0c9041107809420700102c40c070714050f44d80e221032040e0b02d00f0619030000b01c656039010f88000e2030360004103005005029006160800501c15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 493908642 1250 493907392 493907437
    0x1504080a120c05070f06110f07200f010f0e0315010e0603070f14010318060203090714060711030c0405070905010e03031903180c060905010305060402130e0a140c 71
    0xa4410a402035a040e102d26184c103c031039a980306a200c10500c1500c41036135403a20108041648030061440804280300e0030381d0b541c07591501407403034000c240b10a01c84e50701c00e04824105440b81c18440c03090060034240240c2044001400312121071921210b59058012242c0b548400019090b001c0d0694120480b180380c280c0d103074401d142d5903241350300c6001c42ca0348104038108003903002220035604498042c0b4020170400302901c1e00e03010710010110101c50703842e03001040010f0004140010030150440721014200a040180010400c0c002d048005e40041e034686d81039015903070b0800400b94140c0000c1c1003072055282250b0080c280c400544100da02145051416481601c1c000c81190040c022955074640d0085401c5802c400030000b070b0360050003a45090f0000804501e405540c44001c1c000d594540c2c0d616030602000500340c0e400038001034091801800505001621031a03208103076070401c4000e201c1941c0318000c00f00a440c03941c0c0d4004c00c410141c400d0000080d03000c401000951683c0c05003040d072501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 493909892 1250 493908642 493908677
    0x20109090c020a080c010e030f1207090e1501030e060f160c08180604050a090510060306141002011107030e03072c06010c020402030106020105150f030309121504080a 73
    0x21001c1c140e60060300422020000504000003401c20700354150b00010340710403110001c42c80d6900c040d03940c2c6071614000c208a025052920800e035880061403900141c1c03e45400e450307902509000d4195008100003c1c80710016901c242d010010040300c000480b01c05003031080c0703c40c45410050710724070f44414000013401c46c0344e070040084242007a406228246001c80014400750050740d0300c03044c03a500c0103040000140c03da4030460160b000e8044d000b0005694140f4802c5c3c0c544100744e42d4858801d250411a0030007041d0200c03054038030454420388400100a010010490060460040e2903400080c08030303004c014590300052060390584241d08541c0d109440d040c100d450070700020001300c81440203107009800800e60101058100a040c10459460341d4154001001e0341c009812400060b9510000c010ba1280003440082c0040ca094030005034844040d804240c136440b400c006540150034100d084951010100003041c8010711004683da07003400c05140c60f080036440503003000000f03500c4034405003040c43d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 493911142 1250 493909892 493909901
    0x61809012c0901090209100608060102010603030e011809050c041a0331080304060e1b0a09021c020a0905150301060c030813050609060108012405010305092802010909 73
    0xc40c1c6154622a00c120328035900e06001042501d440d5240c00c1040c0040c0c0301d0110030b07030058009000c20081c0a081140040548500814041c11681000340400200340c208019450443d4203184c80c0b000812000f5819800401d41c0c0e104a405500c0c0000b040400c01941002c1c2c01581c40302d40c403480f41030340010784055a501003659008141c3c1040802400950303201d6542d04603070107070386403041e0900140340c4903103020390801c450039a829070b121100407082c1641402044c40c0c04e0b07003000043c1c4043d050385000c189160900c0c015041302c13980c001204910004201c11425210031004010740d030b981e400300002014101203105150042c1c100b0800c101c0019100002e0b00d0584806030380b40921603050303440884510130b001c1c2003007005801c0e20044a000c950103204540c030504c03000000344000d51500baa03060850b419211820502420440007807600d050385540501140c50074a404240b507141c0c0ca403224241550b20b00c541030000b50751b002d86000d005031030010281a0717000b6203a8a1005035222007120030388 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 493912392 1250 493911142 493911179
    0x5220c1d04150903121406040e03190f0e030a050a030320090d021f09061202210901141006140c0606100e1c060c030b0901170c06180901 60
    0x204480b108000d1588a56400320124a01078a000000b040310101d030301044804075480080c1200c4000c00f049031605043c00b80d01c03449001480110f1429845200030081c0440da02c0204080045042910f035040e0310545043e5410745009043d600f00c0140707450029a15040c00c4000c6010900b000d01000e03000c05135812214480003d0100130b032402201c20100300103002c4448040303038815906150702c0e03100718000800c1452104c2c01d40313a8010300c2d07081031009413441c0f848030302100f4131500405c40c0100c0009100d00000304681b581d01c0b07100103621040c00c7d4a000d491044020b100040310042080460411282903404550943c0c60368114607000104c01d003c1c0303200340c1000c0c12095109a0100d103103070401c1014105000464030303003a0007640c640300008962020703e242d0641c01c041c4c82c104460602c1420b115888440d0034a081c01c00c0700d2440300b0081007034000c0500c600320010091501885110005010a6001050050406a13502c601e00c8000c5500005400a00d005030541380010801c0714006685410704d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 493913642 1250 493912392 493912403
    0x3060f0b0a0605031e0c0307020c06091e0a031a0f070221031003022d09060d0f080d0c03020c0f010603050c210607020a1505070903020405220c1d04 65
    0x201ca082c0b4005803aa40c1c0060884c060001c0741d40c40101411074445903240c011003120a0485d56400c03c050020f00c0e040502454030b1041d1401c11070301401d5034803000c4030a695108101030b420318808010015013010002d61000d031054500550b09900c8400d0101003500c40d030800c802d02d40303032912090070403a034034036100e080c84620701035034281140c82d01c00c4400038590110314110278400060326580440e00b551180ca9228402c40c40554080e6051210390b82203900310141901c81c40f0703051a0020011b800340400e0782028041502d0308e61564240315250702241c0c00d10004107814017683d042404003c000354444039680d01c86008108403045519418061070382280d410200a1110089150400800c4007102c040040d034091200f42c1b03a1040d010600120344609007940141200e0000c50900ea01089259000541440e1900c820070140701e404c104100142c0b5010344000800340c2d100c00b4000151805e190b12050b41040da5032982042204902300c0006962041d41c0d03009038041c40e900d141d007400d0815034000b0031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 493914892 1250 493913642 493913659
    0x1508060106120b040b120606042712050f03040b040b010e2401051201080d0e18070c110d0f170a08150316091a060301210201110d0903060f0b 62
    0x95412540283c4107000001304006a4410350000003070403c1c0c00c0c1c94040886030401c00030040a490a885002c0220340d41e0002d444a00c050b01121a480141c0d4a4008001d0030710054100802e500c5070060b0703020240381c0f444099603400c1c903060200a11070202c0707007203809004080022403ca1020030205000c3c15503c1d000c03800c0001d00b4400120340940080199040210a00c4082a0780c0c03010f080c500d00804501c2c020b03220724481200c00800a080450045000790403904010001703003c0401c509900c40d4a03482c00800d10303034041c50031a600101000d0210b42c00300c8184405800e20504d83e80320602c4902c01c147c042461003910941418900410101d8408207000400061200100c1180751301841c50050540301c00440d030703140c0c5031403c00303030b82d044003940907510907101c1a924080615000004421140720741550315120406400754140e84080e0300d5425603203d0b610469000b0b440c1c01405401803016503000320f038000310003082d40d0602d1205440640c20052b8450321488240701e41c0c0040c3c1c070701604104 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 493916142 1250 493914892 493914917
    0x903080d27080d0b0f0a06080a0e010c140315060403080a021006140931030306210f0f0606080114310c150504060e0901210609080d1508060106 63
    0x200038140104c030241c005130800d0071070707143d0f540b801c204101038151500e401c003040c02c0111f00401111820b11a0007510382c90842c2100c4034030707005183e10028029141c0415581d541da811010b034803218504910790411004100031040198460181018002076400c568903041081013400583e60184224252960459920070403070500701d40302548162000000c516590500012022a03240302a2030b41d131008404074030303004059040c0954002820400c108094002c1402814041c0038103880c0010300b00480c04181608011402c00c410404580000c0c00b0020f01d40d444840b1406000e035031031307010a298149000561641d2281e5142e8140c2c5170010249020341c0040603080c060403010550980d0002c65450000078041d004501051500115a403402e4131513140c0f2802600214600459600c5400c10303000612007000d018101014042184155202030303401c504201d4000d00380488094445000011004144c5086410030300c801166071410041e81941c2c0c80959403620028050000000d103c20502c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 493917392 1250 493916142 493916167
    0x170903060a140c0a1e0e01110f120711090a06060306080f03030103080a1e050405180601120c1704060b0f060a17040309050306090105090f01090206040509070903080d2708 75
    0x1400c074640c06042c04652241d5002d108814413014003091000507040304040e1a007940d001042303840d403d040317000815160440ca0b1895803200c072401983c030800e030300101d400028410642070709a20030340007074100d01407420503050710700103006030340625404281020030000700c01c00d000500c0d2100b03a0401000d1350950b400c66031242d040741c0c042c1031114108500c0c082c04a14000c0300c00c03850b1150042c2c684074103035107500d008203020300140034180c905809005082081700310f07600461900d040740c2c0511030024082880030302c155a0030740c001c141e000350503055408100801002c0e522580307841d41c0403907804a55010030300c200700c80340c85510314100000d480a40c143c1262940b681d0b465070414800d040041c011a103840c0801c0c40c140c0d00321030802042e07440b0024801c190606100d4840e519071281c0082c0a02000c1c0d4000c602c4a110f103200300b0b401042e80c4000910424401e8124102560703000b072101d03540c0c0078091100c0d0042c003500c00070076070113091110100c00c2da075501c3c4c0a507000716640200c00c5400e0580c4507500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 493918642 1250 493917392 493917397
    0x3150b1801090503060114031c1d01051308060a0f0207050709020304080712050a030606020d05091201020903160303030e15010312142d03010e010b030a0603170903060a140c 76
    0x4030341404110000481c2640d420b001d1680600b2800c04840000c013a00300800d4900303100b1090341c0055404011802d02d4039503001200c4542d0103050050018a1080000103c84500c164440031014285802010424480205266001d41c40088043c040d03814555a00400c9202d608401800390740400c408002c21483c58010319032090280d1801410000305443ea01c4100f080020b200c0000742001504a030320035010710801028204500c002c04200f04c500c1800351403172007441e440070302c1a2401c40c250700341d000b030940482d8185c50000d0290303607000b04de00303110a000061502088002c282410b90342ca9841500040c039a00703d000000e41c001040c0d2840c3c84507182980783c45410b10401040d501da04903440604002070483c8481e440d035501260304020281e007a0400740c030341c0030504800308200400143c00642d00840c1520003000c1410703502d8840c60160001403803658001000321910030440c60707404107032b0000f0748a10308065094030590754504082c0e90450b150107200741c0740b041002020800c0e40724910301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 493919892 1250 493918642 493918687
    0xb0307150915020f010609022206050301052b03200d050306010c03051207091401031806240902030a06080606130b0612090d03140717060a090e060703150b 68
    0x40d140c0e1080400130143c00d441d45500319907080c03034001446500b020121444100e01f076810612001240b42070a038002d107507110600c601481401200205440e11050000261800f20144000021048186400b41c442480f01c4807081085a02c1400303054101408107003804810503595809183d44e0f00c241c010741d030009881205808000381407101c0030200144090703c5005800750b440300c0100358606a0115821114000801c1c101403c01c107540c80020200c001074140b1607841640810400134050701280102101102410228061a400100c0e4403481d4010f40c052122144244005a1500b010350b03070b104001c3d02c409400140c85141c0440c540c0c0c09600071020004024140351405c420b551004d04181c60980d8a42003035040301004907040c0e50148030b0311040e80076040c00c45116103400c0c4c401030002c508004100355a000300d500040e00c10781c3d892a01e000a04508a010000c641041014544c0d40c04102c551788003180c9004003240c10843d030620388004480c000001640340040d080c04101d105085600b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 493921142 1250 493919892 493919897
    0x7110d0311010c081503030f071106160f1a0c030402010c061508010b0306010504090206030129071110080c07080c070b04270209090c0702120609010b0307150915 71
    0x10701c0a06001c0038001d540c1c00218660303d50100f803c0813281203a264400e044101d102c0e91041011011114410040d40d48a982281d07000c6400030228020035003a100d11160030803aa4008a1504200290b91248100d100d000369100244401040300460b24000103403000c9101c104103000081c0150321500e4910b2086102c0d0f440480c090000d140c1080d000b1340c554015000b66512070005486a0604001d1703140100000c0fa4180040403268010a20030710040c0941120800c1c29082e81804007465115400c264640000700d135a650010b0414260007031035001d03858490002c4a00c04040907125131652401800c000d1500c61510a041e501c4410070ba0222141e11020b014403840000c1d0b44e200b81002c1c00080c540710552101c0d0400724200c070403001500210103540700348188404c5110307890394141290301036050020300341c2d20103a500018807102d21083c5109094411042040041c3e441900801440e010540403102201d0f240c049120851201486004c00189000f404010f81180848403800054150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 493922392 1250 493921142 493921157
    0x5130e0f0f0c01081b030106050a050c030406091401080f180712060504140d120218151c020304151509020f030f0c070c03120e0303040e0105011407110d03 68
    0x1604280d06210440d00500300307940100200001650308039400c554031292120300100000d0412821041600060241c41d0400c000071500c412098050300840c0c00c000c00b5001100c1c1c03a15a075603001032000070300c0d0003190340d466040c01e0b80d030803154090314510b0301030310710000755098690702c0b00b000d420841070790f04010510b071190120001e0380d07507102d600da042400e00030400402c491405081244e01740000b42c000c07070003030381c41141840d48140d1300516480e034040103100e002d642d4100b1600302088409900f55480d07481a80600540707001d0030810018519100c1c00c41301214042078032610b0a080b4002154080e110030321115075031082017101da0101301051076200c2890301c0592220680c1040380c200002e14070040200000b441200c01084045550180c80329a00303601d8801d50341c0e03601400301841d00c4020300f034500e64424194a20f000ea500b10317035203003000f5080365205c5e9542c40c0300707000040b420b1084030f0115000740c0081c1c5036208a107048801454100c042410003904010500041d010002820346c1000240e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 493923642 1250 493922392 493922413
    0xf120215030c07080c0f060702070e040b04060b1309060c0203120109020d06030f0b040309050a08251505030a0f14040f02010212180a0503010507091404060308030106051c0605130e 79
    0x1118090175044402e032005000480030610300ba864040003810300410f55020302e03001c020800700e003200103074413030342c02250081c0c2e540300e134030344440604a044070340c2c3e901003038604900700ba6410759801a030540e4050a414032000c0105441640c41c1d20400d0101c001008074240180f0500006030001c0c0041e1549480000d416aa06e89a0020b01000e2200490301598000284000c1c954050250805020100c0e1101440c524088040c1d41e120304800410700001c4500780080701501025003c0001401d05882c440403030608028000c1c016070088800ea0704851804a10340080503482c07040240171034510001110700d84071901c0c3e08040c0015039138100d04510400c0c5480000700c0e284e10180c071581e00700000308040c3d030200e1404c10030820b0583c0c118a0107a8582010840c00c154800202307030481c4c0502c05142119003608000c6009000950805840c00c00004000164240d05c03800a00c1c1e800d00310b050020052100d058000b013603824034491141d1001491020401703020036a40100c001c0c5180320125000c1884 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 493924892 1250 493923642 493923653
    0x102061005030a0807021c15050609151905060d0c080c0c0a030c151d0607030b100e0303040308120612010905070603050606070b01080105150a24180b03010f120215030c07 75
    0x500c1f601c225646000221508080341142c011343e41c102d2000c0356020394903d0b260200214090745083c016102e03140b0031072030000c00c0307110107143d00203004081c1c0240d61f9441e2002441e00030b00a6116039500050500300000d00481c014015610b12150b000c024183c3c1d42a5a00c1c11146141c890105940e20715800c04003061002503840b40106011146041c0680f0401f4214014144840284078800f07250402c46145045e0307807240e95501c940e0701c02e8140345210b030b5000030209140d400b4a406c020102d850001c1c0e0040d074010304849452207108210743d008546030340200a50b080c0c842103d8001e100d648991000e00859000360402c80e8061000340169003400740d59250b089600d5801c1e80460240e0755500282b10300845403500d84191940140d6440c900c851601101001c0485080c91410444001c906400082c0e8403480c14504800012041c0c0f402190f2a840c2404480e4000c1c442c103e005014228006820701c5528601d00c0242d40040c103120004071002c0303141307005600c002d0000c0300005080041400281 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 493926142 1250 493924892 493924939
    0x7080d051918020a0504051816030c17030d1805010216030e01211d03070302070e0f070e040e07081b120a0c141f0e0102061005030a080702 61
    0x4004261005900c070022403a1044804041071005550540720589000d43c0712052070034120346040c0c0d000203041e541c10101e410703c0301030149010345501900030705040b0b4840810001003501c0c00b03202040c07180c80c2d81d0300800f4420398140079514a01d40092003d208d10082c42d50005200f10b014100c80100c0c0c1076a80d840c6400ca80c0048407130b60f0351b02d020b1040c0c13200341039201c00c1c1249900400c0c01e14010704c00402d00e2500081074002a8280c00c6916404440341100c54100c0802110445e1000c81c1c1c0c403000c5624020703480b10b12500502020201c1070000581d034a084410342802200b280e143e40e01410301d00c0d803c2c000a131140e0300d00240b151140e00d6001030352500c10484102205c0c880720f82415050f40030030400c400f0701d184800c42100c4e03074010645000071500d80f8201d9411298004801d80b070070219080410400c107201c82c8200340c3c84d10501d002520603508540d6600c034540099013a074410360385121060080c0f00c0709000e0140c06900c4000d0213400110391f1001440340d03500040c89100290502d081109054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 493927392 1250 493926142 493926151
    0x606130903020c09040b04060617030405090405030403080f04090f02161b050a0b1201090624090905040825050d12020409050c040302031b06090105030a0e0f0622080f07080d05 77
    0x80c1345440030042400114449c1502400000c3d503004800741d92800169568000c50082c00e1007003400102240c10040704008880041d5448942d8580340e840130b24601e012600a84218442036080020079402c0d124244201c5240010262031f42c0d1642807141c0b01c03103148860341500001d9000c00480082201c0c0c0e2a100007000034000c0140c80d80d070f01c02c10486105401a0180e00030882d59041800c1403240d80982200041d088480910000c16896216030844094100b540304003030461609051100303110307802c001000d0250b404001c0340cd880c2a0111411600440c0000281281d0804240611424850301c5040d0b41c003000780c0d102500b420b072519454006c40300207854100c40c1d040000360400c110708040c4150548601c81018085a0b0744020b000b20f504c51050140041c10000d002001400069050384010041c0e05a181280d02082d400c1c00040e0b900c00f800d46a100680750010004203d0803000c40900d03045551001c4824208030040301da8405581241008607030b510014040300200388014400c05208 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 493928642 1250 493927392 493927403
    0x150e12060105010f08091005071404031203231611070f050906030307080d09020a150c0b090102040b09060304020d0b07050306010915300f0207050606030606130903020c0904 76
    0xd0394941000902200d140403c400d051000440820440f00000303e600c41c242000150301007026581c55404965a00a444100c0766198001c10003000b80164003803084e441d003c2c142c17030400202c0d0011000f18007a210028840c20011210030002e00c0701e1240102c01e02010100d2b051582c1100710804034075040c44003d40007120084c5540f24100003c1c5421615150410000d9000d1840c0c1003080e01da180d16882151503c03400704c2d4603001d6050441d111880c15000a00b83d40040e10100ba084000050a0050b01c1e00180d0740e4440300c9000c104030450600c2101e0403101d4425080b8a00b01c008800e201064000400c2a03a2200414035071401040c00351010f244503020300c0d17a85654a1070b0100001d040c03000c3c03036044400f80440446408091070b030005103a20401c6140032003018401c80084c250b002038017250350010111350070411041c0b482c1c0b44a4014068441c0705601743c8040d55103403418587e0382e41c022140e0701d40c0800c40400052144108d03500100c9210700902c10741d6401030441c000f01380505000e8908445 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 493929892 1250 493928642 493928653
    0x207080315120613030c02100201020c0106061b030e0402120702060f07230702150d0c02240f040c03050a030f021507121d070b0a1205010f150e12 64
    0x900001c0c0a07500240141120603035041c0c001115035558841d401810640c107001505440d0040c1401000c1806103076500034001081c4820180d4028041c0d04080b000741c4080d8248074021456034099034050541c22405140540f6020721070320200c50f40d070154004607821035070822020140c21942c104040c490501038005051328288103229941d4068014100c20800c080c0100d0305c03c410b2510004412810760f12100d00342c80301c2e15400000ca6880b00400309500c0008001086240c100154110900c0007849030244d500b450400410324140304c1c444e10700d030b000c4480300100240315020981c8907942c220303009400035001152280e03902031928048203015804503183c0310092445550400c0510700e240715042d4101d545003071544c400383c4510000000f640007252140c00c5d0788c20080061125a201811440407101000d607116104c840301d03807000e241d1100040c100409051661403034000c80b8100c0766031101d4401e030b152034000b110411401054586c010040e030101d103003229560b014601c12501503004054030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 493931142 1250 493929892 493929901
    0x1618031b090608030409020706021317070608220f0803010303030209040615020604110f09040b0610090f050411090415050310060501021509070b0a0908070f080a1202010f02070803 79
    0x3103021290722a48840781000818070200724044140c40844503d00d00160f1601c07c02d150160180c00b402c80f092140c039992810025008215410741d0481078600025201610380726182141d200c0c10440b8000c40e48904ca40416414400010400c02d03258050150040c0007202e5550790300321a8420391003540083e801141c24aa549441d200e09802040d0481030a900440d421401a4072001c0091000d48607112500d520360040c1c5030203000046411008140030700d1031801f1301c0c000103480000d54800d0f0203042d5415401003007a0040e2180c009849154480d8900d2528000400c0044c0101000130101418140813400c02910341d0700840381349083c0c4040090002d070038001403520781071300740303208040784d60170100204810798000c103031030795035449089841a0650780d00301403525011866100c1035950380006074811a8607031080d041c105a0b2800d00503518000d5403818450b044580e50700070090349030800d45000340001c504000703e00c8440503d0001140c2078050041d514104e8011003000e5892010020402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 493932392 1250 493931142 493931183
    0xc02070b0406020a03350f0c0a02060f070c060606051e031003020609030106211103070b09010810050a06030b031005010e0402090a111303061b020303161803 69
    0x400180c1400d0180504040c50848025522000e00c3e101900f8042c240010840c2050346405100100d15001e0303040ca0040004c110101c0802c07003c4a00510009103040850400c110200845464403c00d0b801803015803111881e00301c01c050050300480c10321075040d0120b000a0f00c0ca000b10001007102c2d03220700d5142c800c403240c1102901101c13113000f01d00c03501c100f04004081324400c50020a0301c0e0150381e1147c5400070200800c0c01000c042d0000084018540d007181c00320160100b120310b809200b0500c00c1510914602819034441c654000e042c50700c8001d02c511810365214078041a800881509800324040d91980422180210f03500400002915401c0000306410200144804900004410400f0350701d460200d02d40204090002442403201c18040303980703500e0340c0e00050441200107034942e542d0000641504813100b8244000c5400508000c030039203061450145c800800c520703940140d807542c0c2e00c00008403807100b0384000c40814020440082801d000e0740f5a0003001031445889580300240e08103040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 493933642 1250 493932392 493932403
    0x14040b0106122a0c0b01080a03140306030a0f060f0c050408010e150109181b090b030a02030607050306030a0516090e12180105090d0c170309010c12090807090c02 71
    0x1400c4903420706290003410349449078020740fa504100e0840c0303c1100a050f040f1000c003520030010701001c0c0700ca000030502c7e03000414042042e038400d45030780d1682500c901144407035000440b6107607419000881a9804507030b0881c1e80800d490f104000010759885040400403c5816801c0350900241c004107081c080c00340b00340716405d24200250010304290904030119071581030140140300c00c01d40c441040d1420803103d505101d121a9022006030301c81c5071070740400e84c2400f215101e010240e90030030125036254100441d4200d1f10a40140142607196915881620b02d81d00c00341017950944112000c40c4003044061040a0001d40d09615800d0210f251419180aa814075004d60000d80c2002209802c070403403141c00c0360103010451110900c10050b9200681e118014407000b1034101e540d10300c0d483d0400648030201310035950801120641100d0002a89950b0f005000100d0f0220f801801440d000c00d42800c211040c001f11450010b1545440d1204281010300540c80008441d0302c0e0f01d505411590103000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 493934892 1250 493933642 493933667
    0x40306180516140609010c0c0611160308070b0606190302090907030c050406110111190807030b0a051903051507080c031e06010905040204060c020123030106050c0114040b0106 77
    0x202c200380c100014095041c4803a42c4182c0320b64070028504906034042d0a090407456001704c948204580d071240c0152074907101590004050250380c5514801c0710b10084c0500540e900816000e040031066039810007041005000b655011300c003440680504400440c05484040b16540e015031208129014800c250401030000024903003480040304016a0160540c0e0803185c2502e000010b87d4081203406005184212000c0400b00000498500840d44928444036031002a80c0e480c11a64815508408407412074841e2079000092800c01c02c8903150503152803428500e410f03480e0092030742e0703903485034508a88200d40100011100081040c1c15400c00045507000028540c3d032851881d001035045541c00e6001806c040100c03039400800d01c2c0e03900c20006c1102034440a0304c11981c994441d48094502000c049080b0f0004a880598083c1d1500c2c101d207003c40224042b00c001c0c1181d0900d0300541d040d0f04203d6100300c02c0d6507135000342190030044900c41c0e402280502c64804040d410b20600078201c070341c41d81 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 493936142 1250 493934892 493934923
    0xa08010b09131106251a0a11090d06020d02030109050906010f03020d0b0406090b01091a0301060f05010806130204090c0305010512070303030c090305060c0c1905060402040b060403061805 82
    0x30a0b100070850415080001d101c0882d03029a85d10b0103020360400104090040741d20742c5107205d04810401c01c01d040c2210b41a00004d51a40e0259070304a000307016242c1842c030300710380d41d41c0521400c205400d10445d81e0442d03138825600541400b61040d012822608242e120442c416259402d101138803006024040c0544515880f1022207401c0d5004219a856203540042110108000040510010b61700081d482903016005176007a580d50381004014110540c1c40c1c1d2500d03c0c28217088011898140f2401d0102d40c0c8040d0491000c2e0324000044d105000014543d40c0c1040c2d803c04681d00c182d1070362004202600140c0000079031918071240003000c0b160160006801081f0282c802c01d100000002c90750120381c0e040c5004200ba040002e800c403503640a82c0d00041280c421503080c404015241000781c84107581d1401110603040c05000039202160030150701a00b190060070118015050907080000d0500e0080e2503146050340e40c1e42c0e84011034524060100003003485841030000c021051101c4152800c880 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 493937392 1250 493936142 493936171
    0x1c0501141e0403080c031b1c1503030c06020705010b0d08070b0601030621080f0d02070b06060a1d030c2805011119061b11070806010e0c180a08010b09 66
    0x9640103018004045c043e4020760001000042003009259041841441040c0c11291940401540340000c0104401d0807503209080982902904c5a103c03846c10459070941d40e0018441030f2a19500002e41c4a420251a00e5489200f1400301d0b0712030f01030018030340d4482d00b10607989044600781160a4840500214109402d2180410440c45031004039292400000d2203130446016602d003022482c03080c038a41e108210400704082d14010040e5010f007104a01818105e20709641c0c0707404100b2103214907140c14010556682a50304401581c002940c040c1102404561824100c1000901205120010880c44400c120800000602c2e041c0c40c00c03000f800d003801d0400003880c8000031291134151f0341d000701d01c030078190355070080501006400c03036110b12810030f40b041883d0208410040140c418400c0110745071207503d40c005030800d0002403c1d4125a02c0c02c4500c45982c564501006441d8030418142c044020401580034040e40c5010300100101809030001840308183d105011900400400b18079406000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 493938642 1250 493937392 493937401
    0x90510061205150c180325030615030f080c010e03040e071701030c1206020702120a0b010b07030906030509100608030309160f050616150b131a1c0501141e 68
    0x2c00d13082d50905626083c0b072416601020004c00e2404204003080042c52250016545001d03d00241c03030710a0302e0050b08240400c5c00802002e008000359803100408402c0e0020104010407042d6000e001500741e110b001240141da4900090324642090300310036803592644d0244689160000c3c40840c02c004000144c01040d851030322040b480c0c0c4003600c1076210b000544000c0e40c0c00c200d015411205070a0380242191221801c0804c0c413a500e0b1181310040f903148800304008504201d05500380e900140c2e240c0d4968a150f420160300320050715001d041c420300c42c4101e0150180e090344a0282c040585181c00040d034492401c030b8052031608501c0d05e800c041c00407100b0010701113255800742e49000d031174080c3d4200365a20304c2aa404441406000f80281c40619071a0440c1401c1d54a40c204080c60142260302202c04100012090304441e8000b032104403007074455242c2c550314205803024810b00803034002c041610242607210706007905c0036044440a010a003008201100b000d48030880340207501d030741c0c550b14180380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 493939892 1250 493938642 493938661
    0x31a01080c01080c21090a02010f08190207020f0607030e0102010b0d0f0b061f0909060e01080c010f03020903070807050306010f23061b0a0b0f0c07020409051006120515 74
    0x9019100203a13804c400140000c0090482d00c5228152101c8941c65103585060311500d500d0300302c0202e01f240001c060303544900b14184242640742c02018402440d61070a60005223800c0258840034040340c0000c0644510000ea030307500e03006450340d140a91607002e01c003820305000a003110160031400780f0409402400380d01164500b1041007240361b01c00003800c400c7d01c407140068194543d95141504030428242c01c01041c0d54484038250403a1100701e000d108003074079820090103900090040340300540c0a4040c2864540c40360805800120841c00d00600e4154840c020a003000c80030307040300b000303503119120403c0103007010003a160041c003070041400c0a290a1201211403035212204d134080d00049480309582039564142114107094035a010340214106041c900380d2035464180c01a10400c0081001460f42d0803907205180c40383c40d505480901d407011076400c2100805061a041d9014032400c0444503aa000310701c1414050800301c1016008030f9510300c1c00301e142c42200c01c90843d00803800001c0c01100b49 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 493941142 1250 493939892 493939907
    0x204060809010f05093415090602060105101b21120209061e04050607060507030507110705040207061d150703090302070314010e150108070b04030804060503091006031a01080c01 78
    0x6070307000080c12608402c5007070f01c0c0c9404104500054061070f06c1d0380014103850b0300c41d550002215aa11103500d01c50303032807000f6a26203a003403144a800040c11400b100c026445542501c43c00652440030070b1808005031206410907041c401c1c00700c1c00441901c3c2c120403954100000301c0e01001b1140081d80f80a001101045180c041e901c10704150464032003401500446110907500a0200a8450350b2201e4084c140072001c0c01c0c0603507080b80441d140c800411000c61003003010001c480140300003421140c1c07810303007840020361081c0b000381c8001d561015061a0307811012071540c84800894010310000d4981402e1556210b805030007202031524140c0f4800003c0d0b004141c3e00222a00f040070110541c144006490141c480500c07048198020281c004c00f0100e0070f650304a040c1c8841004030b594050300d501014080340b10b6400043c0c00748800b48402c200291181e401960302114400641d000034154160b8001a12001d8004035805240101080c400c0036541100785d0040c1440b8000342941000e480011f007201 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 493942392 1250 493941142 493941163
    0xf24050402130506030c120709090525051e07141911012d1d12060a0b010c02030a080702041506050d050c0c0714090901060806010b0702010207090204060809010f0509 73
    0xe0300e010002071ba480549405030b4030180c8600704000070902d06400002c12140050142040c002e2800300414840b521280e029a01030f10055100383c030074030302405e09866130303000344040d03003000151001107801b04809840580310042c420032001059004086038642806184541001c032098078102c0007020442d181e2000c950183c1c203007000ea03001000c40c180c00030085100162100540024466100101d44c0700ca802086840d0115403550343c000e45004200c0d6003510070611643c82e80c84070b40402c03091052a404061600c2c4141003492580140b0760101742015250082a034500101007031800035030409000e400c4514403105610801d160030000e01034494001c4520341c822440c0e0b9200003401032035488048404103ca0b003000c40c0c18259481d44c5024960f016281414003d450b20000305400b0101400f4003000e4844240103042c541c3c1c2070014128207500488001e030b0451282d41e2000481e80031070b10040001c2c110b941c1c0c801c2c600d45444441035003580c580312403ca0400e03141c501000507200700070400e807012 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 493943642 1250 493942392 493942399
    0xa060617013309020309030c0d1e08182b02031c090c0302031603110f0f060325030b0f030d020613021f020c01090e1006120f240504021305 61
    0x41299200701c0215803001da0300b012400f184001300b40090368134000040d003c21909102154010300b0740e410200e0311000c071854484002d000003005885142d00078200c542c0e10a40100b0840561030110740b0140c0382907100030048581c0b10040200d442c090f20400034458003e215400258604041c0281e1658017641214610310840d594401610070000c46080000c021a002000c039100254960045220043d4034442290b88a00d030450180c0c160074281019955904001c040003e02a02034060000345d50006103101c0341c1c200c800e4082d500b6070443c0e10071300220342c840d99000034203030f05000140001c07401180c0c8500c1c0f00390311899a04400f0ba500091044c0c2c819942104242c481d04540b02040700721040d654401d03113081e00c07201c801261540c00113036000000c3c030990f02d1950280e43c0b00001c03c0c10038000c0c0d8140142d221080303014070660b406450301601d200c3c5160000918508040116000c40c0c0561200c04010103046c0d01c0031002c28504c484903009000100c07001c5280c40310503000480010020b204a902 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 493944892 1250 493943642 493943711
    0x807060207060215130507030506070e0f15220305010606122f040b0c06270d031109040905160f062106080613060c05030103080d09020a05030a06061701 67
    0x45100040e88203d0070b580c81401c0314041c7d40c5030702d0016140d81c401c61b190000a0410721502c2011302d40440e80062011018180480400d0811400307840c0754044103801001e00011494200b44a4808048000075401600005000c03420680000c00c400041c03001340144078203101700380b4100e00d6207104900440200d400c3e00000c0e00c1140e80315490602441c0e0103828607000100b0521a4508040ba60380c0c0302d800b008440746c04c01102403140d89080311003c8414581640310600a10750749001c1e42c080c0c061000142005400c151000c00081c2c261004c40c4000c0314039402820074880000158414003000d030107020840741c4e00a0030f00720001d180c5414121208800d10b004213003502491180da01050280103840241c510900d496440320070f1040c4504400c5450701c3c50050962030f914843e03c00d5038180d9a100e12220701c0d01c023045d94400c01a0240b100141d90002c200e500009031030f50304111381d2200170f100c1e44001c1070151510740c0380015081074070035200300750741080317005811141645004001004250344581 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 493946142 1250 493944892 493944901
    0x507090f05150f030c030307050601090605010203070302030403082d0c12031303050304020406030b34090501180b1b0c040b0f220906020d0b011706061c0f0203010807060207060215 79
    0x2131500c905c0c18411070301800700083c06814018003291841c1690b20806050120a55660048ae528441e012000c0c00580040c0300600004000400420380340c015941c0b80c00458031080d803645046060b200480c0030308500002c440290715030900443c00040c1c1120742d428118608203101001c0a00b82e903500604000000002030708558669120750059900006031001c030745410f210100d00d0700c1115491030b4580943d2056000c400300b280c0e030a0f449114407580c403403050320314020054500441c624096080d46106003000314500300030201038105034114102c0684c950405170a45824110a140c0d0b00340580c1c20154542040c1c1c803003004614038400b040c1c520310004003040c6441c015110001500d0401a410082143c050108a1f0003610303000384000001c014000090780195110350000d0b540c0050540f03003000245180c0342030406002c94004520b501060001006a01402c45030101c5454242c6640400148018001048294090314250000b40070060421a02075501d400c00802690a040d607100041c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 493947392 1250 493946142 493946149
    0x90c060c03020c0a0f2c040303050118150918140d03110f030f18071d0f07020c040e070308070c03060c110a0b04030e030607090311010207140402031308070507090f05150f 75
    0x201a0300646c525121505040c50001c02514003071181140144c0c0e010030403030114030b2034428003091615524600140516108007000034111141116040802001110011644008980b03443d10315040c003411007241e40d030001034204c03a03104a25444c40380c0c05001031410803407038404aa801c210030300c0401d101580e0302c003513080c4c00e80414aa13441c800d0251180010310850f18418802070018401f441d960182d45084075040300400031908000182d204080001c024140b40d40804034050402d81514815500d0351220f403142e078060082100e45100c501d50402c01e10802d0710030b00d0f40c404100e180180704003040804103a91807092600151648400c14045002c00d40103035190f000800c13000c0c003915514505540040e05005540c401a90402c809081520a079031011074410181c942c0d1011040171441c45005000007500010802c001000041001c1030202d0a810060000d4900c20001410450b080c01e1000007a40c1e50b0700300b1710f0720040c140130521a0212045080c8a0140b074155000c401034110304002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 493948642 1250 493947392 493947449
    0x11a0f0d0b0f06180324040f1401020a08091c0203040317070b1302040c020106080d1202040e01170f0105060108060402030403030603150b0910121401090c060c03020c0a0f 75
    0x1d59500a0340000c01084114000d00004c0b81e00d00202d091761140c038422046452030304000000002c0b80c041001c00100000c0e10a41d2071060300d40a88440910650502560b508aa0011000002184000341000851881002112604080400c4c141d800310902003002e580c0e07014500004210008000c04041d0107100c100580312070384e0b0400d0032008941403640001c0142044081c00b84e004506102e406002180140120011110400700400c2d00c0034840508580f000e030030214900701e058017003100007040040c18030494041c00740c44865400102031103954502e02480441208440c1e414002080500e030713004140680e2208050390090380d02c0d40c076841c08030000d10301c0d90801800410700b145002c02c030b400c555002101240058950b010152610001d0fa031000000780719000b551800401c02000044210070654203030120003002045030307000e60ba035400702c42050b0307040f070300009042d05030050174941e04006403203180509580c03280ea0a402d1200100d00b00e48180140392203d46200402140f02d03101d03070300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 493949892 1250 493948642 493948669
    0x1020d0c0804111e0f030c04110415090f090c0c0c0f080118020904063207090b07260d0603110f12060a110405040f05011a0f0d0b 57
    0x4004a19100d040904444801d5400380c46084407946860b4450801808080c0804042030b1134240350300d030040c10007039445941120726400d400342000c600116100e50050606601c0102d0400e52901c1c10816444d91b031b121a040c0080400030390490801000c00307404c0c40c0b0304c16078036190f0010030031441c0b40310252816000100010b0402d20525000201c20050401000c150351003000240244a2101c40342c840c8003900100c0654080f02100100b030002d02c03140e0020200c00802032401000d040d0308403032003101d03000f0102c52003a1103140c01d041140c02a80712040304003030410302e401181415031980340c108003051070613010b10107030184060b4110000032138402d4410310401c8080902c040b640381d00e42a078441da88660118040c1d006020022110b10303084014401d4103010b080203114580d20f080395a00a010b101d10203200c544030030880456a81c03078a020b45070621202c80408100c80d45040308100440c080441910300700c46062010f40c50b00502c6d0b0044400e0350740b04620108803070a618001482c500100c85 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 493951142 1250 493949892 493949917
    0x103210c0b13060f022506061a07020f0a0312030c0516081905160b04060b06180306010e06030d200a0b01090c050315010809010b09071d180112050102 66
    0x81040342d07488410b031508008521031030301030003450320b414842e01c264010548610250400c030b108003550820b84541070001d15010703040c0800c0b400e648142d540c000445604000a0011002404409504003680c64080d107a0098406030a01031075074a4100c012054002054101a15041000f510700c3c0300e4030548800c140d0802100f03564580c40e10303224055134000030991007807140143c03482080d14000c00a0f50700f10b81a41001850359242c0b99070b0024003103001041101d0380350743c0f9920740e8141d840d400040c3c10315000c644002e40c1c0b1040350b4010107140c004168894280200d4103410060651008542d6201000c0c003410010b00742342824000f001240a1003004540710310903580d4400500643e040160304035a0341d00002c10020040240490741440100c0f05e03a0400d14641100c00000d5205224256002220300d00000314400c90100003808500c090702e440e0001046401c5103400440d50034030042400328115000403c1c03400900d1702d20300e1070340c0510810130090802032880052040a4044962000c07800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 493952392 1250 493951142 493951163
    0x6090f05060711011a0604120c030b100905090c030c100215090a0c060201020403030912031205040b1509150111030706020304031205070c02181b0c03030f09060103210c 74
    0xa000200030441049003c0320540c2000000d035140030084102c104821000780800c2e150074107100ba084034980c03491004581c1e0386a01c0c1c10000c0130440c2540210301485031801100340c80c0d858001d5100030303240c0140c00911141c1003050301d107420303940000e0180c2d0764080540d04120f0342500000180e00745031024995903126102c0000700018109c02183c01c1080314401c12074500710589600f000c901700e01032800014007041c003069092091000b0710880803100c0d84a443c2c600d40c1e503090401e1190a840081d10200c4001d00c0084c1070001313036410004084c8400c007064540042624000e8942440040030640150600014400c3e052400c4000e00031124030030742101055550b41010b1a000b0050301c0c0c010781540416103000f000c2208540b05000c070301e540704c1d0018023003480002d50326018240680c0c06484e1200704020b144449220300e40180c041c041555050f0003454591814040701c0d81440d50040100015030030110041c00040d9981a061602e00590301c5d00c0c80801c1200b0b003040e00c01f40b0404070050700a034542c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 493953642 1250 493952392 493952401
    0xc0c121f050604050f04050a230307140705031501030b09030712050301081203011d090f0a0b010305060601050304080d05040807020a121112071404060b0708120f060d06090f0506 78
    0x64010034000c2c4800e0350b042000e5610780c102c1c20f154060030354004006030440038103030700881d0182440c040518080c00c5032942144414118518503800b64008580250000c50790103640c484c288956001820150003810302500c10000c4400c00074014000241445a4078010555621042040c0c03400a588001003054051005402a0158000344544061445021f060070001d02e03240c070a584c100d541c1181d40c07105403100d240c045a6807550041010129210f00d05c80440309000801003a60068000d150303011055042d400d0040c2401c070014411414000c0c10428080000d0001c0103e0b00e0820642a00050689491400480f1481001b001070750095540c60b01103001715000ca40000c41a00c125681031564800400307104001c0301d15884560f03a600240c0f0100003240c490304505200307070b200401c001402515034507029520740004e0801e4a40c030a01003940c60f804017a946041d078001144804840707440c684080020134440740c82000400300c9440d40355100400c040110b072004043e6005041c0d4106260 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 493954892 1250 493953642 493953703
    0x40504140a0b030a0f0807060b130213050303071101110a08030a0518011b0e03030906040303020d0809010b060703030c1701090c0f050304120f020a1515060201020c0c12 74
    0x2040d00e12625a0345000c0320b510541c6400603e07010760560210003030f0900e01c025156090542c01001095036100e455402a48069441d040b6009000c0340c41e0303100589440039504020b509144e41d4200341d0103680204807440100399040c0c0f408003405001d01e42049040f0701c0004050a220b0040c4008000c1d11000c003d100c0748440540000f40301d901400c94024285d40c060160609a40d920910000c2460a28242445085c480c26408001c0b16014045034900071950740481c1d0b003580160300680050700607550316100164091181034001040900a03c0300500b01c0c1d000510300d114102006052594909000303072039034000c03800b03403140d1850030750170004640c1c0d101d0038440500610091040058060300344000007502440650340919000300d4090804a644103090310054011b0703e400c01984603403242c100006000d06080b14950040302d00101c0c00511308950004141503d41004013564010f020800c6d84400004180c2440c03001200d003080f00b080410502d50030506180c0259810705c1010809101010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 493956142 1250 493954892 493954931
    0x3090703031d091f05130504020306060d0308010603020a030902040c02060907090608030315120d030b150304030203090d060b030106140a050409031b060b0d050d020f010209060a0311040504 83
    0x24001e84500c120007042c40c4103006042020303044680d001d02001c2c08074803090826515244206400f01c10100d00f140c0f40c0740080d0308860b00c42d0b007190045413198104811801c090001c5500404145d0380c2082c011300556020b048000c0500a101c10581e01081a003603062180e0007400c0707025005001017100900c8908020749400046803203a10350303c900140051001781d1842044203d038108000b031825910b031982c02080c0559141880f540c490080300600304210024400c031005520903440c0002c0403071070030050040303030300322030b10504c1c8156418810000800c1d008012103464603021951600b445040e86000e5009022140480303401d9031a241c070208805441025404003680e045035401d0700c859840e000c2100b581c3c004040100012001d0b24031f0101c41c40520b18084a49100c3d2101040300d40113400800d10003030240d0001e0362103500a034445d440043d0107000c01d80c0b100c030312800203500e4580003401048441c403500002008241c7d548080d41142c100703560541e005003100400a00c00d0700b44803606240f459 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 493957392 1250 493956142 493956149
    0x21528031407270605180a060203120c0409020c1005060f0108130f0b010f14030102070812070504050319150905210c01060602030316030e0a0602030a09021522050f190803030907 78
    0x841b290019801928280b842003040f40c550754019854507203c0118003807600c001400c02442604140f00209080d06c0324006012096035240007025811085040700f03044c0d64014008501890b00c1d1201400f959902800030ba03440f442e4070022031030070b0f1440d05c0e1548101000c620003601041214001107031106100849404883d442d050300c0381c88940c40e4081600702d00c40d0340740080001c14100b0807284d0f0310310701403225680b051030b80c00c2c45030602c0e80e12008642006070031260390002c070240c040390702c042020100107408c40b002489010440c0d03405960712503a907414a4174215150b80b2140074184400d040c2c40003125084011200240941952000040d41d01c1d04260b6603110b08040e16000b442c40c3c540329105010610661000405080c00385031540c00c020b500103401c1d0941c00d40c8030145100580c4880d8500c8104080101d452a503403034015840c4030400104030a000320380c0300b110404206070f90382c10800c1441000102e40f00c5d010681d241c00415101380241e8841542030001104125440c9400704009040703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 493958642 1250 493957392 493957417
    0x140a1a12030406032a0806060c030409020d06060503060f06160203160e1b04091805010c2015060609012307120e0319021528031407270605 61
    0x10000c2d028005c08071034406502c00c0081c540300401700c0303240780d104004c0340d40c001101400c40d614000052210324110340c0950000714120f9000910309032403034054407c84000708002e24066082d8200203000801f10000140f50500c1003e006c154088580840d460881b03446900a00b1202500034034986500913141e98450030300d001d410718000403284500c60700446040d90689403000d14217410920880300600c001418071560918040449000441c00d03ca550110441a104c13400d9032004443d40841c0780e45151007151103900b10f03441c0076038064099407000d500103c00303ca000c0d407500c8031240102c616610a0024040c0d2101075020440d14900400050850314021542c00308624440314081c1c0d038856001d40070342d8142e80311941c51060442038511070300c2514402850300e64640055005400243c02044400101100c504070000e03514a000603030300103422a038101806401c1003294041e6418000800250900481c80540202e8208404140c0800c3e1040880e02c002103446030001815500402c184410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 493959892 1250 493958642 493958651
    0x9010f140f01050d03050d11040b0307021f1131061707080105010c020d030c060213051201050c0901110111030a02250203100903050c01050a1b03140a1a1203040603 72
    0x9550519040484281750980c561724904490500b4800060044c01c841c850100800d02022034403139844c000560080445900610400140e095884d0b008142c45040c60203603443c14816003404d00120060312501e41e5100c40351000f90001040807180c0001c3e600c5091614842c0c0c090128646410070b60040410b6042c42041c4d10941d41d100c0107440701d420078042d8a020072500746040c00180303009405818094881c0c900f103101400d1903507500c0266001110f4009054042c40828051401c080d0304121408031420000d0060707040c0b032100c06603113105244a582c10841c480641190044094010313601c0d020070b00380c1c841d0396031400e202808025041404d81a844480c50368507810a000325900000406800070301408120f0007840f0303a50000c184003078040342880300510200c00804000cac4603841c8522003103600440d040e0242100d080b1030502c000080d20500d4a409100e0400c800138640680c3e02a0006c0400039443c021280a98440c407041d040090b40940340c240c10640c4508084054030440345075403010700 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 493961142 1250 493959892 493959899
    0x80d0c090e042006070605100501020d03020f0409020c030408030d0b04060506120117010b041a0a1e0b07020a09091a09030403150c090305061003050616020d0809010f140f01 76
    0x4007410703100580681c1003001802e0640d14120045034800783c008081302d1401700c0c07664035041503a4085603c2c800c45c0d100e01c0002c012558041c0b21131440240585011840d1034410f00141c0b040e80a20f0060b015440d0780420380803610002041240d0140084504581d194403031004c0c07403005041c1d0f004200703001d142040c00005103410081c003036032080380003030781454030aa08007450071074240c003016040032643d0340b19441c41f50f03076486600c0344030782400d100319202844c200c20030300740009071250f40d00c01c0c2c4a2980f004104085802d03c00440780039030b0303901a282c55541242d40001640c9034115000f030102180341c00504000c0003440c0b41e00c501405003c58041c00c440e518217180e02d451340141d100242c1001c0e8070202c161300144856020314000c41c0d460404010080e200d4480d54074000003115110240c4800701c0050050041c10404076900941f804a26001c0426103d8001e441e461080f42d0441400b21031004240452030a4001e280b407c00c0e0340004010015030740840c01001201a590000703206440307070010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 493962392 1250 493961142 493961159
    0xf0607060b0f221a180a0c080615090d0c0810140c040302060903030d1404030e0427140d0201240b03010b0a09080a030f0f0e150d0603080d0c09 63
    0x4441c900741c6405200b03424421218400c024000014101c80451a0300144c1101a61404407000d0040112191100c2901e44103d01408481d1084a02018404184200aa9940d0b41d500401a07082214503c03501d07850383c10045039034140d00c00c1000340030500555011910a100103814000d00d040c094040c42200a49880e445040b68252046a888802000180003504104004154850700a401c5900d4620001c0100e001c89140e00040d10040e004041400181a4081d40d41156104221000c2100300b000007108040940038081009292001e001e64600b40034440729000d200048800075100b0002140302c00174001c22034600e041c4034078402c11555920340b0b494808602e06940425044501e940d08019588141c1c3d008000707203204200d4521000310f4004000e006400202e4440c0d160741e021400000c801030922031607001d10808001c80702c0b2000304240c2d641068414406d01300500107640d1540492800081c04540d00040e0451100080400280419a0002c8041c101e260390341c403406038442929 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 493963642 1250 493962392 493962409
    0x6150f080106020717070513090b01081507080901090f0c060f02010605030a021203040f06080f070e0904021003060308030c0406020f2e06050d060507031808180f0607060b0f 76
    0x2120700684c000d54052148000d49251350050222040480311071656071000100924038010701c1c04003135616003000c80f08000c070b0340340c0150141c250140a45203405510201070354611005159400300892500403503051102940321250541e08503a0b0b04035506081d0070700c00240c158900c201e2000030914003944030703101c0c41032280e00107940009018080500442d004c0185041121840d11400e000400c80043e204244450741c1c002045242c48403811413a04d05029412102c1c001d1000e01480100b030880c146580d41c00507100d5204ae41268150810710340d40d0303422801000c01c0d40005008100002c1031046a0551401900841d105a401c0b14042c52504005035101c064000348605082000180c01c6100c910340d0600c07641283d004000000c40c40e41d100c1c00039a00d0b103102074041d42d07a10343c1c980a00190542c0b501136507000b00c8604144130003407511070b0341c0d00c401c511a400140f56441e0708810040505d0f07642d076030041da510340c00500c11610780040e81003100c000c1400480e02340c031446d000041c01541d801c1c04a207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 493964892 1250 493963642 493963649
    0xa091b0216050a0e092a040605090906041709031504021f1209060b090103030c0606061b0807080c0f06150f010906030c0207170a0b0f1302120c0406150f0801 69
    0x282640d1402c01392803120710b005440c8031101c0c00360110300c01c058401c494080c55140080043c84001c9071a0100344022110a9007100d0f0284801c4010010030000008501c1e40069020454421818800041380c0a41c022500c446615011b00c81d00c1c9034440e050a00b82c54003840c003c4410380c000d1b034840f82d2011106803244200e400490a41c0c041b203145042240d022840306401000003250144868001035002c11098001301d002c45e0140c40b440080c0a120701c1054050481381c200140001c4214400d00207106561340010086071000070250f0402066905840204900780101e40359240303000301f45a00c545080360100b41482d421050140c03c0e280450112b014100d040c3c691074211401d100c0224003034140c0c1c0700743c4000d42c42a018006031081c04c00c901c0403901003000f0080c000345038142c034003101c46000c0a810381d004402c2740428089410b905035a548480b5904540c0e401d42d040c40403134481d08203070b8050441d5900c80d28104000880b214091009041c0001e26600c41601040305201520301440030301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 493966142 1250 493964892 493964899
    0x30b0d0507030209071704030c120228030c02191505030c070303020702010c050a120f210213090e060a050a020309060f1b0705030a0305060604030f030e0a091b021605 73
    0x60810150138000380c2e0640001c842d142240d42d1003040c0c2c210742d40001d019503040300003a40481c0600b040c0305041c600f0b407442d00981d101070140d100d88180003460458a03e1142040003039400c0c492410035000d00103031504c040d40584403401030f110704410b4001171036080c440c403d0440b040d101011441ca200b04116031188109001c0c4501342040f0361000c600941205000700d040c0041c1080c0e000224104100340304407544945241101c094030f03030030004e140036500c05904081c0141000320baa041c100a580b507524004210800603105c061021544901000360f5200c0d007501e52404c1a07202c0101350200d2107c0c41480a03a10034010f0b9202d11031148100e120484403041d281e00007201250401051790000d980010994025a0070504510404050782e0b200700c07001c4403250300c0011b1808604c0c0e018015a54800d03812a610340c109859921a12088200030500404005145d6054580c6540341c06911019000210040214107107200320504c102c600c008806025100d0f9915064022151044203001e0f0b44015 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 493967392 1250 493966142 493966153
    0x506030c0304170c060a1a030109030503010b0c030921120f03160221041d01030b042d0b0603070506040b0714030d020c1c1d0934030b0d05 61
    0x26124004241c07800015030040e43d504101d80704038102c00b0403d5038014080c9001c00101d0484910b24030444060300050f070750007641440040c201282d04101580c1c111018145030a9540b418400784905512504034010b5109008400300c0c0309080031801c0c00192010950200c440c032502c901010b02290144031041000340c2401c20003d408800000300e960f17100880d50040368862400c90101450350030181003a02c010807008501049007010841e84400f2800031100c00307550170f5041d83c6540c40103400003403003d0800b00c240c141c5240328060300c9220000c0280c4407460f001500100c0e142101400a00765522032003440343c640003103040c0c0742210464044032804280c1901e4584159a22060008032040102c400e0100b03105480300c070700c0c3d54001084008139040c0945825100394184c1003101703d100e02a1820080500d80c4000c6409100d01d2041241c10100c130300c5075543d5584d02c40941000001062208250140761790f68000383c40b80915004408030079182441150486400c2c0107038440b2995000c0c000e80d004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 493968642 1250 493967392 493967401
    0x60f07030c0210020406030209040b040506010f0c0f02030601092a050414030102071e2a1a0d0608030309010b0f0f040902060c010c051b06070f05030903270103060506030c03 76
    0xa03030302210155140b40141c0342e800110364000c4040ba049603000501290300003444e080c3c4d618041c40f4074034a40004031410001401e0600000305071aa072604014240000400f0902c00d102da04a031b54801291f00404440b030641c0c441130024040d28040e15040d0707071540e071142d690300714510303020190301300341450b590715406d02d860521000700d1100208001e40d01035600f00152004140000c070000300b0215003c4010035854880e1400410441c401c8040c0c00d903404e14070300021b80c4c45949141c050211018280041101c0b2101c240c072441c6032194080c0c00002e24a070090010311400044003951044a190000700310a401520500c1815014074614540c881a01c0100c0720440c90268000c81300203001a040c107003090b0b0b20788030940c216007900f56444c011079004203040780c600508107002414001040050143c46c2848540038080080000140090002c0400014000e4030104207485240b90100c07a645000d017140070807000304440c003503a81ca00190801401189c141002401c60f030140704101c4a040c55681d6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 493969892 1250 493968642 493968647
    0x7080403120b09010312020c100804200405040b010f05010c0203120d061502030903071406090909010b0a0e160507150b010905180703060e06030d081e07110708060f07 73
    0x180d4801501c4115910042c0341210f881d0f2140b05806144103400004038101a001c001e890219481c0b442c5104100e2400b44100c419070114225400a500c041d610b01c0c03140c0c034000d04503c4c44007800c80094203e490b12080ac0288040c6c80612412079114482c2e40210a4a540c01180c3c000640d94029402d81c0c030141c1400c541c82d41b00001070a40100d140e10004100340c40c0d01ca4440480c03804880e100040c1e1001c1140724045ca0180040d138001d0050821000c502c4a811011903241d0144454880c4110b00e1440084d202c51802c1d00000c241c010000c090701150341c1c945840d051000307401e907009032410385e11003e2008168050411501c4803600a4030a02076200340007030304c00c080e2409001c1030741040051880003a040d107030102c0200b074203004084041e01c140340400004040301c2d5a940f2070039031441000d0030b100241d00c0125200d442011b00346010900d554580a40d11032000003081200c1c4048288800c015132140c2c0705280c85040b416817401d841000d543c51000d95950340c1c041e01d41c0709220a20304e0218501e0390 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 493971142 1250 493969892 493969907
    0xe01080a0b0a03080301080d02160b09180c04061b0503070f0f06020304151b0f23040303021e0604050d0509030109060c03270512130801050108160e07080403 69
    0x100601040d40400d4a010440c00c0c442c2d035004a4a44001000501070614140074454a070401c9200910f082039540c05c413074020303581c40c1c4180d0001000000700d0040d50303240c80620038884500c2761a8035100d42402c40048840380c0c0b0a100300b80c0000c5018040841c0a1081548024600c0d0080011410000c440c1c640c8420446c8003401210b401440d02c02c06800206140055072046000300011480c4e14042070002003514a80d075400440707103440090309003083c2d400c143c0590312001203142260000310f6840307085510031000a0610b4a0440101c0d00000300347c0e001402000c600c0724946049511111046c410b50784a0090350000e000350400403007401158805c9000c0c0646030030090010405c5825926440d08a41c0c22132195000252909401c00b18406030081d203542e00ca2101e22038145c0e141413a1500c1c0d4403910011403284440c1400104420207180b1880203a001d000e60200030001940e59845103a607803450390064076075450038820700160324000311905034450646a2201101c0b0341c2e076583d003140c528 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 493972392 1250 493971142 493971151
    0x10e0604151e0903020106030209091c0305070207092f0c1b0409140a0b0603030a05030109090f1703040b0a05011412030c010e0705090c04060c03030c0e04020f1209010c0e0108 77
    0x2980e161400c1c000002d0140100e840f6503000381c0000400c54210300502070011070092480850350701c0200b03807001c1800041a84411580d0b01c2c42d0000312500c2ea41c1c804c9060800f65400480034904103034545001060401200301000601c3c0051802c181d80800c400c5810300854521400c0c03900070f01e5200a40081180b803d0790b44120040c8002815102c1c0e070f0300e0081181031819121810f6101d40900c3c42080503403a0000d0700001c0860040d4100180141c00424501c4140280c1c6070035031720b80e03c0c07890800c80108440c40c4016440042c500841420380c030ba1140ea500201e07800d59014241d1030215490310000e201e0981070f00c01b140f90b00b55405511500f40a246903aa030141c49aa200801505004c10300a22070344c00081400c034090001103142400300250480003504440050400f0442005800d400c401d6444c006c0c0d41c18140858922030070801a60003900e031450407074200340005000d00e480603c2e040200034141d0040c00792409074440c44121822180758502010100342107503c49019036000d14201d40c0d20 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 493973642 1250 493972392 493972421
    0x60703050304020d140f07140a140d0b0c0d11040b040b09010905030f01060602120c06011203020f031602040c031b05090a05030f010506270403050d0b0a06050408010e060415 76
    0x4e0480e41c580e91070504101ca0340080b500441c0d02e0824199060003200010180e088511825008002c0040d071040c02134811488000c40f0034000d12170b1030300d0b4500d10b42100d0b60010145045440c0000054a03203901104031402201e150600449007000306500ba01c05030340c0c10b021600d00b424100900704625030700004840c2d050040590000030140e804003c00c40907446c0c024008180240340400181c17030201ca0b01c0c1c00d200401d1381400603a22440c000200c082c11204072500403007400d0203034101070741030840c61051850036000000341008018690000c00211600c01e807001c000080300410308404588107402140303680501d0108000340c5501c500b010b8545400300401d901091a980e03000285821010000d0340030300e944800401400d49060344642000356034480c0020b10102d089843c2d0315070b0b5036009200405009012447e000300c1c4886070300141400c00e01420242c2540d071a41c1c2c010b005d03900181b18070b80c0c3c0c640c00c1040b8450511004900e0b180242e511400240c00c1404104009000d410704200901c107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 493974892 1250 493973642 493973659
    0xe0103030f031b0908010b040506090403140f0c06010f1203080105060c25030b060d030905041a09040507051215040809010212030106050c07060f080403080402041d0115090b06070305030402 83
    0x3c500340700039619080106038541c040c1081c6401c0300d85080d206031805080c85a454030041044617200c0c0700d4003a9009506241400d070354400f1030130b03800745d901511960310701609001c110382a441b000001c000c1c2c142da48154060041e640e0305c8489590800c20080010001741c0200010405424250b002d0001707124501c0c182c07003500c031500f0107808105071030700c8000013001d100020420601541004554000340c00399030000d0b08140685000d401d851803482080c0c02140d91f81c2d000c131081014032422020035240140040401d0a1604110b41e5400305c60085ca44141e464618144500c170001443d10010301802d42e01c00019a5680c40c0c03d1015041030403050b040d40240b40344030a0001a8000440c0600b8a42e210251034072130700024546004200c1d08040103102464075469103c07600100c80a41c0150b251a2101071540c1e0f5102107000f40c40c01242545001d003070341001da901e85d801074001082006811500f00c1410f80c1d00c00c040415612028021900048200013a90209101d0401550301c140094090700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 493976142 1250 493974892 493974911
    0x11090d030c0203030904020c060a051302010203040e07170f04060b0301200d15060207181404061a090a1a0904030e01080c09031204030b0615040b13120501020c0d08010e0103030f03 79
    0x14203036480743d0440e1120b60003490800c91114800e01c01c00d50080159510060140cd9550002c0d40e41d1099000d44001d880c2e08a000801c041d00c0b0b42000800e5a088001d401d8960411080995200c8000d903802c4692a05200140c0c41c0d5044c140b040c64000701d100e140b00094544100700801c410b601400013145100d07241c002000030520404c01d801d0080c0001d900900c03c640ca001c0710031103000d01e100c2110078464240704994018540c00c2c001140c000d60804000610761040e810010540c490700b007540c0e03070406220300400402c001d90303070b1180c000249003961145013001c1c91000c01c02c440c3c00c11200100401d4031155108525403240607a0b681c000c0300300480717600e044414800032f4030340040c08d011030840f07490029080c410419210042d6420020566102d102d40307940210f69a801d001d60300400b04131400c08500105400d52640400c03000300b07407054000f400520241800d1b4041e600c985a05c000070301c900b1104190140c40f0350001c0341210381b240100402d50342107942c02c54088043c40103c6042549608010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 493977392 1250 493976142 493976149
    0x50609030a06020c071d010b1b010209181e01050d0b04030c05120306041103100306021e0f0d1503030806061308190b0109020f07121404030606060311090d030c02030309 74
    0x1070a000c8502c0004081c09443d10380b0b00701c50031004d601003904401c0703014010809a00c440007035443d01e40c500c5038000443c27100b548586009000300183c003540660080d4403200318600752003415020380f00541d00e040c0001d49a845c0c680b2025400c2c440c16401c00403000b44100801c0c88600d110390030500c80d28107840c0034409920394a10303001414406102e115400014800c107803400d841800b840034004032082d410751070000e00000b10360519120140c0455000034010340003030010081c0f84401740e8001d64683e2902c516007602c4000350007034403201c00d8031440d00004401c200315002102003201d030705581e8000196a090180140c50700010954942d0102030314011420403400c0c070160049c900c8820302445c200c034030360900803200c25041e0701c020300d001d1040203103006002816046505050304402148030100054170105e90600c8001201041c402c804600401002560f0b00002c08440c0156024001d0b41c400e10080c172142c4c4144490b0345d900c42030206a50b00013a00900c80130704164002800e6074101400b04020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 493978642 1250 493977392 493977397
    0x1b04021605010b010e0d1109040312140103021309080d150302040c0806010305100b300408040303020c09070c140c04050a09031d090414070b0a0504060f08060307050609030a0602 78
    0x486030390351603a80f05119541e01003035880010301c003140e00e66041d80090326000f0541600000a50045803034000180516000b007441140740420840d041080001c0c2c034040a40311704c000e0100f06d2080303920600c1a8681e02880c0036011b841600028240cfca44890480c01070f004061426070071204410b920300001c007607940ca205540c4814069110140e0600e450303c0010116003000b000700d2100228680184680714007202940c038840703601c7d6440e5001d107103102c05034000c1031003410054461007103603000c000401038400301078030890740b09400b19055016520300300240d0100441d4038800254020808001050b1082401d407013002e00041960f150304640760205095480840e084000d2540742d8031b4080801da40304046146081d0450701990040414100289503c100508040c0010b0f0140e040112890380c14001c13800203240108100d541c5002c443c901030034079041441120701055110001c140c445001e5840b01d88100c80040c0035240040c241400c010503904580c0c402d5400d4440c0580701340000b80306100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 493979892 1250 493978642 493978687
    0x1203200f060c0d05161e03020910090e0709060c1502190e0a0801021c1d0708010c0f0305070f081017011506021b0d02130c090801050106030b01021b0402 67
    0x2c00c00d6071040030341c142c0760a840c4c0181010340e00d0010400448005640031420b643e518804442c405805601c1e18002c50190281b0300c000355028420802440e00070303411070348810444048001c032001503926240140c0c2d25400300d2154038080b03442807610700d0015510313400c07403090314240500041c14110070412206004008684040224603641c81c0590301c1d1500f41001d03070081005100941c5007030215801070711940020742e09890000d45802110307884290480003980d0b00009541103906080da5004403d002e030220003100400f14003030680e01900c0038464040c1d90f11402103a11041421442c00700115a61034005008452414103a000450034002d000c14a42d8280303040c0c80041090901e041400c503000d26258400c1e01554070090f1200128505419a002091004c591440e00142c0c64000700e007681d840380b202c10074082d25040006440e1500100c02078156601440200152381c1c031040282e080311514200c1a02580c05803217510a0f4214070314841d0400280503002500303143c40d4100000380711076043d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 493981142 1250 493979892 493979911
    0x1605030c0606030f0d0909050411030604060b09060108010b0a0c0c0b0d0e120307080c0904060e09101a01140f04031a0901140f010902030a090b011e1203200f06 70
    0x38440a45002c010300c1040c000640050070082600440c061b081d0f04c0144900400c0ca40c07030318001814807140c6d03042d03182c2e00c01c40a8207442d02d40c600f44c40c22100070800c3d0100300348501c0180b0042441035224420b264141e41500b13045503d45040701000fa00d81c1c1d640442d08a404c9901c03038001040c0b036040c10005d0428a0070041c4089640c91000d1841410034246900304000c0c0b140034010131040da64030001c1d20f0340280602c14210703502c171082404207029006a40150706c076090b4520600880b00d000043c02043c1c0300b41100200684d41000c0005542c040603401a14000f401c5001165249a1040c000300030030200743d0403207864150349a80381000d0b0484c020800e2480008a030400803040e400380624401400880c0c01101c00346015144401d002c1306c1801007030160399020001912109a60b4810f18440e40c200c0c640020070340e96043e25032500341c4898030b104a4044a00e90000e01056414000f41009515071501c04c042001e08030f14145104c01300740e9002e0b040c0308601d40d2010800e0144401d602544844 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 493982392 1250 493981142 493981153
    0x1060c2a05040509032a0106051938180a1203091505180402070f0803090106081504060b0a090e0d030b060c060601030b1908030a14040e0c1605030c 65
    0x30080104443c0003e1000000360810032002e404c218004100b1a40c85130038607020b0301d03014460400c540c0140416044550401c2e98010600b21010207001010704032140800405001d0204540c000e0001804032540890240d00761080c1c0082540c500103003805200031360074501019108000202c2c00c1d03605902c42c000e038004403409c40c814594083d1216000c1d1065112115000041c0000142180300300340c0c2c0f18118920145d01d0030003ea840390119101136811505e8014481c0190038800c2103580f082c1c1d0000040d46c030740300c0000303001240402d521000319040300345e04034503640c0c5071603483c040e0450340d440c20b500c01c62100010900140c540b10304c07101c907845035005011400d9108d00107800c80d08800c01c0b29216400500035189190000151154030420038600443e0310007004010994134012043d0381c1951800c032502c0400d1741100000135004841151341c6858501c0500c00321030547e44218094041c2c514038043c00100800041c400800503010036156000c41d15403942c81d80c50454112606074040307900013 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 493983642 1250 493982392 493982399
    0x4020901050108070f120209030307110405130201050702100e090901061e0e04060e071a070b0a020708070803040f0804080f0f0f190203071706010906080109030801060c2a 75
    0x2004125014003420b080c04000c1e414200fa000c0d28603010304940b44208104a542101010700f43d0301680c650407000f50840741c65401c1403034180342c040c18180400303005601c5d250008500091005044d054690183c58862a05800b0707000d200c0000b0750040343c0410301c40744101c0c2c00103545500303032118032810100000241403400d0541c64645010003501e220703102103288106000750b0b0103000310315030000c0d84500002100d480302c81002c4d05184107540f0000200205400203180c2184860080410300e1050b00c04c4003007a0742d0f4501d803804034001c8030000381c01140e0922003603000983e80381c010344c0c000340107040d10f11103030549554495056005810540a9030002e40003000310080412410288015910241001c1032040184070707501c080741a141d8036108000700600080d52030500425000e081c0703500d0328507030f14070240350259560b0384c0c02e2144919152820200085207030781881041504bc0d803641d02c0c03491a17403070aa0b040756400d050900940c0e41c0300b0220400040080580c2807698070710305254906003850300c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 493984892 1250 493983642 493983649
    0xb0403080406061202011e0c0c0b0a0206090f0a030f180b07060b01031a010e0d020d0302060f01140a0303081e0103140f0a0c05090c0712050702100518060309240402 72
    0x583c0d600c081120040f02c0d00c0d18005030b82162500d42ca1050b90b5110900000901000302d903920241000500303450200200802c1b25911000202001c00c01c68081f03541b00c3c0c0b5800301160303030346140815007080d5412503400000002d20a50405020200516044040650300140141c2a890740c0d4014024106e00142101c1004264025204015400d0808100c1b03c0e1420300b1045022480240b2181000005803c06000b40c0c3c1d035038100d090094024042d60910103da26020b0f40c1c400d01038075600d4074400c7c00e030000900b10302c8084ca0710700500405000b03000f000d459a81e0a0b0750308107001e4103c1c40c40c880d5803e504c2c8444600080304900940c0074481140c12004607250b52410003d0300040d40d501500100c41c14001f040d062540d5004540d02038070030720303590b07501c560790001c02d07008002d0003e01496021081200c0c15501201900fa213a008239215400102c100d40d06882500c07071a000f00007400c0c0500c06035507036450484080d6900c00d03081c43c181c48916500b400909816144031103102800200c15041c00306505 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 493986142 1250 493984892 493984901
    0x706110f1c0b030312060906040e1e070812040308030a290f011107031509050f01090b0f1915171501080d0503010902091c05060618061309020402070b0403080406 71
    0x750084c600d001035080c12000410001406a1300400b00d0201003003540c0c49662104201c00040d02c01d50f216828003090b05481d00c2001c1c070780c03003016114030040440d0b15400418035680d1031191414091400d45580c1d190030203908001c00400175181d640000390440c1280e845000031144040c0c500141c08081e4030b040100742d041130345e41c640c100141868107603001c000008404043d00d801a0204410300104a43e0300c010708190030000307080e4054642282d03000141504014034040c8103003028009681d600401d488a5001181c14603925114035400384c8960702c85a0111100c040c51050000882e500c0c0c898840000d01280c0380c46050754840c0814840a038400c001c0e1a0141c20240d0103801300c4901404000c3c9980418092000341d10b41c0010743c01175a59544003141c030f2034603003504802c0516149003055900d0303441c11583c10340516100c4003815902c91104140500c190307401841e015070350385102e03180c1c001050640303402c80e00590300b00700078804034400f440403030b20681c401e980d459100c0c03415240160684 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 493987392 1250 493986142 493986161
    0x150c0313090b06041809140a03171302010c0314031e100e0c0a0504080d050403031805030d2102030c0901090f0f030206030603010f0c110706020f030706110f1c 70
    0x1140341c03004500160f80d81508a0701110502c005820a4010030312501c1c0042501c00d00091419840c0c0b098007080740808501880c03840e00945411400e0403c22107140052078088424105042114100780300641c0900c1170003192501038a800c4120740714108540307140c0d42c0306940c0c0701c50b003010b400040b101004002141c00d0f44050351140c59615a45000300c0812122001b90104c902010b01003001d030486441202900e00400c0103c040b2040c4444510014010340d00501050340020b000000000f924101781c56220216400503009180c03540c11180c0440c2c08020781400100c441c03003c10f8006480030300710f00240d4040c0c0203040d0425524506500090000e03456039000c0040d8020f403603020040340705041c42140c2141d4040c0e49180d60ba580f05000240100454005001350703902d4140b850b903119600c1507480414500c2d440865420540b503010030b030f0392000c945000300842d500c200040000a4030300d40140c040004040ea030581082c501c500d13420207e0b0072a000503030308078100d001703218a042c81c01e01440441 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 493988642 1250 493987392 493987409
    0x90306090f012f0c16030c05100c05100f09050a0c1e0b031504020409050a1e020c060109020f091002100c0306050120120f031006031118150c0313 64
    0x1614003103200302c0080f1420042010822030208032203a06650500c000c80020311250f040148080e128507001c0036228550040c1401034010001c07001c0d60750702580704001042d070803400400c4513010740400070019002d01c40050b4650741d01c981d00c4a0024500b0000600c007540308e110a01e40d03c1d82007080c02c0112906007078403000c690f60202400c1201c500310340300712608400c10703015a450104141d8040b87c064401c07a440742502034642810000f101104c1c0d030014150400c0301c070821040d403140c2d001c001d080e400b51100480c01078010000410000c400c9500920420750001c0e2480d0034146c5a6002a941c0c140314040c0b00090380000303024803130101d010f2081c1100e04e00e050800708a404c0c28180020072180c540742240c00ca20303582c46120202d1200c00c2018000c5031050001c0c2980e50b807100e2808054540050f680310105001044010503602d009006041011000701a4a0304103003c00fa440150142e4076410180c01060101c05e00301c1c1d0018040041c18144411402542c0e02d42d00f4001e55408103903140d006180c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 493989892 1250 493988642 493988681
    0x90608060f0c0315010c0b01062d0f0804110306100303080601031a09040c1a0405031e0c240f03071e0e01180b04090c080702150f0c090306090f01 64
    0x4001c2d200030292a0032101e00155501003104040041e1000480c1d088041c059003a03000001034150791000071100d50071880500c000e011408601841e00600542c0440c101042641c0a0051040c3c0305e01c61141d4014003031805407a5100301c00b404241480404d50340d6040b0a140120107100781030f080071100d0340003070082c40c017000904280c06607216400310210a0030f205440710f0b4003013000e122a004010b0050a905050300c3d103015a200e6640c1210f034440e00c50306002e07001742003034000ca103c80c08990036400401d80780644400d44200003040300b51504841200d8940c3d4064800701340c44000c58003e4001c003c0c8003288983c2da41000c0c00040c04010380d003100402980714a003c20f00c07402e5070201888880200a003407524403003070710012808488d0400d0700400500407001c1000203c07140ca40d000340c204582c0340c1c0c48522160308d03040c8040741c480c17040381400304d40440c40101149041500800d030075404241049a0350815409000203405e1480549030400035a0220016203d144401c1c803526444814400720b285 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 493991142 1250 493989892 493989901
    0x215090a12020f15120108010b10021b0d030203070b1f080a0f060c092d0f3005100f0c020106060c060e12120118020301120f021306090608060f 63
    0x43e052507642404a004083c90428040b0654185056880945030800d4000c604d603100d50025000b403054852a511601d822408400c62500108a440740c25070311200c924880b1441005200070310240f42022011480308000210101740400011402031580c40040c05c5010b1186404500c07070202c07074010450b2608448600000030302810300e8204019031121b800300c1d009104540540d1609600d61098810b0b800310554040040e1a2440d04050a000300340140000e6450300c81003609416a40100001a2410070100c240c098840440d8007844082420050506c015a500c80b810300b02e00780b0496171601c2c0c40768403400b0810824002c00080444520080000710714104008105e195441c0018007025540c1c03001901e801340501207100d03240c0c0c44007006607031141e1009900403861307001d02c40d0104030603010303224420002c0d45000f102d040b240808204480d140040d255001441c80c07100040317901104400020080030b02501501006011200000515600e001601418050028001c03140d00c210380c030810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 493992392 1250 493991142 493991149
    0x191e1103090904020604211a07020607080a2a0e0f010f03050903130303020307050d0807210b0909010207170306060708030c120a0b100807050301060e0d0215090a1202 73
    0x19440040700315908503250715180042101449039070080d8511600c960b04481e080041010300020f41446401c2c400f40045010245041c030001c280e0704c0f400107070041e0f00030420561041c00b41c01d0300107604800000703204030203500d0003659201d00c07a00700001602806900c51241d4001d880301a400900703540e080811500380000070081c4005824040600d5a1403004c240300c100100103807203002900d80c003400c4806407a82400b95580e00200c2c0202c855205040070310f082c0d1031207411298040e807002d442d000458160850650b400240751944100391320742d1440390302a10340c0c450000c0c6018900b040d00040c0d07680300d01d0400841100044400000200082042c04171640b107610440740c0c050340044511b92a40c4402108444500c10544c400c3c8428001e070b420300c401210107620410a00b00100c43c812002907245c0802e541e006421909140811024401000700d140140d28011100300c00130102c40c0c3c0c0c9403081e80050101c8040041c406080d1030b0200d0f15041d981009141d0034050151800060040d1401342e001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 493993642 1250 493992392 493992397
    0x180509030a1b02030307080403020a09060b1905131502010e0303060307170304090212060f1f0503060102160b07060b0109121e060e0f0c0d0209040611191e1103 70
    0x103003810042d40303a4240140700154030700c05001550003001d80340d0f1501d0508003140d440e001800203a100c3c100070a030011780c410f001e1180300211102c3c120268240030090200564111041107100c1c24802e040000c00c100006076040c42001c0c1803150b00502100c3c0c0d09510003421550072000450440e0700810070b005a03942c0005184003218030524124185d0300360810348030b0450180c2e522004403c1c2c00419140040d685410000384140740680720303a0004920359040103441c0300520050361414803565062031600d07104a00855100c101030040314141d115003202241c0d00701c40340d80b260900d9803001c0380a808010540c043c4a007089024a007141c6087d081403820400542095401040c2105007150304052042d00c543d140e0301103400200400a0800403666076807121b0814880c0d000300c0c010100803107003a103410655445041d130003400c690425a61591442c000f8842030034004c2154800340b1820751090034031178200340b21000d2540d079030f0452540d42c500d545580c001d19451406106069981c030040e041c00105 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 493994892 1250 493993642 493993657
    0x70b060d060617030d1a0d061a1309050c030a030f0c0309170c0301050106050301060c08090a05191a03010612180c06020a1109061f02010f0c0918050903 67
    0x80580310621203190490040007240c0c840c4448100a0843e0720781003102001610007180300d00802e202e00091066403845540015800c3e03a480440d0110790400300e6982c0d40901e00540340c240c0a61078101c00c203400034a52014400c1000e00e090b0300e03600c140c010000c3c10302c118941c16009a00030301d00d03041c06507409020300d0714070004441084a01c09940080c503110354210b000815122a02039458941c0d50300c02525041b544d440b1501940c08d22000144035407044048074100d80182d5039586100341c6070341c0c501310303190301904645a00400325807000c20550340d051040004294160801c9a00a29000108102490303403a00070715625014401001060741001c90920700c0c1c41ea003000081c14041c0300d02c243d4040301201b24050712840b441c0b580494040d03000204095030500030780e401d0f00105e13071071020002c6904007128484d400c050180310010791008001416204a82039000106242c03008030b10b81c074100e403140900382001400b04202040111081a0104003031130300c2c060305000702c0c60114650382d62446201c9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 493996142 1250 493994892 493994899
    0x90b090c03090703020d0803040b16020712080c0d03241a030405011407030c0e04020415300605010908010506100e01020f060c030f10030b01030209130206130e0c070b06 74
    0x1002a5008000784010006117a00801d1109202c0c41420848144e800c111402c50319502d8010118810442102c00681480c110f50700270701c61035082c80b8608180c149080c4003214103620a02c90a010103500b03000c242c5940314603a40c0007807240c1ca024040d16070000300026074400130030f11640c00e11900d400b020203020b0781101c40c500c5030364036140c0b40750480c010b08144503400840e81c4000c0901c0120350785a00032980444555440340f000c3c014500c00c1004070b10444c0318005030a106840e400a16030300a84403480080466020986c0000000502d0341880040200f401e1110341d84280600c010740e0010300c10801341924400801c07462400c040818440701c0030741c40e01002d200c00450301040b540e20812644c50010700034019a0f030303503041942c40744c65560010790b03003540f14102c1507000400c0c2040004020089075085400c0600d203910b0341e024056840c5018200789240f0310030500c840d01580324140180700074500701414044841c51300104d00c4281e240540890002e000030445240850521103035540c010108a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 493997392 1250 493996142 493996147
    0x29270d050f0127030c0f02060c0307110111010b220b0a1d0a0623150d09140f030301090e03070614070e06040b0904020c0c040615080c070309140f0306010902040f090b090c 75
    0x1f400010b8842c01070320347d081e419110028808041145448105a4094003a25500101c881c03c076015400d0321645200c05402c6018044914040640e12900303600a2042c114001200d01d844c00101e0b000c19141d400c0171103103031002c80b64100304e481000c8075540c0c1310704906010080385041031040c1401041c1d04040049084e49260210555510038080000510150721080d81e10b10007110035501034000c0102c1650481400142d01180c0d090200b02d40c0e1195480902461840c0c2c00e040c8010001c244035110705019100600422001034441e110700422040003c5264480780b5140704010903401020b90f03902e006a00500007040421001c0d81030b00c01f81c4030200e802680303841007a080d45140c0604816100d13405414508005102030f0002ca4284020074940e44120a076500c01550990750b10826400900046800100300b020221000141d030440000034815904030031428006454410280c1000108650000f81048080f850488220003041c0c0300005100d07062580c40050740c606401010802800c600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 493998642 1250 493997392 493997423
    0x3150102010605040c1205010f030302060402010c0c050913150b0604090b0d08030126010902030d0c03020a0f140f07080d0503040f0c29270d050f0127030c 68
    0x2e402200182c480540204941007158400512080d0f9100e20480a5464500013085244a64044030103803070305900109100e80300c55004403281d4078a00f40c01e440d800700015020915030358440d1a0383c00746001004462100d4000e040404162140c0c50f08034181902c2c003414a44103448100c1036404886042c800000c00300302c0d45011481c4103259010007411214000b00100da03c04014001c0a1aa14201d00c08001030300e800b8202403c03120240d40c0654103610030800704040610904d040c000f414030902c181c038800801399840081a0302c1c100002c480c4100407111150f14460200081e6100c03103c208000c1800500c0d01030001c2d111a2500c0c10740bc00c00600200180c2403000c08622040c0c0395034000b110000140e9152001010300382c0d1a800c0c5141c081410072140401c560391015a00070300c2090580300c142c2c40316070b84035518214102c1c203110b4001ca00b0794400c6011032814002d2914043c0028008100410010854402d0f0012611000086103045190b5001320360300c0012146044d90129001104541 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 493999892 1250 493998642 493998647
    0xe100807020c040f0e060108161e1508041101050a05030a18020a090605011404030203100b1c05011406011701060809030f0c1e011a010305190608062505031501 70
    0xb6800150380c0081c103020b010792150406900030340352452008151074043c0d80f1010b8140d1a0f01e00000368010714110302c0818005060380c1c040e40c0207850f040c3c244000b2515079441e840a400c428038a10070380072034440800c00c4244001030b01001218502407814920b04054110043d226000107040c10743e905664440f00351034070132107108031680190010180790809642d0030080025044c41c2c01580c0c0096110548660300d8a0035400303a0342a43d50007006040110020000e0500800707884044503404100709482c00c5a0100844011003e10f00440000c11652071101d64610480e00140040d410480443c14031944241035648080c103692480ca055421034960080c014a14051f0729007013a0f049400050255400e0000200c0b071041390100d81e400014101044810760032103007802c660300300d401031100d00e500300340d032103036020700d81c48115a04e00b00c040100d00d280382401c4843c243c210142940c065000c0c0b158075841100a01c40803003480c04c074100e84100e6404000c20700d00000e8490155801042c0d113000786a030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 494001142 1250 493999892 493999903
    0x60d020c0c030f16060207150e010201060302090c180909060403110709020442030903140c06011d100302060306010c0510050a0c020304030f1118090607080105010e10080702 76
    0x61004085038043c0380314042031501c400004040ca03080f41410100020014000300710982114051800c512002c100e4050680303103006220101411035595000120040e1b8406c03090600800c1d08900c00c0d83c580c014a10001c2c84581071002070303031161f0340480c00c11240e0f079400140c0c0740d80b2650618042840c0310282040e2031606002d42c0001c1c00007400403402003050351a00700e502856603d1041401c0c1c15040c0304003020405404000c3c9803034407881c05440a0003003400381e0821040700e842071800c2c130f908411602e41e0030a90303003100101d151290400b80040211040a210410081e9407001140b525400d0010803919030302038504c4001d00551003c000201e4503806100c0011185400406451100c0640e2302e150000342401c0b580214541d10f00002ca061851001080d50241c0e03611a85482c400b0180b81c44411074076442e100f41d954014000b108280c0043c00d840c440e0350050405c00010b10f5181040303140504070751416040700e8104804014481c841d0b41e1380e44509101e00c2d5550900300b0761529252030890521 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 494002392 1250 494001142 494001163
    0x1206030c051507050d0503041a0403090b1605010f0506010201150b0301030b1306050703150f060503010509060f1002030301091a0303090909010609090b01091b02060a02090102071a0310080705060d020c 88
    0x20b00030a403000d80020380043c0114423491245179079616041900d81082340c41c0d681550040d00103040e0130350500488400c01c0c018040c1c990258294050312901e40e64003801d551310244ca160981d0307211402c0c0300c1c96503024020401407426102e19501d006080200618207404148005400d03162640082140303000d21844403003120ba0801e2040c4154034002c2d02c0600a4003420b40410350708201200002045000d9038071040a82c6d159540c1c03546107034a00070030065066400340c407040c1e00c2141d803001000c06940e59801e40e051980d041c4c024545035803410502c48111003040b0f1690090401d215104200740e60040121541d090b000c50b00360070300d0749170300e1040d50040800d60054040b0394a0520030340140022070745014100d03410035009200c185c60000c0b10b0cc01b11001401c0d500050b80c0400c0114441c4441d98028012000c0184100c621841e03440860400740310600d401c0c000107010000610020b00c0c901600ca03406800c12800800d0340f54580760200d00503201e014028529140d0114410300c4c1c0440c01e00091008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 494003642 1250 494002392 494002403
    0x207171e04090b030f030a021515090907062705010c140d090302040e0a05072d06030204090c03050603031c0603120201150f0e1b1e09011206030c051507 67
    0x3a56100c2e480300000b00480d035030451180c0304482029034a440000111114040d40e54090500045281003c3c011020003078224000c0c0002c031441003e8540702c020070f0611a821200081a4092610001410020324204510301041540e5026112602040400c0c0c044a600380382541716052070303041185c403003070b50a40040303118002c0c6440103c40a41c8621540b041d44d000b03d504008280121808968076024808010701a41089000300182c088225144203103c0c856a0514442c81002240448459542d00024040799001c10b081c8030700346461288900800300c1d410200403d0501400280e030324041c5440d03000004803002204545000302d50044401180e002000903415236100c14081d01030411903010300c595a1101e140000c01c03501108882d0100e50101207203103a079855030344100022120b60f0405074124581042081001518a014240720760058000c0545500c843d0000400040315100003411090a240040c800320310380442c0b02d400c40d40300f02c9440c1d0101d4030707000039030000d8029808003400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 494004892 1250 494003642 494003647
    0x9070f0e152512032c01060311041a040e10050a091124071103190b0703020c1c02070302031b1c050d0c03030e0706120509010207171e 59
    0x91212500001d40720746903010b02c20111506950900b40d021100000000d41540118411980c8440c000d50111618980300b89007407900c01504400304541800d011808551a9502c000030001d02081805100001000303d8007808203242d4440174421440f84100e1b4103202c4e6941d801c920618a41c00c00107800d0540004c2c0061100340741c070100840080c50003000640b210017941e041f419840c1303414529401d800030704418982e8014800e500045080d0000e00c0e04503030200b58121041030307541d81040342043c4003090708107110709800c0c1d44c50702ea070f03040303074060042130906005000d0303a03142110104660b014055040c1d4541c0d040c2500c50340c220b15000350741d072020f50107006481a400c0941d0f2140511203a60409030344002074041002d9290445400c1140c001c0e0054202d221031069551040340340001c0302d4007038a0042800395519944504102203a80054081020b5007264103805a00c1d0040c1c0b43d020b960380c0021414024951070351000701548000f6104502c07000604440441005020200d1107d510381e020754 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 494006142 1250 494004892 494004919
    0x1d010905060d1a2d09060714030a020706061805041716030c050703122607200106090e030d0609060b0f0f0f03040f021905150a050f130501081509070f0e 67
    0x4c6000e02c040d504003910340510360000b2640c6000d090b030700c0c40b0303c4104000c552079691750f900f144009411002081303c5c81a1212400901000d100d4684981c20b0600840000e0a042c9803601500c00285102c40681410f002e020382c2c0140800301e14422881c80d007506000c404442d0380d1502074281325044e000100b420304403400c16072045510000040f00c9840307185051442080078915005004e404035040c07000100140915500c0301c4074000e0340a24100c03182c002040041e01c0b00c02050640c0d40002e20184582d00118254909940d98001c0200810f0862000c101c400d0030f01000307484622800d002101c900c1e8000410085480f01d103012034115200400c655a124100b81c940032404000000040c7c3c85103101c400d444188038104040311040341c8008180410140020304940c24a4104440084c14001c0500c8900400c06000c401030000a031751580400010742058005010703440c01400c01c00150100886070f54643c0c503099035846d08102c0c5030400c02e440d00b00301d07402120f41014403804541c0220201050030f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 494007392 1250 494006142 494006221
    0x120309021516020925111e0606150702130504050a0f080307090905250903020a12021906020d0e1f080a0f0e150408041d010905060d1a 59
    0x280c0050f00c200c500e100349848020309507040a4440f596500c02c2151242d10703030034403400b81321600c400d0400c0200b0355840d060320060103040707041c2d030148145003074100d0810401c070341ca841c0c40c140c803c400c5065540780c01c00340541c010031848502c0e49501103400d0b990348003007000d001e0100f02c0d01a00d15841080700c0f5101810f4640a012900240c1e41e240100303014a202040c0840301d8001c40344990040e940310041c80003190b1540650030450880c000500120103408009078882180402c00751180020032000d520107071040c0701004032000001d64002141400510070340d03501040c541c0c0040c4145c604062842884d07400150340c100042c090508001b65640b49809a81d04001c2c06445003040000c20000c00581000c00030680c0c0031903640c24203582200c100301011fa0550f0180c19001800359048504242d10340204142c40e0609184150f0700000c6000108081500d9000751030f40048144c070b214007868406e9075841d016060343c00510810316501000905d0300700c80118401a4820003102c004003125400108 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 494008642 1250 494007392 494007427
    0xf030705120403051c030e19201509060405061918120f0602040806131202030f0d0e0f060a0b03060f07050f030705040807140f0d1203090215 62
    0x40390030740100030804040500d9101070b181203030f030084003400200e2859141c4802013a0070340000f1040c51740d01d0091074001502007110070010300b01024000010f00c00d604290780c00141000040303000c0c0e04070482c805215164030300540705824500305029200d410440004410f401a0703000250411408108042c3d00081003081044100c1140c46400c04441e10701c0d0070030380243d594060b5440360750070003000741c00088420211012281c0100001418a5204c48000341009030669405500041d042e4860061220744166560012174a0006506d4200d07280d001ea5483d005540c1c3e40000baa55401040300908424050403652018890540b40c06103043e11445000740030390301401e1300a2042c0d00010341c2c901d01750140c2c1c45c0210690380f00d02e41445102c905282040d4401442501080024040000c8a4001700030b03040240210301c030240003201b40a03040c41030704180c924030300d0300c240c0307154801d800807641c981040b40c0d00e139009141c04100c0c086140041420004d02c0c2c1c00d0f0785107002c4002480c0490b215074001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 494009892 1250 494008642 494008657
    0x606050409060525210608010e0c0a150c030c030c020411030a11040b07020603090a0c180e03090a0b030718090f060b030f0f18100e0d05040f0b13080f03 67
    0x540c50a00c400e50402402c1911340640f444003040b94a0017090340c1d0050022807003214070f882100480c8040e2601c005509403200b00100e0210740c0d00500c10707215203203049401d49026080c11403041402d41300b44140100428050400039003404040a055018103108114a070210b9401030030610600c04009464462a8000c5403042401742c501403071844629044021503080311000700040f400d010064080128540c0040c1a00204d48a030b00b400000180c0c95050304030050070f0500300441001c010210301401d850541e20025801d4008118040b4156245400703401a6230091610030f032280c2d212142554064903a410360b040540e0f429400261400ca240c000c0c548203119100c051006583d1440015518042034400286c0c40300d001e000500c441c91529001d550040404810300341c082c024040d00b40c1880e8440d802d844200341c6803041056182810850841414078a1801d02d10340780ca405034000c80100d00307002c0e074040c0500001e24502600740c40a4503030041c2100900755101100c824580983d40c0d1700080 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 494011142 1250 494009892 494009911
    0xb0a091e060f020c121b060c0c0c010c0807030c0633050a0e040f020409020603090a0b0c16031209021504090b010302070c06030203090a05071202130e12030406060504090605 76
    0x462141c01000b8a009686440400703c0c0100014464103848030200c3c2c1040c0d00c0201402d80303962074400b0119040003000d010303d926482081d0b580800d003410900300f0f001d00713041c503040c0811020000300041d000c078119180c090305442d040356400e95910b8020050000c0f290b425604141080a5041060102040380152910a40b841303081d40d940d0800d205c00c160f82d80c45003440b40000e010005011901640c02d0301c0d0800c4c4010301c0014000015400100300b50815600b00f0201e40c846002c6208000000d803020740c00c8132038449681d0500504200c0b84980060760f140050400c18542103100b00130314150480c0840540c02080f00e40004044201c9650541251040101c4282400c0c00814154040d00c2180c40e181d401101c60b40e051418808150003a600140c420000391007407207202c0c00400d05c184940340c00351900680e02d030700034a420300400120b26000000389040c10b1800288034038081002440d403100c0ca00c4410195160b541e541045401416075503c21a045800c02400f401088402d51005101e20b4440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 494012392 1250 494011142 494011151
    0x612021306050a0621050f06150405030d05070b07080402030c011101110309060f07050a050405150d0f0c170f1602030f07050706080c071208060a050604080f061e01030b0a091e06 78
    0x101030f0305c0c054450507100701c1c2030942105e01003100c40c00c100440214880611000c64500b43d5142e0100c0e00d030442c200040c070002080424030a08105424041507003045a6160130302d01410f1503000a501c3e448811203950600c00020740004078000d00b9004000c10140e1000243d07224a030003040d0b2502d03400201e454030550040d0000058506000d041555131b6181c0031788e54103082600340810f0068400400d10b2001e0001070034080b128614005005405015603038000125001d01090005443c025401c0e0070509150464070401045030203200c0c515074005102c0c00d4280e04079011200c241e00b14401c444d042d008445000038010240823001580304125031980c3c1d20480d1a90318040701846130300941074020a012070103d00c03014002e21500b40c043c1c002070010304408030f20703a4820000384150f11550202c440798214442030758440380140300f0b40d80d002c41c1170f500841ea00c904a0340d0004002605010042981914001048040c0c00f5544030f0203000c0e03400714000c268510480107903a40c40030300310750455196040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 494013642 1250 494012392 494012447
    0xc03060f0a0b03070302130e070903110f0d0b0a090f110102160308191b05011a09132904060b12030a090b09030c0a0b1206040612021306050a06 63
    0x25000703550440704010360550035030311185400c0340a980001604d40045004581c046040010000d00740d0103004546c584291640c03851601034403840389214510311500c405a0380501907190b0440115500da40588149803540d1907008000090541c0800a481d91101c016140c041010481c03d52501c03000903003c4444000c0c45581000704440140001440c0703d000b0302074184245403655400c0c81d220158107214007800751701c2403501041d405900d0b00b03682d240c2d1901c0800e11402c51823001404004425a50040145401c2c03002c0305115004100042116052000c0b80510020a400c04000191815184019403c180c10103a014040581021b881054884600c0002040c0007007214410b50b0503440b40c4d0101807500800702c14a030082922290140104001d0700c03420356440103070802410388001003584400349034548521601c0000c002c40d01452420303030280b01d2403214240342c2c4100f945c111184500e41240713482c008050308403070384450380010500e8800b0031101d4125880300c3c103d108007a02130815851707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 494014892 1250 494013642 494013649
    0x30a0c060e031e1608190801080c060a080c0f07060603020f030d09051203221707030302100b04020c0d110f0115050d030525033002090a0305060c03060f 67
    0x10340d00303d040250343c145444a960f42110f4060901c1a002d0301142c40f180440b6111006581c1c021904504041529200c0500c044d40203e210383c050190350008040c10078a01004c5041489010b40c460305000785240050301c6142c1d03c500301c0781c91a240381c808585170315880c80d10801400c050f000492284403003041000640c2070006161480b0050b560b81d41c25400e1401081c04087d948421000c5502c0c0810060490700310f41c00050210341844000100f00c4540c81e054660403400c001c0c0c840304003190030880d4100007190f400510609d02c20800540024085510800030f802482000c40f10700a81c0543c110051070713a504042801d0304092441c0545000382010950369080b2280f803000d01c1a4041e10703081c188054140038561804241c80790403c2840c1a4400c04400c14580300c0d083c8030502a6540c1d00d081e400c00d5441030040300c070160b600b80420451b41d207840c0380c0c045d900c202166640718140d01180d40c2d41c0315940e80740c8000007160010150b5100c0d083c0703415034581540c0304407003440c0100700c041610b601a05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 494016142 1250 494014892 494014897
    0x801060801140a090f0b07090b070b07020c0d0b0a020a0905030d0e130b1c080c0a0b04150c0e190b0a020a0c0b0a0815061908040309060201110406030e0f030a0c060e03 73
    0x164858205c40b03206009035100d40041e40083c1c440000c1000c00d41b40030488020000c0100032141c02000507484a10389200000c1c601480318910a000303248050a031000640703000c480e5500300e940c4600151300c0d49035010040724411816444542d140c0704284503310010f40000c840001c10b04151012000c262a0b85121001c0d00c2070b51b0301007600010100070307401c0410903079a807019002e44100078a9180a0341064914542401c211095641d0300903035043c4070070020904038082c003e004c0c0714024020060004809802c990001c0c1c0641c2c043c1c1e14441261880460300c80031640a00b4031028800c0c2c6032845144003d6642e06c030000d003190324031192180460300c18441010303651407440603669414155a91542c1d0010600e156442540241d030038043c0201d82030900c1001b082204143c0e0314041e1a18041c20300802e14001c2d688004256450001c008100212520889054801505020440145100355039182c00d590745045090781c0404100c2c0c207403c641c002c051501d441d000711014459021030402141c4c80340b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 494017392 1250 494016142 494016161
    0x20408070501050f130305060f09010908030a0905210405010306050604080705060d090501050c0c060a05040314090607050f06010f0e0105090402041d1c030c020a020f01180801060801140a 82
    0xc0d440000104001c0d88241c00400f05101502d001d2402d0078443d41c6580000700842e0800c85158206204200e0102c184105240c1d0050307921000340322580080e00c1e507500f6840050241e03242e1507200c20554081c8070040180407800700502894a4000c1002810305c01c981e0401c1c09002c1c00a0708140c40000c0a19040094038183c481c04000b50511a10f0700c001c01403079602c91002c1c0c4e400a0b0715040800c0114100707101d00307071161401c0c00c0c0c030030398440607080e4132810803000601d41d000c82842c1c0703014000401c0c1e02090103030500c1842d104240d076500c444000070320980602c0c1e00041c124800c40d5406035001d10301050b41812146c82c2150b030a039251326a01d2080e0303160000d008144c0c00c103001e40002005480c1c0f581250300c845405a00203c0030400340000343e0305001d164a080b070225180703410890180303545403007040c02c44030700c40c40540b195410302d0b40021000600224414100410144081c10450314441100300400c490402044919603c29045010303150661030420f0320048600001c0c4180301c0c600a503441d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 494018642 1250 494017392 494017409
    0xa0302060d02090102120408010212010501080f07112802030d050c0309130204030209270115031403090d0f05060106051206210a06020c070b0406050d02091c060515040204 75
    0x41041c0d00700203200a411000307030181144541d480c040c1301007088600030005400304000140c6e41d10b400c3c201c4602e2403081a444207040002407010031081e904505075aa400855a2520168200e510181213241c00414080341c00103a6a0a40d00418011600c50341c6100c244290706031215211a880d0030f0b11a0300452548218a400c100300450080c40d102d040d040c40441014401400d007900c3c0c1d0081022508101e904198201104601000b858000d10b400e03002c03000650000d01c4505000c0903d030000c00d01910005008003861000703211060350034802d650610b803000d4007841c1c0c1d1a1540c10031a01c80015200d050314036000340310001c01c6491113582142c41c00c111803100c00d5101d841d40d1701401408217880c41e81e10301140484c0c003070225410080c41204001401140c025880d0181e00341e005007443c0c22580008806501004200301550300101aa00100200e41b001602c0d207290201140101c0700400e40e880b0302562418003a01040800d510240c01034140010b50b9284885105c1030108903c030790b0160145 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 494019892 1250 494018642 494018647
    0x203120d0b031b0315090a0c0602010b011d01140904060b070308040312053705070504061b0201080f090a0602070f0308090105040c051339170a1a1504080c0a030206 72
    0x448401035640003950003081f41c0c00c0c042d16440349070741e1400c982c01400060f5101c1c9405507156902420340c40440d4400d044c1420a50400c4002030034041e115410916400c0c0d01040f09681c5944c0c5078094002880d9a07001a039888016150080458104540860200d0001c900c96180c0e100c442c864280701314134098180b502d02c44e07500c08400c0b801400c0d030300030804421a4410365098124501626000b07008603168580c0311402c104c409024005a100c44511401c001049600945c1c1d009560b190808181c84141c1e8240d1907444210741800d1403e82c01030000c0e4000031340c1004008410040c083c2c028003d0b610b84403903072140d00d1035500760b480540700a0140e0881107800c2c0590b203800d0748024030b00c281e40d000c005080c0c0f4074140601c044046800f15162500548040c454580c40c5d28000804110170070714050151a416188105620350041c00523190f090b42e509130b80009600f0341600c04450400101011003002c00d041d10112280e00c1405218040d001d40c032102c080c542400c0e184101641c1d8020312060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 494021142 1250 494019892 494019913
    0x70b0a061208030c1c060f080f060610170f0f090d080106030b0609041404021215010312090803270f0d060203070c0c080f01061a0909040203120d0b031b03 68
    0x260b90308050301c01c0d092020b0810111415600405080c2200408814042940c504e00900d802085100741d001028075007008003252a8018007203042507106600f00c1e001d1000f0700102e003046544101402e440854140100240449504d48801341407048041118812503591440030340b9849150b188a81c0e00480c88410041c0f0615000350400880702802820960400c20684005016070301445140d110180840003440194100020324014100c2d00400134900c152642c141e0541500051201400d000340713200b01e40d000a88074042110041072407400300ca031a00c065000c15841d0f5400403601c5050341400d44180c07503850030140600113440ca4010400d0152320342c1602e0700c1010b903100900c00400c10109034101400030310301a0042020b4214800142500c04114101d80d08440c142d400c84003002c08000a10400c607079843c02201d2298405172560742883e240c0e4070100f46896081101c00801501c04030783c01501c0c1c99103900440d0419401c400315401401070001c1c400c0a1030451241c40e070103170481800380 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 494022392 1250 494021142 494021153
    0x1e02120a02010f110720040209031e150402030a030807050f04230405091504020a030803040b16180302041505030613020f0a06171005031b0f010e030d1b080a05070b0a0612 75
    0x54848080d20149c0780c210a900082d0400071a074501d6044d000400300d5900039004200700194801401c1c0c14407140c0c42c2827940000381d031101e11040c010200f100c08000216514401c0061b61194400d8020640e1a503803500c405800c0d480c9040962a40d030300c0c150300d14030b03124a458020302d07004a02c950040c0607101181c190310003203400e0041080c1d0308210409000000520410000c1d4461070042c65900b01c207041c108007040f80764002e140c0309403c1001e4049503100985440d2003e0040b80c1d4110340020b0521008044c1e801024000d50281354503014210030050341c103a85100200a092080300e199071400d0040d0f0411a90741e0980c003c000000d810101d006000b020800302082d0808492507007a20302581d1440002c2c80c182802850303094031200307103808680a092000303007180821001d081500d080c101d0b90740803079031364070440c00044100000350960110000604403106401a0085c500c0365881000c03c20141c010b038804a02100d102503108001030080256105840c02c0d282d0b15008586082150707104c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 494023642 1250 494022392 494022443
    0x16140301090e1504050606090901090804050607051c1214131214040330122f03160207031509110909060105010306090c1e02120a02010f1107 62
    0xe45940e12030f008441c1d018140301c02c400343c441d07840b40004003105e14210043c03007101c0380c025296440c0e981c1000320800c00100d20740241c03070a1358025501242c440c1030758145a49055210101c009480c00445140c08185905c2003c0c540b02c2c0d80145021301050414070007180c52110100c400351041890160340000140e03940c1c2c6491680555494024001490303c9601e540e15805035000300c0d541060340c2e12000d803060040a00780c2d54030300302684003941c100300c0000180c400007500421025850751000c00500c0403410b1000c10034810118a25004006540044002c0760361042d17410b149180e01942a195085100146c2c120599500c001e00c0442c5005034510b01c4054668200700b1500003850028000032920780029039481207040400910390340d413600b030001d0201ca94a030094540181803800041ea6039400108043e000080d800010b4a01510360b1070890820030030104441c404000000e04010705070b8150000241994100b508111101003541c852160f4800c942004100144c14122a010315109403013 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 494024892 1250 494023642 494023661
    0x30c020f0d121107050603040b1302151b01060801110708131503090201080705160b04020402040e090f0708150f090f1002040e01050a030b0c0d0b0a030b1614030109 72
    0x35146884582e69403460307400d188000c00c00001c0e5007042d4040030280108101c000400050745c00520350300b401c5e190002c441c040140b0400c0184110600c050454444254010000c15030412007070721a0365503914030344c80d01d542140184482d03003800c3d008625150103209000a80351894020751802502d0b90b103101c00c0e81c2200030045202500c41000190326441c400e0038079004078150f42c0018804030144009448918003078112420808148001513000b0202202011308541000081182d0340e958800180684900e40104108420744d0040c03100701000010741032008102c8505543d90540c1b1413003850759030100340740c0c208076092110010500000c2c180c0e07455500028800d081d524412420994641341c00c0c00000070702c240f107500103030400581c80c41150705805010b00b1562041d20030b03c0c40d203e00000c02005031400080403400901d06007040f800c4e031302c0901e42d420050304003414140d0344d04080c96010f030222030a411076117420090301da0040c0b040040700d09034140a224981942d0801111000400325000b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 494026142 1250 494024892 494024899
    0x10f050c060f011806050604120f1b031a0405060a0905010b090115090902090a0603150e0a0605010305010608070807181d06030705031b10030609021c0513030c020f 72
    0x1980906100078407020784640b9001c090000c01c1d5150a036042003001c507842031103a16618102d801d000d16039503a000c44003240c000c40100c145681050030220740d850340d0054004c01c0d00002c81400c0c08a1905841403104690240c14040d1069580710010141030307004031001081034004400286c080000340d408071034440e01540000034000705080218254200c283c2001094015608522144d103034840c0030074001c0e02c41c00b58198204074088001c101c410001c0c3c021a81403540b1840144c0f00c060641c1a0f0341c0052110400d01d840d039003880155072005001c03d024132400642040000300e46640030301074084c001c20490b580c1200a9035000012500305c0003c80411140100c4540d00140480450065500d050b914090840c441e00701603040500d8039001c0d501c91b80c060b80140b0720300740c807a0040c0c00445510740c1c0c1c01e41e0382d07000145202c4c8088000b0112078210030300081c40440c1d80d44280030091707404100b041a072031080003d41c403140c41c1040714440d014401400541140700b68001800d10030b001c42e04902025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 494027392 1250 494026142 494026147
    0x6081003150b03010c090302031906110a0f1d09190b03120903061f0e060402070204110c07140f120312130308060109060509191a041805060d02010f05 66
    0x350348510801c00d0300310040300301c10780700e80204900e8502131060144000141c00c224007010314643c0400c1d280e4608100c8005210b00c00ca401c81d040c05150b0704488950100c141c030850351050950b02c00b50059100540c400002000c015207258407000c100e110b0075202e2801010721480769103036a03020f401407010740e900005468031954007000c0381d1410800012804000d845844e00c40e68214103040c50320100a00e01400300401307400c12202d0142c2c0760303004010787d90700b80c09030b04080e5203140101d000383c886c03c03a000750030910304036a80104050440c0508000285501a0303030420350340e400344080d0081a140410747c4600008100b80300c614049a6001d40b002c054030a0342d04215105145a40741801264200c1100030700c01012020160300c1480a6807194013400d00d61119414064010200e01403524114028218030346000d130940b01c08480d4000807c0800c5007060036050400c031108540e0003a104004075241d6030030301813003030303c0c41400307079500c5402e0140480042900f11b400444242e5a1440c6100511404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 494028642 1250 494027392 494027399
    0xa090207110303030c090301050c0a080403050703031803050403050f0604120e01140408010c090b0705060a0b060702030a060c020c010905100e0d0605090109140c18060a23030d09030309060810 84
    0x40c0f015500c501c0541c005a41c42c1e95018042c10300b503c0c0c0040c106140e000c3c00f04a41c01100382c05c0032140781c0054140c0b42040d1100c00c1c81c40c05800074111411400302d04405513640c2c1c401c055105009206a034410710650f05d11001c070b000d040396901c10507100248001c2c8c00c5d00080038000e10a94080c07004c0141417400c0d0070580030416801c0d1641e070154100408a175110f58070110b030160030003080030051040b03c01840c64041c0c01d0702d03841e0f21200c001c0c051400c240c0e1211898112503a0700070540390243d80003000d5480c02c07811407404900404130304940c00054006d04a43d41007541c080c121440807104058070f4a00c00d0145440e0480d101003441c0b000d1a408400d41320080c0204a00f84642482600001c00000e803150303003400c0904074240c0f200b04503103040d48401c041c00140c0e102d14040c0d00080312003082e02420303034859500046901e21160000c04011802005e55040322031030310b0304008440000d4040d5440e480601c54215000c40c41d50101030007040c038800041000c1e07880b0386d24155001c0090901640c601d42c6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 494029892 1250 494028642 494028649
    0x2012a150f1803032d0c03020c03033405030415180503030402090606030c1204021f0e0a0506030708011202040216150e061009020c03040801050f010806010e01050a09020711 76
    0x2d500c44201180d200b00003003410035403d40326080302c1294811850886003041e81c07100521015007440d4400140d05c0d01c0038400d095000790143d80144900500360382c0c6903d01030122400450301d000800c1e090307003460f059491300020004040f220070784040d61500e1031952203440b2fa0300085000700d00c3c1403105542d080880203005450542d0450030380300e04003656490034140100446001d0240ca00c9100f10070230014407044e544034004507400c0602002d03419940d0340d074074000104a0000c002c84140d1120546540030711aa03404a84a0711002044038900c0c14191600c05000c4c1c47d002c00c45060340400c00c80f05c018800da00300400c030b00103114402000940b90800c0c1c83c602d81c400c00510740c401c07a840200100080200140ba0207a83c0b00c0c901490000e003440c0ca08640c1816680341180b01e0b00f1041640003070320105a007001d0007200d0241c0380000081c425810140300101c00f10760248100007050080c0e0001140c0c02001280c41412100c1c020004104c031400c18940c8070003035129100c1100c402840b0240000c1c1501c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 494031142 1250 494029892 494029901
    0x20101b0b01060503041b0612180c0f030203011a0d02090408040807060503010801050a0b01082a0408031210082d0d02030c0c04020306031e03040b03040b0402012a150f 73
    0xc0c2e40d90b5240e00c90402d031400d4020703000c0d00e4468503485410010240f013182c3d4000900324641314002c03070101d4080c20f408880348108200e00800342c140707004030070042344201100a42004036403080c0c0c002c210020100f4a0b003003000c1d04000d0200e9000301c450024801624240b00001d0b04503004519541c0340954950700300e85400e480d0750041002c1000030004100c0320f0028840e49511500500e0240b09100c42040020120722008103820140060080e440148015003601400c1e0a00082000d607916a100e400c00ca5480d0408842c8a803404064800101441400a9080e086880000041004061070040d459811140c02d01c00e882d41840303071550a48090041000f0750f0307100000d801071a40d480c11494010704200e9041e4000c2d01440c0104144107a503100094040d040413188520384403c040010030309030551240c0e91000d10720702408404c0c0700a0044405240d400385100340c881d44c003e4030400050038100c2442a040ca000138040088004c0410400d10715907020500c0240e0001d000d6030080340840480303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 494032392 1250 494031142 494031149
    0x1005040b060f0703080106031b0c03080a0f061706250804021804061409010c050d0902060405130203060a0e130b0c090301090c03022107090b1c03030920101b0b01 71
    0x85c42d00310040103040d1b0548207607840e1011082600009819458010f4003600103241d00030100019000000c4800c441684011a50807800030280100c6075900c05841c1c080c41c5d807154044d00d50095078003098009290001c0c0c0b00c403401d0141c0c4000d0740c03045000c400360765521000380103a80041424006090307818130390002a02c103500c16500010200800010081c109d007004001041030303032414185e0641c1503000400c2d1103e5184070040402c00700c4d6640f0100790305028039400307642c01a098403050142d000803a00a944641000d5500da107401d40d4070944d40c2c5100c003054031000a9a50a203400c0400710700d0080186500401c111080d03403510720100003007400c42d140d000c2d0641e050008828280114034011084110f103817885110700070701c41d001241d01340d22104a4031884036500d648000300021900c6046003000d1031340700c2003041c003503016050a01801030500c4110417100c2807000b03101c00d42003107003001c0742410146010340f9403103004001142c151403031000091008981480106000c00069042c100f65018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 494033642 1250 494032392 494032397
    0x5030706021c09170a26091210020f0a0e0406030c03080a031104080304140301020304110d170d1b0221090310051303110d080406091b170709051005040b060f0703 71
    0x341c0d10f60704241d600020035150441d00710f000ba000200301e54111b00c06407066030104503269908020f5000601d403402c17140300840104140041100400000c003000039040064003901e41d403109082c1882007208450307003400300a00300c03081842c06202189403e4090310040d80e0b2400c00007003e400305038400b2025000382e801751030190310001d410710008810748014030440300c05030025411400c00355903840382001d58281e003600031940a114181881868410000c40d40c030b500842c580c2c2c602c030310b003060005040b4100b8014601010103c100b88003d1000401a030b800e15204400040388109405804d81544050640707030741482000403072100c52045115950260441e17104c00c10300d601481c0340c054488002040081c0c81074206040801e456604800001c1e8481e40c448800528881d0701d02d00710000c48001070b506031180d04e400c2d034042107001c1280918803c08041ea4110782d540d5656401c44010380c0c80407186041303002e450072803c108900b000c0d0450350908000500f01400c104060006d1401b60304841002e400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 494034892 1250 494033642 494033653
    0x80d0b1906030c03020403021e180a06030b0717060f0406031403070c0f0e07050d02160c0e0a180816050a03030b090c030601020c130b1002030d0605030706021c0917 72
    0x700d90b0544542081c0000c03a04055090503e10b80000310b1646908a0307290030740c10020000d02030350b66404006000640700100304500c9041034010b0307038014a07a90004841a0101c40041a202c03400f0703000f030f05500301d00751241b904550381d038100f400000c508007641d050700503494403000310000d00d00320002181440d46030000d5440e00e15a08040d00700203030582c042d400c0c02886400611800400300c1c1150b501410b85d0408580e80c045000e0318100904c1000c214511040600100340108007070001e188040b01d048555003211601c8040d001e0044070030741c44001d06030610040c000c1d40040c1070a409800011b14210303950034514119100e8504000207410304500095890a0a840d2403a0004621f50400e039211492800c5190407800030350f40c5c81403040304500c1f904c0c0340b100f9441c41c81c00e6078003c03801c07240d0040e05a618a219104e03005c0e540360465031441c1d80c840e080c0000459103040c0010818200d0705581d00403c42c01e949918400e8070507049800e00f60800a06041c00710b04500a10800c2e40501c400400800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 494036142 1250 494034892 494034899
    0xe0916111e0607050702060d0b061309090215090f213003070906050d0f020c0d0e0d020f12010b04020708040801051f1502100f0615110a080d0b19 64
    0xb810160003d01031414080144003c00260304c80000b44c6803207054454000800180c5880000c03075038012441204068200e160000c180d1280f503400005d0750030300c01d40d610414101c00c0030040906000e030680080d0490301c0c07910000070034500840e5014071030110f0380098218244040400d4141244510080e0b13050003c102c02d1076400c01805c01400415440501c5070741941041040100000c0051041004100000c2506c0d4000002c0b90f000303d80c02c40c03500000f155100100900c0342c3d1030303007100c0701040085100350380d4002d118104031450500d0258028040609070311080200003080c4042c4640568641d40d95400440649562008056141c043c031140364030b03a0715018401e82510801011402943c5048102c110000319201000b001d9030b1041d48414800c3c850003a0803480c0c1410b2010b0224003904241000305811050792104094901501036101da030401c1324400e0301c0412410080030150303840b41081c034004c96414400380100090105020500006081c0044c403a066841000040048a0074040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 494037392 1250 494036142 494036203
    0x60403090810020c070501050729070e0405090a0b0702030706090b0a1119030f02070629060408030d18020904060c0e0a050d080903030f0409060602010506010e091611 73
    0x1100000042d0a0a51620441800f0a0344884080c032a03281486800300341102042520040c92600b400719501d000c000d02d045034a1151044c00c05d40c0c40d0408100d0329207440ca81130400d401000d1040303803c00c6c010120710300b2a40d9025412480103180504501050012400240060269101090043c8141180707030404800b00e4007290b2040078011b401907010454010301c1a65040183e0569049040c00950400304100d00c1000c0e1007044001026a86003607214440f0101c1c228603070721500d518400c10445002d41c030f001e0100030700c21805000440e500600244d0080007a030b8200302c02c06109095004a404419404501c1074001075a0840307007141c8422280e0500c81d480a02c1c107014000440f11807601c03a19080c00300d980c0c9400c042018010750303000503403035100c3e40341082181c0010300344400f0340e5590780d0ba440702180145103074002c400c01542010081080e56100d807900b0012514018889481030b03e9001c40e1009196800d0148000e00c901004940000901031102d40c11191001c1040c0c04d081c000b202c81d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 494038642 1250 494037392 494037403
    0xa1a1e10081f050d020f13020c060907060201061a0c1c020318030c01050714010b0907022803081302030a140106061e0507031110180501150b030a0216050604030908 72
    0x1846031810002004000d503039134400c4d40d00e042c190180c818080d501c110030081400030045a5000781030ba030000540f10500b03d0300040b2203210b9440d07042540e203503e8aa204c22030a8a51612481a00c46d462003100c032a0210480001c207941000320b811152100800240380034032a840402400250700701040c1c9500074039047e10180000c5100702c025102d07491990b00042c085020b03408002d4034501c01d002e01c007600c00c0030942c401d086400d40201040502d01c0c00d4280290746501c009400034030380c040c24400005051130b0203055040968180c8420980f5500c26044840400b03c4000581c1c4c584580d26a0340b0215805648403c03440c0c40c0f803030000c00c8183c20700202410311041c039080c03104820b860113284000c0c2a800029100c1030b60703161901003280c400c2c11080074075003880c02040b030360250b00d001281c03007585ea001e5441e1020380c0e2240009014003480e02c0840104200d00d03201f0b040d90b500d03080001a181481542c01421940e040c01910301c69200d054841c1c0c0d1800c2c01c116003c5002c40c403200380500040d60304100c0e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 494039892 1250 494038642 494038681
    0x60807170a0b011826071d040309081902060f070605040309150206130803100b0a03020a030b0d02010e04110d090b040b0121231c080a1a1e1008 63
    0x4c512000900d8003114210780700922a0031854420703040100340618505019040c0202418054200765050000300700c0c2158a058508501003105a14006450400464501254400d082c00c101c02c20003180c0a00a0039882484084c1c0c40140c2004182d0000780b00d80729040c040c07070103607454200c10341c00d140341c424041596441000030340d4440f5082048004001c004500303626800155240c480d150052415900c2c1c11540003c3c01a09000c10a070903070035416400781401d560743e513038180300700019030051008001c080000640000c0d00421034201c2070602d42c00c01c14121400703407401843c104090701c425040752035500080340c0002040c1c0500c030a1200541c0b0340c602402001c2410703845110710500c608000f0a100000030180400d400c0180400d041404400054210f001d00f40c0b030510141d6070a45c48140004407024001c91032220100c1d03000ca00f036100e2801c010362840200385c4542c0b0514200501c180e25108051b0a10030000c17a84107260700d03811883d1f409500b66131550305250900c07004e14280d0940c0240c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 494041142 1250 494039892 494039927
    0x41406090c100c0c050f0f0303040602060603010b01030c02101d070b13050301020906120c160807170903030403030528050319140103060504030c02040e0d020f0102040b04060807170a0b01 82
    0x10f481c0c400304286101d0103003150002c591903040c903403034003000c0742d00c29640411030303541030002140000d10030340c020841520a00044008008040106005404031065a44081d00607800040f407804a0f90550b84206a030184182c90746c4070801240a1880c03603c000c41e0400d2481d0071020840615116000c08000050301044000354240303c41400401c0141c050b8417134100344503059201252001412a04690000e01003035008003070141c85007418a0942d00a1801301c03a8002041080034103d194a81514902c4070002c01035407500d0724549007140c0c69040000705203000d2480e154401d01000008200060714032a42d103e454032481c1c010f40000c0144106082c0c3c440340360404070b000d031141c515400a03074103595000600080f26144c0c3d0030212070071281d200009400a24003e04a0040c1300c0009941e204d003102c5608680c2101050704180d0700381d008604c41c4407102001800107000c40ca000e10301d0154003801514240340e01d8620b203c61039540c0181076403800701c00381e03955251030844e59020000710300b03100000c0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 494042392 1250 494041142 494041157
    0x615140118060221070f03031e0603030e060c0c060c1c0f211401080318011d0108091f0203062b0602130b0f190c0b0f041406090c10 58
    0x442c0a5107524526012460b130344840c8484904a9850100b5500105d422030006108564031b8600a8001d00d002a002c410105c020302c00f484202030140500801d80383e259480b9040c2d026400203014064010785003d113010f0040340100305142d20b401c03000d006050b0b1a2030050002100711461000b0fa0791444104100f0050b02e402c1e6921341036000b0340729112003c40009194403c0c0d414091000c014401c00b80c0c51031000400304000120840004007400705240b40403400110400d8420055031450744107850311034042c441c7c0000a0903136020760916580000000d06460701250410104130803040091514205180d000c01030003280c0c20500940070004081720f22600903041d152b0360402201d0300748a00100002e0f0001350180d2001580d400b10001030540d4042c0503280d0408042e00d00241d007200d42091200d20301d02c507100e8046442041604030042e0812a66001074841d0000d18140100081099850310f0074440b04011010041100390701c981c0c882c0c00030b861081d0682c0d04014014910f13522100420a0b80c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 494043642 1250 494042392 494042399
    0x606080408090d03050c03071b060219080d1113060e01050703021f230f0f100b030411090f041a01180b0409020301060e010e16080a090615140118 64
    0x81c41180c1d070342002221408903000c003500d03040b1040c1c4289a43d10360980000314840e030800c0400300d90407010300781201300c1c1d81c142c9448000403070b035403d151024119491810a00540454502c0e4020202403e90400100300361651003469040c541c400d40c05a01c1e0005501c40c02c111080e031114490b1003a071824600146401183c0d28001d5030388540149400c008213881c41102142d2104d540a80c0380c0700c0e1400100c1021801c80c003041000304a08844480360b40d5541c500252190280030f914510403a2074066440347c00e400c0024800c0b15030802042222610400c070450207165541d0742405205900c0075000421500d8149446240d01e034080c04d88042d11558800148140103240010988d140c0e0410300000d03200207254002000f030700030014007a415528240004c25540c900040c40350580b0340d03400345064240c40741801c0d42010104250103200040748130300410700c48207403900310790381990084202055802104144410012003a880b142c2450103801e03459600c0d58001d84c407100490f09524808004c40d24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 494044892 1250 494043642 494043653
    0x80601030b0c0a0c29060307050a0b03072307060b040c0509040e03130b0c060c0a05070f1109090303071106010f030206090102210d0f0219080a0b04050a09030306060804 74
    0x70702800120b20300c080440e0b180074040c818241c01019540044140101c001c40944805ca900e440802c141c1c1e144100c24000748540c10700003600e00803141c000c1c1c8110045481c00510f60b00a41020b0010006c00074090070105441d00402a002804555480c0c1d46688011500d00903084078501c901c510b005034207140b0140080c0f9044001e54010b040150380129051040c1d10135541141b00300940060658503081d404641d14040f5000391100451034801c4540340d0301e41c03041e49201e034051042c09800140b0708100400c00900785004a030703100c51042d0310400910081000049540804440070100c55202008104040754085201000e243c8400003410031b95041c000d840f0145100740c040640075100c000362840d4a640700b0010700359040c1001c070b41c4404920068640c021507a0203418101e0405081042a1001e42c191388201c07002190340e510815a42c0100250035203803034400828100d0040d582d04128040c5468501400d0b100c1e992907440015491304500e03015003182c0c07054001d00d040100030020040000d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 494046142 1250 494044892 494044913
    0x1005090a0902010c0602090d0f050106090c180b0a12140405010b0612310c03050c01051206041e0c0201020301180902030a14030412030c021f0923040603031808060103 73
    0x290440b0317026039150200e0002c00d100f846030311001410448060054401d005065200c3c03001d4924005c81408400005803080360f8161108101602a140d407200821450561900400b8011114140302170242d98290309141100d03c1d070800309024200d204204000c000080c0301d006109035044828500b13101c03c0c281502c40300d00340284240700401d0501e1088040c4403595a0210366600c880302d410401c15601d02c1d010206401c0b511007101c01d4800e591ba040e64a43c003030410744220703c92252800046940d030104002c09002c2c00100034504003412242100d01c0150360003075899126664002507941e51414009502c0f100c54a01109101d515001e00f000c0180d4000c118500c14a40241c8120700300b0390031244071411441181d10101e00c049600c0300c101c0030160400b003001041c9008407503909100c041c00441c14540340c4603902000c00641c46103014480e4003942e9039050300350005188030500c1c036404080030804a6030103810030340118004c00101c04601e09050f04807406048440c6c00381200d545580d0726186ca00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 494047392 1250 494046142 494046167
    0x408060f0906011d04020d0602071505060103050c03040f0f08040603020a09140307150509100e1e0a0512010f051f060903080a080c0d0c08060103060e01080d1112031005090a090201 79
    0x34200b050201d010741d9609001c035203803c1c0c8c01110031940c036001031800400004503000d52940a90a22001030002d602a21500c1c1c07003654804141882d40da9140d03200170502440d02c504840300b181c42b5100001150422010b031004d04440e4400680da10704002c0003400ca0822035000300d1002d610680c20080030740b00426082d0440340902c0740019040c11403a03007610280075101079950071600c01040c0200f03a81d4044016032200f03401391411815108032104e403800c0060f84030103640d0403200c1c604d4200180c4c10090341d60303001500113400005008924800e0b100503200700766802e1410103004400740a1440c0501c2412008040714100b0000e1185507a96000903401403070414824020440001000700b42940115288100888010000610902d2018040110076109640000e00d4402c0109810b000b0005641c16102d030342d4010500411007a004035649800c81848182da030007059024602e502c4034031b001d1802840b01c0c030009942c807801c150a00080003001445550720506045022340540d03040300d070603500e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 494048642 1250 494047392 494047439
    0x60c0a03030e070801020d0501051e031f11070b0601260a020d0902040905010f0e030a1b0c0509011205010c030c0e13020c0a0b060a0f0b180301060b0408060f090601 72
    0x1072020b80795210300b00062503000745810b5000090001607001c256205505807001200d0746000c02d010003004d40d2410030b0920300300c6c0e050390000d120000c1c0300b01035484c943c407440441800490411100c1c02d101c0e0154100900842c0c019544500b440300340d40c0c0010701462a90b640800342c2d510045100b00c90b240d00c000181075111503590008051001c440b5941004a10a40290046c042503a451030124000c1000800808496140050240b0789480110440301c0440540c0d03140000544440b91542d03214503100022250030f10003800024103916070341001802028043c90a000044c1c2038104a406d4079814159071041620b441d020004498000308000c08594080e111030807001c4680c85142c00a106007801c4540b144a00241c100420880c2e220f22482440190351258440d41c0c1c400d0a041d00001c2c0b8000c10140010034098028904400000100c110a00800104443c0e6880c58000d030141e01580050f00581c0100c800c00c1100310a00e0f86030b41d00b00140c9001466990303d002100307008800486000b818 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 494049892 1250 494048642 494048651
    0xc0302150903062404052703090604140a081911010503070c030e0d150b040f02040e220f1406132102031309060609090b1818060f0a0b060c0a0303 64
    0x541070392503561003a425401905c2040b40b4204146050242c40e00d407407002024503504418608031080c0402600c491360001380c8480c0c1000d04103085407030181c0560003415000150380000240c0c0307010800050800582240844000181505080c0b400074400b0741c0c0c80d07060040800520003210752080c1009219070701442c20084018014000440d180c440000140800e0200b510f6020151940c0d808107403491000c65040054410001c0607070141d003c5d51103485064080100000c0d4018911117486120584100c0b6802d40d0300b4043e550340106161020099411401d00c0a41c017000c01c0b000c0100d01d03084882d044811560420564031082c0500d00340258600308659101c00ec24507034001c10594840d038000c00320b26149561144940c00003031000748180d10010f08100710000303203424030f88034006901e84064408202e944482082181120000d01029054003101095070300b91101030004034041c5003d80d0820f081030410861403010345118200b1144030301410420b07a0030030440062910f800592608010a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 494051142 1250 494049892 494049931
    0x6110316030512091f11090423040804030213200d02070c080a0204052208090d08070c0305010b030d1b020406030503030c0c01050106030c0507031103160c030215090306 74
    0x6560303014001007003484006090510290340d5010171440358801020007040d0300c0c240391072905401d0b105c1405050301420001c210000540c241504904000c1c10000419028020740d102e0b80f60782d00408480a0710400c0d000b250500440c540548604110050303042c00b40440030303110300e4103901d0040790701c1900c1c840d0300e000031103a5161200d90180c0760802c0d001191080c40d60f50350098a602c50700c0201302207100e03610f0840001c0340c44607001c521008031480c1000c60b0b000480b5542c0c900200d98050840c1c4c0380d0042d0b44000880004851400400040d407040781c440441034514540700c0d003510310440b94507109802c01e041c01201154882c001c40f6000c9014500f140c4040d0340c2d400840c00a10054202819030300000042200010b00749005003820f4088500070801c0d6a41d65030210b080f80c2d00311080e9800500200100c5002c40d201d0301c009001a160b04081c0c07407400302081c11200b083d01240300c0458511300708250400961801d0030044418241001145180a02d113100098480c4d030020040402c400306082c065 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 494052392 1250 494051142 494051147
    0x6091e1b0109150207092a050d0204090f021c020405030c13060902120f011e180f181e0c0e09010b0603041406070e15090607150c090611031603 63
    0x400508034803c1980c80d440380c442d802134544146001d0700d10440c0c00e2030814441c03024440c005206011000192001c0346140c81403c07581507114005d040ba005409000100b189100c0d4403c4481800d4040d80043e51780414000d40c041c140c00b48641601c1c203d03c10700041125807400301e9a0f411100045848031307044c014521040000701865004040c40d50710214400740300180c1c0450f0300c1c1c091072000c40c800000d81c1e82c0d00c03101c082060400c0c41da07004260051034200312401d00c01b030280b210031030703940c0d40403642002d01c803400403c481008882640c4860440503100c03e1000b0b440300100e1065401140b4504c0d8a0243c4139099038080901c190703080c84251100141c040102984440b1007900002c204c90b41d0f03070910b4101030410541c1c3c0c030301c1d0b807029015410205100c0b6004460b0168004c030098090752070903030a84c02d41c40041d003024281b44e800c20410000000011140404c0c0050000c105500040e6601056070040000700c45401c80001c0c08a52203916010000c000241c9000b0b000301000d40200c0241840d04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 494053642 1250 494052392 494052407
    0x90e010e01020406200d090e0a141005042007021c06020f090f1215070c0c171207030c1b12060902011112180d0b040506091e1b01 57
    0xc8918079480441c2c0410306503413001550b01503aa0400ba5141400200b5042e2603c40c0c003107101e403101050418208000a00031b11803134035403040c0d03002c0300040c00b0808101229031481c001c03039400c0c2c44201c04440070305c040d10b49407262220002c0c100d44822100811070341f0581b140d00c58614064426804a44030815070311440002c4d60102d03074044015500c030055105002d0303007600034460040c0302d6441d00c0d074002007074100880d246059540c52001800b020b81031414486400e00e01a11501c1002070305c00c1d440020a458101030001420f1810a054010890034403c41c1414003003500410346400030400300300860780c0403007100b540b2900035aa0482051105444404071a05540b0048103910044400400d104056022035400b50007078071621082c5490701c402c4c64950f8401c131014101d40900f4004108464500c070040d10a55030081c1400a4a2060b0340ba51010561300b107400301ca065000303c0400491000030702440194401054500c400000d070303c1c0c03c1c0c41c0c40d116030b0071011540c40144140c0c1e08260b0b224541c0c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 494054892 1250 494053642 494053661
    0x181b080f160509062d030708100e01090201050d0e030405280806101707090504080d15050a030305130f0603060e1b0a0807030f23130c090e01 62
    0xc8400341a404024140c80d004032a4944030204058000041c4908101801c244125001080b44840202c00540100f082d41d03110342200c603000c510b10040102d51810000d15000d4115207004080b96907000740c0700d900707550303036a540744031241d05244041c0e0060341c000741a503104880303482012031010803000c1158030707600a039405543d0040301e0308250a06640120404a94611141081d881e42c680720300c071041e03941e00180d410074440401000200700802d000c6158070030759222182a00d90440e42e41040308241c0354182d03410794402c3e00004e01051700b80302d24468030441829503112901090310300300000d051b2291f40c2c400501408000900a0441e00085c042c401c0600140d4084040c90360f200c2800038010f040354011252040c070707102c0220b90784c0341080d00400c032103286e12840c0500d000a00702044900c1c80001d80b5070000d058807803184980d2004540501c0c0c2400e07200007000d01541004641544202d40c01410010208041201150202d08001445d030281d8041440104030020070014030b6005045580 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 494056142 1250 494054892 494054909
    0x5070504030213110702011b0c1410030b030d0e15210a0c120209120d0503070f052a12030421080f060f0a09060807060f05040b04090c1e02150901181b 66
    0x27903022861410500509843c1417041c0e80000c4609010b02c07040e421034103c08440d50f41a0b0045c40724481c4184240b5000b04074803009000c02210440040710358100750005541581882005000c59000405940080354020320b1401c06103e10610701002a02000180c0c901548aa80005117034070143c4459204200042c50001290780a10300360b003006007150403d542c2c600c0080c0c0c4480c00441558841d40c1030382e044031441d02d0101e4100c0d404200906102c407002c095614280202c5948004440c04032000d58130650254860740703241090180c045038101c1c2c1030410305045c00909001e2200780306000f0b00d120350000f415113a000103032041500040d65440c40d51301107201141071109c0480d00c42d40200e82c4104840740b640390a41d81c40064a410b4500340074901405880000070b010400002080ea04000b140404500305042d280102d15000c03e003440c0b00300d00000140c7d02c241c0304c0c2005984107500b801d9001c2401802040303540400640e401c2d4982840402404c848407580f11158981c1c841c4403002e0041910380f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 494057392 1250 494056142 494056163
    0x1608101404062309130201020c190e04050706031b0804020f030c03010f060806130f12030f090b191512291803040f120c0905070504030213110702011b 66
    0xb030042103e240c00c5180c5004010600c0820030808000fa40e154110398140c0103403240b1000c00052040c0140015483c40464004000002d0403158044005000e94021806001201d0038a02c018081c1d030005030a003420400740c051101651603000401a070060b0341250740000340b005400000f450100b005034903640c50b51815100703070400780c07869000c14100c0d04883c054422030307925850090b07a4a040b40310040c021001e0041c0b217200003590b500c81d640d00f00815040001c1e03000c1c801143c80b07041f40c402c08422501548030300d0501044000d0801100910032102d40280000f05500d00c503140040c081d849028102d4110f58070701e03410402d241031650142403444d40100d00c0c406c0b19030030028502d001a554410640740103444060302c041c0120895050b65445012a05c9103880c1045005800c03406005c06c0c0e5110a1f010b50100b4030344030070b00407540a440a542c840d903c40d4190300400041004014840c60301d1860089041c075000a90016141070300c0d02401c2031400400346401d1850040c502060040a24240 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 494058642 1250 494057392 494057429
    0xb0a06050903060906070203070b0912030c0418090c180207151b030c020d3c021204080604020d170a02070303110c03070b03070908030d05160810140406 67
    0x444040e01c1046011801c5855079195130140c6a2030340c0c020355007000140c10411100022407038070782c24250400b0310360301144c1c440c9002c0c407002c1000307410543d054905090000b60410030704071281030200c0450306402c4100540c0e0415600c52051030414401c400044000c5d004c11040c42c122a070540c0c8501d50804580590900c4228644008240350055030741d101101c0414800304900c2480b540d12280502e4009041c2100070420a031500d101c85241c1c103081c40003e01d2440f0410316021305403002c411300891075400324508241c012f0300340700080124030b40f4040c1c01e0104200342d0b0710020390030750030680542d6119403440040c100100407600004114143c4100001c024024a900280b0381c4101ca0095840d41c00e20414074a2094030307100350706003042e8150701c0b4444c2405162002d000446c0c020300641815122550380300040d9045801112100c0c411690314410461100c072410703004003141c0c5007440d01031402e00d00f0341ca072140c905246018842d8080d1101c1103480343c5845a510181c094040d5183c1400c00780030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 494059892 1250 494058642 494058647
    0xd02101a0d060f0c05180910150305040308090c06040b03090703050706050405030d14070303110c0709060510030501030b01060804020d0c080a110306011a030c040f060809120906030a0c030b0a06 85
    0x40540c03204141502d1300030000340c81803181080c0ea00301c500c445400c40041e002d40041000645002d4104180034029880000c1c442d1924040c00603104141d8030301081903d0a801c014040c1c20f40241b00c1d28031078100a00e5940180d481008440680eaa0709442640b030340c0ba40c800451070944141c200a01c18460703444041222600b00300600102c5070118210f891010b1072040c02c6545041810746041c0c1d4030014000d850001e4000d810194000903080100c034140400c0510052902000d544814002642c420b0107001c2410001040e0414150506050100354510398034003030034a405204500030042a5000300d41103580700015500555004030b0840d02150b16480e521b030b16621a0b0030300b00c0d8004c04104030310b000b908004c035240303040b41d50131112949003664541007000c103a4001030036020740410030880400c44206004400c03001d003420395640c00320381c44e01c603403000e00c0c2c0f0310301e5505020450818000d170141c40d030b14001101d50101e0b101a003c41c0b030a41c019000d070301911440005580c444101c0b40c01084090f03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 494061142 1250 494059892 494059901
    0x3050c1e0615010309020105090f280503060112020d1b050613050f010f0801090902010c050a080c150f0105010507150608063103051b071410020d02101a0d06 69
    0x1854000350460b9200418019822144103100090201300144806501c0d450443c0349850031440180400e0b569103645880000703a03506500320600014250340061141d42020086640540325940c8074401f0381030749400041041644410080024802d0340300c0000307140080e48844001c0801403ca191115014145203004c28250b00807540100003403801a1041e62080c110b490180aa58031440310b541d003030400307141c00780c25110341c02d078144004100814009001007280b989014040c094854482000d44003c3c1d00741800d4500b11103644c10000c0a0040c15825594001d04641003401d10503070f00c500620b0710f41c1c026600741c240d07281c2c00d0b4a48a4002401d01011606070720850301c08045410004440442d500e400000500c0821250044a0390200282c010402850794030401e2480c4580a1500c03010645403c0180d00007440c1d400d144909440301e41028942d42961080700c1c0054940705c940e1485c02541c59000c00c101003016a268603408a080007002d04071042030302e010784a0001601a42010300290 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 494062392 1250 494061142 494061151
    0xd09060b0414070f0f200c04060f0b2703060a05010e0a0c020c04090201020a050313030605010b030411040b060c0d05030402100e0d150b221a01050703050c1e06 70
    0x55003020700c0c80e4401d581e4940143d2040e185911510f00a104282003100d8003002e0b25548000e0052a000380356079180546103c007170401060009140b905412014131042d00c0d41940700c81980129400107100c0c2540140a852100348200070485c19003424910a20610348035001c40313078150040505202d428255604403505030b8040c080c280d50240c980580810480e400c40030001c0c0140c100c01c01c0492245843c2c0c01c6031502c640144110340a611050315050f007154080b4040400c05032551008004110300c5028081c014407600400c7ca00318034154403903035540201019110301c0340341da48000c22091baa0b05030a942901482d5030841d206c2100c0040050700c00c2d40103840076489940400c045441251041d0400350800d034000e41402d4941060340d54620240d03041d400800d2100b42c4411440c80c0f030b41c861001d0310400380040e004005507200103200e907034100d40f50518502c04100d0101c2c5001d1042c3d030441c04443e4200c0e40341c580b15a64020700420f8600f030048012024000701e019003140100c000000580030301a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 494063642 1250 494062392 494062399
    0x1203120606030601091205071a0a020c100c0303020310030c06390b13120504031115090d06110403051e15460b040618110d09060b 57
    0x903459810810441d80002c0b00c03a0781c00200c107041d06109040712241640c8034148105d0403149142c0c0c8a040002c0001c1c0030301d02d2240341c0400800c01c1c0311034070390400000004100544040c0440441c081004000544065014090540000203d0300001000070749000640c0c201e0107403008a80c58110041c042555401c02c01e42643d20305400750901510404800194040b0100466032211555039103e0041001020300d4841d040b40b65803400440d401481c0c1106c040c01a0340c6003640c7d42d0861030112060040786c942c441c0588041006107911b60b04410440d55000012202c80c041110315140020207030075040c03400d070903212000c100082001000514181032845034244c4501003042c540c0c95540d102e111645007201d00749040046032044c0d00d94021018950404212500000c031007000c4402000340e4210300c0ca4030030510440020781d5503002d03c100300065904a600b4001e00d80fa24405040c0405441c4010604544d0703005580503450032003040b00c24101ca00f6006011101c05403c105000700307041c0d00c51350b00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 494064748 1106 494063642 494063677
    0x5090106140f0d0b120604230a0609200909070b07020f100809281104020909041a0c040e0420060708031f03051c0e1203 53
    0x2103c160340c000b02c2c0b00418a414084000c40d8070a42c0c1c02e640c0c01c09400d00c0001600310030340305000c15039008a110800400000541000300c4a94020703c1c80386800701c00f8003044a06c1800300d601c401007c60f040d511601c42002c2c07103142c072811190640c0c1c9410a440500c0308080301809403c1c443e0001d080d1440c0d000084000c219914407a1200784045201c040800002c18810044036244082200c1401c91a10060180601010f21003038000c210700400040490301e6140c2e541560300001d80109600a02c0c01c09040c204421112000e48c0d456080301040002c1820308074004441c1221032a09180c2d002d5070321503d03146952a176080c0345818074030340e080801405a0341d000280052602840456a403030518859809241c40741150001c13280c2400340007000418404110081050160034503100c0c060508401141d2010718440e90740c1c1d00c44c9140e446000304c05030010144c81c00c201402845c0e00f = true := by decide +kernel

theorem cover : BRFrame.Cov 493884892 494064748 := by
  have h0 := BRFrame.cov_init 493884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 493884892 ≤ n) (h2 : n < 494064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
