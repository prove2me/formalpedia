-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3685
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:23:09.887231+00:00
-- url     : https://prove2.me/submissions/20cd75b8-437f-4147-b784-207558b215aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 662589928 ≤ n < 662769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 662591178 1250 662589928 662589937
    0xd0b04060b07051018081b0610090606140706020f04031a16050a08011e0b0705010f24060c0303110a030c09060f2c090106030b0a050919150515 63
    0x11020750303418102030584c80c4c0c2100d04010300103c018031180c03400030114102c2c2c002044111620320360f41c0e254410400d0454540b02054842c50000c440c000c104000079202403080c2409000c6030710340030300515650491168a0300400f140a8071842c1d00107400807038111444216401154004003030405108411300e5100042e004503513801000301c07040c45251661303100b0411260a41c0d02c948941d6056420089120036445203544402e0451041400c080b071950303040000f40809912500010500020080360700b0141d42074a05500803040d200c0c50420b1082c2d1403516100146e03140ca1820504401690508070090801d203010354501c0c07200000d807a04040d90541205030b070009103850791451180c4c1c80e9421110700380300250b9000041d131417020f046e201e2030019100640d800d90982a0054100034030000682504003030b40840301096441d40074070700c03d04003810450000c050443c0d40111601c0e02038800022080c01048881d4074995640140720452031003907041001c0c00010301300801d9821861502c40c540e0b8007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 662592428 1250 662591178 662591183
    0xb031f120327031203052707080c030a0210030c030204030206160b07052706040806090f0106060c0201090608060a090203180c0d050a0b0408040801021603030b030c03120d0b04060b07 80
    0x40202540e150302d004241c1400316076110610a800940002c3c04030300a0a02501c4103048201480c01e10f0b411040011001100c112008054510035180c0368006142216640203d070003500700000101c051b80e110002603041301503a0902141403124003800b00c000b445540c2009600c00e0000c2a410b0034140310030403c41080f44114514006925100403e64080c0102c03009020002041c1e0b108030400b2200b51503d0060200141481c3c1c10283c84807056030501400311045a2981d000d01c10040645509028100081a9038105403601c0d03074581d0002000e21049015800c00d103c10b00010414903110509408000c09003080119102d0401042c81c41c541c0c0748100640c0180e11988420200340d2070060005845540d002008245154803a07580c6545003000500c25180941300b07010004180c00d0138001071100010b401080030a80d01c03149409011909c110031800d0003503001c1c181c10085610005004800080c0c9280e800380c036001082c1152020340941905603070041e00303100000030507140c40e401502c0c4592 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 662593678 1250 662592428 662592467
    0xe1612210e040c0c08031602010212041a0115120b0f0406060305060a05060306090109200c010617160b0f0f07050304030201030608061012030509031f050901060b031f1203 75
    0x1007101800c80b5204c0900303801034000d80d000c001242030794100f14899031405c400ba000140c1030805280e00c550000d00e04a5090720211100c84a9040300c888140340c513400761100303000005980030081340090400c1d440341c00e004106030761000740b030382c191341c40380100c070800c1c2030060080c45101e0329500f00a0150030262000781c0500d0010b5001701d0b4a00c0c0400c1502d12400029005802c16880c106c0110094045140050714401e04210b8000071120700d0402042001045000480c9c00c516003c0341550f0b5150325040d244240e008458030800050b8040807100855020200258440708250310610080c403815030408065880021000100a0048084d204a9000b40ca00300041682c804150b0348803102200c00f00100b0305002d0b010300482c0b07860303001c0b0840c2c0c80c0a4600142420601c6001c68130701044071f03444100c03090203110320072602c400781d0240c2640105050300900c806441c1c100c100303485020280c07030305842000007421a440e038101c003180d49006114180003030240c01070500300a03006003564000b460300003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 662594928 1250 662593678 662593691
    0x1303060f1112040c1d04110904050309120f1f050603030a0915030f06060c2315190510092a0e04200903010e1612210e04 53
    0x3a0aa4412086101c0105107103a203401c10305000485a050010002c80390000c81d5800840c0f915100a407101c500045000d5040c410b050900b440391104c192555414461100c40e02000002100402920b81a11041d20f041455028207910a41082c40c0c100000005201d409000c010700300e07031742c44014802d40000c2c5003001326440b0902459100c0c499079081c0c07808100b0b4503000700000c0b508030018020441280c0340004c1d6102c04003114609a5190307600100001e40e50b01c400320144103041400782850380c00f0640000c100d910050b91152200c42d5118020bd45201c1040081d090b0900a46964118030070200104060701e0941e00e007a15003c82d5008928155103400080314000040c2c4003861610030300a60f10350b0b00008100400c030b802c2a82e8040541d0402d403225102a44001010851040f00c42c0400c50b2a80b540246001c1c14212000d203910407100b82c0c0308402050071081c0759031b1101d084ea81c6407031100340d142e04c2c81d0800c0024045811000c1c1143c0c2569003107001100ea010049666401007264140700c134 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 662596178 1250 662594928 662594951
    0x20907030204170712080f1e09010f030e070501110f060f010e0f0405070b0a1209060605241b0a050708072301020c0f010905040f02072d0b041403130306 67
    0x2950024080c400c1514402c00b80702d800b086c4074078042d110000e8a480158600f507a0803040420740301c03660a0500071008081850f40341583c000c05946009059481c0c02c01035104645500d03940c0341c15038800c0e603050204248045186240c1402024410350a8404550aa0500300b81c0b0f10243c1300244688103101020002040040d241285400d000d680c014009104081c14042004904c0e40302c0b0346802c05202c080c02240381205403a01400403c07d000c1d0000180c1e9503c0d103802e1001010b000d001d9001d9200080c41180703200403040c170546007010f0700b0902d21203007105045203403440e200e12010081d0242c480d50100040d1500005040e00949001c01020356005031041380540482800100701030158000c48401013075800d0008001d000a281450b042146950328804601141d950304045881d03943c001440030107001e40078941840350300580080b241e007403038510002c000c01d9202e000c00508055961001c182840000c0c3c1444103184c0040066036034071310a00c0310b00b440a00f80d41c030048036510f08107844180c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 662597428 1250 662596178 662596183
    0x150b0901090b0c06160e031c030f0b060f030c07050303010b0a020c04090302191b1211010203040e0714090a0603231603090c0f080f0105011a071b0302090703020417 72
    0x601c3e06540c0020182500d48030303007841020700300842400030049031031001d400300e40e41000540a52220440c2403980d0708650000101610b2102409021300f904114841136207803102400c8541591a1045254a07615408443c503042e00c81e080c0050050b03c0040b00100d9508400d1006000c2c1030701a4085503212020b440521040c1c4500f88000340150304150307240342030344281403441c0141c40d01c07955410081609840441490813102c1d00000800340000406804200c4a03124100360f18400340002c605191425485060f0444014440410016880c42c00d11400d840c0c0303006d40d00403010050005441588510740240144040700810002c034103002d010164144403e050540070394640c00088040030300e4505c00340c0240c5030505044802400800300098090303c0c602034039010b4401a8050410003110300300c0c0c0d07401e446c01030304030b080f641c403d500100d02074040c0d100403560140e51090303d800c00014840c2c040900f0808030351003c0d402800403c104408264183d0041c403c0c1c91201c00c141035844180d4000c42c0d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 662598678 1250 662597428 662597437
    0x20d0525051b0114030105100309150617011401060c050127030e0a03021507050313081f110a0309050c0a0b1b010209030c010c020a03050a0b040309080a0c0513150b0901090b 76
    0x1940e01300100b005100d0740c281440b454010105509020417600c030543d895815145144402000180d42c88406104144800c4400040350709903e000348584004a12500541c40c010710451050118030805c11042100039001000024948032400c06a03040d4208407840350116500c040700060f20402c2c50304400c0c0f5001d10182c0c00c1d41d801400306000040c600f0656016507100d150107444910040c00070802600041c09010080d06c4054040d1248130325444036020003514031a02d080f40141015080039201021400f56940034006181c08140c0d5061390604904080f5042105600060b40e004003081c00149000180a03903ca00b07a441c1480508422415080307004402805903d50080b21040c40a503120b9414000158001050038040d01c0d6255181403404002c00070440c1d50010034407c21080c1600f0940c4c4038000d20074880545059074442e594a00f0169080c00354a1088030500307140b0f540404246d000c0b4425428414200d482c0e00d854000e0800c80d074200e0102d40340006c03640c200c04945120510280c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 662599928 1250 662598678 662598707
    0x5090901171b010507060504050318121f09060e0a02010f09030b040b0a060f0617010e0405030a03050901060b0c010b0a0501030c09210204091511040501020d0525051b01 74
    0x2c1404840b41d1050040000c01248028104207051115001040242c0b0444d4002c0c0d20410007550307614000907843d5000708403d0105446007c914605046407040840c10010709056403c04000d0101d00400b0107000709071204016201700e01c0c180900b0b00d1201e0008e1441c0100d4001d0b00c0d200c4443d64031740400c94880c0b8140c0001803007100d170751b000b190005587c400b0719074102d61182e6021401688441c9686c1e80c00f10710b40e01040006440d02c1c2051031100c00e04d0401405408070107043c00c140d2419880b5660349100d141e201c1c40c00c143d600c5000800c52103081d4040300141c4000100d4030782d80d0110b440d4450103001c000714401e110301c105030000129903020340700f035900c00300480d200c43d10210b10300360022460300300b906481840031f1281d5000d10016a40ca00c1143c0e10984201030319010480e220030142e0032a070003801d0540d00101d040005000310784e0002912007101805141031690f50000303005105450310f102c104103d007100ca2403c105e04001c004141414440c41ca007190341c1e046c8102c20011554051205201c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 662601178 1250 662599928 662599933
    0x9022d090105150901050904060305031603140a0c0b062b0302070902030f060112020c03070614070c050c0607210203120702190308070e09090f0c0301051509090a080a0509090117 78
    0x2d041c44d0b50041e001340000100092000170026640e803107040c203652001840075880603103d1461020903801c11860101c54044071801030400e000d0403400303001e14500d01400741c84c2203d4413001070b4481d5a01c0c81030b208241003040d003495074503000307000341040f8100c100c00272000f40c0212903001c1141221442542d00c43c4841115412094480100649111142440c14a80c9a808000d0000282c41c10030042c40b10a120710b400291a107506040b80c15031000c0a0310003000c1050844950021074000541f9511200040f0b4155a03600c0760f502c1c0003001c0b164400251003006900045d24081d55030023202501070701042c1c0b03051810f6a62811003c0b80c50350820f090f43c00c600c182844121f0f011070311035103090740e2142c002e0500005045280300001c205140403110040300c0d5002601604000c03106101100c05108c00f500288102c0c140030805000007403103000f00c140514200f038009038801000b0440020100c2d08540b14981c2c8101e1814002c013198402d00860340901201e0000041c0c01032800c00009108604d03030003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 662602428 1250 662601178 662601187
    0x31f0c0810060f140a1d0f180c0403020a03050a03090e0c03190b09090a0c0603090b0406021e120105041404020d1101030204080111071203091509022d09010515 70
    0x2801d0b280040c03098055070404c043ca062180308900c2c4c0d24000e0441007070684901e080c9680c981d041d01041400030752080c0c06080346d50405299501c0d032040080c0f02103c3d0700d502c61110350340c0051030441800b41e41e00c0a584289081c10000600c080420945a10342c02a038924103080c0c1c565524500741c04060301c240c2114001000002c045190700c0c01150741c22000d600000c140a00380c0e01c00640d48080503a0303c1c104d039800a40c1d00f9000c0014001d0400c008000c07504050080780c4042d10340303500b0540d005001600081d00060450f1003c480700c0480c40701c40ea000d940841c0c56200044030b582c0286003d008c2d01d8015807826035a0b854107121242400e12072a4001c3c02c008140c401a5101c0c801000306150032810300d9020300002c240d00300203010701c5045402d40381465858244600b80000450703031000119040c07500c0d040b0b0450203da081041d86000c036500020100301c5240c14404550101421a841080046100c0e0007003003420f1540035002d01000c0488518040380d0325002000a410280702c025101c1800401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 662603678 1250 662602428 662602439
    0x120109080d0e101a0102010c140703030b030a0c061101050c0906250804120309051c1e0f0605060f0915040b271009090209130f02031f0c0810 62
    0x40084500d00d12030b800b6941e00c68801400319007903030524641000700d40c10a249010003560709100702d05100c40c0038a801c16072a80000c51000710780c40345041c06800c01d6103803d0f80b40100d0300c0030081d0b002c40b15070154020140030340d148030081c100100c04400c01c0c000d508140c040327005041d2010a640d205c02005025900d441c6c1c0c0c101c6401c4d410071124500072a8185414030600104000001a10040c8141030b500c0d16005000d240040180d8016009039116421140d904040405403040ca101c0071540000600c15004a1203050040030318103040041144418500200030851990003150045209881200641c0e40b91010040c2c01d107411542020b2420101c80f8040d80740c64103030030003100ba090180c40e80100f40754201c0d403031889407003407c0f9890f1110401410310004d1042080f80c00c00070701c1c80f21810001580564000b43c400322002e070900c210900c03107034040010b10280b40da00d00e00e603d60050845100c4905140d207c614542c1c0d6080500403185800c0c80c0d9802c030f9002d1240148100d210006091001d130805 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 662604928 1250 662603678 662603681
    0x3060703180f030e0415030519080d060305212107031103090a020108010b0309030d020f0921070f1208031b0a0e0a0f061b02120709060302120109080d 66
    0x20840c07814070300907100580400d4010100d0400c9900135a96004032901d4a4240026a90110b1a41e4081804400100042880401c034903401200345110030314100c0b550700b4000518020100c8102c082403400d10004100400000c6002e0460206645501540704100c10403100b07005030303001100103080382007980801d0324041480c50b0b44103074036080010b01404001400c010307a8104640640c8660722880b40c4400350341e0420341c2c050043c403040702001c2c514500086e0840c2c40e0300a059146542d00c0d000304410100140394000c2d00c080760006422041c3d050030507070690f5030781d580801c0000741e01d014043c004100ea40751105948151086000c04c000c0519465030340c0721256000400504120000800c0810a003008000804c03c0200a80e6104600101c0c5420489800101c0d40420346c0280c441d20208446501318020b581c0c010454102503200404500220702074841c02e031407002503801100320220302075076103612035800d4030700a5402500d504aa440b00e18202c810010300030304950401d000c405045040d9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 662606178 1250 662604928 662604941
    0x901091107060b011124010e061518060a121109010507020603190513060c1805041a0307151115160c02032e091e0503040b03101502010b03060703 64
    0x61500c41c02034814103407179505000c00811000d081414100d000b520a02440004c3c2d40501070003000801e540c00d0010015414841d2a00700c07021081001c100e0081491664140c2c11003280b025043e80d0ba204403420f00140014031440c0b4241140d80703804c0e02c2070320500141c4240d952044060315120300d008100e03000c2000070342005100721081610a10120300c19000b6010301400384207544c080c8403d40c455072500500751a45150744ea02081220418282c40f04c8c030244070301041307a0003581c00003982c50082d0360749510a031513040300740d07098458090000358601011a421000e29125603e1186080340840c0d819106c0c45070700c98450303890406802003244c9100710180b4455a10301400d142408510340e40c0441e00704803100400c6980c4400f404082c5070b000108402503044041020402c20242c01c0c02c2c2d9a140e03030b0b01054850701d222488900c4035907003002010011900038003000351074145c407454050305003d8004000c0c010f40c266514440240340100d8014000d21045ca9030060203003245030b0b00c20100700c004140c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 662607428 1250 662606178 662606201
    0x3110d0c0b0a1a0604090212010b090607060e031b030316020712081c0905030d0c170a1806090c17070e0a0f060b0c2b02120c150f06090109110706 64
    0x100384000383e1650f10500100003c150142c0d026031203801c03000001244003416070204403075000c10070200301300307a44040403200c400b075111200042d110310541a0f64614040c0185400444100002e03030340300044008040c5110f00c1c40c1040ca4841250303c0c001c00c130b032180218807074001013160701c0f007c890024038900c000c0c14900d02071418a45c000c0081040150640b901d03100155056000040c0300021100540648c0c2c1a000481c101502d070441e140641d5440340100510f07a50740725681d0441a40c458158418460005401040a0009008e9410620780b080300301c0c4525403180030f03030039907405084502180e064111030b00c04201c0c0311680c0d100c0702c9031000340580d4507c1038a096615503003c203510340e1074006407600301d0b9984c00505180c04030724045151400181390101d080a0403205414105500162102048000c005040e8a440c100307080c80f0310b080c070030b01e01c42c4201003200c03400c00420440c07842085220f03c10490301c44c41942d9844c809441224080003040700c2c1d8120030070000010401640000740b0440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 662608678 1250 662607428 662607461
    0x309120a0b070c0c06030203071e030b0d1103010506010804210210021801020606150711040b0d0b07030b1801030b0916092a171801060303110d0c0b0a 66
    0x3080e561144214101101c000001c190006848010b00c01c0012a00001e00010705086186003861318024201d461811010300d000070b03240e2580450742e442500700c004000b00c042c02030100c44082e0b2624806156601203102d000b58a00b000240603584500919801981c21540402143d68100301e0b014a030241003580000b03510030b004804080510510040030220ba03600d000342d1203960341500090900b480a0010703481411100c0c40884410441022102e949030700840c01d00b82c12240c0804107001e0007110a1290348202c14122a40500c1a0344450500c40c1c60240d80820140c020380040141000c18030060480103100e8100500000fa6804060398100364400d00300c98861152910300300450308980c002d40c07080781d02d0780c10310075024411202c42d400c0d01000b10554481c0202c0320800a21a04014004100c41c13218100420341082100d0107400340c4002d80301c0207109441e164280903100310040c1a0380c0e03140d885440c08200c0000d00c50007004203440c0e40f00004101c141c072602c00c0300001d0603141014402c2103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 662609928 1250 662608678 662608693
    0x71b0809090a0603050606150d15170105010e0109110f07141b030f0106080c0603040212060411130c140c03090306010e04140d0c021905090a060f0506090102030912 72
    0x603a11011501e100b50850b880124685055140050802c0c402806560040366400303609801983d10300182c40180c0c410803000145a804a0340740e20924060b81d20804a11210f10b49829001c001074020030b059440d03c0000b0991a41d8811900c170031924600c010700c0c03010343c0c14004900103190100c0204401c500a5801d070004941c3c240707040d4185400d040301c0103100b00e0300c82482242c0e410244100000070101000801040b45484d8842e901c42e1060806030344202d40000c0028110b60341c4290035008113456004503456450b21b403410281501b00c03800340512030840440c020072a14224024810503030101d556260048807074212004a0b500300c01e040400c940000d08c11450b8a890402c8454000c00d2100c010348900d05083c101500c490744000072507613460b004482108206508800c1071907180d42d040c0d408800c42640e41c400c20a041c85030b6040303140c0c040c49003418800c04400a0b0020010f460383c4004400c4810387d034034200f003100c1c4100c00100d0301580090001c041580350540c0a904600d045000350b4640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 662611178 1250 662609928 662609947
    0x3090506130b0c01060512030c0a0609030c050a0b07080c0702061c020d02131505250503040f06200304050109030807021306060f0806030c0916090f2c071b08 69
    0x81e5080300054554070385d5510820880d40c5000080c100a06800501a40c075040314510401d4442940050191086803664110000c0501c030782200c82e03550390094155002c01c004c900d000001e5074002d648040c0041d5030b260102ea60320703000f00d00711441290300070301403860440c0b0f003140b004050242d50b0f0440495503080c0982c03d19031046000801000c20138040403150305041202014100291000084c204801070140b20421040310351030411280021a0074408040545041881e5200760740088100e40005800098425040b2094800c1c00c8032680039000044810354840d41c2d64003d0b0f219407030004183d0303281000801d8a06005000d074600203004035521070651945d400545002d0380c40b40000645d11480c01c507840368013140d001e401039000c5000c1d2100c3c600c850002290300702c001e01602c0e1001101c0c1c001240c040d01804001c401413000b0310a410100b540c1d6501152200c03c3e106503035210b0014076109003850341c603142501d407081501e522544d4520b155a5a1024100c1e80140c04803070349a0b00b00a0940c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 662612428 1250 662611178 662611199
    0xc12070212160605010b03010311010c1403120403170c03070e031e031e030103050c01080601052b0c02210f0705060f0a0f05061f0c02060409050109180309050613 71
    0x214548400381c0641c2540b2515028080b41d90517808044641018001400002c3c584007076400406001d283c205140142800c1007944040303548d02d072441502c0300240391011611514402e600c80c0e030007520780d03101135130390303820412504507046520f500c1c5000e042000400e010700445604042c054054125442d60014108400f0a002266080e001d140d1011540c2e0300201c003100f031020a260b9034002c038203045515695905684810a01300203040c815001e0010f0f035140d1007641580c410b100a0b03074000c4842000404a440a04043d0f016881610b0030011021000c034000103013881d495032007001c1a54072005800511805410140d03001c841982e04121080110384100021402240904404032403803c000382c0c04001c9807513680d01065081c0c28541042000c0c0e44a4040f0760458101c0d02e440b0340304840b610800c4400d0501071800a42c061000310300410415401d80c8501d0503540e1052042054403011035039200e20003030440c40280002d0a80b00284021300f083c5c00030b089640c6c00e4a8000d80c00d01c1e141c410009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 662613678 1250 662612428 662612437
    0x31107080408010e0f0703080403020d06020c100605030d050a140304060e06090f071508071d15130f0b0403151d0313060e131a0409080409140c12070212 67
    0x200382d69155110045165800e100c103590f20b6028030010f090b030600c0c5603a41525402948000b034402c00c2d10700140000d0003401d4044841151002007a6a000c6298800c10b50080c0302c0c50103840c1c000e100b0b1040d083c0505024100f01c5a48504a0b00d610440e040e80e1a03944e02e16074030041040f100c054442c0c01c0219502810000700740078115440c05070040105090900e45041c80075880251904080b100c2d03424001c0d0000d014a400520070f03c3c0c84030303607202c1440d07510700c943c40749104454100602c03441e0076030013044240c09801d04e40002c414610b03d8a07945d0491250340f0300140101450030740c2c00c00c010000600c40b501d07080340302c0a80c10320125181ca1280342600400c1c14058510740c2d02c1e040014210482d041e0388924601505103820f0501c111003020303002c43d159030509902004c40c0c6a980f11304964014007805c4036a800c200c020818040c1042c689001c00550300241b0681d1a90390421840d80340f40b0381e98888991048008000031030803c4603207600c240b00c1d514064020b80550040f060402c418114000c001c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 662614928 1250 662613678 662613689
    0x6040e01090c031b030804120c270b09040b06101e173102120a030e1c0302030a0503071e032007020f01050f040902030103111c02030c010311070804 65
    0x1102c0c103030329508040030201c0e1100c071070318401c1c501600d060002541d0345050342c040d2902c54030340194865481c60414208801c42d0441840680c0442c0703200341c010614a0400201c031304034441484841c01810502c000c0810580d00203010110305000030324241444400e40141d0f510310b04d4a000413004013014131780f15130900c0810300006841140e030507000c0b00391920040d41000e00745840460581c8401e8500d60060390724038940720a840d031268090159613a114241802d0000442550b00d5010145000f07445207100d249218024504001490380410a81d0444182c2c65095005180703001070f5550201c1c0d007a0f200901503008e02070000824481c050710885040304001007510000351205903165840c411501d0005000d8101004008504c0141c0f140c000c18915081d00382406920380b40310b05a00106801250040e043e9180f010000005020340f4040c601034590055a2044c0820344492140010400344040039402d68490b0121031495403003075100d01a81d00d034103641c0c542440302903a5411002e0307101d076018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 662616178 1250 662614928 662614943
    0x4081b060403080f04030f0e0a0b04150f090308071b17100e0f1e03190e010f080c191e0903060e070f09050a1b3204090506040e0109 58
    0x8001c10550481d1446802c140d19403d0340d08130345050342c0c006141c0e41e4115010020450210b03115485070f01d548050700003a102c0000c01580301c0d07455091401c071100400c94440d002501c2001c40d01c243c01c4c002d10b120001e1f00d40040c032041c41e205503510755003443c0a0380e9188001c14520380c3e50004070009141c08503501f6140c00710140155004214030002034401c201103110a13900440c2c0d202005d60070000d0f050480c04444072500c1807607000145118110b028080000c031504415020007428154001c0410018503000d032101c4004040e0150100c0d04100300302d4805041510401c801941890380405040c001c980f28030700040440454907186650031000c25a00e000300340f0314032040c41000350902400c1850b41004005141e2300b881c00c0940760580c29144181c000c86595500801c40c00b021070f4005000441c41d128a81410030f0301524001d10707001002d0644041545000c440110f0300c07a02c0c0d1120310042c50260a09800c0c03a00305003c00008007005031469621503945d41215440f00028081d00080328040c3c0760 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 662617428 1250 662616178 662616181
    0x3090712081b032b0f0c02031309050112060207060912180e070507080c250815012402100501030b0f090f100c200303100605090901060804081b06 64
    0x2400c903a22101645010710341d810600c401d503209103402c01e060001d1501801504001c6050044c01d40081c0008030048180380c1c24285c04400c8160004020912010000010010246e0765886041103c50038000c80e0580d26240c0701c0c01c008580705070040c005c104e0180000140d190200c3e43c43d0b401e0180d5454640000c1581c0001c0e55507a48200c0c40c4000043c0050440030240380b9002c140140b880c403030304100800301074000c644100d006030100700381500541c404a240000301c100106a00c1c84c00014450b407240380c4190b40200a0505a00900c2c0e41251110700b05502c031400100c00010103040c07007015110440c0304000f0003208007492402070a0007940100b12818080c20b02050755400c0c030300c3c0107080c1e010551060035080d0b41c2c0e08000074602031103948842c00242e840f0030b000701107461861f01d02404000704141c4002c2d182c00b0001000031030140f840058119050f9a803080e054502d402441403281c1c0c405030040040100030300410345941d21612484440e8a40600001c0807050314460b4203019040340d20010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 662618678 1250 662617428 662617447
    0x8180f06070e0904050604082b020d0b19030201031a0312040509010f030c09020315030115081b060403080d0b100f030c17151c14120f0f0309071208 65
    0x200440b04220003600c2031846407500303071929981c0f01c0c40500020200030780020701040303001c0501d400007000001c444514022040030176242002c2c1d000f00c5c821082403460500c003032007a403404c58100161400c80c525145580362071600151300030450010b90000d00c24416840301c40c030750340034007028040500c4082099215424041030211910050708800d01c0526914418008203603000403040403641102c202694a64880381641d0404881c16413040c1c140d0300700607640142d00d507802a060b083e261624202e0f4940001008550340312829410301c6600688204814000705400318000c021800f0b00740d1000c29401529004070308459007041c20440080c1c0e80301020344a09a01d40150540c0035000e1130300100540c406245030340780300c0000d428801030042c80c407240003440d00c90000c3d4104440c4100d036500c00000c4c20341400d40f0101c0180d04103008500441c080c600b41032120030240e0b0000a41580001c0c20042d0710700341e01480e41c1c4064034030002d034031071410b001907102080303130001d40980c0c461410703243ca40340d694 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 662619928 1250 662618678 662618687
    0xc11060d11031b28140a05030411060f0a08130803090618160504090501110409020d1805030405090903090d08090102160503061504110703170a06050a030308180f0607 73
    0x1600001c5420f2010040021311100450400b4500400d0b40030a1004603107502098aa44c0c9207080b2039801407901040c6610303965008009940720301e0103a2002490004540304008051240488204440409101c20b00c420707485001090780c041040816040c1541054480f40e2840d00206c0b141c031b900b40e1084040003a154900440000341d824078800a10404454441c64014152940100c90055a4440c0400c2c2070180940100104030002000c040da29601d40354190042d60000c05a000264100381e1144505190342446c030303a2903500302c1c000d0b40c1030a0801041281e2490f014004402611043c0000c20085c1d40c2c85030180c0d0301602c1509196070710315000001a007051074001010850024181080116840215039242e010160030021000d0340840e90000d401003101c092024800c0001081c240201a04440000c00d0103404c6550052103030348a000c60342c140c4042d07020b055000307110b4550400003c1e014441c201e03082041001c00c00c807203001d5486500c0c58a21252101c10040d480f0301c0c18002080d401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 662621178 1250 662619928 662619961
    0x315090303160201200f09090709060e0303070b0c092202070b0105010f0f0f0311040b0904050105061908180a212c030a05060703240302010c11060d1103 67
    0x3140000d02040c140d080b0540e511000d03100040c617400c0c40014400258000d05800c441c1803a4000b002800c0504010500405040482c040c04000ca02002e08469007460000241d0f500c2903840f58038168195583c0c034820010b60400081603400c0a4100800c10618100c802d140c102216118001a164031490501c1643c3d40c40691010341032103402001c440050380e0200c8410240c00580c1048800068441e80450041603040d2007a16411004a004642003101c80000c0406801c200c40074070480c0d03201c904000c5079200350b580c0007440e1040744800515481c010741a25500030040d090024184124405182c1001c0c02a182100d07408810340e084064408800740c100c000c1c40403031801c0010b5462011070b1a41c2038501e00c2c072807200c803040e000e08a40c070f95904001c20f110b080d90140680e0907030b041c904401f4010303007808003044c584200f410b5075600081c032419510f281100d405944896052145480d1140130701800c80c0c01e1908230f1070410949044201038000e101482c104820490342d00d01d05403c0e140003d00301e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 662622428 1250 662621178 662621221
    0x12112409030d0f0c110f0a09060801270b060f0405040803040201080f06030a1113060b030123010e0d02182e1401050c1f0204090e0a0b150315090303 65
    0x10820090502a4003103070f1428682d60000020b07a460f003011001032486d21994030203139070140e0103140211710241c8503000300c403c440150009202820000304000807250003940d48420740c0f400134501d200418044039a654000001400090035504500301080a41340e0803038003641c125030004244021541c0c010252540010011601046801c00e0000640c42d1900024094a0b601b00403c0e900155500c5c0b1130513007694558a1003c1100c2591421503050302c0d0800d01c2a40852040710b004546401950301ca01001c12030140d44820450182104101828103842d03800d90700a240606542c407044207130700ca014010314484110600c070381510003c0032000c16032003003c141c0c0e2849074042000707600e203006070000951100b400c0a548a40340c41090074070340416040107110310100c04210000c01d40702c0e80c0c01003060322002c0a0520080c0b101d0f5401c01c2c0c0e102c5004c0e100928461807080040d082c0324542911028894005003a00d0480722064201d400a1030300b03540800458000105100c54444001205d42c0c0000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 662623678 1250 662622428 662622437
    0x1a180607050c0c03211806030411011403010302060415030b1011011503080d110c0a0f030908061b090d150507080f0103120311040312120501090612112409030d 70
    0x180740b00710b24440241404158402c031080425811398000ea10b0000344a1240087c1c1815101d15180c00c00400100500c40c8140c04600200e480d84a0480302c1000c9a05036034003d0205444c252511780c0701c401d843c00c0d400d00c1c60101941c5a154559668032003100020120003035542c00c0e1020301d102010390854155042101e03408540745810000030301d11301c00b0780700030135201d140c0000d06054202c050051442040b40c00f910600914a1010030054955100501c2d02d0003075584106254480814a54a00058800d200a10300900804040700c102c01c3c001c20a00303801820203d0350b40d000e640d460a900d50b00c0d400c8503041d0b80d102e0307040050341d80d801000f483e071004260070b2061142d49140c54030f910f2200c001d0200410580c81760112013140615804036001107510060885d80000740e100003d0003c0400c54044040d10b0030000002191441c502940e419215020a038100d9800c080d40c0d0948907c40c1520895003104010041c2e2403002484801c9150000e018418240c3d2684600105810940b41c14014818030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 662624928 1250 662623678 662623693
    0x20c060705070b0c0c0a080724080f190f0f0f0c0c030807180602010509060f060312030912132c0402010804060914281a180607050c0c03 60
    0x160340000c12400f01d400301092180c0d00c60010024900b007a02c0800d549030002403904001945a800203074500848441c98918402c100d0040000c10944240d4030344d000016000c240030448000c00152842d410803040c07640745012540c1c0d89a50010b07145061584500305e5500d000e5400b80054a00410310580b580000400c90810403c00180c0180c9580002500300507820000500e0309000d62041c01007081500922001591350340c1e40240a418110b500325070701e0180714086a907480404401ea40100801005041d10185080c2c2c0f8802d00c3e040242040300a110300b400c4c0c521b01e100190f0003884100e004008401d00c85041c1182202c0c084190131040d5817080b03030120000503d0601c0c24100350441d60918000b1080e4a071820004060a100c1402030b102c907160107020381e5402000140d0148100707655074180a550080503922150790580c500c080e000e042440d121410b60b8400c51410f07548000045c2c1c04164411070080c5040c646002220390700b01080300000c1681504108015000f081e68040b0024440c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 662626178 1250 662624928 662624933
    0x30601050a0e07050904060b0702190503030a030903051308060108070e09030405040c110607092907080f040f0807050a170c041112040b060f090f040b04030309120f020c0607 76
    0x3201d00512820441554003404211074502c210b04071044264001c0003400070980351052003000f9031060034120310600341c80c80740319001d1591103e4801160002800b41d42410a800320a42c003802501c81c084041100412488950384142ea4124018140c0c100017040380b0340c10100311a00c0c00c100e90300880341b00b4007103004020702c3c450000200c40903a001901d02007010014101c0c1500c25050000010150f80620020132111f694802d0000301204ca038401c04240f20b8000002d01c560760030b0912019a5080f4017046041c0100301b40d90000c1000318101d01810380342c20b0744c5041607083e04209070010b01843e08400d01c04c0029290071a012006001c9504003c84860803034003803140d4411000c40c0c0a8040c685441c00900c1c01d0a20320256103130440c80f00c80c505514a010324280d02e250004a910900c600c2045ca0007194034180700c0394a0323101da400b5800d403480344c3d141c9485101c901075000300210b0807d80c44d01c0013140001e03148001500202d01a0b00d5070880c41148038006070429104031401d500480301805803c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 662627428 1250 662626178 662626189
    0x15010206220f0c0b0706051006051201120c03020a0803030912090108190608030c0f0709020304020306070e0301090c030b060a231315170c0402280c02100c0302060603060105 76
    0x6015840b20b1a5002406989000101e080407039000f601e102101084490074442c80ea00480e1040034148401308049032076410548080c0190405500306c4038044006201d107005060f0340040e410b001c1c40c00458644d54130f50008107030205a400c003130b2a941001c030034443c801004000c1103150b0001d11021b5818480d8040000f800d5034001050800e6000d01e0008410a045047e4807100240c041d00003a01d59440c80a50a16955020311210881c58854607900084c0c0c01c41910980340200e0b8010080c104580310400c0c221402c104408900345d0556a411b07003440081c0035003000c000118451059410140b802d023041109500d5168000d502900a0b40082c914101c94500040c41c180c0085402c58080000d0695210003400030010b09100c0c0c000e200b901045905244102c41d1201311040c04440c203940219051000343d0050103400803a2031120703218082100f09142c80085002c0c0c0d20300c0c1c80140650a900002c0a003070760004501d01060306000c40d64203059040c00030079401300061f4010300380c5514240c080303030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 662628678 1250 662627428 662627491
    0x180e0408120402010309050118030806151b030c0a060f18020303040b22060e030622060c0c12030501050a0504050906040305250605011503050402030a020402090105040e15010206 78
    0x903405014440042d00b107a009a01060516070000002c11141b0000c1030031180c241c2d0480800e901290042001401614092040c00e083c0c0d0b50324003095040c4100c804021421100c188419201030106001886280c4e01c00c20030340381304130f0140101003402421080003008582c000303807280030030001400100000d42c800104940894442c0f00400b69680d0f184000544008400440340219400300a4000784e81d80c0c0c0702c10345403000d07401141610316584070080c1240c80b10452001c00340d8144141e128820105140d40e02c04095842203041c6480982d015558140c021941c29900300c0c042503880c00140242d081c22030001c00034040546040203541040460b0542d902c0c80280020104540010710b442a401c000c80341c0d50542401c1500e00d01354450510b40800a42006d0080440e03244028035030202c414483d0003001e000b280c024001d0700032001a602884084d601004110b81403000030800040e42010804d60fa81c4102d00482246180880500c002810524060606034822040e003107a0000781842d1360300c0c41d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 662629928 1250 662628678 662628697
    0xf020a0e1008070e01091701020c0c2b030908010c030c11030f0409020d06031e060b0d02130c18060c120503011d060a05061206121f18020a0303180e0408 67
    0x10b00d031916008004136105003480d01f00c48031a61038501540504e0f07105401400005c6400e4040d80c940d02446c2c014031407011410914020024184d16030b61321560006d21102036070500034600303034000c95140c484040c01d440001c4840f0300001d0345ea61580d80e1065001c0c803420352900d0305002561510110540740405c60149018a08a00707070700081442800b0003950202005540c80050341a10b10354044003080c0e013030304103041030303803c0c5040c240c8000151800c0c0040c011140d90040012054a24044a130340003400c00b000181c09009841900c5601c0501c00e5100b44010080b41d0fa40d46901d0040d031034201ea00050146414090007828030050041c08c0301c00c003104021403030a074a12100741d034480d400904001100d41c4156013080c0006207a030b01c4010708142c881d209400507540c11411285420146994400c503c0f0309146003901c01c240d003200b00c40d46800024030043c0910300f503a0b0f800c0d410703000070314030300c185900c00c502050765101d80d80707404400d02008800074050061034001514280d180c00c100c034414850078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 662631178 1250 662629928 662629937
    0x15190509030c151009060501050403080d140903091914061e03010b03160212091c021908100203061309020303070f060c031406030307110a03060f020a0e100807 70
    0x10348041030400a40c0c1105206204841141c8011204025032501c1075468501d0441c22540100e400a00ba000701e00444006a40341440c20f03243d0f896814494010381a112489a2500f00c078070741c0d000ba0751b02c0f03c50240861340c016650310b000401c100001207640040518002c0390b0701d1002c1080d140138200410004105840c00795540304400c1c1702007041041c851790024401c801000101c0c0384241c01024501c54003900b180c1c91010300003410103a903142a0325100c40c0c42040100310800f51410720b60724940101f11025001e0742030f926180d0000b6109440e202c102240388406103420091200304004120024040030011895800d041000c40d42041000c04000403a03a15541c032001152801c1046942e51904652079a50781d403a90328000002e07050002030680068103000c402d0088422100e090b07405450010002d62500c4420303614210f29000281c440da520400c00c0c0c0c0d00001085503405940c44a0106910050340d4881c2c6003005000202e15420032805099000c0d010314072075800200440d0040520b040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 662632428 1250 662631178 662631181
    0x3032e05090414030d02031504050f06060c0708150a1808030c0f04150c0b361507020a050712020618030f0a0b040b0a140a02030702010f05040311151905 67
    0x2864081081807800b40f500c076100015000b090618154003940c05118061032940da9040400704000035200191007031118a034040010441e5803900400a04031248844c0940b490541d0f203407069420001c04c80da1100001c02c4080401103065030078455800c06181c0070310680d40340c4010b91503810b0309010087c05c0c000c01900002e04900e2482c04801950018a1000c12500004c091a0001080c408000340101c40350134200300803a14500c40700f81d540d090100348a501d140f5902c1803201c400b80d000d250514481c890f020b42c900c0c2d8950042c41d458220300c9a4696002403407140c50382c0c94210300c1c18007554014040b0303940707201070280180c0e1038204071440207809a45510180c001c2c040000e090820365056511a81b00300110002088000140d851059000c6c2d4002410342e991108918141c6510040c2000b104e0001e000141084035164095508000684000122040f8503242030b8204c0c1c200341d9068012070840c5490b06900c1e1800c0204540035442801211900c0c1844408182d900c10954001d60344503440300e0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 662633678 1250 662632428 662632433
    0xc0204090618150e1b0607051617030f0a0809012a02061b1e040e0a050f130528020a14100e1e04020d050903032e050904 53
    0x204006545034000030200151009400c14241c101e455601c122618002d40c00f01c81c100100d40e1003140f0f040c010030344c0600005114081507440d269018265982e000701d00b032080b04081a010401c000000c19080f90101c01c039418881e400040308640f490301c3d0b4080e44200000711b0700015400c15510011850704150200780c0390007840901411903052200702625038480c020786941207454401011801507029a4066207400352604110181d50b9020030b207401c0308001101084c0302609001142d80601c14842c0d060588801c040800801c0c19114441156120b40c03d01101403003101e02c9541002c201c100110b0012440e83d5901d0b21650181c8842d02c3c01a81c504d81800880c02080145181c5607000703240306802078450b4220403003000d0503004103010355000742e000803086000781c1e160312281c54002d2401c428006054940003504040c040d06035041502441003051f00743e014003c2074044c0740410080c43d16440d10b220410a046218180504412a00c85024510050400309003040d42d0341540c41c448565203d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 662634928 1250 662633678 662633681
    0xe0903070206210408181203030601080c0f040605120703090201080103080c0703061d060106020706080c091c0b0610030204030c091112040308071403010b0a18091404060f020c0d0c0204 81
    0x4030f8070440c80e203901c1048104045c80c2c00419005000d0340201c141d000c0e100301809449016050700404c40c1c0e1080001c00c0c201d600403040c441d40014208256480c3c40c181c42104001900a94008000310340003143c0108402e40520302940c1c032601d0b41c41c00b00b02011107500000e1001c24184000f8050300da0000701881001001c1c0002c10203940c02000900410341d10f06903603400000d402c03030043d00700c2c054640045211480420010304403000d030342d203154094a41300510072866120303580440d4040301101da00c80382842c00585c0f03c0c6c004c5000742200c20740791400d03109118264006985e0b410404d841040280b0016090094100540300001c0c00041d000c0844000814544034800318100440b091004000c1015032002d40380b4819030040c0e644401c00f000e00f08013182240403c0c0100340c00c41d18203010302d0058600c1f5010004d041c95861551000e666580e004460850311050300300d07032495514404000c10f11101780650304480524030b00861030b01592030003498071605881030640c100424080800250f541d00d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 662636178 1250 662634928 662634967
    0x70f062c06071e180801140f0106021507050904140108100e1903050904020405061c060503010504030e09190c020d021605061c09020901121103070501021f02040e0f0702070e0903070206 81
    0xd0020403403d41f2050718842c03242011901600e10040560000c05d00901c04607840c5281007014601a01d1622002c0c002e0701e003500f2101560350010341e201240c1d0110040d550400c1c0c000c01800014109103402c680c03040d42543d0f41c455581800d40d00c5903825604844882c43ca03c6000b54240c80c2850f194210600000c0203849580e1229901110204800701c500105203040610301c601c000701003000a554805141c240c034402c690150103d1080d1407400d030941042d0300e8490b07103d0304d2803030010041d00001a1020031555040340900c01640890301420b00340760108607000c0e900c07602d004440740017460600000c0461180440358201100c800003510984072140c0c0003103044c5507004108a0395581c4410040c0300d00b443e0014140c440c40030b254034424190501180c0340055500c117a000c5c00c600480001911403000280030007900c1c0f10360800c00055554030300841d440c01550400d038646c41d2400d0401001345080c40d56001801c440740c810003401054240041203d0b01aa030507030b4410b440c0c11014000b8002c2014 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 662637428 1250 662636178 662636189
    0x110c030304060b10170a0b01020307060e010e070609030b070e0d06111305010507050607050f070209041a06090907060305130203150f011406070f062c06071e18 70
    0x30040c08200316858001004040302558402c0340320609040803202a60503221700504400c0d00c0340402c9403092140c0009140000600403286003001e10750b2010300f151111482d00c03559075924180d83c010001e060000c1402065940362003018542152104c84018802502023024003c506007850401d40b124124903000d6600035504002440c200342c605c82c0c00fa44095042d20480445146c00300c3c1560146060b034140c25080002401d45503a803040039180c5a115030300b40741c0600c03428407200d4010b90310300b42c8003803146110309001301070061007041d0102e200300040d004500c20002c0c201003024070040040d03040102d800a140c04105a01d42d2488080e138001040c4000c0c0d014000c002011020381d52980c04103014850030040e4480f0b40c0e98415520180d103136001d20080d449581048950301107a02e0340c459099640c010080000e4445205c5500100070130000904600180c69144c2c655400703905000180d48002c1c039040a0040b18000d5100d1046501500a5102848400e50929441c00404c0381500058503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 662638678 1250 662637428 662637433
    0x201080c1605030c031207030608150a18150c0507030c0b0c09090727060c080304020a0b1204050c040b010801050d150c030605130b01051222080324010203030604110c 73
    0x140c481501526a40240aa60481d603d00000f11342151300ca442270504a41c5120701905d42d03c1046698400b10081c0506030003152601c0e24010103e40b15901c81c44200c580c8150141104a201004208165990701a140c2d05102c0c09128a00200342c10242003d142031f03010110300426543d04400c040c081c050100b00c070b50450100c10401207450740019017120416104800011451030307003040b05911013020b00404d40002e600d07814200c001401c05019640240c03000307254400d07840d04c8241141d1181c101c1d80f0344501619140043c003040c48018808141102d406450a201107000140041c0601d5010301c0b80354082d01a41030204144000b00d01c0c58215110b04803400c5c000c1400394030004024203074500620784240200007078881290703114804c0d42c0d40c181c4180c4410341807083c3c0305c484840d8040c0c001e000c40019441a40c1c01212522030500c0d40340820b1040f0040d9440f0700301451f48540144c42c0e0300103d2260042031800d50f003140c0c2c0020a4279030001089070003080440180400711820f000328a400031441c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 662639928 1250 662638678 662638687
    0x90f060108160915050703020616021b13020d02070b1003211b032703110607020a090608150105030303040b16021006031412190309021f09210201080c160503 69
    0x11303a4482d00034000d481c0079500f1a04541c4500b2074050380203650f041130402592143da0f40b40c660050303109108001001c0100101d121505e20848403083c0d03031015608201042e4001065810800030048907a00061112000101a03055035101e1040b0010146540c0d00400c1380104998064400c201c0c103141090f10400142c018211031502824042c20a100320541407442d000c10a844120789540104a9401405040e0691612802d10110707521440051743c00240b1204003003203180307685c043c600050031003000510703002030028644050700e030060700070a20070307081001800007086d0400006600246558424881486006426441c144103030014021090070000d00101780845000045100d0b0251070035290012050b412500c042d03c1510016410001c8600b00040007030320039803284003114405020000c3c44200c140c0a1018601c3c2600c06200294480700705200b030750405000e200009001d550681041742030740e4000f0b003a1500c0123005514205010031640e11007a10401013142071030f00082500d99a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 662641178 1250 662639928 662639969
    0x30516120309060c0809182d040f11060f030f071b060b0604090c032703021b040f020c060403030e06010812071e030f080106141603090b04090b090f0601081609 70
    0x541f4411942514406001c001e048074101c900c0b420f8548101135050100e105507100d5a070551400b82450b429a09a1b81c40960059030352034500c010002c1d07098400c459500e0349004046000c08440080800d03040140b074807405a00d0340c041000c03070122168411004070344c020201c00072a03040c1c0120b9100360340c1d070703030400f03a0300b001c011740552011066907240700c08000c0f0301e10410a002c90348041440e00500582c80300d003100c42d42400c000540e40c5a800d0091000c15803801129003201070342c00008800c241c1c2e40280c1d052204141d05032003042481003421000c0c020540c0341043c40c0303031117541c0613400d110000340006920080040d110701070b900d51040100304414a080500b03005105001e202c07624008500444000316525020b0034011181d03401c2d0090480c030b030060003039021511868a0b10b088043c00701881010034a000380307074054800341005090004400b014803042210004c0c3c05800004a0040072090012a9038440b0b1419484010160007032581c5030304813001ca4036150740d030f4410004a081ea01c01d4840 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 662642428 1250 662641178 662641219
    0x9150109022d0a080a020c0d05030711072402010504080331030201060302190305030f0903033a0b030a0206130305030a0c0c090209010806131104030516120309060c0809 74
    0xc0c80c0780c0d81c410041e41c45c81122000c034800c40018565075803050400c03c81062099004587c410241d150102c00ca15440b0b20480c501801500403003010018011960281c84004441e013104031441d10080c4180e00b82078840c0f0f417075840b01402d0750a07404946200441070314102400e1450030301810000e60a84083d030309009000349420301089200d81d00e825010513400c0c001c1036034401aa508500074624091604500309011752018030040c0d0540030a0040e80c9000305888203410810741e51f0b160305c181da010354680c01103e03008110400e040c07292402054440948000400c90b07c0070b90306881c41c0355101c00c0c00102c10a4611203900c01052071000041059646520028092841e1b1003081058525622031b01c000d000d07405400810390000b1000d50009200b8501144500c611000f0b0640000e001c001c907400304012980a5007090701c096020b0601c64813404200d4010600412018942d0380450540741e070000d1880d40140700c0c06041254400b1024244140d06d402c44050b0b02d80144480f02c501900a000d94 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 662643678 1250 662642428 662642437
    0x12020a0f360f08030c1b04060806040c0302040506042901030e0304080d02010c091203030f0b031b0324010303031505041a190612090507080f060a0509150109022d 71
    0x3201402c03070311000120000c1c00000c0d00c1d103c000400141c100714078102039910100c0e095081c100d90094481d100041d41e24000c0c4101402607008120949849045006000580710b0180c0900c0c0902c1c40e140002c4d03013284000c822100c2e0484171880c82c0c00c1ea4408400124060410b01400401ca40030004000034199000203000c02c140001c0c0c0c00902c252407a03d041a13808800c90f100d802511011340141c040041e00c03d038003581d404040220000744180715100464640340603c40c01907110071144014039042d180030440c1203101d0117140300300d00c11803100c48000705640030184001000e040d207500401001003000790003200078140141c001c1041f828001c81030042216810700e403a0084080780241b0940140e107407081002e42e0401d445e5142d9a19000c4107400090042c0c11041c2d0b0035000740900469025010f00c401c45900701c4010040070350b4140035010004490010313004081c0d9170b200c0030b081040318150001c0d0307d044a0480c0310058440031514082d216401c100300140800c00c141d8019222204628400750 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 662644928 1250 662643678 662643689
    0xa09030309050105070b070c0507091e0f0b0f090406022b0c0201110f0a090305030f03221112010e0f011b0903050a12021e070612020a0f36 61
    0x800e01241c0c2c0d4001502c051089881c040d100d01c081d1400a8106801890a4815644110304a44285036900c042c0e0045030074028400c0069601001c00c14000500780c0200700b682c004804080103002c05280c001541500c00a20150080c1c5001e0005002e202040e03040c6c2d00c00c20f40d145202d000039180c032400c0c503001b003545a0040300c4480c40c1241c20020603105225011142007a0b000721032812515009551460708650500400c0005507107000c400110180b0180000d00800d00c840c03901c0b0300340000c1c50390541c3c1c25007031000c9010000860403808140d40340080420003000b60340242e04038610f0301419025081d181c400c42401c1c0701d00702e0b9143d805a015072000b40b4400c50900151500003056004513018680d030710001c0c0403a4418103084000ca9640714101e40061000c3c0111032040d5450b10314881d0130744000030b8202c41746e040840f08100094001c2c803641504440b2210442c45c24042403000303049186600e0000c0f04014110b00300d0780e0441c247d20940c508000b01491014409640c0030813010806c0c2d4540200b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 662646178 1250 662644928 662644937
    0x112270c0e15040c03020307090303050c1f3c2012070809240703060510021c080103030518040e01090602030115020a0819090f0312030528020d0902060a090303 70
    0x15043e4511910a44e0f00400b45640e6410940d8030715142201c2507040389070185a240030700081d200b0548103d0222502c0300c80b686a0200340c1414a0650311071031080000103081c203d402d54100c1444033f50320410000c0c1044031940005071041400c00c14158442c0b00c0c0300004000c0780004103131201603400b405840c0319800943d0343c0003a41d43c84010090310b5000145078180c0140460002807c54241e250742e00b948406d851074005280b1345e4880028050b55800707940030001d60425050540c800c05c510f400182d1904403400e200e106035145503001413042c490044d555034480b0403822210419500d640210420b060650300900112200f0b08001c0c0c0254070a200f20900c0f840d03085601905280007142c9044125009074000c0e0501401c80100b000d14100c0c00d5042c2c04000000f007011031520035141d44040a18061206420120004000070381181c1e400b4006442d01c80031550f450118491a02c5074007407d443c4058050b8460712088200009481c1d2505c00035031205020803580c0034941d00c400440116806590b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 662647428 1250 662646178 662646191
    0x90a0818040b0307060c031409090f100e0c04050d05010b041a0f03120a1d030d122a0c020301140c09130b06030103140f0106140112270c0e1504 63
    0x4060f60307040944a03010224401203c6e100210f4011207600c5c1400012250741c91074a1103060011300201c0044410310a142e16810034031800d1443c110368080902404261b850f10340c1003040208a0500991240c030344198211104901001429000900c0d40c5c90050018491003c81100603080719412500c0107026110704254100c03d4540002d1080b401619070040c05e00e451031000b400c942080c514400c4d800390826150310b01e852a10200054283d108031644c2e40002d1032600208070b010740f02c05400c4140c90707031010400d4690341030b03800072032607076404e21741c1403050b803100584c404031b8050906601c40100c0a0b032010f041103604083c0c1c400030718100b001101c0d440008100a8001030407070383c41d034440c10b401c00018001800000c80842c00704003040c05200c100c0c0d034840e0704800c507203080d9680d5030058003204005c3c1002242075604980c0420004c0b20241c01840409004070403150070450103419038108600610404041c00741c8148840060589404408000e142003c00301001c0d00781b08500d50300a40c82c1c41c1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 662648678 1250 662647428 662647451
    0x114031606030f0c030501052b2a060806090c0c0c0a15090803030f0406020a03091b030308091f0c0302040b0c0619090b06011d040f0b030c06040b0a0305090a081804 72
    0x6c1214140d441c014141c000b84114282c401c1404003001c850034024403411003002c0c02140351141d03030043d1060220309014000400343c0c0d568840c00d00741c0e404142031002c6032090100541d036038859507500044841e1503d0b10f450041e0100c919140c0c1d44c8204a42016140e000481d18008035103007451100f0303d6071903601005540c0c144842d602d120464503200600601001310300080c0568008100034407003803401090305051a00e80840302c0f4801c038685042903400040400406130000206640851200050001010030030003400192441d5880140c2c0565503420035291107001e6415600a44050003541d605c843c940c40340303c1d580320f505a90a41c80154410391550040340e041c0982c5244541c49039041e211900c1c0e4200540b2480d50b42c0002c000d0078007144014401079100c511800000c80b81014010031250210700034982412403c2070124000d4008010070701c07440300a40100c0d9940f160340d20b000141a80c0ea140518100082d03030000a00f2550001a0700641c1008074080b03419050044504000c1c110703016 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 662649928 1250 662648678 662648681
    0x12010f06050d0b010e090c0309100509030a0305040615030812090c0f01111015051215011e0f0303050c0c190b07020604150908150106080114031606030f0c03 69
    0x80c03140380300080c001c0003018003600940e0080d00d07041e0010f06240d2264003030700700042e42e940011641d085040401004002c0d12500c20064203002201120040055060269400341c80e40318110b40c0d8414107440304041b0b8104880d07540321507108000d4808030266240c50b0700c0c0090260340b000c8011a041808400482c40e03903200418440d0310320070010a1884c21581c014010b69203200e03d654400007a00038441680081001070080d206100c0709500c040340510700b403900700a410300c81c92150075441c0d44010260420080078014650540d9030020350010003007551a140c0708000001c1e00100e01c1500030305000810590000007800040c0040780941756142d181c50305111001249841002c00d007280c400081120702003035001080e0050000c0d0100f460071b911451015410843c4c4a8000c0018150b00000c00c0045000e108900d007075a440600c55115504d08107004010620600034001e03007001031110039219581c108210703031144c000340400c1c01641e662004094000c0c0100001c01e03100e5070800300184001c6219 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 662651178 1250 662649928 662649959
    0x50f0706110a2316091103060904060207050f0a0302060601030c0c0203060703021b120406091a0702130b030a050610290a03110f090109090b09040303090201231201 72
    0x400140910040c0ba00d0f10301d00302494049000d090000640f2144200310103002c903d19140c070341041c20007180e1400500e20100d4803c1500c0c54035001061050060555901540340c3e0400d400c60005038071000203085c041c3c1000303c3c03000c140d986485480802c80406801241c140c0c49442c0c2601d04000e03100c003101041d104a041c6003c000d43c19048080069403407030299011700b00c03125851403070000d41d0500102c80f07841c00c1d20380340100c400d40c240401c003000120303448840c0c400034090f0040f10036409400e03940c4050180c010341500034856010840e021030710100d6540701c4240c0d8840102111a20a100d04090b80c56040a60b01d21100401c0d064010a5403a411894140c1c48071003a00398070303210000345c00c0122480d004902c0c25005c060b1a98030807004007194002909940c000a03014641d1080d520303001603d811410390101c0d600b00e0816144d211295240040d0039801605418040f486c29040d100407180d517041042403162620b00880c80d104030910f0070001d0300c0c492148040044080e6203459284409440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 662652428 1250 662651178 662651207
    0x10f0614031f080a080c010c020c03030d0c0302070204050c0a02011a0609152802010510060e130b030303010b091507020d02060c0a0606060c1a191503050307050f0706 73
    0xa0410125600c22402c90044060300201c0048001181c0c460600901340706030600182c8a403032000c22082c0ba9004284560020b0f5036840c001000d000840101190305d9000c7d0722290030500b03980d41d00b10521a4002e4044810041d4000c10411135032034404c48000546c0c100108100056190241080a03000202c150110345000200300509004040040280310070000f203820310700c45803d02c150007400b2150020044c21001e607006500d03805451280090850300c1c0201038080741c00410400304602a00460301048a0030169000c00000d01d000f84548040d10a0502494040c84000000204110540080c0c00d40c0d1904940702c1c681c00b1098a45040c0c51f004000380a54002402c501c10f00041c50504000c6c80107090440aa034880422034039a4000c942e001d074040c0010400341c0b010b50b010842c0c2c800c0211006101d8100300201421b0900718004a00f680b840303c000c0140c1e40b0302003030218000305041000250b0303220003100c1d07903080d0502e842e035240c03c0c2e9424496010300c23a0450120708980501c01e91043c031072 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 662653678 1250 662652428 662652467
    0x141809070c1a070e040b150a02060105031603120503060f0d0506070216050a0b0322030e0f0102030a0905120106181515080606031302030a051c05161412070605010f06 73
    0x130186420840145031120200303602c001c182e0000410001d44001400c101c01d01600035110039031410b0207042c140191801040d0010301c40440a00000e42c5000b02c0c000b0340c01e2285040c2da240c0d5100000703c0d00ca1080842d07026440318001101008210000031074500c12140d90b400d41e480c0c044e24108840000c110b40c00743c00c1c0d0207405c02c030092003c42410310146505c14850f404503402c41802c3c08242c8072844802200360002045d148035014141000d0b038031003e000100788019450510700701e00080c410740190180500c11200c61a034002c13803035801d41082d005480c80004104030100c0000e007550041c1603c0c0040e00c4003000c000ea000812064441c0743e07442102994841c90001d940705001c00c0007660004216110790b080c1d9403402000f586081020440040c480c40051041e20040025018204103040c890700400c0810440b01c040440922040c0d0005170b4450340301d030304211040c000c050510b005621810306407000456040c0910a684d000baa0403100c0d0440c5e5100141e89511044408030042041c41042d00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 662654928 1250 662653678 662653697
    0xf081b012d1503210e0f030303070c020102121b070b09030601090b21010e0c0303090a03081303080a090f08010c0c1112010f0b01020c09040201141809070c1a07 70
    0x2084a82007040c0d900039036100c20700b540d0385a0f52a103c04030f0441c200c0d5402c000a98407614465a000a0400302000b02115072101700000302c00080e41d2072000400c0a800c004005400c001164000c0245180520a058449840d01c041c4500c181001d86030616815061155010000b2499100300899140e140c010b00500141d0f0308202003c030103402d88550fa0f6800c1076180207038540b401c84c070b03008014a519086e400864810f486040315498038000c4070302184280c0080168080380c1e602c422071a005c5a0380410041c0e1034030003852224011404607480030b440c030301e800903c1c0040180e00c0b07440c0310300381d80d25280850001c584800200d030132500f906441e076021a6240501c200800c3c062070386102240001040d2040c00c20b07400e5806425500d10150101c0c0c06903c505070780d1119a01031040341d04103403017501c00d91440c2c41c05400081c0214000301e9155000180001d6210400041d64028204031002030140080b504149100500300310800b003050b201e0013501609001020345c0c0080f036a02038100e070b940382251b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 662656178 1250 662654928 662655011
    0x825020630041a07120f29091303020a0f0f02010f02070b040e1f03081308010e031213120804062315130624020601061b0f081b01 57
    0x3c1c030005844c0c8018002880a00e03400c9440c0e40c0101241d402c048900800c6485a1307903003c1701214002c03100201e20300260201d25240d91070310740d0030941c8100305462404010006050030381c14042610030141400751200c03904800d10440c4100500014800c0e40d40c400d000080c510203d8850000d40904107611404210400441107410522900000c54104200125052103082c207a01515603100302d80704040030820b0701d039511650002c2030040c0f040c48002d120f11504c8004603034503407084e01907010f0403007020301c081028048c9840500f80c040b0360006804480610f800f001400605d4200c800300c500c1410696865000300740d00701d001c00c1b00b036900300300040700f9250302100c0403e1942504102e03030042146442400800d1882c045c0308001c100b00d003d00b05000300000b401c05140b4614410a0095622080040040d590711810941c1c1910305140c41d0218002c8515000781020349c00c0b80c1c041c0003100041416181c007501d80c0c20201f41c051202000f0031049504000c02c00e4170700c40005e4a12048600d203d450a00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 662657428 1250 662656178 662656223
    0x806180705010305040206090607050d0201050c0f0d020a0e1302030916140f01020f1902030c010305040c030f060902040519052401030f0f0603050a03090e04082502063004 75
    0x5c000348000c0044d41000501c801007809900503500c150313184d900503000400c000d902807099541000740c1881ca1031030070340c03101408001d078407032512115522030f40054000a403d20905031051040c0f0010b0403c229440301c4808500030b504181c03000d21545c0038403003102100115600d403100403240030b404040a84820030f0104040d003580008114198003410071201c1e00d0031410301080300b031030003044541031400c0340340d0044c50300e007030704109006041c580740206200204d00c036034014104895006000701c040c07603820b1920401810030031300c009406c41c1c1868103104106811011500882c41c00c038504100d1a65a40c0b510450400752200c111201c40a011901e49294071079007014400c074003036040c00301c0c0c02d407503d205141c1180c0341944203032196082280014101a4850b030908014035207946415003e0400c1d48440c1d800348030301c0000c045c01c0160402003401011000620030504c61700241001d444402c0e8107480700f03040305c50100702400f0000d2405d08400152100041074022600140410310962901d2070303100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 662658678 1250 662657428 662657431
    0x40201110f160602060a02071a070309080d1d1501091503050a24020a1b050a05060f1509090604081308030706150b09010c33060806180705010305 64
    0x2440c500a10303980040210040001d180054000320081c510185400350090800401401c4444840e004020210200e06030000d1400d1321100701f048917046031a01130742603005003812a4003e01d00d01001c2001e6201d08220342c060b04031036400300203488040240b0f880307568440c1300030900444074104a60050000c4070310b55012002c407082e0541c46002443d100d4595600d0310410580482e401b403007081076003041004401c103c4040300104c1e002581450301c6180302800c0d0010955050850b440d6541e605024000204142420960040141d940c41c0c144040e000c4100c450407221603055502c01841031046040006149200711101c401034a100c1e00c07166141c2c1c4050303002d51158514400d01200110b200241071008090141c031810b0001240700d45840c040140841640c800f00304800d0502003961282d80002580285c0d03607011644194100c07042801c1c0040d802e034030103608000e10100c4010030240e03046501c8182680d40410482d07030550340e8605880759102610810b610345401c0700c50f007084194040e4000c80d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 662659928 1250 662658678 662658707
    0xa02030604060e04060203010510080919020105040915050406060e0307050609030a0c1202040b01171f15021e0601210507320307080a0308060a0b1c060914040201 71
    0x829160354512242c0f528140c1601c050364556030000041102d8a0444070342200c10896080c06441840c10035401622a01c2044405d00f85104155484007161b11a074120f80240c111418100206004d10035400810960b07401351741c0c040d03842e0141c0031a1a5002ea5031000c501f100050042100d00d0a01041c03012a4005065041d058813440310294001402c02c0d400b003015209202c84202028041e00400082d950f2000e1850b061010780000180000e120008256000b620061210301607000c8004076903445030603078040468591895908c00c0541da000c55405e0500d031031000380d500480042500b6a444000a203c3c0005081034800800040c8e84000b0000d55428061030035280e2055952000d64955a00a402c0118111080100c201a00c0f142903121180031070a60040c9081c0d420217100302c2e40c4500c05c00c40542481060000100710343e5810101c40d010740701040215854902c6003400300b0740180610741200a15041683c0812020040d124041000c1502d484401064980740c005480301017184000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 662661178 1250 662659928 662659931
    0xc1009080c070303021b0a12030e01110f0f15070f0c0501020d090c15020d0518030a050f030a080c070840091a0d03030c1e0504180e060a02030604 64
    0x344800c0030103120400046000b45c014100440c2200c5c0702148185030003094a20071102c144050000c020050301088415605040c090740d0000d0175001030f96800242c41c0c61210703904c40c041050350707000004039002c4135048041048800107602140d080075580750403100b00001030204401014003500c50b620844800d03001c0c100042c075040500d0f0800c000d071506c101d82580d0070541c2050070845403031102c1181005c1e42e800d01c058000c8050002c0000e1451140c1d500c1d0340c6d4042803424038042255028010540e030740e85d11030119601c00c14149407813600d940190b0700a40c0861811800100d403404000100c400c02e0707900002803860004207800c441003030384500c0001881001c04500301c5079500d160b00402d0703105080f2491144e9403103140024640035500c106c00400001c0303807800ca80c220710b5119106510103066040c10040748200904030704450701c079003001c0d003d02c041c00043d8010382800d400c14002e10940342c0d5490300307030700124000701508140c480100c41d035450395120344001680c03040c05a01454015000410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 662662428 1250 662661178 662661187
    0x8040b0f040c170c120d08041b0f09091110050301030605070509040e100509120d0b01030b030a03030c022803080c0f04090b1806060a0503070216030f0c0b0c100908 72
    0xc6212048400311143c48080d403007040180410310307015411a07074296042c40141010040242c004100b0403000d44001c010b80e03101181d120018080701c0389075014040302030440408a64840c104800790140700400d8030300c9244c4070311a1400342840141ca0700c1c5400a511074038a164030359030310440240b030010000c0040001c1802612a141c7c0c8900540601501c9100240761503084e5281807021903401030304080031507000c101200e181d400760106032034218981c204000382c01c40e007400040c0c002c1e0443c2444241d043c00756400c44010940c25600c2044500313110b034212200c65421940c25000211b10040072460b03840034070020000203105000e03080d4800c0d0300c0741e80c1d40e0900b0032090507c003e03900241c224418041d00c41c4290b404a0801d01d030241542da06e55482c0c80310508000000c00d034103104040c100410040d0000000c0c10b00c5008008804071034032100c400383d840b1035890801000c00c850500303017250a041d003e20000383c031541c0c900941e900040b00d9005403002e1501c45000e50b00801829808540c032410030700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 662663678 1250 662662428 662662439
    0x6040b040e0c04090504110a091a040b0301110403030c1e020d0204020d09120906020f07050117070c020a150f0f052505030309010e0709021801051c060311030c0108040b0f040c 77
    0xc0f103000e94450101c4401f0700082004100f03a800c0c40b908282050342c90000f07281050015074030302c548014130689001995174079460101e03025124022060351308000c0005c0000c00c01d6808101490040c2c058181c4480d201800e0042d01040f10180704041d5008100303400722000752810317074020803060340035002c0094018004d580310741d007100f109005400030845c11001002401d0301841750300d51105004001d0a032490a18001138000140b02c10703050b011003a0b020005500a010f44101c4c0d01050b001440b080c1045d40d602000303c0821200703040d40c80011591a1341662050040c04c0c1001124042e8443d00d0403e124031507042006020347c0441000c0c4442e5440060106006000075409400940004101c000c41d000459150034041c2c0d01c2829002d104010301000c103100e100321441400000d2a0a5507038850507566828000320741c030304500c0740515000000040041c032050344a14084c0c01d03000d688038210190015250f00c203049030b000e01402381440c005404080c0181807d40d000d8460028030782034548030b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 662664928 1250 662663678 662663681
    0x201050d020c07030308221a09030d050c070c0b03071d04021209010504020405060a0b040b03130203030a0e0102060a060f050603130c080706080a06080309011409280506040b040e0c0409 81
    0x60340203401007902c110601c000c010300d101450392145e5843d15407c031500720303503a2500c1e200e520304549101c4003060a008600008014003ca0b24041e800c810144194204040d000103664043c40c0210313054014264009554001c05080d00c0c890b01c0a0b45507000200c6070082d000301080b00351020558001d038204120650881004919805001103e000080510740381c8140030072200081e00007445000007580c00c0280c03c51007400c40e01585c50510300709441c2d4540880051400c201008000c0d8103000100707010b40303499800400340400c203d00368211410b0780c030b80d00c181c00202d0b8014064041900c46c480340902c480e040107001550844001c1c5083d03824030406498070078104e03940307800402030740d04804006c0002c5584102641d8100200b244104420b82c60010a1645c0340b250020003410b108001050300440311224080d10707245100544004500c42092801007404401d0600700300c92501e4a103030110b80e41c1051000d49050340c503e01d455515180c2815966560010000c003401403800003000003003a464001d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 662666178 1250 662664928 662664943
    0xd050d031b2f030703270510030207020a050607080d0b04020f0d0e1518070b09180403141c0e070b030103020613030203070f0e090c1f0203040320120a0f0201050d020c 73
    0x390340310410f20500718034410300c0311a001131400000d03900340014052648c4002e0080c4403954642401607680351a4804180c10796010340c0304617488200400d007641413000e144001c1403c1e406400b810018040d0340e0080004a001d804102204018240701907410001140d20408182d000c900c1220103118002c8801c0384000310480340d0a1031040032243c0c54011210400144001d45040e41420b030a1a00d00c202054040d08100c0e0790504024416002c2005d15004104807903180d0361501e100c507914a4062642c1180321021001b108030240351501c08000ca00000c1142800d4990681080745076900e9502080034981180c86010394003d0038080010059504209030b60062891381d02440c561403600c8081d02440d4001040c008641e0001e1301c10380c40e142e480f24010754070720f038a040d4420070020012804900d14069034100806400340c48107825400101081e0840243c5022220b0010a0102e103a1482d256080c503000100004540c801400040d070094000d400c02c042139900050030298211004d80c0360003013 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 662667428 1250 662666178 662666183
    0x509190b0301030311330c1b0f0f1203070315091401030210050c0604140109020306040501060e0c0c0d0c022b0b060a08030313020604050d050d031b2f0307 68
    0x800310300c010100c800c01d200c0c84050321410350511594100340c03c124000f00e80c00f0404541c1d00b0790701b0300028003410b40c0c840c191008a00000d000b81000a00f49030401d64503115004680c01a04c2440000d8949260006040c85007072680c180e40c0f815a2581e01094007d8580c3c00d5041c203800007004004030302c20106106001c11403040101003c07003949980107000880b21240e84480c2088000c02568003905400a60f15400642c02080112584048110302d401080054002581405a401030000344041504880d05440302c000c10780345281c603100100702080c484c0800c04800b507005040c20a10003030084482c07245003400600b01104a884070100d40c0e40c1c000c11500d44c0c04103030110032701c0c070070510001c100803543c40403064030541403031070409800700e60320300009046000640d007192000d03085445100a480007010098103007074001810380752071501c80308100c202100082c40c000703012000d12100700305510000515202c07a5641200f010300c2d43c030301c2c400c1005000010f40710012468400c102c01c0000704070690 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 662668678 1250 662667428 662667437
    0xd020d030c030e0108091903031e020405040b01020d0f080403051603050a020c0f0d0204090213060e01030b0a0506010f0e0411040803070213020f090d0f061d1c0509190b03010303 78
    0x42c0c41c000d407485030702c00d034480e040002c13110030003444c07130760000d500740005844541d000e8185c041454200d018240b0210030245d403110700a441040342d66541c016000f5a6012a0b05110760b002000c0126500d820490304d640c00201507a4102d004140240702c00e80d00b041c003034a00186000f240030011a268100020201c00050000840107000d6034103105800c20108110f9000c001d04903000c0024500400c402e001a1140b56142900f10440d5140d280c02820b07041441d00a00c20160755046002e0f00c4402444142c4a840c0d4500c0001c0e00e016541c81941e1080005845400540030150400c40382c500e405000301c0c0d00300343e58170805070600300b0500103440248100c000840c0c0e962060700c140120030713030345404401c002401800420380f06c03a013460941d8101b00c410358486d8407402c0d13a818500e041c05250907003d022546800700680480340390030345021002c030301001251181007614044110442e030085d20000001c400f4015181c180c40c10628220006100110b44444981c6501c00354100d64030030790040b40842c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 662669928 1250 662668678 662668697
    0x30a1a0c190e011e091e080111120a140708150406140a06030203041128120c080a020f0112090b1e0f13030509010909091a060621060d020d03 62
    0x30340c0d000500c145281c07441d440c00b100e1303007510f203a018100b4544c07401080140760006100850743d45440211900800495009101c50000042142d00035885034065180d08104000000d4403099240034203030240c4180d00f030b0800c040e5600202265581d00107449160a15200c1684a210f82d6480c020140607085561269841482610400c203c80c44142d00c040d081c5401072080101041c0010b00c0108800820364a942c034803c0b803201c040621201e1000e0042e1007101c80207000c03c00c0504452051500d520581c1d250400a8071b80000b20340e540d00184000b58095400d0003c00b009503c0b524156070700c81081c403400300718002d65540303200b0320b030300300f1242c0c070200405800c2042400b00c031130400a604040b889079040001c3c1007030071440a1108004101a060010003c0d00c10002d910882d107503c000c1030440350070400c8412a181a040380716000710007031300e201301c0140850f0f5030349021012640002d80441e103400c0d02004240715050007840003030042d03502040110b101c0000d6240d801c050551203101e5a83c0f00002c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 662671178 1250 662669928 662669957
    0xb1005120f010c020c030c09090a0804030b010f09060509061009090218030c011b0b0603030d060e040203011d0a0b060303090d0b18012d15091a030a1a0c19 68
    0x71a00c11100d21070441d13001c3d01d001c0650ba03d010840c801858000d0308c0c0c046039987c07000031540c13401140a00c01407100d00c00207400402d21520310849810f0f40c08103a0b404072195929200708083d45c1084c001d05a1104444000c18114a0700101b0310f03c0003c1142401c41c0401d54400184040b60486c00c80c0032240d59181c120804185800d003e182d44125003402d001c0b038003404811800541100043e0300401d041d1a003404290355503010002c0e035070b50740001d40c0f0500485490700402840e221081d90100c2c0a582803d081c0c0e50513110f401e074405400b017003c10080000040c01d0300d403001c1400d0040c00064150000f040041c1d802e46400c00c92450060041a00e07449505041400700c07000c2c0100700140240c0e0b490034002e4078808050034210103074010b003c012a11400d4000300c1d80c0000f040e100d04180342e01034100c0000104201d460308600b5810710b25103040c1032003540c188241500c410b547c040c020000105d50126841c0d41c001800240d4103c2260705100b03041c014070b00340b51194111020564004210182a1502c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 662672428 1250 662671178 662671181
    0x303040b120c030c0a0522032102150705070213020f1b0604050307020108070315080c041512020d21030501180207020d080d09020a0e0f0702030304030203070b1005120f01 75
    0x30461404142d6919603e04103009650342e01501c580c0c1800c100b0009400f8a107114180c0401701a00341400f000715040c3d5892034100700c0d01d00800f000418484040203480c0f091400401c410856030302041011440d0341e03401d4421035482e40480385c03c0307901c41c0030306040d4054040d480c030180c070313401080003545c5170358240c0701c21424103010444407035101560000c820080002c40200c00d61306426428200306000d40c0320850b00b900a4403401890340015600c00500240d010400119160001000c2d81c00300038000910002240000141c010b614020360110728040050400302500000329010309035142c070b4000c10350402201e0922030918807002030303104d50050007202d00b40e0749ca103080910a4501185008421350104c0c50015410350090303c4054086808a0030550351303003111100560060401d404651241009070709250144c80801d010311402c400209028000021130340030300e8054009608040481d66404802030008000e03428000c59440000f0340303929059606410500290050046444031f44c44850 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 662673678 1250 662672428 662672431
    0x60601020606030d05070f06060909050a060e07030b0c0a0207080313050406050d031d061e030f0f0705030a0207050c09091b04020406090509090a050d11161818020303040b12 76
    0x180b03e9041320042460f880d8108049501e0640e1003842400d4010f0642800d0f0010010b940c030100e0b40c6c41c145410f40003049004034117003d02a00c15801040003945000302d055689007207000041c42e080c2d50402280345084d00c40007030001105940704a9050a495070005425604418986054101050700503c8140b0f498010b44001d820300350345c0e03000200d85075100144062a10780301082e0b48070410600d1103051b2030b0384048039012004418a40d9450400750ba1100c8280c0c4211100048814641d0100d04800c0500054900502107503482505585a40861800a600105040b10f0b42c0c4034158501c202c0341c0340c13200c083d40b08400ca1405000080070101d640c101c500c40000120707101f2441007005102d265000a84402901d2056800705078503518042d640385000b1a03071802802c50301c1381c1c01e10103c0070350380701070b840040000301001d03903964074540180c080d40c855041c05017030380c4016501106540c400080d4008004103800380c21400ea000b4183d00803c0c1982e1164020809034100029030090003005259201d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 662674928 1250 662673678 662673691
    0x11a0a0933080d0f1418150d0b0405040b0c13031a040b0a0e071401090906090506120109030813050a170d060f0b07030f05120903302a04080606010206 66
    0x4414144c506140140300184c00c40c1d2442501c0700104801c0c0000070b010100c1e0009000103006208031141c986d0320000e041d00260020004a804c1c135552407018101030003000e00581e440045404562555034004400350881001c00140ea50030719000008200e4003041040c0c1c565844507d01d4043c285401c10188000000340401801410070140d040c46c0200058200100e50350320903c05807692420f17004a8581042d079200058080c18035402049003507a690001d400740e00122109611b0f80303200c1703203031509a414105c80070380030500880024042911618800030041e03c04d0003a1071107001d143d42c5120341c1c1038250f4602218000302003881344009041e0701c514030281050b01c003805281841e2900f02501d9204040340201003020004a0300c0d4402e006806443e080d0091542000540c5000c620f0648d0741d402540ca2030120b5410b40000e500d0140141c0c0380d41401c12560b2000c01c03000d0b9181c0e40032800c103e40400314040781682c070350035103124440c84402410150a8103400b9206a00740755000a260030005000d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 662676178 1250 662674928 662674937
    0xf0807030f12180803100e09300d0203060609060c0d02060714161106040b070203010c050708090f01120c0206040209100608040b0a020f1605011a0a0933080d 69
    0x20704806a000007010f148070f035004012594a945100340140001050307031203110b42c581e1190900c0031076100401c004040e804900b04140d0b40e4881c1e00524002108005030114141c80100300c181c54108168006640c0031102514161402d008140410a0b81d8004910290950413440c4c658040a42c10300100c3d41188503450031650460070024a801184240810f0b01d04007402543c10b1400c200e0b124a4041d0404030040034243c45650303441755401d40351b100c81001c03031182d40380500c3c0c2d5114030700580654400603003200e85a4144103005061003c40d103000c0300300702d0502200c900c152940180324020700708032420075805050f003820588180720b11039801a04841c1c1070369150070280400b650101280e0350050b08980844103584454907203000a00c15007248904800002418000780d4120a21904e441c030710501c020840c00700c0d014150960018100c1c0b880d83d100d949a00100079044860b00300c44001c03819603c2e40d140000c1d285054080d60b0016003c400465903805504004002c0103010320342000519040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 662677428 1250 662676178 662676191
    0x308030906100b0c030f180a080d030c020d0504090b0109090f0b1f05310308030f1501020c0613090510060807050901050a0c0f0515180a020f010c0f0807030f12 70
    0xc044d5140d018052158400e25004601e400101d1961200d0a00a0070007519120300e030b030785030300b81c0580340d6180c3c00c1480046410701c111a10083d10001d020b075400d4107960350f050f00b81410143c001001d0403600c0c00240c10480d40400204000b2001d10440c00b200300540c0340003d10ba0300310020303c5030345152038119441c81c64001c3ca203107600903001003c03180709415901d203064581c8a40e00442c0c01444d0406454082146205000b2041108031001140159800c01040c1000d43c5c510170038120207043d16808030700603002804e0020700c9041400140c1791000c86002d220380ca46864112040403108109d0710181e81a4100a0070007415030002056071300300800340745c0a4603007201c140c006041c9118210380752042045ca0058102030120016000381070682c07050a9480d03110380c000c1c58002c036200903144c4900c60741410501c0f0740348100c00106541d020358003034108040c03204180019962201c1c0b4030826104621803804da034000030109002001c01d60700c03070741300d404074030180d108010402c90807a400f003a4094903114 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 662678678 1250 662677428 662677447
    0x9062d02070818061918080604031e120e0304061b1a060a09021204060606020307050a06050903070c032f03031e131202031002030c040b03040c0308030906100b 70
    0xb02220450701d40666610034000141e000324a003889401040700d224503404201d505456804120700343e0918152802106050315903144a4480a05490003004a40a1200444100e44420510303000391210300380350019030904544141a1502d03441503074002e400000741480440c0c2c204204400400036061081c001003100d580c1d40c45070000950055180c1101d20300003885079600e0580e00005041600d6080d52144488a0305910700356003a1003c8480504061780815650f1000041c2e030541d1f0b420000500c8045103546880c40103010250204c441804100240700216031039500d0b001c0110320881200065400d0340700556404009142d00c11080310000c070740b81ca1107a40010540340c55041c0e4042c5980311510b20207101300c01d803091400140590b80e461394001030701c185071145d4800c441d00903420b0318228219582d13040203e01c021941240d00d00002c1c00b081c000d40d90100055507206116041c04200203071a0384900b4800c1c0c108035506400b0f640413104102c00503a084500c2c1d0018900b01c0042c60500c2d0024 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 662679928 1250 662678678 662678693
    0x11010606020d1d0607120305041103031e03041403032d07050d0b03070e090127051e030702091603180302120f16050a0317061005030a09062d0207 64
    0x1e40c00040e025000300c03c0003059944010844500c181c1c044000e40014441400207409482c5c00c83d000d0300d400d1032541480285040200444200e56494004000345550b062400c1c07074103400103402542d52206402301c40c407062004100a5000b810030000c41a05c0c41d0140c120f0340e40e5078840160681c8030008030024440c855070040306440e0010a00000443d1a24180780880c0c60840700760300440e01d420800f828040240410742c00450382c180c4030707441d414580c250b90944c1e60000f44140d8000f130655000d02010008190010500f009484140701070341d10b00000342d0002030b04400250340d041c0c0b202210400074551303240c041c0f143d00e100140c0c815072101c001030b450f200a5100d5400558102200302e00080b43c0c070402d0980011202c040841c60b01817000761071241021951249000320440c04180041985079540c0e02401456100780001002d40c010980e080c0c00441c0d4542004d4032001d042510381104000049050050311b86004441c0001e6002298400c3c000c00170040031092440000c0c8100204004200351 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 662681178 1250 662679928 662679947
    0x30c2d03010e070e030a060c0207060e09060907111c11060613050a0b060f0403060b01210c0e0d051f020f090607050a020a080303010f0b09090a0b041b11010606020d 72
    0x85011060a5440080944400fa0044c10032981030144404034420080e155108174401400350342120340c495100c58064501241503440d003035101e915200018070500d041c040680d031060861608164200c01c3c41c840314500340704c80e09901030881414010601440d031002d003020380c904100c03004241a007001c0d800301c0c415080244e00002d0454442d40010482800f0350007220400740c0141c02c4030b035610000ea807091540e030018002100e0030341c03c05441079080d6110316404804a002c000c0810b0020b1080410503000b000060f0400b0240014101403107100c1c1e88520f42010024090005402440c402550844980e805035001020040c0b060040b1008082a00c080e45d1a5400541c6d40a94a07202c50801d945040b40d0b860f030003548028150804206400048051070485085000100b00035855041001250003180b1125401014210000e04c0c40f02407500440d44200303001d40001103003464000e540070101d4654030a00003042400c0c078000d82c54503091007014000d04862014010300c042580004109698 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 662682428 1250 662681178 662681189
    0x30415050402040b060a020708070e0105150a090b0d09030f05030705040303030b030703120f03050615180a0e090307050f0d08010303260a06050112050106021e0c06030c2d0301 77
    0x240c920000e8115207480d030060001503401017405840fa541000002d5070b0b60481c0c01500030500450000141040c010468070303050300c4004003c49203031000800000c1090b001f00380e03070004001c03644500107017414500001700784004c007048012502120600b00600354000706030202041000c10410005910b6005081c0c4090380ea05250208803001035000180c5010b2260704007501c0d00b1141c5142d8070754685c010401001412450310140301690303034901080582030121000070040407041110580924044080c006580d00c000d16800341680c84280184808034101c2c0c0c0090958400180300c010b00904208280164100b10700601d204105e0b00e80c01010200e06103c010140205642e0f80d01601d0b000c50642c5005424000714a00d552a11080781000b03030095116450104441c0d0700842d890820364000c19042e1050b5800512140f2480c02c0002c1914842070344480d054060030b03481e15039039500d8000450044100a07001611640a0000c114807ca407100d4001400c0d10b07800076042600a02c0001d5904450 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 662683678 1250 662682428 662682431
    0x150306120102090301020a030e15010803070308090316030f1b02030705090c0d0504060911060c0d0818060406050402010e18010e0601090918200607020d0602041523030415 75
    0x1400c059046019010310110141d03d94004a624010140d160b400300440c00008400c403960000f81500d000c240c01d4080c0650105a041040080c011a000d102c540e03411080c0f07002101d01c1c0c500d010074915000c50300c8000c01c0300090508107680b000142e111a448003401c00400311585511080c2d80040d41d41c00562060900503500c00002a5155203e441929000d0704034160502044c500351511900501c0c0222080b1800340c400201a455400d00700c060f41d0540080800400c202d5800c4071041d907004000134200c203004041c6025a94102d0b40621405008074854203010401d810301d0320025001040340c5078241d00482c030040e51402c011240700d6581d411280e640b010f00c03405440c0c5800484590505d42c000140c01d90500005007828409800c00c010402d0040d41a62941540300307a4140f1500310700552640c0c4010144111400340c58800202ca030038504c0313450700524165a035004c00c1710a24800800c81e000c150346059401201c900d00d40300726441c0026290072851071410317949203103400d100340e000920707003d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 662684928 1250 662683678 662683699
    0x2d0e0c0126040c030b132001020303060409021906030204050a0b09030712020f0d03080a0f0510030813170304034227060f0528150320150306 62
    0x200d1403a50f40005180c00c6002c0300000d180800340c2d06011040348400310780b001210801300417459803000b503003030301ca02050340914030310340311842008045c0c40d28400c2641c1c400f480d03044201501c03807140900d20081030242c8015844620307003001c0010b403129640c0481e038843c4080100003216603001c10031500b41c0d1504540e4001108481c00401d0b80c0032900891660070007030702c1d0500410b040d0032184075449a000c0103820320060094400803401d985050790b0101408a0b0481c1c24000100080301500304441a03614012036240e07110b0b03002c5020215a400c41d605900001010b0051000032114070340b4100050230344603c2a04081140e441e0740c240d0b4030140c031000c0d0b40071351484c030103802c0c40c7c01000b521400c962030000c812840c2d0b52800500b00c5500b80460384145030403110303410100e450081c2e0303210728051100c00300c003840d01007810a002841310519001003956551806000c0c4125151719018502403e18a6800441101d4811514040c03411092180803501804500b50540b501226408401a281c41100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 662686178 1250 662684928 662684933
    0x2152503020906040e0108011d10090503190f090f03120f120f1d06090a02010c0f0506090705090702061027050c030405060c0708030a2d0e0c012604 65
    0xb03014001c0416403200001a0024500426025060584100200811411040106040c40141601210700c49078000c07401101a00b00290700284605000b081034a10304170f9441c2c40f1801701c00706100280040741d440d03c00300110300e6100e0400c00c003809100450301106800d54403580300380440c0207105000c21801107128288140311703030341c01204040c0b184814429007801800080203003003054851082c41a40e007034840300c4444002840c0f4000c48010380a032440b001603400459962003a084192500d2890348250400248200400e030b11548070748000e411003074208070400015490150040d421940101c0a101700c1d020b200565030b084031000d001034143d551224151008008400e54112901c6181c6410031006841850055204034403d4054801e140c0c2c5110000c2c2090191b158080c00002060001030368100c3c4903407204845c000714440800100c00f0464102040d0b41500c01d425910944500c01881018000c0002a15200090a102d1041401d0070bd400016a135400328028020a01e200410103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 662687428 1250 662686178 662686181
    0x90c0f1d01090b03040507050f06070803060409020105070215031b031e0a060b160203150c0703050d06090207030e030d09081f15170c030a030905040e07081b0102152503 74
    0x200401801152039141c9810041d40340c07d1030388602800703640103030000c0503103203800b00807204000d50001040d800c545555080c00000d06070b0700300413818050204980c9000d42d0b6000d605c4000c03d040049002d43d0392801c0e82880d080a2200d20301c1c86907000007442404003403140140c1c904403031503500c00c034a003c40d91500c581c2c5c00a0810355000400d45400000c4451a20b4018010150618000c0d001c0700c1c1000d4841c07400010120b03045524507102c00060200340c0000c0d10a85c024100d0314603100c008a201c0f42c07202081001c981c00894114045441e042c007101082c1018404900306607000e007421010030b807910040c1515a484001d0000081242c900800c0c65682c550303028066240809814408881c2c603030100d0743c3d424810083e224039910400034080744929001660406880d450fa40c2d034000f5134600f0303041c400500b00700382d040250740c010b40f00d002ca85c010041250109540610f81d404086003207800029042c50104240c40300301d03d42a4081011009400d00b68002e107160405440c0e00b0074094440c100c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 662688678 1250 662687428 662687447
    0x50906010e1807030603020918030a0c080702090c03061801050108010902070302030c070b031b03060604060c060b090a1e09200a031202060106030e1605060c120301030507090c0f1d01 80
    0x40000c03a82c0500014562542c45201501c2c0700f0703a440841c0e61990f2151000d41d400001c2c415801794010826900890310440c414100140f140405a0909003150700107400e00400712402050303c08081b041042130310f03044c203100c1e00140100040b4883c95061500003803003844140200280c07540c00051901c1014420404c40d010111442c058841460702d9a00160301c542c41542c8084c05542e62010007417a100426007107070b01502e030050402d4505403a110b401c4d500754149103000c2e603245036246507258280c0c44243c180c0d0700c01e100380500009c59180c2d09045802e6007101c038005211031440c008003600002c408070308480003001c45201c2d00d03114081f070400141c0d04000316040240000c1164056140044e00001c00c94140d4411f51007d225a070b0740050030350f80d10040c1d0f00c450aa00450dc110801542c10301c20020f085d02c03c00d0348142c521100c1d01c40e084d40d850b40d0003a030007102c0076400381c04100400c94052141c1d1101c041c1d035182403a04500d601c900100718131a20001d19045034055442541c11b40c2c006d5903003a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 662689928 1250 662688678 662688709
    0x1030b0d0c150e090f010608060625080408100902010f0e0102060a05041707030201020705061302130903020c0a0f090e0a0308010b0c0c040c03020d05060604050a1701150b1305010504050906010e 85
    0x1309010304d003000c1c1c50141003400303203c0d1002203180d40000c00c00b03515201007950b460380000340c8581010300c18264141d4201d04080015078a1007000c22000ca19000180404a60070510410100301945a84001030000c00072003100420000d4101c044030440e0f03400310301107030468020f010124071900d42c1e041140d0f1220601f82c400c4070003040050403104040e0190098030001c0d02403410f036421990340c9020518038641101d8001e5120801030f51510750034078a68030880d2154000e1040350380d520f000b48013050b0001d5040c1c11895800100c010100046c00e003078000c031141128088041d100c107030601e41d0041c0c080403060062179071241d004140f06c4a03480041080d1800703000024801d0000d07000d00103000d4000c0d401b809500b41c1c20790030200064198280041107404583c0d0240c070080d00e503441c1030106520200440c008101a540390051000307810b05035248400034040184c2c0301a035901240342e01c000d504049500241c148017042c40100500d0755510805a4081d1007800c10400e04001070001800da141d988080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 662691178 1250 662689928 662689939
    0x20f03010618050a050f04050910060f0306060803090901061d060f032502100b0103060317030f2805060409020d0c06020f0114010623070b0601030b0d0c150e 69
    0x140480e4042d0301681e0011000e00903400d81074840d024000f0f50301c00d50140303540000710500b1448581c02d00d544030036480140041524220400010b101d0184d400300d9000780340d17540a401061040c0115485201e0051110100030b40c54030301102c1c08100714040500c160b409102545c20140030042066410b1100c82d5030007041156115800c070300e04003064100780c0e08a00720a11030801c00401c2040c40040c0160130b00075400400d042c1c001801c5041c042c0809071002410181c072508008001452017441c034542a4040308841d8980c941403503042041c2c1d10090884688103090404002055000c2040401210542c403000c269680d40764080b40240100510003504401c0c201d01c00d100b80044d04880030259041ea07400e8842c01010345000f41d00f81c541c1a078200646413a4980104880c0d0b0159004622400c000a520300c40d070300c803401c4a980b054020b90301c203803803000c06034041040320341c0c2c0f5100e4178294441c00c42e14000c08543c25204c0480016490265144801c400180017400790b01a022000b40c180e0000c28 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 662692428 1250 662691178 662691181
    0x421020d0b010b0a2007170717030307080601090e130311031b0c0d0305031504060b030705031b03040f03080a06080307080711010302031b030c07020a15201f020f03 72
    0x10380c40d40d402205100700061205000a035140d00301707490801e403000b41100503c02c10707040c016105032420b0032200c00e000c24416014001072020340300348013640000c0d07072002954807894007040241c05c005000340000e04010700c942c010702899020202c21500644d07468101c2c2d840c29000c0ca010745400a040301a00c1c40c82c4000300d504082440c11200610741c0b04500021b980722084c1140520408030303031603030000300880c8081c400194071504200a04a00800092000c140d1581e1081d030b8808903401601c850001030000002c020700a07022214040349003108035001440c42c40e00392036001810900c500c1c02800c011958000c203400e80e130150852800307011080d054940e200094074240c141640007040495040210940041c52503000e4030035207100e101c01d2040407042481e01494400d0582c401811107469507404e03c501405601e43d1000340c0040c21040c2c4143d291f2407180d2502411801c484c60182c030510481205070035110034041840d080c9650700003520703055848152840400790180d544809002d01c000b20 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 662693678 1250 662692428 662692439
    0x2040b03011b0c0503040f17070e060a12060204120f0c0b07120e04110f070b100501140c01090c0e060306090606013009060c08070903030206010501080c090a081c050421020d0b01 78
    0x238240c45c181348102c400c84680c1340e601c92103800003800490740990301608001042056070500c00c1d00440300b0303228480051800d902c070900f00261610035041501c406001001c02c2080000d41c005a801400c40d10039603a06011a950743c140c4c020b82d40c400c2c00000c1200380c0000e6803240e100c98020000d40420345211139260b8551002040c0c0c00d4100c11000d603481e03d07101020400000c041100c1c481613800603500c03951391060314850200154030003903125036550750b5030f0302a2000c16800c013101006801c210b00280d48900704007007018035204028000d8026034000310107200c0180e0300b10a0740d83c60600e948041c40c8455503824004003c21009202c4100c00c00e04080420b0104805a0f00505e10b291050f01c5500a0b40c0350301e001111000c0440c040240903a12110041c401c0d9801001516072100117a0744240c40c3c1402140860240340c0907501c03020113035200590003510000c00c0001c00803651114608182400c0ca00b4110040c92000614004e007541605441041075485104e42c0c1d4690607000400c1e41010359552 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 662694928 1250 662693678 662693699
    0x10522090f050d020c12060c0a0207120305070b07030c120b0112051603060f03030203180a05030d170105042f0f160b0a1e0c110d0201060302040b03011b0c0503040f 72
    0x3c4004001402441900421032521b8464480e01c03100d80c5005024a0380e641c800241d20398031200b02c8009511884000185808960000403079041c400e99480d500d031a900c1c41c0c404408800a0990410315081841d6a0f68240c1c0c40b90608031511000680071810803003160050b5840c0d0601c2000e444564102420811030000c80c034600c01040d4402d80d410080a0b40c1d070f240003070042d506404002c3c0182c0041007406030b5401031a5802500d10f00083c040b20b501603907400005d103004054015000840c1110060f429481780d07410343e840c01040c050700c0a05c50300480307440f1822141101d00c0e210410402410032114503034400030039581b41882e00034240741c0da400d10ba442400007001d03180d011520701540c0e10010f01141d2040c0146004404102802d0340c1c060801d03808813001d40070140c01c034020840f40c0c490030325400400b0002109000002c1c0c00000c2c1080c20360042c041543c080782c25890090f81070044d10614400000d44051111000b49004960841c00d4601541141304079800400d242d020072001003040d900c01c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 662696178 1250 662694928 662694943
    0x82a0a030b0412050f03070c020f060c0f060603010e10020d020d06030503131d040b1b0a410f0d05010e01090e011a0d0f05071509060503010522090f05 66
    0x1d803c0c100c2480704011800c13100c61142482843c0b1945050001c241058005c0403150f20a520003400082c00c50141c03004608503820046000200c3c0c7d104000101c0d0784d90040c0038560300080181e009101103500300304032555813420160b12031060759000075041d00c6000f03da8180c40313120085d41c10500c00d4650341d007422039917608980540880a00841800078010892f48c141c00410218109103169694880d146e890b103195000308041c106500c043c05d044485000140180f60030703401d503180c800662800d201d6070b01c4039240d52031102d0b416403100c4900071003040600c2c40c0a02254600407090340d461044821982241c080c2d8600c01d076010b401c10b80040f5460040c418144e050300c020250800c905103040811a00b40e03101d200f4800e029a40011071f081c0e06007040200920486c3c05050603c89041c141d9032024a024035940c0304080c04a405e100c03118071564014400c1d0010000d6250441c199410700b80069402c04c60b041070b400c6403c5032400c1d0708003c5022a0882000160401143c0140e100c450800d0383d105e414 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 662697428 1250 662696178 662696183
    0x140f0a0212030405210f0609071a09210304121217040c09050705090a0e060102190b010603020d1b02070501030e0102070c0e04050a021207050a060801082a0a030b04 72
    0x1490300584601c00029241141c00082540d10324110850a20066210300214400c907030151712010075a000c1d0030440c203402001848018003c1500e8802940300032088200c01101030401000394005a030f4174606941980302c0e8602e4103145003c000143d152951040d507114058410f41c03418040d00348082821a40054111900d0707002d0010b130002800906010100c0c0d005003050010407050024065039803203a940020305081c000d2600030303124005220070019501080d10211030408100075540c0c14000c0038905650400403202c03012840d0350398480e0040502841c801c042e80400c40f6012041690060110180c1c0c910036120081031880c4002d403aa5110301542d80801c1c2440341030b6654880500c2100c070115005404815071509001d0b40c64003000001d0806d860602c60b458951025036522080c00b150f01094400500c08076181c0018402d0656250b0706c9036061020510042111070f00c0400c03000c0c5810306142080595800300e404a00c10001c6582905411500245000c02009044900c050082d130 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 662698678 1250 662697428 662697439
    0xa0506150603060d0f1e1506140102030d1104050d052104060212070204091712070206010f060509131b030e0304030f0311033f040c0b07140f0a02 64
    0x90100c0180100c0744400e0f5099074025100d04072410105000c0c409101e100e610884c03040818100d2445000f41c2c02401c40025203102c02c1d0140e8109040c8106d1080c034000b000c840300c10136040c1c0030130000030791603002c2c4d03000c54036401d5110f50700e04410641c004215400b610005040800707080c1e003801d040e6a5440b0385010b8280e64014590240e02c90b00d8018103540840c1c0a546c000c150008650340840d140f81c010ba002217030499242da0007140001d5090b800691340400480a41d5110203106104410f1404040c0a002c00c0d0b410480040c440b00109440c00c00540d05141881680e820103a070205513045040d8000040c024a82080303461461444101805070010541c2c0038485036000794140c0e42c41303215910004100408000042000078094643e00c7c004007a501e0540c4c0c2043c3e250010b4001e65100c0905108500c3c0e002c0748900e024000310f608241c0e6904100801600600d0305644400400e06107001d0f024400c400460204104141e0001500325252210247c42c43e411700051207a60741d49611400301d1181c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 662699928 1250 662698678 662698711
    0x100e01030b120d030b060d09030806091003110616020a0618062c030a05030c0114091603020103050603070503070308030103060606081605180603280b06090907030b030a0506 76
    0x38508000320b01424540880644001409000164024a0311041558000d40148442c1313080109912030750320303118025161a865850000104010302400514000302078110304014404640c1221031100f0303541f025582e0503070329075092008150807580f016009501a080407001700f079403076014640700b541134407540c1940c1c90301e610750f041503034200303802c1c0c0c0c1d407000c43e0399a0030580300010999005042c1c07010001c3c0c00d44104144907161141541e02888419003160744540c89255880b1700000d134107030322510140240053310080e03069070302c1909841c0b0010f4109512003001c201c060768107110346002402c005003100e2440356207103003908140d002403000341e40341e524103200003500c0c07405900c0c1c3c580300b00c640000404000000302026141600200600c01d8800c1c61150441156211070380110f024040a0710001d8162945004c0c10340788180381800240000e04042d025415905e40009660801000b103440311265a62240110002c1011009840e410f105001b201014080301107030301402625042d9204400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 662701178 1250 662699928 662699951
    0xf02090105040209060904050414060916050a0506310303020f0c040203060a030b04150203010b07050c0a0f0e1e130c1d0c2101060f0210150b0d0b100e0103 68
    0x22401258a040d405c5001000b02c881c031071401c0c2c0c0c881580184a0100f0303c40031030000841d10724002e403c484030300f50717944941d409444502d885485032000b09411120100002e0510003c543c090040b660144450302c180005075885a0240644044556082a640e90055500e080c02591003071061604050760082400406240c1080d008a81c46000e000c0c001c010510f245a0f92140a500000c00c1591030462541d904501c8031818002540285a00c4280b2504d4035524100b050400c465055182d1040d086000e0030454421005850700465460491111585d07544000e88034a0303000c9810814651b031002400c010030070003100403640000340a485084003041e00c40d6203804c08818410000d0107200d0074400015003040c440f0b4014120756000e1300c80803540b602010310b1607070f10410a0b004400030904540300003e16941c1081260308106c01d0030001d1000010446210100203030500802d03803000750014100347d81030710701d4200120a69010384440e9658074103100c0200b401101450460010b828080304420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 662702428 1250 662701178 662701181
    0x30a0509011205040b160c0204021206030c10140f1606060303170103050616020a0203070806070201200d0c1404030807020a05010f0f030c0c051222230109030605040f0209010504 78
    0x40f0325400b042c401a662108000c0c205020700f428041b40411001903070a00040e00d842c0040d0020700100d0a0a0000f400c3c14001c060030a140f50403072901031310010600110441c0c0c0504a000100160707400d0369a0f441d030810603528184540c50865032405d401185800c100165a441117007140e010b6503401c511804035610030582c0007401c0c8806810b40e401400841c1c645c0400c0740320308503511000d00450700d08440603400f090070000b07940e0246405410400400c04502e4080c06054469041e2640c00c04540c3d0302050700c3d07071300340c01000d20301c4291a660b040d803e06118026030300710403c058106541501c440d83c034580090158841001280103092078a0005125406902040c000c405982c03503000840c243d214040b4000c0001c02107140030401c003000810701003a828000c5140800721400302c0c075940c82c143e01c581c280c450030f000844480d0a01c01141000480c080710702c40c05a01c1c030840c880008079204100101c40d0001c00b40c2000e043c0500d40805d0004000b801031031194074600c00d96841c00310faa03030b5904000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 662703678 1250 662702428 662702431
    0xa0b090a08031813060810060e330d140d02011a03060703090c050414180a030c06020f0d050108030912010606050d050a090605040804080c060306060d05090f030a0509011205 76
    0xf0722191848400c80442d00c0c3c801c14007450010b041100050703082da2010102c4c50503407a5a40452030726540c031002c0c04a8640180e0300c035031083c2007142c0b042811800744007200421140784602040140040e0030f00090346d035144642c6407001c2d04103040f41046900e00f0303221610758441c41c072014055840d12143c0c104581e401d00d820017440c40004c003d0220341d42c0d04070040d805010341e02000c0304c0308079001c00c010407259030b944151520701c2452000140342e4905040688140c0722410b4070105280d01240b035400010f40d01c98180812550700c040003684400c0c0341503800c0d015020b42405090214104000442c05084c0000038040241045400104d400e81c0ea0150701d00b00d4141e40901e0002803000c00031681c1160060f080642c00403441100060038900d99100d6004540c004d41d0202c9109000040400c5000402c021403004103e08680c1203246013003800c0014810720803140304620742902e40c0006040c0c844144032000c44824030700b044d41e595981c4005c00400d581d10840301c29020075603031104000407102030f00c10709 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 662704928 1250 662703678 662703697
    0x1f09090b0105010c06060b030901020405011101050606040b070602121810060e150f030601030b0f0108030306060d091b03030f09080f07030b0402241215030d08090a020a0b090a0803 79
    0x103404036401e1400468100b40c1108058403090703269000080c07003d141d01c000398800e006680c00141ca480c1488001001d00d10301c900140c0e02c036030420050282664818080300c04a440d40e5102030f44d248514500f8a0107401141c44055004120710100201c4d40c600441d1144040000000e803000fa1034080001004c90f2950f000d00701e28120f05c0b4000908500303c5206019800304020904444000f102c00002d00d4560300341c004442c903200140034070040780f041d46003c501406110300035504600d0700e00041242d038069a510f2004854583c0061070500450810031040000161072070b111040e228100a048214440b5503100044c14903140010292000f04040b800c41d0880b2002c3c3c00460b01e942c0303a503c80f12501074000da9118091880d40b0300701c0080d10409054003069030f0400c0d40c072910101c8802802d42c0c9c006291314000d40850940d604141e60100e035041c1850020309105029855070f5083c41c0c070b040c54440380207400001140b0701144081819000c0c4c101010100c440b00c42654403081003a40324010030015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 662706178 1250 662704928 662704943
    0x1c0b0c1c020423040c0e1210020d0e070b0703020a30031d011a041113030c061b1509080c010e0a050105070e060304081e0d050f01052b06141f0909 64
    0x18000b4915101c43c50440c01d01c0c46204030340a48e45130000032401c0380c0c03209030548401d07580d0f8a2134195020003403080400400c1140c1c08a4103204131901c000c0d4440310755000003000c2c1074110307407240c0d822402c4820290300d6a407101c40c00740c40d80d03040070809002809003610004580b15100c40003008008140903800d0144071504c3d03000d464580403c00c1c88003910320b40d1200c00e6003800502c03061500c0b044024034030004500440c040703d411850b140e4007504803400d64106901000d00004600081140d84c03a24200d41008407000181444082c2842d00302801200644001c7e0750804074101300c089800203056100900403c001c20140d2030f0700c04150ba00e0307084000041e40080c0140001030103e42014003522000a401d8280010352641d041000d034242d0101e000080b07441d940e0310504c4540900321400300d015110985100d03104c03d0142c550481c45d0f12034110781002c05001c1000c20030800c10150408400642e081d081d0a0203410100205c0c1c0305079416540c018552604c1c030100040b5152180980c4a02c160803688 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 662707428 1250 662706178 662706197
    0x5090f0a0809030a0204050f010920041e151106010509090c060309150703060602010c030606120207050106091401030213110a111908091c0b0c1c020423040c 69
    0x807044225009242c4059150013580c4019000d610313240a10303032080070303522418040340d0306004680717048801e07030508070008020141190800341d85107000c81d4184c039008035140da41601c041c040101d018031150420168684920002903445070040303610101c1c0d040040a42e010303aa02ca00c18400340030021100001d81c0d900c038400d54a841e0814000650300007600c602039540d00b115182d05201100d4080d12072000103035030350741c042290702c0d82841411940041c5e407130188070340391800800400d21080a007001c095a580001c0c0b200804c00c0941c4000014042410309020381c644001a0b500c03903800903c416401031300702100c4d140080609200c0c1a2008910b040c0c0c250429150300401c4903032124602da00281e600c91400040e90190b840410041402d105002203559030321220203004039003402405198040b80b0300e00f48080012142414180d0119500d0802e43d1504608800b030714a4903244103014100780e20025021078003c288004c40b0014140900d1440303071504141080c482181c0c0e02c0b0f81140e000070b01085 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 662708678 1250 662707428 662707433
    0x506010b160501110712030b09280504050a06060b0f0708030406060e041103160e010b0c0a1506080d1e080c1c0b090703060303050a0503042103090605090f0a 69
    0x20300325010710104111686041541c4043c2100c0381d10140d000c281c80085100c604005650041030400f05c00c515051000b82d5604012400740d841c058092103105400041c991545000400d00c521807441c24041842641000e09015441d550190015501e031070034030b48040752001c2d42c00100d0b034084110714442072810049850f4020290400743c41190415254500000c2d000b010b1510507001c1c0c0d00807a010b03241803a00c401014070713101d0511880300034074145500030804800602c403051b044980b075040c13850343c602110303001d58200300030607000030090340200704605d001a8031076024200f0b480180341100d12852070b07200180c404044009400307030070b4420144174402c85485042200e8011141c14181c90400da240084100132100000b12500415a215041001450181e400301c0d004001410200701d00c40c00d40e14004e10030b10400c084001840b0340080480c04020350060b480703801d10b105806941c1169280600140070b42420301041d280d807070500c400318141c00d201180c3d0000000c0480c00800c420081a03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 662709928 1250 662708678 662708699
    0x5040e100807060e0a09051f090608030a05072604090c02030702060f07030315090b04060902160b0709090906020c0c040c08011a07050a0b0f130b150607050f0c010905030a050601 78
    0x5424494102c4040721001031011b811340070300c6000d6119800380d0070000a0800c0c00140d81c1d1580e50100100a0514030100400100441264100c1c029464800e503204505c2c107101140d5048407005107401c0e401e1480b0080c18003118000341007615103800c02030040c8451104100d03964011100081d41c82041000b1000d4440098001000f41c036120b400c01003090180f40c0c2c11010300281035071101c00c115841e1303101d202c99440c26218610150210200850a0140c2001c0317a2100b03804468000b000a0180340100700c505005400120041c41a00018024080c6520b8444060742240c06413082d41d1003006c0c0e070300700070386018055180400c15070398840b61660303c0c04901d94141c0c5c048aa00002041042200202103541030000b00d60084c0a0305429445003000c50f100a04094001c0401203032a0400e01d031040000c40f13a0050540210341903030307424080e19810700003544a02ca4600d00501038030171380922080c800d40224025400c10760903200d56180d0b5941c0d4041c0758491001d0039004249420840c014860b18222 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 662711178 1250 662709928 662709947
    0x20102100b010f11150702011b210c110a030504051f0822020d060c080705070f0f1a160f030926041e0509010b071a0604180305040e10080706 62
    0xa80d000c444001c8040222081e902c2800d480b6a40141d4441e11043c6804111a000d030102d03503030b1403900c1418101040c050303d0221001101c40c41c41e40d07403202f00815456124018091401c0c1043c000e4601d1204180b42c003401540c0b1610842c2d000d025100e4041400c40320102148114030303a1515843e0a569401c207080313080ea1095003038000000ba5410050780907840e0403030301ea4201f9208240004200c48402c0014006400003410341080100400c4004000760201c05202c0c0515480603005070b02205070b1500e1410010340e5029503058840000802048601803583c0000301c5e40c10b43c031410721060220302c1c21000d0315540302d40a01081c8491b1101c02c001030b004129220301440440d030850600d52603081a511a0400100c40020000c805005004c10700d072070049240142422a8940e24008903550791a00c40c400c00c08243c0e0400600c00005402c0d602c55800c8003254114000d0380070700781600c3d490058526001030051441d46160130001458510050b0100c04c282d9903035000900d6040c0c0b1349101180c40300130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 662712428 1250 662711178 662711207
    0x18050f0402030607111905070f08060106020706111f1a0306090c010e0a0312090608130b0f040c0506040b0703022512081306030603060f0504020a0b0f040819020102100b010f 76
    0x18100c12501071003042548071050b00c4c82080071b003c100e846e100001103080789c15008000650001c10040004a40005001045400c58205150803407001400d07141072020400307075420000724000c03101120f0005580f0240d0403100e150b1850500c2c9074440c05041e82c900d8100c0308010b0540c4440340c090501d60194081c3c441d62030004200050b410703141d660b1f120801c010540c503400030400e01d48062100e16081440c81303078480c01400c84020505110748481c124208050312490452a440c3c012409000750420b000700601f80140c803003503685645220032200c59011074800e03001409556603801030200e01c200b07080906101c4c0303d40402000d040c810304400d482d40005c02107580306000c01862106071142910385004100f50b440026200e40fa41c20540140d45103210002c03809440c10040000580d0798404070010b54910058907a11400702c09603141c1144900d4201e4100c91181186880c8101101089400c03014802c1c0c0c2a44e0241d108080c0362800d565090703c403c0c2c04100044c1d003d81030244035000c0d20000c8032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 662713678 1250 662712428 662712433
    0x40f0b0604361401081606050f0d1a1e0f1012060305060601090602010e070e0a06051e0f06031e040f0b0f0601020f150a020d06050a18050f040203060711 67
    0x10700e00d25074440c030360000c1480400ca580d110000074122100f403a0f40140141211130103040c10140312994032010b14140c0c044d090074004c1c086403541d2981400d1094880500ca0380404000900b5410a04a801d2403141c0b886446081c0381801c0381c010040360307440306842030b2015000c4901900400108950070004280d0203040061000701101d00700004d014201c0298010406006941402000101080c109403c14015607060000201c1c01c8600011402e0883e000300d03c00041c1d07038481010340005003006a02042e40041d803050f403110a603441a000043d4400202c507548943c45207078051000601080b110708803a0f21808218441844402660541c400c4c0b041d24101407a0405640e6005086002c0e03034000c4036591003000f042a25601080079106107402d007401040040481c418050b03e80300c2c01090b40c00b42c02c2c0c010810080f085041d40040010341310007040000d0060310b036900036031680508115009403d08090200d002056030344130050096802074040d0040380e45009007518500a0700c40000c0d000e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 662714928 1250 662713678 662713739
    0x30603030702060403150f0e0d030b01141209300d29031002090a1a1b1b09010e060d0f12051206120312100f0b09040f0b0604 55
    0x603030b5003d0003400a144110820905c1c0b0ba851280641107444500e91881c44c145400c0d4150002440040c860942590320700c1e001c11100c3d01c201c0101d81588000503c5c003205034010070320710301c14420442028401c00c8100100c65281a40c10f80d00303040c801501a0030915100c01c202504144044030005200b110000c080109044208144502146100046041c402159080d84000b1440c090150300f0b201252500103604110030500091800c4403039229403400402245446840307400208d055989400100c5107504505951080140d21211001c81120b0b44208110100040b8588603c403141030725103400c019005079455100380130148034010001d80b210303408046880001041c000c0358690040ca5982c41c9500e030003004402030062030015142d64820044c40700803002401c8000160b8004034a406400f01858540380d1a07400024002d0300410048985c001001c0354040068005000e8000191010042800110300081c00c507085210243c1d84114100300030030140b03840c0c002648411800b4451580c82 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 662716178 1250 662714928 662714933
    0x1a030a0b03031207022413020f040e01060f1502031c0f0f02040603110408150c120c04030b010603051009020c031201030c081608030712030b030a0308090106080309150306030307 78
    0x40d6004002101c0d4580340c07040402c2040c945c144090021800040f80c000204e000b0503c450001c4040106240d1003000804044800e555600c4441c06030203401402c100079110408004a01030540c40c002ca001c01045014000303200954111030340c202c890309602660034040f0030b086030468079102c0e060030250310303884084103a4821001d1040101d2007a00b001c0050f0f80301d02d40303240542500c103e9280d082c02484180001c1140c0744c0045100304005e0404011051207a4034081201c05c070740540702c07121900105150801114a25003001070082e00d015100f180d1140e079981e03500f141510800c44400090f280b0a02040220310b42c550080c01d02078200301c059905001040036074403003c9000340c5c4150f840b9085c0354001c2250301010f0240807882003150070107021490501c0b010740c1d6030f4841e600000f00b803c0419002040028420340c001340784038130010f0580f0044129030800800c0c1040a036826001c0d540781080015242d04000304072810407202070021a0130300940410340d40c0380c0d00000c00c1c082d00750100700082e400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 662717428 1250 662716178 662716183
    0x70309061b0b1801151d0714040305030703021b011b080c0d03050412030207080715020409050406020306010f020106050d020d050c04020406020d0e0402130e040201030e2d0303011a030a0b03 83
    0x1080b1103920f040c0c80c6142d9680b0b9400d0035190a8412004641e0311060280b212a0400c0301c2c011306e44090030301e22103030342e12100021500000000b0344c0910202c1c1c04074000c403c200340400105003480c025401c0343d452420a501d03d8401c41850300541d8007045011361900f6004a00c2c0703450114203402414081e0600401c1984141403041c0594044002a51034003000308003c00e80d03854046032401840c00710b04200c01c66684010320710032110f026000d245450401c07800010b980c0c0456000c0d103018901407010b41030070701d0014081d41054070b0702401700c0c040b01d0003000c0c0c0500c14420301c400ca0b030005220000d115540e80a00c5288038601070141c42500481c181c2400d140c9840c001440100501d40c024503801400004c000c1c10040c0030b900da00d03c200d00400c11a110115141ea100341070b240f001000e0841a103407480180c00410b5046001c04c2c05000703d64140c05150803000b101c00c60a82c1d51000c8940c00304042c881307583c40b88024018529504009400b0100c03501d11103001e0b6500a00f0304000003640040540001d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 662718678 1250 662717428 662717431
    0x10b0a0c23150a0908030106080405010f0204060906082a09040b120309010906050a0e0f03030702030a060204050307080307120507031b0b10050409050a140709060b041a070309061b0b 80
    0xd040d68001c0d402002d004041801d0564032544070981040b09044c2941d0713071032051106114000800c0110703408201400020b41c4080262a50801c0455031a6030302c1c07501400340390070352152101141c801d40000301c0040400103140e480c0070100f100c0b0003c000092003a8126604855000342e0890f80c0d415030f80300300d034031400350021000c004140210703100d03118034000402c900883e803c21020401c00340021a882038201140088400b01211040d030050030b1540420b203180a01c2c00c000c1d500d13110b41481e0f4410711a03580d00910270354070146c080d500b105449190f0280e403441100002000490a002e00081252041e0040c12880c1e12901d0000c8032441d542840d014100540c0e1000d960b80030385401841041e0209890140007440306035402d002804072909c40343d44036244e51401610b1008412038000079281d0034052003015104d401c004014260b118200825a901706018019002d040404440d00081d00803050703501050f45541d0304d0b901e242c1044011903842114508100902407071800760707000110740c044100d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 662719928 1250 662718678 662718743
    0x303090f010b01020f12070f1b18060602060c0309160b09041401060e151902010603050f28170703050c061b040303031119090f050405010b0a0c 63
    0x42804141100c1030908459003160314605550010308441e50000005c1100031003100da13400e40d66112a0b05040c41c0460f0b040c007040c010004420607403511088945404a2001e0312614070500460624010185003140c10324041c080150744103c0c00039401b80c03c1c050040d035002c4500030583d40f031190040d050f403111304144c0e000791021003800300b00442d050a2070710541d07000f0408508424181d52620b0b0019140c031190400c5140107079102e0341d400c040c00e000042114941e0340c41c0021140441180c8200900a007200e02007220303540594207120041c460006030100c10b54001500c840f12140ca898032072200811405000c9a0f10075518464100100e443c00240002900a0f11500e660383c106a400324248280200803030749085400080d0207099060310300703843c2070300c1d81400c002804119605400115005202d00c00308480c611004408040d030384480c5044c11a072991100c2c61030940c8410400003070300c0d8240260102020240a2260002c1c415a11702440c0c0b030203141040700800101d480c9100907d0a40c180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 662721178 1250 662719928 662719933
    0x60c01061203030b03030a080c030a200c0105241201061203050702030d030608121305121501090203040f2a1e0603270c0e04031806020109020d0b0a0b03030309 70
    0x4000a160f018040c03800d488004801951402402e000e0140c860034026111080240e404000141d03007042c81d80c0064801901e101800c1d00360000314000b503069a0242085c45d5075542000080b5116098010401c00300b5030442c0017070b0310100d56850500090320301c0f001810004d9900d0b020000f8900e49180d06a031400c40c0240e65080d41c0364640d0050500d8a00b003003081408142c58070008100d2500e003c2841008440d10366034255540c10040c1034043c5034600341c2c22072075000b0008031104141d607a0001d00450b60702c05040701804142c0e61151842c2c100c3c0000c8602030312100202003206c001840c00c08a207c11411400d07282070092016450001c0140b11503006500c44103c65145803110110300c4003401c004004c2840d0a0241e00030b5640c0840307034450300d00d003015442c0441c8420f4800700b15030091503a0140c80260314202c128541800d0080031220b0301d81d0203403510790305c418001c290315106000e01c403c0d00380c0280c444642915690345e01d203c0101d004001054641d5140900403281c0d80c180011405880e41100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 662722428 1250 662721178 662721209
    0x906130e030d110a0206191d0d080f090607080703020415030b030709020a2705150405010306050d12200a03360e0c13031a070201050123060c0106 64
    0x20440129031544403c10200307107060000c3c9a85550025445510021a180148141c00c26001010151840c141c00420880740c007613036050140300008000f008810192385004454642030a001c09018096614015a8200d94000380741d4600400300c468104000e171800516099803003003882200e081d5407591500003501c0e0300950310b1901c0e041114101405031000218900744000c140940060000d0b0203080200090450b012001c4904110480050802500c0d02d0b82e68020140d0001055007c2d02034036020902d000000b240a05080320040f00c01580300c4000302010200ca041a1600044134003c41c1c0140484462409510420700100d100d0034170a4551100790045410300c0801d628132601d01081810081c0f40315407000071101c0b0000c045500c08034600e11141c40712404079084d03101d940001003404041c504000700f00f10490b140c0c003001d8052301c54204c0307040c0c6403c203040342600c10a208a00c0c4c3e821a6505001c94007000e070286086085c802444580ba04d071003601100c0c02d40c0c5c0c0703a074064009940410f1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 662723678 1250 662722428 662722447
    0x1b061409060a1137080103051207080d0513020307080f010e0a02031905010212010e16210b0307081606090b1303231605130204140906130e03 62
    0x1460300820010b02c10f010044695483c3d4042e80900160b000c0051560b070203a40c80721076640404400c040201c01c4507604020010405040c010b400c0c8421641d40c8540301c018010049130340305a9080e594042689403501c3d0020310920003400d00985010380703040945a02d0030050381c0030040c3d24000c080d4003010349811501000348508403400301c110040b19405c16214040142d5000c038052a803401118072400080c501410560300901a01c3c58004007909000700100c4c0c40704610420754403440c98a1001015200002400c448003040c034440100300580700c005c03160000c19580c102e10b6180102404441d0a2903681c4042d91401007190005c00f05850004800c0c00800d62100303164000c0d0500070885454601e003403000c005000d0107840040e1840494450300b106004114020701640900c4804481c5030982004e140c110710111407150f9440b4080151402c5012052030082e0350071205542e1105851044400c01c0c0301d60100000d0115074001c481a45031900c400441c0321324010f00901000464503810401c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 662724928 1250 662723678 662723683
    0x18040c020d030b24070302030c16031101021609050603030f0d1406030a1518060e01060e060411070204020a02030c06040b0603060a020720040f140f010909121b061409 73
    0x4100e11405214011035007050500c482e0704403448001d440295954480c0035080890541c049d90080b016140030701c01110048030b004481c1d0205503802100380390303042c100660040e079460050a80c944900003050404004000140d440940e00410240549207481c00d243d401407055441060307000c051550320102145500c081d90506540320000381d0003030188a076680c40e060809011000c000b00b003070b500c4443d01040001c613804000f048030360240c1c0c06c0c0101151101c0e0140030f04118000d111118050f040000d00c00d180074060711043c6a0050350f010320b44800ca4013400085c2d40f10759624402d41c4010402a004010100b00e42403085000c6c9950403a207041810405081072005420056007500502014001c01d4624420222800c201d0210074085804840400c01510b0300e0340181410340d14002c40c030720a44d41d5a00341075100c1c3d11101e52000c52682c8903030305901101c14606020b0443c1c8100d0b0203043d4210700810a090b2001c030810705440044c1c84540e03543c8260342585003012500c000460030f00840c007a04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 662726178 1250 662724928 662724941
    0x1212111204150503011211010903020a12050c03033f041214070b0a09020a080d03020a031d03040312050412030906021615050901110f01060315020406050405010518040c020d03 77
    0x45181844c955458074403407043c090b1009201900d00b403140a0311240c00e81c040c01c000380080d5805003209054a5072103900c550038080e11141034846006100b008201881c020007294100320036130309000b00c84140444030030309001c00040d50318200401d03e20b010380d00340400c0b160103110b248503e04100c02403a990380b00030454141c2102080b1310010a000350f00011790920141ca134040050840062b8507a070600014020389019030164080340104001492266415002040088081e46090114101500e0040d490494001ca041c80c41d400c140000e00004441c60500344c100f1250740f400c80c1c10039450b80e0098010282002d8110007264012004102b51030701801641a0210700d0300034101d18a1902c2009010002840d2102041081c00a041c040e640e008224115aa01d01481200c00300180c1020250090607103010030344140c010180e00282c040c4850086900781e40280d5a9641898904001910035402040211461240080c090f00260b20b4030b218552001d03105500800c0d5000300000c024044604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 662727428 1250 662726178 662726219
    0x7140a090513020f0d230c1504090506060c010e07060314100605030703020706020723031806071113090312060509180a17041805011212111204 63
    0x204800c00c549440304242c0458056015203418040203490000260501035907400203041c0030090f21a40b40c2e60b4170720784d020b41a500300d02088502d070807804803c000403ca400c800c0711000c0c03034041100313002c045000e400c800d40002026280c50304006090700384d103094030403031920030816a204500403c401e560602a40d4002803890b1030076607141c2018038400150410368000c2009025000000c07a01c0f45101c0e03330440d00d80c59005a001c544a00c482c4c54a816404880e400850703010320f260040303d0f030340c03003020049510000c0c40c0702c2c000c1ca095224000384a03882d00b003010242d4041000038001e07680c64a6641020140c142d00500c00207550001713250103400380c00c0600300b0f0306e00b01d480d0610511180c0c856040300350700b0a80703240747e480c9144e15545030280740a40c64000104220308280050004203034030f001600c03c2d10326180081c0000d074460400c14013190f90901c207615607980012007000214915082c0304c440d0b441700d8900318203c95058030310f16184c9480c000c0b140c10b5803040081c08020410040c401c9104024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 662728678 1250 662727428 662727431
    0x20f0a050102031e01030f020420041d0105100207030b040f14010f1118060d1503140d1e12140903071a04080304031b231608060c07080c07140a09 64
    0x5041d87c0b160322000b07851100090013256121185a40d19071803089101c09080380c441384a50325901c0b01e103508511035158a201a02d040e080d40082251300e4010007400816040385e0091007118999111100b03c1c10000d001515907a503183c4061010400c0c04400600d15001c00001003081c401403100c100442d8031001319003030302c00c00500c4038070312552110040303000d008022180281c1b00c448203a4014020016070071032100c440f200340e40001c20010451000c03c480342451080d5003084041e0304050b1805216200c1e18201d620b10040418417580c01001e00c0c00d84415011000180410b2241d90780f120120706070b604848a44c0007044a10400003055000b0030007010f6040c10a0f61420140d5510649000c007910003424010000c00c13000016a40c0d003400210160000c03290b00100f00404111503005100880c9a01c65008441c1152440038400103540c0484405078010451542c0384070300b09883da0001c80e802c64080e0390030005401444000c200d410081c00c825428111002c3c001003c100c0010031590094220a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 662729928 1250 662728678 662728681
    0x3030e0d051011040510080405060c04350a051b1203030c03180709060609090902010905040e0703172805190909140901051e04080a020f0a050102031e 66
    0x218042103280000503042d10101d10b040350070440c0d0945000d80e400ca10b4000250700c00c0d8481c483e910159460045005038142c130b0070341c0c03104840c042d4507114070301031580041c1140361004404219160040c2803c480308109500b0045e14071041c0703090076040700c005e035066481006ca44800340417481c90401c0502007107511070000710b45000b0b619183c0c080100b0408400d803000c000a210316119500c620705541d0b141040e5002a62103010b0032000300546e004a000054491401149016561180c4400302d0b8050710b5043c015850b05003044060901c085030624640607a03540080002e1424400246800414841d544c84040c00202c2406940c03404c2d08504250a4a03560740314070940120403107039082c060028610090042080984c3c810b02c0c00c1d4020700d2034a00e4984803030b0007000c0b882074050040c616031009003c151506200c001d800d030200c00303c03001128980380105001a1035040100041c0740c0c540165180d030203014412a0800100e090183c54036500001000070b0080e200003200d805c0d40305030600c0240c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 662731178 1250 662729928 662729933
    0xc0702010c1403121602061b180a0803120402040b01020606010c0b1b0a0e030d030506030c011b0605011e050117131412120a060531021303030e0d 64
    0xa21445000903000c160910800094040300f8411664a010200c1c01002c83c1d050240c0101c03c3e004404209000502410020949450408140710300d40c050321040c0c030b03041101c03c10610920b0107a1011baa0b900400301c00000442d08030078006031403e40740342c410304001d03403074140144401e44c0d500c041d001d411900090b003004041d0780c01541e80701e60300d50007903489041691070b034a50311810920000641580340011503104400c41e401510021555810307420341d4042b002250058042e1b403419513000340e142d04049052001c651246a807080d0a0f02c0b10400c016143d00301d51540411500c00781c10030b004070501c0e0a1404005221b440d0004000d00c001e28100202030030460b01c0c80700c5541301a005c00c18540c241c004d10814448402e902e402c001c0c1141c0242c904100d0000c400b2080e503440015583c1e048051040000d83c0d5a10510034041110005001805100307400ea000089010705480d04904600301c0d00880d9910662600c05007050210680081061031308505000d0008800005103074840c048000e640f000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 662732428 1250 662731178 662731187
    0xc0a081f0803091e1c0807060f05041103061501030f0902060409021201080f1b01050d052e080d050702062506061203020a0212070803030408030f060111070303210906060504050c070201 81
    0x1114018180d041d4403645a2078442001e22a81002405060602c009e00c030300340c3c00d1980828042c610440d21902004d588809154a800040b1441048411010402821540aa04005580300030308200085400f8240e0014844c2d400c01d4200c0361107107074082141460800c58030301480c00740c90303580000c01c002c44608071300303c4c1c0c2d070f0144000c41c440c2e0381814500d40c0071705c1c1d0055007a41e4002806aa007444945043c4090300840307034040310303100034800031100512000302500c2030610550761408040d1009a0184500781c0d010b03846030350704036084042004006100100d00c100c004503505000d40c64000000c2c07500300304040c0c4000b6000208084e00070b940090010790000b039002112941598565001c529400040f401c081c0198080b481600001081004000301710005500c110000c59071038100792100c40045901071240c49403080d83d40c1c080c86003440071a0040c684c4040364800c1d1000d0103158141a041310099880c521811114507840300c10910451610f80652584607042520060901455800082 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 662733678 1250 662732428 662732449
    0x30304020409080c010513060f02090a030b04020a0b0c0f15010e07030e0c0604032a0b160804050d06090501111e0c0109120908060f0c0a081f0803091e 66
    0x24403403980c031500b6200704814070040e18405441d90000f04401e1610701014004c50031034a01c1100c4036880c0181c00042c1075118425185079a0f0701034030654500b81540e841c800901c601800603a80002840c00000c1d0301034548004084d1030a007100500030810820f50b05d1482d10640c0b120100407403107540010321000607003250413a8000c0380c514011542c004c001261b141444d121103455a0410000100070040c06600c0084813500b16016008080f500540c0d0802c10340022507000312a0006001c024a600d0315148042c031046040c0603401d0946041d0391500054050718540701d08990182d12050b0350011b000b42841560035140002d04c0b201c0c90318401c0325800c80329015510303140d886200c0105402212020941c0603403040f40e8007118042d0b0480052802601481c140d100710b69180c1302d028000307483c2070780003d4110f025002d1301c000107007442e02c094800d8540c85001000410607140030701300b020310411498400b200400d001806107a40d20035170010f000c0441c0f01d43c48c10380082d40c079156148803251241043c04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 662734928 1250 662733678 662733683
    0x10608070c02040608070f030c0515041205071511100605010807050a0201141f081f022206110c060c0d050f130b090a06020c030a110d17090f030708030304 68
    0x51001c40d0302480014010400b6800c101168850610085070398112003542c2402da83c0a0990204031a60318001c000c8031010700b0100016040f000e000c10003c140c0c00305020010701d40300c0c50607a99078544901c420311910507090404000640c10140c4111114010f005848810014207070034803166041c0b0002804d401800760091040000c0000c065154034801e40c05100035000d8240d10450500b00b000280003040d070252540606400c0c16030380000d14010028110825000101c90711030f501010301c8040c4000d4000d080c17400c0ca007014a0020801a00780e004081029000070380300c45103003546401582c0e24000f0501d440034090a000c00c8000c1e003010b000a80c032035050700340e0b1600e145c1e90030200c00c0d00c031441c1c0110315036600c0d40800382e140825215062406004001030580d00b035080c80b940c1e48000c0769900c81c0105101d40580201241c3c5c800f040d400a07500621410103000515050926a50505c0c448034008411080c0700000c00e040318640740420103849208001c03001032541d0fa080c0f1080070749a00c00607100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 662736178 1250 662734928 662734937
    0x10905060309070b0c06100617010501030902040b060d05091b0d0b07230c0607080123030c100e030d05030126070306020c06071202040b04030b060315010807170601060807 75
    0x20900030341085010044d118003140c00c2e0f21102e101c14416555103055911034040380c4c44100100b503143c494503500c4038007401382d039890030709900e007400550081440800c282d8010780c8072814680141c83d507500411085013003800004551920303820181c1850b0400404200c2e564503a0b1101140340e640030f030b1401800341c001d450000c95444003401940c3e102651851041460f4014141d6821548280080d0060600c07081c02c0e12070315914040126000c02e0240141c80d403011042d07100c05004000310700e915400c0f0301c1c05070480e12419403600003d420382104c0c41103400021800002900389090600007500300d0400c900303000e42194106106501e600e215100091a0324071490f640303078019141044544c00840d0400001c65031031702001903c40d128401114420046071404a001025400503c220780445131810a45814141140d45100c041c0c80068040381e0b041c0b00d800d00ca442e000600303191031380c001c00d14180180005407800755184c0b80c144180325203407642d03001100100400ba0b080802e43e0f500240300d250 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 662737428 1250 662736178 662736181
    0x3030c0307080d180803070f030b01090605090d151505100503061c0f0317060108010b0d090206040317040825092a0306050f1e0f0d050a0627020109050603 68
    0x10500028200288420200000400c0801c180400d64000f0747c080d4195545442c0300250010064003946d98003c9000d000589000040060f0b0784074001901c0c4480f0000c1c82c481c201c50081d1910422001c41c0000b98034040d80e101c160b0a500b07183c44809030010142a07442001c28020b904010300b07180001800b00e40210082c4503611280e10b045104611416030150f605078071041641402408803400c071a00c440c8070010708004c04c200d98003591444e412120103c1c103c034540402503004002502d100002260862030900002c0000355000c010a076081804408080d1a2403616200d50329041400c4203c100601c0125824059100b0780400f0209841d000c2001080d001084040b00d103410010710449282c50528002600c00d299154100d6411a40b04032807100300c84c03d1190800503001c2030118001c50140703074000e10301c106040030109040e003414000e140d603202c02c0ca6900c6540c28404091402c40340c00f9642c00c1030782603218682d44403810b0809412000c1c2d00400445d40041c04481c464091644a40070100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 662738678 1250 662737428 662737447
    0x90807081e1005070806010818073f0233070309230a36200c100e061506190305040203070b030408030a0e01110a02100b03030c030708 59
    0x840c001c401d82d56844100418940a000144069402e49105002940440c0496440c42214080c400003d80c814050001980703401c0d90101c143c4001c0c021554801059404d0103404e2860610710184001411612083e020003441004a61849400c0d014400c01c095502c4040200305513207003042c401c1920a03000e507501a6070a042e01d800071154040e4081031a8200350f181598040c4507a605200c5045d2000125551606070211407000d2084c6032911894800b0aa00524540c07540b0400c2920342403080019209900e95041d00107841400000d00b044c0740c00103150264200c108074594080018a07030400500842030685503d13080043c142040d212011002000d09540355001c0360740301e500d852025040c1a451010281c0a400e040f10180e105c1d005401000070710441d62000c4a02c01c660110000380b0303680d504041c41d401442c0901040e269036617241000000000100300a040c8000030340c00401c0c0c815510000401603400c5040b40070701903003080c00491800b0400009558400c0e80c80040c00d80c031047c111 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 662739928 1250 662738678 662738683
    0x61009090510050112050f010b010f05090f0d0302060103110108070e0906221d0a03051215180613060f05150d153011030307061a01090807081e 63
    0x103000c1030030b4492074400002001c6000391803040115102e01c0603034001c124000706d5107003210201001300d40407404040f0032044d150300c1a4028511117030018007140ca040c111074046950009402c4084015030300c103600510a1014a0500000707440c001d1030005440d24150400602184850100c540100c00c2940814819507400310701e011010780201c00c194000100d80d0725200502050109078042c0500102c0c01d04070284045400e801050b015240c081c505144280b0f010802c900003003411800c04048210001c0b04c0e6650300745d40610b064001c281540c1c50030030000f04800b84450351100321809180083c10060000511022000c0b900d049074802000c42619624580b980b003800881c201c9540b509051082d90701410107240250742c0c040450640041d80e141c03c80c8508206401001070408220110074009041940101101d00303019090f24145a119540d1b80e09441482c01028443d80c0404400360095900085000c0100f082d0300040c00302d18603103080240c0f2040c60440100d00101c0b000340c0c0300c00b0315104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 662741178 1250 662739928 662739943
    0x160b0a05071401110405330a09090f0207060608030306100f1103040909030801060c0b0f0a0f050915060102070f05040f0207020603090a06140708070f03150807030c080610090905 78
    0x1103400a010704981e03450741c10313a203500c180a42845510700c89048140a21401000250144d440100c1d0403200310100d252440d81d0000a0007808002100c0404504904a4092520030204429016880d07400c94034084060702c101e80c20944aa62050041101f155101000740c820710020b4140205540c01035641222000b8000340c40a61511000800052904145d0301001d041c41c003998514840341d0302e41e20104e90035424500c0152990341e1250210f0052800c034000190400d9040c60000b9510011987d0303601600c2040710814a513411000a00c00300c00c196246683e40118244058603259080096100c4070740494082c080c05280d584810208220041d4110748000303400405960302c83c94144032041c6e88030042c3c0000c4594074101500404441e02ca00d028900411058452441d00d17170700d140e03040781c0303900500b0150420503442d410715240074611081028003400c0c002010b0003206045050981202c1c04a500c144c480d6440041089100302c2c148005005851300b1290200350044a410b04d540740048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 662742428 1250 662741178 662741213
    0x20a02010e0a0f0806010317070309031203090c141e0a0608041401110c1b01090332030d050f131b0b040b07050c0904021c02040f060305010203040203160b0a0507 71
    0x20100700118884e94006040d5040720701c140d0003644001c1c0003070200e07910781c0a804c2c801000b040340c0700418000101c00c40d0f0480c900c082245000290000341c3e40383c80d0071110031513110440000711040103000303500b444050050620080703d105a0702030141d5000c291541100c0c0b180008010002000c9410000c28101c46c07502c2d103000c40d000340140102c0b6030054610b94030205000096108840750f000320342c5180d1080c04c0b00800161110b0803010b181da00c824158000c2d500340c107101c0100507a02c00c1b0510b0b0004408820400c80c0100943c0c480206940042c1200d1000d014241c41074080c4040242c000740380ca5180b10041d5000c418008108070f020015070500310329800000c0512808a00401d02d512254080d2515600500883e05919030b084180085110305907406504150501095091030000c04c509500c6940701803c0007481d001000c40740c104407007107504112000e075000018001581b81c1000040142c100441401020620742140310205110765100002408000300310300c0c2c00c1c09203000ca0314001c0003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 662743678 1250 662742428 662742449
    0x5031602070b0d050f01080d0c03050d0b03070608090c06070507030201030b19091b1107090e0a05060a06030c21030e04020702040c020703060e1204140f0d0c03020906060a020a02010e0a 81
    0x2049085030f48080e000442e140d000605000000069026001a80341300c00d0341c554403407807408041e40d00c04465aa01c0000d0726400b181d203810b03088455860810410005094a40e08c11513541041e1100a061845a014280c401c4030180b0096020502c0407904908407642409c00040044054000c0381e810304110710f8801d040080910b001850203202e8006820881035a032101e56068410078054817480d0002504400b03952001e0403d1182021942c001c3e801e45110170200c5081103410366a9500d800805c035200d0004035140c81c01001040031881c001d6000e00b100a03e070596600b1b051a048580e05c2c00360401400300310740c3c1c035550045a1507030f5040362401758011304280702e4101000000780d560003641c4801c131403042c50250090218000810781c09400b81c009211a8586460141010400200e4451030350b48144018660103035580c0b041c440d1107141d440f4400008c000e518500410803808001000c560140008111800d00c0c0703503011503421700995090814500001001d4080750842c0902e4101c040700c40f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 662744928 1250 662743678 662743687
    0x1b020a0e15040c05310911090906010302041809062909070305090c010c02060c060f0403030b03150f1005031b030c030a0206070b07020c03010219080f0705031602070b 73
    0x2800500a000d49080242d8051283d00d1031040100c4162294250a621040e005810400c0710300b014808950149540c03d2648907041c1c0798580300040340c0780e0000c8100f0300040020050542c1c00c0640800d50f1140702424118105460080d40521010f1801d80200086036560fa24904102c0d185d40880b040c085075507010488916281c031401244c1000c02500303403160208800041030f1f1403081c01840e100d010604040c20848050300300544468101840403a4070031814006071101c036a0400c21148109806403003500c407401c5c21f081c00740803505403514060181d0442c0311841c401d041d11112594001c901074407452120350710880660f58040d080d03000070303905000345081800e04414003640c2d908015000c60942d4000d200d01001c1507968052184002c0d01710500b801110003160500801c10b034041980c0c01901c04910b03002d40003e0882e44a0f24414807010465a0008482075010302c00540c040110009044c05052400015101c0c0c080108a90004000300c0b2031483e8451003406200001c2200820070381d2103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 662746178 1250 662744928 662744941
    0x80d050f2d03011809050c0111190c0f0603140c0c0a1406011d100302040902010909050709030b010b0903060c090406030602130e1003030509061b1c09050f011b020a0e 73
    0x80340d00a1241c4540c0358882c160711100040141701d0001602d40c0134004202d045140c600558841c5e0b8420a001e01602480245100420398071800051052150400c045801d0504035420407003501508078204152914011449501c200c070102a080041004016220300102040a01d0821108402401c808801410f250703030350000500c0303a050f030b10b40c03d40310300f84074004c68100001800101d0b103034030269001541c108098242540400003007030040c9000301c0000c0c1c0b80e200e5541038503001d540e81400264030501c20400c1c000c503c03a0407409004003129a6280424450000e9500c40e03025010044038080001c90020682e19a40031200a5500c0305082d500d5104110558004208510480000f4000038001481c40450a4030241c16a0f0341620303003506001c0c0c1c800900519400101c6140700380e1251600c1c14120880802074802c4484000c8000c0400c0b00c401e540c01010800c5650040d400781004585034031040ea046000501c40b54400c010718003d0807128000101c5214503540300f440c8000012003400f45 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 662747428 1250 662746178 662746267
    0x150d08070503071a0916180209090415050c0c0d080c0409110408190510022a01020304030e0108060333091506091003060506010207032307080d050f 65
    0x2032004e01c0070820140d43d182c210081d1200c441c0c824401e000d2a61000030300402ca85515401d81981000700700504209410002c59100e84064030305840700c008001c1581c80310708050184a40c400200200c40782480e42e0b504038250f842a07410802014800e103c0d00040701c58600c070302a58001d001103002441802c00b01542403000354420b00407650300e07001c0d1011008405800c0c003907003e240782d44480180440c0d11380090030320094100b2000c3c2c480c4100e10310703403402c8000e000040c1030032040e0703149000580c3d0b0f081c246005009600702070b01c141d051283c0c0d0010080103640105802a42e01c400881101c3d450851800300040c00990726008818507640078140482030100143c602000f51140080c4255a100c00d810070040203011110714050309e400000905c00150150002600800180100c031006600ca6840c0258028081e548030200d180580188030303100010000b0900400e2400c01404910b88020402441032142e1500c41c29200340c0080e40003600c0031010a500004119210f000f132942c000d845140b21b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 662748678 1250 662747428 662747453
    0xa02010f230603060f011e090501060504090b040605010f0c060b0406081f061410030902090f10050402030103201504090203040309062f070306021204050f06150d0807050307 76
    0x782a102000000c03164180011030700d000710a92141d83c036040c1e180400d4031607004201d281e6103c3d00c9078801e074009211180350042c0c1d80600700710740702c150f221420002c0510840d0420f286071840799091003010000c9907040002c12220100c28605900785070080d04003007000c0e20344080b400b03400602e80a00002da00c0400324290105440b03400004410b60321001666041d40d40307038020351a8401c11030100b24854030304140415034030110f03410040703103810303054002407a100703401c0740d403107614a851008102c4641d141c0070410015000c203c07003c60442d415900d5401841112036030188020f002324040e000306079561401042c000da8082c1c44d4666031620740b4441006500241e4044010482c1da50340811118040d03810010340c0c61020000b03407004001c0b07440020305511a240c45034034900441c5004804264140010096507020015407009030803d440c01501d481641d2030029540d400c8002801010002d9000310307603042c0812a0040740705841814140003a05c50000018011b11000510004100040c00880d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 662749928 1250 662748678 662748731
    0x12010504110a170402010c050f1f15090b040b091e06010309150f15030309051f05030103060b06091e1f050a03021803070e09070f1a0a02010f 62
    0x780921903038a0352801d6680600342209021485002d86110581400801c00741d10038014501440c0038106a2102802c0c88100c104802d82604260040b012120b07498840840040140e81e04200340b00d980c04041580c1d14990051010b2640c031500a07007100c0e52290032074288104010711301b0b90a070504e00440901c14555150040c5000d04040001390309601074400c1081003504210043c02e50550300d4a10001002142001d4280300d503a04504083c00c2d850b642c004018520035102c7c0c0c80f809060204100600340d4142d0030082141600e15010350181e401004d03030781129030056021540030308000c0000c0e21809520344880c4c0040d0111201042d070030306841440c00e034201c29200c46440c1c05206180b0760103510031030030f0340d0041041002401200c43c4264010098003020042d0050681d00020005e820300005501c132041d02d004010520100da1000e00c81c0c50001c12081c1201240c5501e0f0014620400c480d60b842042016404140044038034000e400014800385011810000d03060031070004a050001d54000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 662751178 1250 662749928 662749931
    0x303090d0e04060b030112020a09061701060f0602031b0a0f0b041a27070e10081506010c020907051605340306050601120e100b0301150608060607020612010504 70
    0x91890707505291050b8400d980c142c0b0900d0386181e0801c480c88641d00c1071002c08a801c800b0400000071010036074819800600710480000500080116070b95007515055040381c1c0c29050449410865507400108032071980c200304448842032050007a04038240100741d00081d00350424550701d030b0104146109002c0c1b25911400c41e140c0d001d4080c2409107909081150032600881420000c46010080f032816881d0249107482119200342d2250280c000f1441e091340c4001100c0c89149017403080700c90900c0095007070150000110300515003800002c00308515940041e0080c0c03003420101701000d00c108110340030404110011954000341d803500d155107000940008010062008003186a00d02d094090381180901055101d0312500316203484d0000d040141c03026040c0312446070580100420b5000e80b1072108001d501071b0280c00f01102050050300c40c0e44041a07ca03925062401c030f000c0d6420072400303050b540d00c1d01e840c03040b80d611100404c02c58425024040c0d8080702c0801c0500d8056030400105041ea8800e0702e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 662752428 1250 662751178 662751197
    0xe0d0b0c04180b1f020622060f0f05060909300c070302010201150506030105040c090e090d091d0703151e18020304120c03023c16090f0e0303090d 64
    0x1000304c0401182602400580004010600300e50000b61500c003102d0420507100c1403041e050740d850301164400c101000d4195201e82c92100910414030899a000d00156180c0c00c040c43d10403442911480a4a6181da804070941721410780b88206046c82c0c1507040103401501d58400300041c42d56620452403001f01d005600b0209040f000c11026803e480454030060710f8030b400c1d81d00301004c02025000644007041005580c5a002a5200810b0f084601a0581e540503103400900d07028020518a0603410a100008001082d458000700a90403154803154a190000d21052962480034500f20503600038607100b08910403c1030408a1865200d0072078016000141c00c0c03121001c003400a0b804201c40107040641c040c0300c5590075a0040441310302d01d0344644160340f61140c52140350035003205070000000c51000c504244905110001508aa40302d0108c401001c8810200112092410003800b0f8909003a8640b001ea01e142c1c80c1503000358542302251b0041c0ca0703c03864054015541d443c90400c120000410400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 662753678 1250 662752428 662752459
    0x30a1e1e200f150c0a03080108060708071d0109050a151d0f01050f0915040503010e0a020a15020304080a030807021b090106081504060608090d0e0d0b0c04180b 70
    0x35405021001d018052401c051401010855820790b000c49040d0040c01c100890218101e0901c0300c04c11640c4241c94076512035062130003136442c100b0001d10308000c2c0414001881245d036003208588016203901500c1e0100d412500004032100b04440e84010703002090f92001140700c400350300000050601943d030b50411013414501c4012440c4001010035000000030f05054901e51140d001003d00d50290882c585c901800840402c034001c2111120310700c800804141441189000e0290025802204009015600700c9030001445660544610666a45440444040c840c000e00c20ba40081501c4010364102003250304010340400000c031001c90060098140d110502000b00e54080d4200c4005049404186c1c20104161100d00c0c02602030030400040c1c0b441040d44d540c0394055100a00850750703406d1480d04040250900e007864034000801801000b01e103c900c1078440084170710702c041d04001c000d080d603107400e03400204e00d1245810964214007448414030309400d0a80281d075181c3d40a8034100382c02480340 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 662754928 1250 662753678 662753723
    0x60106080a0b15030a05041403070f0c0e190b0a0e04060f060e011805180d1205060d020603040206091507060e0d08090c0f03030c030703081b030402030a1e1e 69
    0x1a6003803c018414808109201e090303a002c0c0350300920071303c0907201c0d100007407035990b255030080c10702168404d540c81c24080812240d0102c040042c4404503e54825090446c1c0d0410011070a00590818076a508000c0c580d6a58035003e8a0060501c24003c43c4c127800c081c201000905070f000b00005071641800320018040c000000c00310304a81a19465144403403940594001804001c4c0c020741f01c0001444c00400c88240a0200d03d12407449911002c05000c02c100c03000055a000812403485000c000d01c80c440540c80350000c8a0340241e044408c280d480c040344000803042e44495411440014010410004000b15540301d440303a5060102100c403c0024104200c1d00681c00319050841600000e40318034540c1804100c01c11309207070040c04c1d2410024940c000d1031641c0c208500580004e20003000340721404070084d540340900c0550766a01d07451460540c01103a5640402c9038010415543d46185002040150390f40704403040e171003510720311803503803a8540c2940c1c00f000460540d40d00b0b401c1042c10002c00e035130707 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 662756178 1250 662754928 662754949
    0x12010e0c0306010c060e1221070302030108030403080d270506160c1214030903090118061b1b0f0311040501060f2f07031704030809041d060106080a0b 66
    0x1650b42d05004d00d200c0d43d840c009015114000e4072280b02c2e1200d04810745540720064054045030089410b10003003104d074620f10034040680030005061041005001c40700c0080b0446081c3c1c0e030449001ca5440100121080c0208a0303c05400a4900c03040307071030700403d503203008170300480343c068800c0b50000d840d00800c5200da02070309080034001c519120400000200454544d400c000c411b82000c28148401044500440c0c0c0102c03005415504001f62007201583c006021003031350551f0705a60f189960030704e0000b40000382c03003481d030300324940b80c94140c2401c2110346240341c2501c8020f04034112001e80c0c2c40940080480b072501040301e500031340030480c04107030420b8401c041c100e505590755041442a08007040d600780e040d44034020302d030709000415402402c10001008044e160380c00c0c000e00d030081c42c508241d44048082006801030782c00c100302c00c04c08500c01c401913410407101124006038880300840c105030081801d00d5109800d010b003000000f03aa079008075031140b1401c020710080c403a1080301c03010480221078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 662757428 1250 662756178 662756191
    0x50a060810030b070e04050f01060914093112030b0103090b24090f06010f051e0d091509140109170906040f120210110a060902010203090612010e0c03 66
    0x98540402c08503503244051500894036042049400e0031103404a401d03a042180c400c885000140010070400d07910038107000003030107e000019410581c140c00114042d601a0000020f41940e001c030006000b81d451541c0800c0e400c401d92407070241d0503407401c0342544075115038050102c0e00e400b41c0091954042e00491484650244451a19984141e0101048030a2100150060108042100064849229640c01182c004071024140c0c03400170001800e1040c1d003040303041007150074001c00c1c94090350032501908800700c1510307507070b00ca1440b010090300404e040b0394007074900303940c60340d08485021003035018a0f58240200544482088040b07005400d0314a4500010f00d013082020981d0040546079028001c0801c00600322881d1a40d182e00ba201c5000b03040d00505001c80d5006010000c61a02020100c10401c1504100e4100400c04020355116030000502400c11030721141c010701160300c24801c51748036541c000c001d0780c0c903404010301e1070741a5882400b5200350000c1101c0411044a052410350784100f4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 662758678 1250 662757428 662757451
    0x20f0a050d2319020111120f0105040c0206070c0312050c1c0209030a02041a041b020c0307050109030f050f1c030608030f07080f0d020a0807032a030218030a0606050a0608 75
    0x5071041658080d100c0264024003103544e01c0180d06e101c00741e0100181002003007a10554018100b0010a2038011010b900c038902c19460b00442000c0560003003622039214041c0d04084005564a05080e5450704902040e803004034500070801680c0002140940401c202200503080700a547c6c04485089200381c0070990340c940d000d10501c9005280c00d81201c4000b010780b800380c00b400d1420001241c10707070710002c915860844141800100301c075410003005004110490081c0300261400740082c0009940d400045c0400c0a080105024084100112215455401c04440d003241c180c0599809180c0359401c00000a0300700200012407240000584880c00d24814403a45002d41a5507206a00d900c045012aa1400140701c10112420360784080c0c50748030300507100d440c524584030b14000c04031101600f90300400c50301360a150484803000b420345017502450b41001030b51000040d0303c0801d1120492425903251007007203c00400c100f5140c1144007142e4040c2c60f04600356403201c9054501e110308403016468007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 662759928 1250 662758678 662758687
    0xc0510020102160803040b07021515060c01020406050304022b0b091e06010609080a080a0c02010908011103041e0c0302040209060904051504200a0309060209181005060405010c08070201020f0a050d23 87
    0x41e413442c0004be01d003000281030a18000702c0d01c5415003646c001da4400000301d40088104070a605080d0400300308407044903440e04030110f01c4034440741094036480700503086a0a01c0f002030781501c01006030fa424920300800000e410007000000303950782d01007401884001002c1e848000b03a00080010f40944155016601c5410503c050000326040b10114030b0982c10410300145c0091051400c2c41410644451550400d0b030300c0c541810701030310400040a4100358031070b0080390940418003059102065960441d405a59201e603400061514024a109a54828a008284422450201c82e8080d40751400e07202070105040ca04040704a804000d08650000d010030130543c09000d10903404640c0720b6126503c0181003e0111010440240403024083d00710718134241400120421110004010701049440d1881c15052400007400c540c4018801441403201040100c210ba0003417060460361554041150f0000c0740ca420943e40c1d40c151482c072040410003182c000200c00d02070500080010303414080342c0e03190 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 662761178 1250 662759928 662759941
    0xa061505091923040614010e04050423060910020a080112020a0b0c01020c0c040c09060804050712050307060507180501081b040f031403070c0510020102160803040b070215 75
    0x7145940707032984800c901480081001e41c000103080ba0540303407405010f11000450b02c1400101d80703158001080e0101e104e5108031090b03910040540d030f2100180e602060340c2d265481c1c14494a90601d0182c040002d0303c02c0303810324550380011500c0c070403000b00e01150700744104200c3c01030891250542d0b01002414440060040d240591042d0644130320140000c200c8036502d00d01d860860708401900582c503500040d140300040c004215a40014604480c100901a40000003501e10640c0d4490314041c000c1500015003484024001c40c402007042d47d00c501c100560360b2070034985907400705408442c00d626040c0420a041e00c5441c03080c440a45484044240d18242801903c01500041c01c2000213088070a084450110501c060002002c0000292020a0175480c107030b1303c5449200003256407540144500400f154004801c0000c44400b0341d61240cae6580e0040c1c0403400785c030417a424681c6150403040000c0c1041b92070b8008610032800749000000e5601c0c0c403a03080380c5415903004d0b101c4441c02d4100100d0300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 662762428 1250 662761178 662761189
    0x50f010503090a44040528090501060908030301050901050d060222080111091c0804030609080702090c09030a03120b130f0c02060c07030f031e050a06150509 69
    0x30045020000c41d900f1140d155110100c5080c060100026110340c0310034041202d2450b000409510140b441207400300016a61024550080307108191203176482d04070340c0380b14402070010f2491007000401228101900c41c00c0c8040501000c0c81134000007048404001064540801034a040c0c440051103074446905c0c05081060880c44804180d03900c07075082000e800028880c0b00205000d003440301500c40c41601e400744240c21550101c01d490071fa140704104800d050b44d115400d250903400274180240d0b949140d03040803c0c09010b02c1d000100360520340181b8a081c400d800b4040c3c44098421110070b44283c3d150172282120303000e9040225059404610082c001034005c3d84610350090f100140060000c22481c0000c0400d80301e01e984a040780e035100704000d000c00d0a40290803180046000030203890500c1c51b0300c90740300d01c0b4401000d8100311803d149152014401e4206219607191314011070304030013201d000000108010741e51014640d01e0030307000050f107031007100041c582c4921588640f82864282e80601c01e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 662763678 1250 662762428 662762431
    0xf0a03030c171006020c0103090302060f18060f0a0c090b07031110060608090105090f0604150b040905030a173601050c1909240e060a020c040f0204050f010503 70
    0x906100300c2c0d541000c00759807125140c520408910405100251078001d001e41484030000032a810581480d0544010a4002502c1c2d178000004c2c1c044510940e03200000d8000c04208040710720660b00804c03042c4001d0007028141030380510005181000143c5012101380e800703031414486e10f040d0031418010407001c40e0081c482c80a00c00140400e9500c09141402d0340c00c1242c4480d0028004145400306000751040c0c24450036600880c1a4010023410100303100e80c41d6240401400204940706014a05e4080300031600034200074103028009018000307180c54655101c3c1c0013039a904c000110707003844031000807a203800e00794003404c1505074600451195030000d03c0308001c1784096603511307640a21140200c55007403203690f118804002c2583d8440b0081d05580d0b20104070b010300c01c010004558014081301c81d102c1a80c4032031400c60100f80e20001c50300101070352003031100a44260b022101207011410030b500803880040f01b5104440400a002c46040208200d004030f000e80390304400055130389a8103500030001035 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 662764928 1250 662763678 662763701
    0x100909110d060b280b0a2c03071410170a020c01020f0a0903020315041203050a0e0a030914060313020904230c0906041b0e060f0408010c0e030f0a0303 66
    0x100741c43c484140031412800010070951029810b508140900220101c0c1030809003003c400400e1900181c201c005000d1580c521000c4400c1d20b804882caa80091141550b0320090400340075074186655950a0001c00c8a00b4140d550142d0320030712003944614450358401c00c48808001e08810641c6800c1000030094000d110140b0041d9403c00c100c1e100240d000014010702000c96860503451400c6105241c103101000b1501074911154106010001c3e01900c103400d800324907460000368956510507044003924100600305403602401401c0c90a00d41d00c5034004d4151241c00d8000b0b04d00341c1a40043c0005488100c030902a8095082c103400010b282601d0801c0e00680217803189010300d03081d00d105050006500400b14181c2d8040b602c502218101443e0b44c96000b2400c56003003100c50b03d00b510440303441d6000b28051081002d8000214820390b02c0109990a07064064844c5450b203890f400d1140c000d004103103030400422024040c560603481d0015810b0036031074001001e400c0100d45540c05802030014100b03c0e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 662766178 1250 662764928 662764931
    0xa032012040b0301050411040e040f080904020d05040606080a0f14030903060106030608190b0604110f0d0e1209030a03030b040b10030c0807090b12041b030b100909110d06 75
    0x100000e62100d005040941202400300d5541e5240a04020807501d955070f407184018000e000411060802c156030941c41608565000700b502614036281020380f0480141715480b07803002c5450b03041e0008640c00030340304a225420400c1150386400c1040c6c0d4600b24004000c002c13802890101000030380384072034441c0702c2541c0002c40e41070901000004e400c207030007600a64002aa50407003003003112010403003810301c90225182c451050107544c0310500d18a00040845004646495040c0401100341c2e08030340b8444000c045250f00c44036268071030005400c15002e59803d62003885800c0d100707008a4000c5405540b070040003021100362070340d000c2d0040c2510000d00340c0d001d0340d2080821113944840c61440c00a804079900054004c25140f03014102c00d00180c01001004425481400200880380c00ca5403408050000481036035100e14242003200845200c010744070301c00c1140081000412540705016110813242ca502643e00c070101d507012034a410358044d125940e5041505014180004003030010f80c0039000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 662767428 1250 662766178 662766193
    0x90402040e010602060a060b0a0909020c0a081305091506031f08030d06080105151309082703150907050d02010c02120d02010c03150e060607120507140a0320 69
    0x3010490020243d0000300580c01c120100031000d0200c1c0300c1d0710042d22000c4107081c03d0080d90300c802020994640503550781070340e002420103600c40702000705220302da60151a0950715003040741c1c1d0b44416084e620510340100414404207240200c1c0a00c04404040701a00103401c55403030070000200c03d044244280000c4150420205103ca0240018100703c0255580460700c1441c01c40300343d0850b000100030030052280340c0101c5001e42c3d11070300c4a5501c50403051003c1040740150905103041e109508504080c2e0b440c01c00410190010703204c4581032424100c00b81c2c4c81c01c0b400410038141c09881214802850340184109114501e004e2070700c403072401d0041c0340044080b00550301164180d0035551100036030303620000d08588015824011050094201d00d014040401200c03107a04104069001703a52843c1d084d4000a806d90301d4410650761610703002940e06080e42031082d405409a44041d02c141d51080079101112045100001d00d031074465819510b00c1030612041c141507603080170b0400c01d421a80601034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 662768678 1250 662767428 662767439
    0x3011103061e061c09030f0e22020c0105100e0c0f090d3815010801171c08060f042307020f100608060a091a07020c090406140603070807050609040204 66
    0x44605001361591030b40002d80d1500c0d82000703042ea800038510442000849031200b01ca946800d554070494012408001e03a0388460269510701900401c5000e950540c640700c00c100c04029034101c0e0304120380780f240c000c41d441d1710340c0180520640b08010011500032400c20100da81414040d0120010791300500300e482c00300001502c000d9012185107803c006082c0c01d07a0a40c00403200381e140c03942c0c01c000410941040b8600c6180003074400380b814848c1003600b6828028000d10200f0910292458450001c0c9403001c031020050f000c0e0020000342e400ca40280803000c100d80441c01d0a11a03c00b00f1407900a600c101c20b00e41c00c1d425000c00d24002c1000c0214002c541c0f1008508108010300490490b490340045415410101d066180c40001094900c201c0e05050b000000309904140501c0065911044180d0341c0d9221002070341743c01c0c0e00b01625904010004200014840d0355800340d9554001010648419203c1c0f0040640c3c03200c00740140d48441d01309080400061030180b00910b6411406070000d405d090341d50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 662769784 1106 662768678 662768707
    0x309010f1e0e0a050717070b040302010e06090a050928091e0f0c0f2d120f0209160f230c15070e03011103061e06 50
    0x202d42da095401c0d01840010011500b000c1101c0080356550100c0207064155441409107008020011410800900440e0100ca40594400d070300c2200e40f104102d402da1009403066404400b014000601f91510006a480ba00001001d000089601500d0390041800010b41d281c4d103e10781228880040d48105044255844400d013004405500346000d40320078500d0030740540043c900d194000b8041f045104002c00b0348a04041500f000d86107100c2900d00c640c0c807001100405124681c0c2070000359407544070139130064000c100341800030003150081500350b04180c503c02d8035070542140741600c4540103030b0315803100782491901c0c1d12183d444030003058081a10140f0081030100c009414150802e08000815043c900007800c2d1450741440080501401a04200d003402075080c60b5940030851189400c0c1e0744103800241041016544c003010ba01400b541d044415944090188491004842d14 = true := by decide +kernel

theorem cover : BRFrame.Cov 662589928 662769784 := by
  have h0 := BRFrame.cov_init 662589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 662589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 662589928 ≤ n) (h2 : n < 662769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
