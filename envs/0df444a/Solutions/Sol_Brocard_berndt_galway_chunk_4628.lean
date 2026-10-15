-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4628
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:13:43.593987+00:00
-- url     : https://prove2.me/submissions/466f09b9-c7f4-47bc-a96b-068be8d70ae2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 832194244 ≤ n < 832374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 832195494 1250 832194244 832194277
    0x120a0209090c130803030a05061008090601120c0510030e0106060318020411190504080709230a0b030109151b050703110304030c0305060a140c0702120a08040f0614 72
    0x3100c08180380e0007403801a490b044003801c9240c41d1310141d490b58100b250a061403a90f584240aa60300d46842c1e4101e042c406840c0c15483c61406201c038a40382e001c18440d8224000650f1404402c1242405280019180281c0f12808507018410010087e12256002ea0f01c1946080400300340988640550300200107201403450042146500f404020319011511040c03a50301440543c440201660300340c0800c0d141561200c1c1c030f039814220747c05d0400d007140e40110203440ca031240060020000c11841c41c2c06640c8007500105070707a51101d40703001406000312080d5065281001c41760800c9440d04003a402006a20010071552142e94a1440b40c0e000d0440c515000c100180070200000384a2541c10410b406403400b41d0303050aa43c1d81c0d9180ba0314030140c104a0300c6030001420403503008410b2040c00214608640d0482440c20003604d0103030340d132040103400380c0151401c0c010703140000010005082c801e540f0003052580c3e03541e24810702c41120060b0140300c0016260302d14800c1d0102c007080a0382d0805c43c9400840 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 832196744 1250 832195494 832195501
    0xc030f061f0c020d0203010c02060703050a1a040b0d02041d0705040e19050705090109020a02010b010801150516020a090213080a0302060f060d0c0b04051207080613030c080f120a020909 81
    0x1540c00b030440c02e00490b44403141e08030040c0161001c0c0110f4154030b95507001001c01e03042000b8003400ba540010311020b065840c00c801c083c201c1c00c0c52100440103140598001400c1070016000c501561861480a5082400d0a02109561041003144a40c0e03500d1070042d18292a2110104001d4450b030301115100d1750301917401c079140294018402c40d5140d106004a42c0016a00d10225804010903444116102d80c003003001207100d80c0a005039040340c0000d01e000551076040c84c00c803074140c44000104104100c800308100c0c564452464810582c0c54008200d03150b4155180c904c5c00c041c2d4040415800320100008000551420008610484681c141c0140060355601664501032000007094280d00c0000c1c2c01c08140450680744080000d890290400d84d666800e02041c0300300d44001034500c4003030740d107c044104441d01d00403d0340b1380c100e003004100044850f501c1c10121092400240003800c84200080c04045e0100c421005041004d400541c0c42c003599074200784003080f4000c00300216000905003002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 832197994 1250 832196744 832196747
    0x61501030f02120114180702100b091003030f02070801020720012610090f0b120d0903080c120a0f0311030610030e03160f0c09060b04060e03070e0c030f061f 69
    0x144040c2540581121171464080c1c07016221b50809841d12000740e04100c414041d01d050134059400c3c0302c881659088494200490b420180010070310000c0e04103c1d198038041d10191003441100c0051640500a6489107424144141000c403a0700f450b20f17859522001c03480895010311090b20303070080240c5c0c408400d2040c46184503403040b0000e2201c20740d41030060010a00325054825101c4146c200507000904c8140d1034107002000c0004443d000d8294480840d01004507800140e0206507035100c0d4010ba1100c441040e503e01d0f00c8159031201020b0140407800c2015658802d11030101040ca95800340500e05844030391104920060b205103803c08156002071155500a80210501c282d5140c01c0360701d07220041c00c0d05001400300d50300485a00024943e410244150b19070b544010300b01c009410400540b403300c3c03c1c0941c0c4a944103101c24000c00c070002c00c00320b6406000e038030000c044030b012504131480e08040b44140c503401120358103007500606001c16118140412245c401d29042040d1810419402c0360 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 832199244 1250 832197994 832198019
    0x1701051003082b0e01052202060921030c0d0c080a0513050402041217090d1b1508060415140112090c06020f060702030304050d0503090f061501030f021201 68
    0x11088900f14610381400380c2907020189000e1007a942e080010303100e400448058259180508030744480c6207640d2000c0007070082210358040e655811280285da403900b00d40070800a07400b05502c0081c03c1150105100b20000200082c103081a090f030603500c111181c0e00007910015104500540700310f42c01d00c02d000000d400b6000410380c560224103002000d5541d00000303800c0c0e0b480b80d0418046140000000303000c205542c01e100880ca01c4110850341002d1010001c84c1c800c0300500000740c11140e0302c095054507200c9a91921001e01681841c40d500c200102001a0000d8810b0b103440b8080c2c1c0ca405500030f0a040881442c80c1aa582c1e500e007082c046a086d40111003546072540e0810b51195038a1400e00010030b002c000c0c0380240b00076009000036055010890341007843c0140183c0964008000b0030000440101c2d05600c03081c20b40c100075880352070701d10589191880d18001c1510340c0c40780030280410b42c800d076140222400026602805228905405c030401d90042d4800d00141d24602c07001448401030110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 832200494 1250 832199244 832199257
    0x50f0f0106030615030c1205010807060207050d021c031e03020703140a080a05151f0e061305060f0702030f1510080304120807020a0f060305010506040806181e07170105100308 77
    0xb41084001f002090100102c0d242a449076070710340e0100d01d081080d41e40510042c1c000f480e04441200d18a00150045174400c40a011031460300114a02000e080602655040c102541d444070001503129803901c2c058000d504c00385040e070100306c0048200f40310300c5091044900c468180d0352244ca054680c1c0141c9406080d020302a07a07182e0880040400b2681c4500000091041c1101c190040300910072001500020156092501a030801c21000080015600074002203231400cae501c1035a1046180401c40e80d45c06500d038000d6240c019907403154000200090100441c030011882d451103603e80010000400810b8400d8509642090104004003403810303541500c402d0003051a0780c0340152070750006452001641016120f04003841c0305106003030341481218050300041d13406511303090a10364120361311007000b80f418211601001c020b14076440e0510440d01c450210400c400b0345140440001511441140a07070103040800d035035508003002e01402080d02407000003d65001950075515a40d10783c0d4482c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 832201744 1250 832200494 832200497
    0x31e0c0b03040812060a0b0f030f06030604170c070306061d0a0e07090e0f0d090f0503071a070309080708010204080105161e210902011e0906120f050f0f0106030615030c 74
    0x54400044041f080c0004140380042121550360701d1402204071151020040c1c1000e000303130b006104100004440700b90940d41c651907442d540b1340f40d988420389603292403840d0b040140413a003854030003d024400c0d54805c954050203040d13100e0042e030f59024442c00b121582c08500d041a4030601d020000c808980d40041000880f071001d48001c5420090352701c5c41c018030142160300180c6420402c000c05003040791142d0142000300c0c05024064600101d494201c82d4440000000c4135000403601d00b094000c500c010000d1000c14180c500e902d548000240c002c0d0017510030380000c2e500341000280e962582c07031081c1e1018440b9441c0c0e9801c1d641c0c040d0704185191a2000c041e010b01c1680d078003100c10002c091160244a461000c8040758040070b520006108002c00480d01012b401080049425290015240c03400c2d04c0d940e140c405020840c94079500301501c041c00501c500d0900d040f00380800c200c04000c1c4240b2924015004540c00d90f84c408040f02118007922504480801c62008100f2aa11030340007295888586e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 832202994 1250 832201744 832201759
    0x71d1017040804083c030d0914010b0f03070b0a02030c0615010f05070c0501050904060314060f0f090a0b06060405032d1b060d06031e0c0b0304081206 66
    0x5880081000c0321040d203040e42c050401042c1080884002c000035954002480ba0004d0404c540d00202440e5841c0940182c4c03142c0050100e4428240c4108103840c10b45030551414050f13480c1908010408400700461082e0650a1484022041c28204050980807030b02038020b10107217182101c0f403550f9400c0386541ca02140030410480200000070045580100400c444064482d07040c000003401c420350325540303001800700034040c000109600901d800221442800c0460392141d503003000138001e2400381c00040058082c040d0101103d000094058401d90348080912805c2c1c0340d41940d51407520044a020f152644405910300000b00000b1000303030403980c041c06040c1800d440b08002400c00c0e000010484400c0306004026000840c00785001030100140d50103030142031000800942d9240300121114003c0c28001850503418405500c200025500180408800180c1c4080c3d043c2076103922130240d94440c2d49000c01300c0d0b102c102904807406690701042e12454140100070058403268002e0180350700184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 832204244 1250 832202994 832203017
    0x1090c120816060b04060e0606070b04080c0a030302091009180207020d08040b0901020c0613030b042904031715270108030a1d090403050f1903020d05071d10 69
    0xd540800c002d14403034180403640120440134402242d81e00d9010400e0100070074180603007900d698044907105900001615001d94603800c3c000b143d4881c03601c1200701485a41194814140c2c96030180007002022101c0907040a891041245d03c4440b07801441c0071040c95804440988000340d00811000c0d1003c2c01074024514244c6608d407080c0c01c543c0c403620070f0b828000b400349481d60f414000441032a0080701c501e0b04003507404010100700142404014000f400040209051100148044244800e10034258032000c42800240341c03640c005035022004030f003a011038800c0c3c18070000c010902c40c40000600c8045100c0740404c10200000c0780b800905007160501c240790800094140702da002e07181a030700440d95105c0c0901e005100280007078681541a02102c4181c2081d5070b242150758110790140b400584034524010368007558440c114243c0f051100c401032441003150141c01501c036803c01d13000f041010340c0d5581c800303446002c10b215401d201c140d401e009030b859074504054651001c90461030a14120031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 832205494 1250 832204244 832204267
    0x103021807090801140a0f06081009080c0715110d081501051309020322050d0f12050709060807081303050a0e03010609020d0c02210915270301090c1208 67
    0xc600300031034121080745d481002a00c540da4011011440d00003d0104803a91910701950348644143d9a550301c0e45031500250340c10b2120b00c40039a482d02a10b802610885503440e1001c0000381180d08006001c00c1207403401c00c2e21000d021900c80c01a18060b110300c010340c0c0c0c1d50009a1040c1846a8a1505008050003440700d001c002510400190944000040c1c1d2410302d082c111440e031030020003041080d0100b5aa0310001240420710b45142480341c20b020029100c1c00c6419544000b002c054051154503100421a000d03611100d8007088801580750075006032120302d01111303c1c00d01110b00000c121603565000002030302c40c0d40200160011481d240e10215000300c0001e0a440d0f0f00d40c0704024564011a5068802c18107114070440096180010856681c1c400d495202030915544040c502d03d40105451034651035003883c1d952101f00ca0b0754150707607a501c0070030b00903041180c10b503c24008890030042c0303c0d410304051041842d203540180c080c5120703600d0f02000000f00131804100715010b80c4103011503d11f01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 832206744 1250 832205494 832205501
    0xc03080c0f1204030c090b22050f100608040f143004060f05030402030c090a0e010e06010506040302060d06050405090a050615011e090305031b150103021807090801 72
    0x8044680a001c070010503500c1c0524252001c02400018a4204020070000f1038060014044400a5401040c0381c4802000958010171100b00c880703580700310341f244a100010381c0d8081e900c50101091049a103407a80303500d0659402c054007881c004030f1a40d00c04a404907450800003081c1d280700704400000440c203001014240101c00c2d0b194006000c16200c1081000807841c210f8074000c0303210769241c0c00d2a15150008261450288402c814007800002150a41d2400d100f000070f441d902074149072850600a05c00d40081c003d164800000e5440c050300141007204c04103070f8604803403000303060074209401c6400f0000d641d44000303018229540c0d1983c5c0008d95417a0f5002e400d104002140103000103a5039401c01c0d03428800010001a00e40d0803e101e102002c0e80c006401c030180241000340c0b00030b41c6030008801d4903404010341024129200c04203000d6070640d69130212903045200071043c1c64030980b0905402d80d80305400c0c0002035210104440000e040304130045882d52040c2d541c6802d031101d540d50f541040c2103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 832207994 1250 832206744 832206757
    0xc07020f0a0f030b010909030906080a02040b0a05041d150f010e18040201090b0a0f05180307230306130303090c0b04060206010e0112122f0f120f03070c0c0308 70
    0x900b0034001c00304144a003200d41280104031288050000c0d240b503135401001e20000303014402c00c0c80b0030359003c542c1007800e650568010b80040c0c24025900e0b1003c50340980300b50424032503405140c3c7e0302c0b002d04c0c4410300541d40c101d0240b0440400040501070b00c00c10402c3c14200944414104a0006000000c95032101c440389000c030b120001002460416000042101d4200d0f041350b1003051040140314081e03039010300701c40d0710a01c02d0325040c0c0d00c60f5a5000c19580907031500120a03418401c1440c040392011100034458014010f200315035224012510500d0b407201411a40760384005442c4504c00c4c0407074066000466828440d0806001c220b859004000d81600a600a1401a480040140310762042046c4182c05005604440e46c01c2c00380541e40d10704801d424265130010821551020080c1000080c07515440c144c0e400000001c50101d45100c0e03a0702c021f000081c05e081e1098503061141c1d411840d0807600004011118545180c3e00d4900c10b580e82d51403600103e40410100c5400400b14103090080d000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 832209244 1250 832207994 832208009
    0x130816091a1801140105030405060f1b180a1d0c0c031204121218020114040503190506070302040b071704030204020c061f080706030b0609100c0605070302030f0c07020f0a 75
    0xba5410303d07442d0707800c8100d01d04e085410b0003c200b00340400315030001030866000707043c0c004003421543c480c01c0300844161a07400100340d8000c045500f0081c0d120009214010039810348058100659514112520800390380d0420751070704405003c641b8580918008260510070801100d1a10f040c111418202e01003c843c292a001e810141c041031180d403011030302500d0140c20034180440001d80c5102000c2c2c4a0400c0000e050011340d080c01d061410052095a009040040c00e80e61902c6101e00c245090001085c01200c03540108000201024020720954080e03858111002c2c0c00c20155035141c0c04009103d8030382a11952040c00000b005a80e1400107080c1655041d0150045051850040c0440600500d00d0003d040e030004090090580c00105d8030f040313400514021650302c0280c00452801d210f400c5a1a401c1818a0200f0900700d070011041440b462141d80c04000964941c01e00310100d0000780d40c0b240402c0c4512022500c410a000098081540010b0400b2102000200001d80c00c011a81c070041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 832210494 1250 832209244 832209289
    0x30c160b0109050f070909020c070509010b0d0608370501090f0203160b0a0513050319052a040b0316170d17060d0302070317130816091a 60
    0x20300240d024140d001a0307110b100d082541070940c001b4144070614011151480e07408610181c405c06d08000c40d40040201914114181d61220f002c81204d40c459000d180c40181000c00000d194400080e1401d03499420021940803040c103d40080ca0001011904440b00801442d103000031490a00c20b4554941c400c0d078404040030020300c1803500b0300085500b680e00460059030104a0800d5400456010f0400c5184c0705554104900803080312541c1d030b4010139090b118031000c804580040f5030044000c00e004c0e40407102046c410030980603803124845501c1741004081c2c0c0d0050f0440c103064000c0c00c9004c400030309583d0003a1001d5826090102c2540c4013102509800e00c21644010040c8048a8081005d00d010007441d1010b0b607600c03007110700c05014180038484020ba034109040c42070000301d001d95804200a00c3d0b84500d0b03540d190154001da01c01e80c608400c004e40001d02c01c00005040400b50405071410f110092400341c0400c020709580160107103410031120b8941450b40c0354132000c07019900c12680003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 832211744 1250 832210494 832210499
    0x170403080c1608161a070803040f020f10020a0201032307030c090501030207020a03023601050a0f270b06070f0b0135010b18060312040f0605030c160b01 67
    0x1075841c41d60b10303800141e541d00203d00f510700080207103003900300f82c4894080c031603c0c4031401200c00b0030601c5212800b901ca90310220a00081040c440402d840c41402102c240440e080341c1e904000030000203100442c0540c0c0072880c076100650181e040960b115003909054900c09551001c2503a0040044800900180e40e804140f42c0c05030700981c03040050042840c00314100722060f400310b04803140500000c0e00c2040f8000440006100010309483d40150340b030340e1000703480481d00da0200100e400b230040038490621004003168856404600f2070131212000103007070081c1d0b8150101a564605a03108455458540c640d0b0380305c545844c002024414401d03129510600c402d0300305401d0002c41038202407911100c0c1541d081c00e5844d00d0f00351840341041d11810340c1c1403130806d806560042507807900300b54100b0059401d4403041c0c0145004a48200400d40507100380340c1c0c4a070000345481c0705501031008143d4080400744045441070028583c88030f045c03403d07030380b038107295105011040e2100d10703080340c1401201005 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 832212994 1250 832211744 832211773
    0x509250e0c0c1204062708150a14070e0d031e05070312050106170702010902041a100e1c0203031b0303180109020108040210050d0903021b09090703170403080c 70
    0x500071565208a082505000004100d8038014484140070350203000e4000c0e000344180c5025000f41074180071510502c20323450103504051411a1082c18551070211030301d6500e00d60002e4680b150080382d1303c5400c03181e1010100050b0b00b2240c039058040003450320300742d078541d01c0d52004140c00846584800d03131500c090703217402001c2039040356840701c82c0ba040500400c14a508030700f10308000343c00f004202c01035589030101240108146400030b503000382030500c89200a2115a503d000e450340c00d03500b401c3d0a9281c104103946000020b81c00c150489940301e413449080303140c041400766240c07004050740d146c0040b00d400c0030f1041e009a180301115400001c18000325045d00c2c1d010380c0000c04401c00a01074890190000b03002450001c1c0702a000700c1d0381140e41c0413414859000c0321a13000e800041002000114180255a1024900d0585248401000c04401890174109130b034071401d005001042c961b17045a8420385103503000c1d004a00f001e4410302c004000035601030003400084041070018003091001410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 832214244 1250 832212994 832213003
    0x81510050d180f02210106030c0306110a093614010f0f06050307050d02190f0908101d070311090109060806060d02121006050406090509250e0c0c 64
    0x4018444118107400101c241d984540d1840e01158841c00d40580300044070b0f0742c5e07080051007003055440d051011041000d070503540001c0e240601b0040040000c91202c1030464820842a400411980441088081300c15111180052441c42c1000c4000981e203074100c0c424040d0204070010a521f6900c3c1c3c01001d4124003031640101444103030310404606d018941003031403109000da1410030030004000b600040c004c0d003c440191101c1c040440d560030701d000b40d400106030001031361000943d0b0071541c0c03e01e00e44a25840000d46081c0001381c4000c41003411014014045400240e94404103000004800a4180403100c02540112010710344c0300407910800544580580103191860300c0c124081c031810000091070b952000c0d00b035592541d03000031400007600701e45a0341c603202c00e01d100301c01c040d0342d1042203078024600301d0350144c0d801e11507036482d03000d03c00913070300c003100d00700380342d40c4050000342d86503103007240c80c540c411038480e1140a45900c8442040780f10404032040c01140400181e0030344100020003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 832215494 1250 832214244 832214261
    0xa0303020714060115180e0c0d05010605040b0406050705011d1509010c050304021c061508070f120f06140403050c0c09040201091401120e071701050705030403081510050d 75
    0x50803084d81800008603d804440290720704000744c24013410404800d001400c0b0150100000c503c1c1540340c0b40d581189030340d1254070402141403d1000000340340780240c0603901980c4520412500301810910100d8040e00080401c2d5100d43d00c54480d1804400034006001c00d0305040703c0030b85440341200780400b40b4403101501d9031740c81d0380c9800b854424960b80f00c4141c941241d8111413219046c0c510380ca27200c9114401d03103400361240e07151844c080f1030025812012021601c0400540f2049981c54014600c911041d01c60341c903003070400303840340c03000141da942610b0b009900c0754500050fa00c2d0162146101802c04580c2100465030020760392a40c940100b007107042d11a4100c44442592a00d41e00090035030509201d00705e01030802d1200912035a000d10f601d180c01c458800410010203461400c0c2c40e6454125114007403658020366032215039076170107000309840381c2c440d85c0380e0710b2031601c07656000c441000b001081084000c3c0f00301d503070032510781c2c441060751700c07a40b01665520349410402e1040b00855aa40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 832216744 1250 832215494 832215533
    0x7020d021c2f0f0d090e0c040306150f09060302130b03070902030901140f04110612071d12010507080603160b3103151109210a03030207 60
    0x165258140e68800c0c5501440e80b8594203007124046800c900708080100c2c4581c04403140558110301d1142e40c0001440c8403110000e541c0c0900883d520400415181000d4643c40303501c540c104810310108000742c000400c1110900c6518070032682e90740031a4075000c0180c100184241c1c5940c41001503180c1000b80246400400c10200803560705040003980d40d0056201c1c1d10265900403001901c082070079400603d13920301001e158442172408809004502c541114203c0340c840d04005401100d0a001e8207036444040285103108041e2280c490a84040400e0102d80d0b881d03841f4400303040c030140c035040f88100420b41481c0000c03e05083c003460103031800d0001400749c1c0c06640110031210f0041040e1070000700b02c6140300c0c9015031f00d200c09040c0c000c14205052003054481d42c04005200d001742c80400c91001c4a01480b840890300030300c80407460640b54456451020040144171020340380c9012002c51410000344108101803011a851880c103200030035209801080c2c0c04180c01d003d2000d140b91225041156 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 832217994 1250 832216744 832216783
    0x918100c0f080402030c04020f09270103030305330102120f0d0b060d151406130308030a1e0903090801050606030c0313051b03011b0207090c120507020d02 68
    0x4160006103051000d8107144100032401001c2010364405120003400d0304000707481996200740c54100001d40d60b004000040c020440200d1001441d945d074981da01666034042c0d44002c250346541c400720b0151001501c01c02d43c41411800038201d00d0050900c840d0740e1282220740040890502c1c0029051000320b030b41c0000c1c066001c126420900064208403031101d400d1840004407003110700c01280303d40c014440100703502498000c1c0090a04040302c40a002c4a0f19907c160095000078418841e4600500d81e1036940f08004131814000500540c010b9548120007800008040c040c44020f0b206500101d200c0001c00742d96041d109003403550002e00d50003c1e00b0401e00a010f00e0801c2d601007a46480000c101510340d88022002c01d103002111500480541e4121040f00da000f90014850070140c0200056140700e0740c60a6203070808041040e220921902d0550060540d0b039250115040180007903610b10010002c0f81002201c9403407441c4a5280a51115801458030508641c0701920307124584012080c103420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 832219244 1250 832217994 832218011
    0x1501090c0c0c17010605060d0207022706060705010f0504030915050309060c1605070801050f090a0c05010e0102011418011410150908061f0b040303171302091810 71
    0x80c204610040f184207102100c040030109001d80d0041080307400865203d200056040009501c0d50040c3c01c20600840341104000300e07000d0351004c03030340054040c00109620a40080c4030342c6800f20182580c80d0151001160650a0828900c102d41089508602084810f0400d0013490b0714288254045c8289003000d61641c10014050741d9603850052800d0000b000000d0608664402d800e95800895400000ca0300440d0301c1e460200c6c0604000c40f4424040f6166000040084000013507280800d40c0203854001101c2c1800c004407004680c0100c00c030306664960707100140061244001c01d00c100000b4413819000c036030b459080f60035141001c100c0c4030704400031070603c101c50900c00d40d02d804451448030495400b400030728042d42c200d411a40032070040c0c0201030070010741c00194402c008100145138144d11001e0b884007042a002c0c001d40c0805800a040388515080c440107604683c0d810001d010800100804c1580c00112211400c84842103c601d40410120703040d00d082043d0b900d1b0051203102400243d1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 832220494 1250 832219244 832219253
    0x50a06050c0f030a110c3910181d06030c0306010e1302130e01090c06020d09050d0f061d06090a0f23060c09130c0912060b031501090c0c 60
    0x7018000312401c80e52101e044540e02c0481048950a0b28079100b41d5144400e109000340b5440b508800070342c03030203070081c1c7c030300c01031a450400400400400034403282505504c0d520440d80c2c01303c880c0f54583c0c0ca80203000042020301e100d45209468140c01c1ca40d842d801d14205041c141864101c0e40800c1c0240d104400611440c0e181c00c00b06641701c660010040501035090000034042d2103248048030506180984180c500c54064028800142c065080c0110150303803000304a0f80e0380d02094000001520a80c400d005500e08200360846035400b990440740c4440c0152580c0c800c980c410f04c156100c1c04440840c201c1036100074089654403802035400f91400030712988440c0254210148001e1240440d01c288080d0200380e1070140003000c0d282403c451451401c0d40118101c0d0340101640c07031040392204548000342d0340c41d0141c60320340100c0d50b40c1c1d1040341d0310700502d05580050068003240c01c0341d21040310381e549860400c0b14110012101443c0c00d515403400b0562412103242441000400071039200b51000304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 832221744 1250 832220494 832220497
    0x9230705010c0501020f04030b1510120e0304030515010e0a0e12160b0403090503010f0b0a17030d050705030a050114030a030513170321070c0209040303060b07050a06050c0f 76
    0x40d0030a080c00101501c0c10300e040350082c41101429010484040b5001c01070040400da0540b240c0c002c6191107201400010030000503a0004880348001811800d080c80022900e80000950000020071a42020303100c1d0b45003030816001c2030034111080c68520040004080078800941c0001d28244200a1543d203040410385625101320943c140744000605061f0b242c1c41246204099a0400b072080c2250905281c0200089058450300d1700c0707076007003003014103a80406204661049100404507009113180403041d9545006001c03103104240030a101c0342c00180c0b9180962486104076a445640d01d01e05264584100c034010782010f8000c0000c131044064a407000203110b00c2c00c5d0b40604000e520b440001042d090b100c192034011920522150919140c90382001002d0242d4010a0715002ca80324540c5801200683e01101c6d41c1740010b8010030442c1c05410a161001c1e0860b0292901182c503644907490501d083d80a080308039140d60140703a82100303010f0306101d00c070b420043c03800d00f42c1c0c030700204000003401d40d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 832222994 1250 832221744 832221749
    0x9100528020a0c240f020408150c12070203070210030e0a02120c0a140f010201140f07140307020f070501020613060f0204051906030c0206060a060e0102100f092307 72
    0x601e6000600b081550300a80e00001c0c1150f00041581c260601c500301c50a6000e0206000b9152605081e08000c80103140d00a980564003140020714000300c404480c2d8082c5080a0003200500000308955611034032480e030024070070f0100d074000b181e807a0260700c1801045151058140105890649298450500800c400310f0464040701c1c2044080d000c0c56465040c1090a00501e50001c203076500050745c10380e00090b00a11010441302842100300420040e8241c0381102c1d0040003141e820800030b218074289180350303500a03d452a06610006149000509550045e00c0c2d0b00050303800b008400d011060200040ca0241c1020720150500d82002e0001140c440b00c201c100501c019294000300100c400c0541c142c800800b401000701402185031402c0702c83e9440300f0301031940041d04145403c21080e00020b04e0a01484000c0d1544520b145008401c5803000242c4c2b01c1c0f81e046000e82203000b08070402078081c404851000810028105515107485100f082c09080710183c080c0c25903c0000d9a0503010441404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 832224244 1250 832222994 832223071
    0x10f15050a030b0121200403020108010e040f02150909070f0e0f03010b0d061e0605010e040b01110f0601170105060315072309010f020303090604060c020c0603091005 73
    0x96580c5000300507100340c070004a4888800c4140f1854a081c40c17403540000494400d00c000048544000540c0c12113a4441d0f03000c06030116440c0f20040184c007101402d0b10790700a001c1c06224842980c0ca40c00581ca28404e84911444030502041c0c5001070300e01019a0307500108281041c001c024003440000c3e054050746200e0b40d100d40c0381c0c0010440d15407400e40180c4540c040c024554019520716203003030360040041c1d0f1105081f0801c604180b0361282000d00c00d00781620b00503196140303100b00354002c000c0500a035542c103c1c10030180c00588501030b00c0802600140d0300181000d80701c20360402100070281e5554000f40d0400d03a04000521441c0e80340400c820501c400301b00e01001d07160791443c0d42907176944c40100540c11480808042e0054400340b401c00361078000d00981e240198940c3c03080303080382d032404180d5846000e40c1240000c2000140705034080f81c0c40600c01d00540c0d817034180c8400040c1b0940c00442e00c10030755030000090360310080120f1058a0b4440c080d10407013411070340040c1e450070040b02c0201c8186c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 832225494 1250 832224244 832224251
    0x2010816140a0306081204081c020c040914010504142404060c0203040f08010204091b0503130311012c0a0506011a0f0403080706110405150919030b010f15050a03 71
    0x840b20b4403035004840580007420444141c81c030002d2450444e43e1062044442500030000703001810f14159483e00340c940340650007810184500f00810004089140381180d481c0041d2120301c0c40e68100f8010203200d140142c0c0900c2e81d8076a4400d00d0382c1019444101041d60203000603c804d45004030340041364019400c16000122a20042400c0c1d2031031140d900610801d0070158000544004150001c01c10ba5a14020610007240e1007000381091500320356904010440501c00201c48002c0c061500524a000c2d10301803494001c1354523100c0c2180e50700d40c44041c3c500f0180280011684400e0003408049207210010000b440c800c1e00d445807115410300640c41710344401d0003c00100c0c54044141c070010316007518802d42d110f5492521308090360050f0022180142003004034100003180030141c0e400c44034040c1c055112421740d0b4851219550018514542c00481c03004038041c6000960140800303075200d40785c10381d101c1d41400c078508046549680030110001001841c0e401c0c140d03200050754141c484e5400c011 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 832226744 1250 832225494 832225507
    0x6060408150606160b16140409180606120512030105060a0c3e030a11100203040f09090201020f030a090603052211100c050a03050306150f070201081614 67
    0x21418841c00c1c400c011102c0d5401300800500c071001d42035038014040f040c983c240360240d2103001c0d959192043d44400b500701d401d10041001840a030061020741002c45049200c0c050b1aa981e1801c44120750810011011640990f9003000310400c0074014050b09a43c4240c1998544000107149124110400b02003165407409070007002000062401185041c203900800600d10750750200440070134030382a00e0140450a000301c00740c1004500c62280607008000604441085014410b41c0041c0c0d0200b0021840100700c005845801607a202d005000036840c0403413060b1243c000286481007c8216464a400800c46180c016401c211440300f103c28900b408555030383c0320f4040201000c441804800703922480304c0d00c001000300764101d819006600703e64406e0449049030007240c4800c0501402040350b84458003180c04240144061948002c00800c0003011007a01c2c040071059800010214500301c0c80030540368110340c0c101c442036900c0000c40100803420404003a00400301c50002c0442480c2d0361001561 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 832227994 1250 832226744 832226749
    0x30303110403120824010c0602030c0f0f070b0f010f0e060f04050f0601030e0a23010e0a050d0909022b0f02041e05010926030702040e1005060604081506 67
    0x54038000d5070045028028581d501c440542199801c590541d1485c499501c0081c503842100319007414504183e503195a12806941c8900080d40081c0c4144c02d407070024085803218004180091002244266165880c1c81a500e080c024054010309102810071580e4010303c40b480b40c0340201001c440142501c4445915200003040c445c002c1c8800c0950810700300f07020804014580304149002c0c010a980400000c0358108606881e800c09080003800400e00190329807400c961b10b034140502c0e0021400029004d02e42503c901c3c03802c2d0004000712032132380040e01d4140125800c017600c400140400e10003580303450900d100e1802000000088140000d41c00c00c1c007020480016070144a481c51403890440d520307504c901d120841340012021420a52100d01d1000c18039520030354001c8200c036104240f41d140c10442040070100b01d40f5054280380f491100b800300c000581e0300d500403411013044e00b0001d0080064440f101109441d8020900790103550104020050b0080024003204d1040a030942080141c481400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 832229244 1250 832227994 832227997
    0xd09060203070804020307290c12070f03080907060e041a151206062508070204141807060801120f050105010b030106110c1c02030a0b0702010b03010c020a020a03030311 74
    0x18262520100401c51156000420540518000c80c1111586940c03078441340c00c1030b009548044218007444100e607000d14000c1c4003500002d40c5000a44005030040c640901132a0800759090f1200b071650399181c402d2542145890750020054800751440b18108440a0022032600003c2e5000b0740d0346003552811801d0780038542010040091046501e00012901070205421410501b0340c40b90380c040204800d464814101d45030301c0c0d80ca0801100c1080e16040c90344405403000015100c0b14801c101a60040e5501c1c031a42494044da09014516030030300c070405002c520b90b80c00a58547d907100790018014507030402c4002c2c0c1118802102010340c80d251f883e020740b9400248800134400e60a020020030044040f1008c3e6068071041e0f030701c81803101c1c2c9003412a80ea071655a071210740c1007000e6940c0c024400500c041918061030007d03088403880340c165a9860b840b4034086840d500141d6440c1403c41091600380540b401c540043c0c402803650400c107400168600903d0b00c03009040c550b84041c1c00804c60160300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 832230494 1250 832229244 832229261
    0xf10030b0306010305070501181202210f07060e030606030a06180203010e03220e0105040506220c26010b0c070b130509060a1d0408040f06020c03010f200d 68
    0x2015140c41d5656450091b9a406560003240d010039180300300c050449192241020460b40d904d05008107110390b507003d2210180605c40b04d002100008000d00320040c900f003140c5103101c22500010f011907446c101004059034440d070803c0303119070404024001d05540002e03000d582035400c000b00056180144804203036000a0120083d010350901150b00503001010000d4166450810341ca000700140c01e540340e540403409406050080e00641005110508295111a621410141c650302c803c0200b2910028160f900504820490349c450425003031055116030581e44000d2030101900490101e09584a0261014000d01810041c046401c109100341044140014a40400007a90300c6140c507800841d0600c02e8000c01e03010700311a0010410a0425203070603400c8800c4e0b03102051601d82c501100841603a4050026101503200b40004108802006005402410035400908072a404801810b09440c02d6403481c1c281c0e40e28140c805d01c5031064803140b401228034581074543d0f6072907045515000900041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 832231744 1250 832230494 832230499
    0xd0e0603040b06030c0a030f050c0d0309170313080102190806011b110d0b1f030b010302040c09030803070512090703050d230a0507060b0301050721020d09050a0c060804020f10030b 79
    0x703030000140a0f023007450b00886030044064903561403a100903c601440c0622004002540d009020450000400d840313544224050040e289040d0480d0460b03040c1000316000240d042c3d50006131000c000c2c0410509081c01031032400c086903589011400a00462400070f0b415029404240c0d4000401038480091200420001c00b504204c0b003190410f2100c00f90111807a40700e0f2020f298410000801101a2108032681312012103216030840d42408094517035400c4060503c20004c1e40480014546c00185201da6034a030f5505032175111400802ea01e00c0e10103030101a1603001204140701207180491045580c410030308003107140c480c0d1481c00345a420703201110345408000c0840c8584640d5031140c000c009060150209110280b4184201400c80f8420b60303083c400305210600c62008080803600345681140405030050034200402d4141c000e48010351006c07500c0b5081605c00c1d004210070300124002410440c5410001803034264086900d909441c60070038854070480c2d014200c200c1c46504040701a0001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 832232994 1250 832231744 832231759
    0x161d031c020d02070b030402060703050c010e2b1e0e13050a0504291b0c010203011508130c05010813020d0b072a0f03090e04080405030d0e0603040b06030c 68
    0x40c948000d40b40c1d1000c4002a00601070701000203402d0701e0000541c0e003c3c0350020101c42c581003c036642683c030752348400d078a034155548824070882c100c4401d011422507841010150030f07020b1000701211598001c1034590205000042c407401c91500d154480341e081e03509107400d00582945900300051711a0540e00d0450655909100c108090440103030085801184103c120f42650310810b028000c045075042591541c8010540000d08144c06400300c10510b030742803848580c50050313000710060a82e4002d80000601e0707034200000d4400d0325030081423183d0080d0542c100c151a5829036803030a40e13141480c4107042c100040d0b1300124525200341886841c42541c020940404450345260405d070700c1d8011122100450380c655010910b0b420840010140030601a541c0e810743c50403075a0b40701c96046107410a90811688000225044003150300d01c80c020380c000d442e400d840f03500d03040806242901222400d0308005081ca0401540d40320802500e40155200000e80d01c2e90341c6000200c1e00d081c2101b110254410003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 832234244 1250 832232994 832233043
    0xb0a06050607060f14070f0311040b040e0105130e030a08060109180912050a0e19080106170106091a0d05011b0f0207080f0d0c030513090b09161d03 65
    0x101c40d030012000b100110411702000d0b40140b0200d502c1402150382802142030007525036210341c8250300c44121102805140c03400c00e80c64034520282d40d00140c200c0e06090b04c098006014510303129030520079400403580180700301d81304034807410303200d0013460004410b0050901c0403980d246e020b00307501c8010700310140c0c40c000002c010904050103441001c0090b580700c8003000c0308a0400c1d208404440300d401c120341344c0c2030038810031b5028001403452980c0c3e03802400520030f40108921400b8043c11000300411011180c0c28051080c0e1030382103815079803080e40c0e450305d40b540c4800311003084040079500c0e420464400000da440390422902400c100916440310300c8921215540c665000444003400050b80d90850b03106540b01c4900c0346e511030200080700c0782a8050607424404a00c02c4024110b032910a180440c1002e00f5150040c070094942d41041c0d44554680b0300309182d41c24a403031155482030359060f464070040300c10310003d800c1d01b90074018140c011841001d03004264804120f11a000100d61440001c3c690 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 832235494 1250 832234244 832234253
    0x3b0a24090c050906190b160b040506010f060302072d0605070f09080a050a0602220803030f0f160f0c0203060109020d0e0321060d050316050105070302040b04030b0a06050607 76
    0x1801510b10503c034410100e501350030148035401c2200081101000f649060120701ca5580e0400d00c08091140d07030b03002118001400c2290010700071032003030004003034a506108201c0292040d80c1c018108061060250b9004110740e4450700c0d13040c8091226840002810f010007112440c5e10700006080c0d00e00304030901004591103540503030200740d13035665500345c50f032140803150715140822000344c0582d02c04544100070400f5076008060340f450384c2c00003108543c1d1034410a0a0a0002da01c03a5030650404000c22440c01d001d41c4400307070301641c4441112418a402946103081c0c110000d1582d04000c6003201001025000b40890b42034150001c04540703aa680d80d20038400a944500d098030f1040d800c1100c9405814000401c4d1480255030b440345070032012502d401c42c800e0000042c43c155214004004500219505000414142c071071001c05442d142c403113040a6095802c0130f07043c141014410407040106000302420754040d254000200040c039200c440b00340b000b81000e500440d030311810004a400421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 832236744 1250 832235494 832235513
    0xf06060d030e0909100e0c03120306010302070507030f230a03120e100203012301090e0c13030803070306060912151d0f0f010c0806060309103b0a2409 66
    0x401c0105004030b82c64143d410b601c1f03184900d5050740541c0b181070104d00784c8004401540d80b0900614006081c41c4403619100e1600301142d1003a140011055410024040008034000e42e03ca140c1001c2050011018100d5590b504142006001c225041300407502c0e081154104c80240c0c0320b0b11089601040c241e103a010020340c420f102d92401402012038170b0480078204840c0442c0d02c10b0585a06205900e048185c90020200030010301240b1b038100105032181d01c2c43d05100b0043e6000701c0c031494607880c1200019003107803400e410000500042a8080040c510a0180148143d5008a400f022194035100013000b0b05074400d540c1d0524a0368060b601c0ea0990005848001725a5500c100c030b20400ca003c04081c00c0700e6a0802450000d84140c00003100c0307041c000000c0d90060b02c80c000320761054400e0140201210420740503507912050111800c40b540800c0f9500f100d485104185140061600100c510b64988244000905c2107202e910074068803000b0081148211501034010f122441c001d2400b170800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 832237994 1250 832236744 832236763
    0x90904050f250e010803030610171021081903090f260a0e330904060b031302010e010212040e04060609020a0c141f0c0e030f06060d030e0909 62
    0x9100220b03400040e64200300944038103d0b440e41d00550314649665007030010722101506a4030510100360364001061030419102881410080b54904400f4108090602d0070f16204038140c201c2595285054045009a400c455031003017540c052034224660030300c0c15800f0f000c500c41c001c0c04050004840a080c45490b00d61a070200e21444441e02c0c0301c820550ba1940f40d802041009800258035072012203460810761400c1020000c0a039001181941d12034604500c10a030707080c0c138801010081404440f60070240030300c9001d04003810405085107881c00d054a00c21801d4000a810041e03001c101d10300781c0e4021b000c610b2a080318600116a1140c440c02c0005402909580c119000303480c044c400103070503d544c401c1ea0141c40d80c84c0d60b9440c04058584644512240c110b4207400b09001c0c1c410b03400c500060b0b4200f0084080d150b24404600400681c0c4050403034074850302d080e4040e4104403c01c04040c2801310381158450303002c0720301903040c0f440c50070300f102d0400d104240c141d003000000d0b003400701258002802400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 832239244 1250 832237994 832238053
    0xf07030b0603060906010311010504091505010f090e0f06180103050102070c0512210d0f06030209070c03140a0e09150f151b0c03030a170c0906090904050f 68
    0xc064a490091598076402103811203d5500804014000035103402440b607096201450520700f45a21954650100d900040c2c1e401c4511042c40b03410030140d43c01440a402107403090402a240d1840d240a1401c4500b0040c49a010548491300189965039034054030322240a641060a03c0c40d07071a440e190b8001c0d4403144c03041d201c2041814000a292401003541c60300f15650310082c2404c41c14483c080312010b20038800320307144040248444031389001c403841541c1e6042000800810400d00d140140702c41c02801038989020018000300c00c00101e500510301e440c0ca408140f454a98819419200b1624201080a40c41c0e004c2d0092041c06100700c050302c3c1c141d151a1007182c091200b59110803c21003028400011805580e00c280180c01c0400310403031600c0c116001d0081074581c1c40407280d00103030031a0310440071840860b030b01a00e1100ca02c0c519051032980102d10090007031600840000050b0140900b15105108180040010303042203010b0110000802c4040c084411907000c0405030424803018900000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 832240494 1250 832239244 832239263
    0xf0309080601140904050109051606031104060f0c1e0b0f0708071e03060302060d1401090b0109121a01090b10051c050402030f0607050405090105030a030e0103021b0f0703 75
    0x600d164045495030480c1e00c00300050030400c203030030180104500d00a009944c655600c048c4900405d400f485070852440c054080301000505001024084405000c00304041c203a0030311051014a80140444070708a40724240b0a0170f94845107400d0110310b903134030781d900b142a44468241082001042d08a1b010f03c040e440c1c65070880d65040c004035610942100c40d040001c2d200785100c06e90168209840070030031600c0c5401700d00591a6000b1819985c4111040f46d006599958054a91a40008000c0c0942103118050208860359400281011800d000c4c0c494900303545850407003000115414000d5184008100080070341e590b082d10001000300c961924080d1120014100b16507200310100c0313149603428500010107980c0c03001e02a0050000402c101d8251040345004050440104a0384e44998010760301d160341c031800d202c1170000c0214181d0003c0e001c0d80c401101000080d40084680c0b01a1b4001c0c03800603228241c2d40d002580c500c0418141045a002d6142c03c2840c10b1800b28400c2c065a00038210b05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 832241744 1250 832240494 832240499
    0x415140d02451302010e030a060501120201170405100f0b10090512070513050a0207020d1511070209150112061206051b03070c05121614060c1e0d090f0309 68
    0x140600304036100c3d43e2084207403242c00015800380420385035009015003250b20300364580e035410301104c80a03041050400b60003542201103617808582c01e5205910100d402039a81041d82d281030303070303070742d41074404034905403a682c0000040015511a0301d800350001e021114050004202616010f000c3c02140c1c0030f01220450510b60040000d00c500403104058251024050281101c00080401400306482c0c40d400f0094503000d6694180c0c41c0080a000c1c941540401c414200f002c02110701160741410501c1e018860f58015070381c1d600c0704e0b49d03002c1c14025101242c040c01c540121110f403615aa618910741c0741910118594080022944030316102d040c04001c141ca80f0200c03040e0119010344800303800c0030b080002600052203044040c0510b4461012601d9603200c5640a000300c0d000001c1d11110100505c044d5005e0250112210076806586000381010b0300344645131001d913110345400018004280c10905400e04200822036014454011081240c803c0b0780c501742a1070366000c041070307000603482c0801 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 832242994 1250 832241744 832241869
    0x41713090c02010906110c010e012d02070204020f0d060501020a080a2601230909070612140a0b0108060f01020d030e0a0602030403082403070e0a090b07020303060415140d02 76
    0x5d901150b405a54212601702c81c58be086400c55080030791040e00141c09004040068650b400074002b0805100c40a030340f04c2514a8000b001c0352100c1c0d218504640c001580310700810201d8044890710090380c81d1420408104d0802c442c42c1d0200c0c00260444846940c0001601150015110403616074824444010070b5261080041d2510142d9111b451900301c04010001c0501805110110851006002c030b101c0b200c6190158080004540218449032121404440766034004181540400304070340c0c0880303049c0c04c400000e41d580c2c1108003600c140755541114240c00740c403c0008000c1e80f03911940640d41c82c40c0a24004102450943c0c41c040440100310350281102c032071018940c60650301500a003101490489441080707540500701170a00384d41c44004002103010303460600d00c2020b80e6002183d0b0390402c0c0c411b1100300d0b105203001c2100c3c140460014402c16054003c04058444c0407100003c1d40440da0000031014035840f03034142541801400012070000c039840303c1d45041402030300c4904114020598 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 832244244 1250 832242994 832243001
    0xf1308090a080d090504060b03180f0609010902100813060f0212040f0209010608010602030a0302030a09050a06090210030b0a03060b040b030709090219030305090108150d030305041713090c02010906110c010e01 92
    0x1d4988c807104c0510000c1c21145c1303c4101d046030a1a141b0850300380300c40c40c0216504104081d501c00600d41d4551b0007400550a284c0c20304071018140c1e2034074210324645080007030015210b041000b4100b030b440d40d0f81d048503560703a9016642401020700c12030740c02b824503240c107e4031b00c050808128050601e020000075440d0003550485e0403900c00f80c010f03525010f60301c1400c800a500080c0184a41965a5801b802040017048109045c03449100d00003014600343c0104001d502c0250548020103040040c2e00c40075454400c089012a0340c400c0c0e0125684444a00040140105110194051061400c00207400d5102c0c0c01401c8494025105a051224040c1300e03003000c44a9400040c022620411650a041d4859180c09500c494407001561207012500005400700429030000d42c002a11241444144000c6d01043e100b00b04c1440c400c82c1c90405900c03c400d4016102c0c0c03087e400d00a42d1003404191050003900a0350005034041010031007040010a000429040016540c0041d0703e0500c0030326600c1c90511 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 832245494 1250 832244244 832244249
    0x9100c051902190305030c01110408120903010b150d1a011e0c050303010b040f090b031c0509061209060a051b0904090b010e1801050f1308090a080d09050406 69
    0x41c0001d01200008000c1c05100c980c01241c0001903910741e49600200c001e0303a000a03511a40255545841c005203550a4030a01400d088100b041003104004c054400148501c01910020701c103601c1d00c02440000b0700401048450300d400c03460400150f06039100b840b0081801d0604041c08106c520001d180c80030b16401040340480c0401c10300e01a20203800c5154840c3c40c4c604400740b801d001e4403402c603a1011700b903800a80c46030400132000701c1c044c07080a03d1000e81c40080e1184100400444c5806000241c2e681e200781906460074012084a80380700748514111020190003400481c0d88400b1040c01e0004c01604132130400301801000081122403116010307c5005608072101c81c5000561503180044c990303c41041954425034800e46d0200140120404500800004401d40c46903d88844039202a0114189208199150100700220003510b8007985070461b04e4816031034680816407420707080511404028a921441080c0001102040001d200e59001e91a0750f501d1162030350750003440150f42650 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 832246744 1250 832245494 832245503
    0x91c08040b361603060605011b0f110d05100b0325090e0f0a050a020f06130303052109150601090e07050717031501120e060a02210f09070f0501020607030914010c0509100c 75
    0x3100ca0802f141c0e00280c40800c0e048002c142c1d00c3d09040d80c2d40c4a030300d0102d00b174608204041e00da240c001e02519003400b41840c40581b8191221650300341c07401402900c42280030f03400e4129524a039000c1d188004001444000d04003c003107400c0d0058904065640b0f8000c500201d21640b01000102950301f0704109581940b2034507840e848000c0d0455505480c2c43e0400e0b10440640f004810018824498202c20140030355211f20241010502107240402150310080c0131505000d8400790800c01d6043e00781c5c6440e8041c0161400513203c05061070040c8103000f0000e041c00d4110408030074085011004180092200800d880d0080082050229041580c0a1500307454046c1c200c032002403150211500101480f8004042c401c170b200244561581c080402038580001c1c1a0012041006050080241002a003900e0303480b80a4a0300c0c09000030b64841e0000c0a010401d40c403480706104001d03109103007800300541e850082c030084e130903440c1c01881c0382c109012080c400c52580840c1d14800c1d001c0c10782c043c45650003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 832247994 1250 832246744 832246763
    0x3151605190309020102160f030507060212070b061503090d02060a180f08070c12031202040f0b0d061809020f1504030b091c08040b361603060605011b 66
    0x101d0164000c0c00e0243c07099041d0b0052800030050055045a5000601160503070523204600794240315107041010740101c6c0640d401440d500d00000e1061041c1e03400e00313a21904046d03155403480045540e00d800d1283c89150520048244824a040869400e00913040350f0300300c882d1903690341904401d81740305004a415484541240700042510800c0c48802c03580030300035462821200b0b991741d295a4500b507202406001d514060181055403044484211404051003581054200010112198424440c0708c02c2c220300000c07245842001c0c0e4200070020002c0e1043c1c0c4040040840240000e4240598100d12070031040040b0340e403030710b050070341c400c4141900411181010f0640c1d4402e07e0007600900300380f07541e22a5006074580c0340198518080e507207209035200141400d05140c01000104054030403035403048441030100410030700380540c00701005c0d41c0140d90100d1b4607040c11903042a00d5005900a60341000c01c020080c001d258100d441183d000380d844404a1a003030500882041d6070b100002e002803807 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 832249244 1250 832247994 832248037
    0xf04140a0e012105240106030501030c0902180a080106060215010305060106050c190807150b0d0b07051314032103070302180d0b0f24130b03151605 65
    0x101085400b0b0f0000c600200380c0c07800645030b202c00b0b1400c2d5210802105031001d5049041031600724850172801028035007000d0099504640e68035425030810b01805081590103e040042c4ac4071080d0711129080e4007030065584980c503911540c2c06000140200d40140c0304c0d2401e03005444202101460491390010080c1c45141d003081d0088035164022802c0700001c0c0f0035441c00d800c0103c1105080a0340d144a2085207a44810034078000f801d0b684a103617060141842d03c0e4004401d13480e07032070003510b034194002080c00f115911380a00361664000d242c0110742c0310f51320319000300e1000040358603050030708421800c84a107007404105440051a110078800c288107014030119030b619000ea0050a0111000c000b281c3d15843e540c40800c00c045200a02610007070700010074890251403620700341c2e07045107400541542c68501800914205060240d00354014560302d1210959080b2580c04040b4890b00113054030000101d4405040c00004151054104900044943c2d18403601450484107140c203101c0f528001a0fa = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 832250494 1250 832249244 832249259
    0x50918090c120f0d0518150c160914060a0308030703110a0c0c0803031e1003020d12030506040603020d0b041704062a0201090302090c040b0f04140a0e01 67
    0x5001038000c1100c0d100740c0c10100324660307030007000100034202800205507249014510924000c0114510810300c0410042d0000c58120041046092001a00c1281c00c0001039039000d400c51040c40c0d841405402040e07400c603c03510f4680540411544040c505001c008845001c0c44400b8000362101c2c0da110144900c10070004150b6009940c0c414494100010703d030554184c8a070f0301d81c0c07040000c940064000712150b010043c00b6a042e2029290311001181180380840c0381d1401c22034802510900d1a0084c00000c0a1003031b031103620409198040e09101c0d0741400c2c1e24109a46400d07448105011a04040c00190a414144640c40407240c00400e0140b45140d40d840302140078802a105a444818a10310862041c804400900c020300322542c0e400c40141c142030703580c100580c0040b00306294200b00c11880d80540c0c1c0c00343ca50300681e8bc0445104d6142d4842000100d600d229503400803840040114800724004074401c0544115400c0c00c12001c040034104042104295141c0114080030711510010701801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 832251744 1250 832250494 832250539
    0x1080303061e09040c0303110a0803130503090a060c03110c0109031401020712050d14010b0301031b0e01091b020c13052706040c060c0302030a0e01121a030d0509 71
    0xb00c0c0502c921182103030008045004078a00700c4e03040c1d0340d002c107038602001010f5000e080d00780000c40d400054161211150b44040f02844060070121080070809811028003c0078021242d512100908408415a4400300070b417103503120a0084e804248600d4640306281c40c08241d4070a4501c050f17460356000b900359500c0501c1e240000c0f5220030950b500380105070020307055803860183c03841e89231943d6488002800c108001d81d15900c20300d0040051100042040c3d5420030240c9045d0380d44000600403480c000060f200600f001030740841c0742c04c0030303c8000043c1c03044203500486011200315865a0b0b08181c103101aa91041c11520043d0401034901c0d04074040313041d5900c42504102e6044003201e42c4031190f80780713100c0417069240c01a455007081d400d01c002c200c2800f800c480204a1401e00700c40100654a001e07499001e0b01c000d0b00144030f80b03120300300da241c1c0c0305140340000070320301c20300070040e0510000c60f2852040d486040c8a029120711b0121158550050054176000100209445000501102c074480d51 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 832252994 1250 832251744 832251769
    0x906050910080d1404090c030e1c1409031609150608071b21080f0a0b0d200603090a060c02011118040b18040611030403050a050310090606260108030306 67
    0x3c02c0e400d01000c22920580c7c001d50fa410589035501155000d01d28041e02c0c2000a8000903107075003680100081034840e081500c01c01240740388040d46031135049160109060047c50b522280c0c402c003101d980880e01620a40c41925101c5891289144068840f074054a0000080c3d5034413000c5502080e000b64030140f52400380c00344520860b02d41d411075251640201c1c100e40200d079120080b070703408820010014410800c50f0303800901203c1c04c0c00030a213640c0c042071124440071400741528000041983c500e03402c52541d0940ea10b0003616030383ea03034074041c07201075100ca0305603108480b181c0c01e00d221428914414000c04125a8281c28858540001914110091048111444d0b00a1740703030040c0e11100e680364015038000030301c41c0100310054989440c0901c22134002e0f0000505024080c401d100c0800d03840001c1e1040ca400c00d00b02140e0784d0b03c50b806401360040603039000c44031203800c010001c02c085611882c0303094141c00d40002c40203080794805000111a0007400340c019903030710500024000b450400600320741e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 832254244 1250 832252994 832253027
    0x19080306041e050a0f0b0d080901050c03041d04061506020601060c06090f06020301292a0703080a030e0a0807121827140609100506040906050910080d 66
    0x4040d50201c0501040d40c0c001c40e1a044c84a54801c080b0b89091401e004180704003c044030341001e220a10b9950f0803150007000c03e9035041240200e1100002a0108100d802502920201c039898000c00c10300c0c4403019800f01c038115001f40c10190000aa00308030178404096a0041d0040e2820340c0c245071040320507010480050780c4031600c60b0607210114002606884a050103a18056603940c14280c10131424004514107620f03a800320590501c1c4007000d001610980d1440d20001d4101440d5000c030f0400d8180c2901e45e040c40750241d16800000c02101400908140340142c801703210f0351104600e49501c9450300c800180100c0020032070000024138040700801651418207098504400b401c049415444054110480340840624a0320301284514004000325091400038010540303601c0b0f40c0d020b41c02d170240110340110070304c802003000c2280307420340100601030140280b80c489a0750010800901050b00c12240501183d60118105c1d103158544002900c0c4004002d05140e48014401c90348540e801c6200d81c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 832255494 1250 832254244 832254281
    0x5090717010b090f09041203020d060b0c1501050d020f060c0f10150e041a04210818030717091903150b060316030518060f091908030604 60
    0x1020034400104550103441c0e0040419280c0208005001c5440c841c0075000c0d20405504080000003044142c0c0415040c0180c5800b40c0c6845002040a000e8685a044400d00b000041601410514000395982c90358100c450b4600c2a640da400600604051000010f50403410f1000c60300c4403800e00744e00a0607105030030003c45030100e604040d81d07401c001c408150720018070b40395107070034881c13030102000800500b030200308408040c00c09650340d8010701da0200310702000f400e6500c0001c2c1031022903050941c4070035600e500c08801c075441140c000d000f613108549442201110101c0c004c000c0f40e002090341d82f0743d90b20036208070600201010441540e042511441c1c0d000780d440e41041c403103c10100d41a4002c1d032040a00305031080241590005549511882600820b000d10070044004c0c0680c0c0d0684188510317083c0050691144002d80c64095001e0794546c641e480790100f070000594108025502c030b0350281d801d0381c06d500100c5055081d05820003a014181c90800d0001c110186016840b101d000384080762600e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 832256744 1250 832255494 832255517
    0x201020306091528170307060c140403021003060906090b0a210308040c1e150e0303090607020307170d0807030908180d0507030602090f030a0528080711010f08060a050907 75
    0x144000d801420317800b442608040b036000104035080c0545200c5000e241080c4458404568000125000c2c40c48064840d055100c000041c09002c0ea110340b01400206409002854540300c1d150050021911032601840f1309402c0000c01c903841c680c600298180c169081c941220300c940b0116440b2502820540f0030320b900040000c1c0f41c215010608841901c0e101d00080402c0c5001482101c04030034419001c00c0c80b00e46420200a5640271040f01c4040804859444d10748420740003082c07404000c1d4004642b262810f03d25030f8030316000014401c0d101d403150b554180301640c03801130840c01d445104030002e02096007402800b060182d140206421200080e1000002c043d440d29002d240c82c0d001c0d031017998056800142e40f41c850400400700105036106400500800b07141c0d940f8196140c80c070403d0640307000303261030000310700601140754107110303503003015402c3e80f5521542032264480381d8214499001c01c05c0c81d40d200c0fa0440c01102d10700d1003032b50000c10f21a40c0c1880c240501c02607100c002c0c0301c44100501c90088 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 832257994 1250 832256744 832256759
    0x4141516051f0c0917060f1005030a150507051e0a03020c010513060c0509010c0803180a1a0a0603020d12030f0603290910020c0a060501060201020306091528 69
    0xb54000403010b4103010a0380724000300042c1c1014019004900581c0250f030a5400251000443c140c101d0000e8221240f00d558002011150b0ba015812030340c0e050182d26040018000300c14402071404480c11410402030b16144416519481204030b00010440802034100c501804040682030208003401c015142c543d5010f10b07282111400c5505460b552004040c40003070003110310508075001030b02e0801a20f04000c18001034203c44075000002c08a00c0c0010000da22201880c012404001040c070454980c0d004501d01190f40c11043c0704450070004101d03000411340046400707040b00310303900602044482d106640307505001c4039142e2058400d0507110030326001414103e12860000f1805007c1c0c40320f00782d84070701c41c1c11101d590400500340d9005c5490144180d5203c04a401d0007004c1c000500181c1d00c01e81040098103020380850058082440e00f000028803e0301034004500c105000ca8115815a50307180411108028020f0000d4001344154566408500c0198014200e200c54030054208181d85d80003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 832259244 1250 832257994 832258033
    0x110a0903121404030f11040b0f09090a080f04030302191e02030a1509020901083c030f0c06070306320d05010b01020d260406090b0108030414151605 65
    0x4591901e00a17982600340b040110200c0c00142e411078080c0310352a02140003480b0000c503882c91522481c1070f40e011038110441000202c151343d6201c1002e541303900500303445da03c10b03800c0f81c401540580205d29a402015075001003510405900c0070780c5007135201c01e401e41d420384c0c3c00305102c040785c041c822445100302040c05c034298a1460b4204400120788078240c3e206021022406074031002030755002c0041011145c494801d007007103954143d600283c1c2d9403102d000101e506a641c4141c1d0042d030000250950f84203034040c00400000c50054102e80154542c12811022283c4c1c9220b4001044414165110b4209584070381f09065102480c410400c140020300103003503040395001c12122603550b007043d50210358052203076503070060081c14041010048004c0507200d040f1240750b400a1046540009000c02c140c0b540f0044c110390300300a0f00701315513071202100c95032a13000c1e004070720481055042c024454504200380741c000d040381d42042818018004074081401090100894071b6006503001014484000d98 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 832260494 1250 832259244 832259249
    0x1903020d2609010b01170408033105010b0a050303090a060e03030d18050c0a0e070f050d0203070804020a050a0b0d05090f030705010209041104060206040f1401060803030604110a0903121404 83
    0x1c1e185200c0c4c001401a00f2482607108800b1005020003022549200550350b2110724140c09800303600c94003c0070160207903100034000c00ca0304145440c40901c0015440078a28140903560300c1c1c00c7d83d03180e404241d40c034000c2c030340510790026009806201c013a214942002e48400040e04403400c05280d01048015260320701300011118425540c2d001c01e101c8100074010b620001510700b0040c9030304100700c640d180140281288103100c0d001000c1c10440e03100b20115036104400200071500c80c203294200a01e46d01c0f095506070301c22888044003050b18034140741420104c41000c00010314240d400d95000700a044024010440c500801c1e042a1001c4d0040c13004001040c8100001a99041c5180c104001c4a41408819110760001d01081c4909a000640e90b600141c2105541220322410301c1d040843c9030055004c49429402c25030001480301c1d001020314050704d001c48050012040c405035a1003a80620203862000a10507101000030424660300101101028a04144040c0c8000303a24641c503442a03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 832261744 1250 832260494 832260511
    0xb01030b031e010605060c0d03150b03010e04150e250305030f0c0d0c12050702151b060c0304020a030803070203071a041104050705090103110c0109080703021903020d26 74
    0x801c1c1c0810780d000288181300c041d007021500e150070055042c01030b541c0c5100c0540002c0c1810394480c6c1100720b0404100c2d8003401029042c0d85c0c29603940c1c41c0d4051428841056800b00c0340c0f40718080741c0080c1c00c030984c020490060711680041440c010100b55440a120520704a00c402882002000c0089101840100305580788a81e40320794407907690307c2c120700c2c1450b106e180b80300f00030004490a00084100840928082c600c1c5851900e1b00c409000040001d010b03036580c002c000c140003490018810046610700b811081304001d4030310f55510351003240c1041c03104403002584183c20040600c0081c071403801454200038107104807410501d00c0d0f541e420040c06035440683e1004000000c00040100c400306410108400b40c50034410f0781861a8060010301072070741858145515848502520036120f015502700342d010100a001120702e50070301504950008400380e0041c094440c11040740c0418403031032440305078590300070b1003480f82c010411581a0580c5034104074503501e01c02d506001e404290303252401407211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 832262994 1250 832261744 832261783
    0x806010938130902090703050402010f02070509190f0e0f0c0105040311121002070c03021519030b03010b370b04030f08040806180d0e1f050412060509100204180b01030b03 75
    0x9d030001400a1310700600c5c10b0215400b0210520071600c4218400d40c01004641c83c00c103001c28100c0c90900901503030031103429050701d810101c0f500840700054504113201f80606642c0d0300d60508004441030f00c01c80c00054084209242409414202801c5040e5074030b88034000c0d14260900c51101d84203a0f44201410f48442408480500642c43c01c00f00444480031804003051070444540360114925048800030014503544060342506038400390081c03c042500104078030707a0302c60f05d80d5191041e100c03200102c0390004003450040390880107801040060714500102e0358280341c6103075200168005181022202032006000018200360104405030240040880801d04c903101104203d00d0601000900000c10007051a4000640c4031002c2c00d102c04010300d0610640c4166581082e22144203a5201c8001c050207405c1400074005a6840280a1170258042d1107548692003442c5040e4060b6009101405070302e0000148045210f03405424001010305001c28080d0307846000030304040c40002a00041100c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 832264244 1250 832262994 832263001
    0x2041206090209060d201207030302010e010e01020403200406050411030f160e011815020f07140a06210618060e0108071707080601093813090209070305 67
    0x404442c2070f5807011042c5c42113203d08500d9180c90200c20b40580800703a0464280706924520745554407040c1c20b070320350401240d442c1d55807860003d0003040500350864603540f82c0900d114103814180221811250048002032440142e82000b03000018000080e0b85d00c243d4804000502d51128019101000079049401c0e80740c0c42d0003482c0003a8070744014901183c0642842c1198a40794200d20341c20002c42d002e03e0b21340e01c80c5c026010120008029600304055042d03402e001d4000556000a544a4103007041b0b0036075118964034000444903002d464222640400c031000c0c244540c0c3d1085002050354000c429401c1601c3c5412390a030380444070150402c0e01902806507a0080002d0f490185000420031409104450340c9042d94064440c4801d0144c001d500c4192804d0f007800440c1044500080d0210340103a4080d543c0d0b402c230110040004402ca00c401044001c500340c0384243c4603100c50303091800504100c0030400071004010031010403188050740155601001d201603100c0311520351107903946441c001050304 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 832265494 1250 832264244 832264249
    0xf0d050307021e1906290a060201050f010605070201021c080a0617060109150915180c09031209080714090603061b18090403020703210e1003020412060902 68
    0x2003d02d910302d080c07a00c143e0a1202641070000b814000d00503031506842e9a04014a040c3c005480b0000c40c040c9a10701e1100031144502c0e00c0e000c03000070180c00b02c0d14581d10507920f1406900b40e480c110b4418007013000900041002c2da000e4801820200e205105440400b094541c4402c81e5201a0343ca05001500410400c4440ba0b20303171082e80068040780c001e864054199858059a4103414024018403e854100100c826510880c08101500207540203110107206111040030310021489001108081604074003240c00d12440343c5000110b032a9114400035086880301548611000082c40410031110000680303a101888400c1c0900400380b207014400342c0c1041001081c610107003845100c0d42000d0180400311313092a21544c2400b480645941d210401c030078254220250b00104250480e40002c00c001c10587e021401e8000e0301e10603610321144108926140041301c1141030305d40085105101d80b21147e2806c00e007088540b80b254940540780c01d48950461020300c0c2c0300c1c80c080b142140c90b41500700852 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 832266744 1250 832265494 832265503
    0x30204141807030b01121109010e06090a291201150302040b0301020a27210309080f1905070f0803041a030f010302040c020a0204020c0d020c0a260f0d05030702 70
    0x3551084010507005055441344c10180e001071041c074001070314802d00c0b281041900e10742003801d1000101098036641e900d030021400b00f1400c540b076500c10038400000540186030744c450350174003011010f1068180d40804201c0d203186000c24014a1748040d50300358813528248240981c0f1301041d07600b00d07603484051551041c80292008522034070b21990052100d0300340c2c0b55200841c40c4c02e5181c20001103048948501d20120791619a0700181440801d44110b07020540502054106a034820380d40d0b44001c2c1d51f5410030304c1d121058455008165004400c1007566100030405e0302106074007881c00c0c4d4000a540306060003d81425520180180d0804282040b451154036400361141c3d45061580380340d072070701201000c44c030101400024410795444540040705482080120130341039019200b159034141480c0c0099171000112101e10051145480381c0c01e060600c1c100d14421143d00d401e543d0711076201d81c004500c1c00d9807150741c24885403244400380480b103442000324580e0303880c84d52141a0380b4140890001d081 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 832267994 1250 832266744 832266781
    0xa1706010503060f0c0a0e030106030b040b1e07050f2512050301080d1b02090c04140607020609040c14040621290303040914010905071b061503020414 66
    0x30f0304014100079424400b40c1c82580d00c120310050b440c0e5141400c543c15601c98403c6811560150b1030481c0c04400c200740c55a01d03900450003094800100e40d2904130056010500c20f40403c044011040410300030381c06100074044034055081001d0400b0072032081c81e03600b119200b10b032009541d8200640c00170f01c0121100085600000d1070440c2c915810020083c2c3c1e00d00d40c002c4c60301e0400c001e001c103a03104e5201b5001c06840e4180e0041c8540b44e40e0820209000d001d41040c01011500d0f081240c124240d4a00300c001c4406150b4054140c40c07c102c50001080020583c4000000034007800c0850324000541250044c000b80c140e82d01d0b100d40070038401c44118070051100a070910b0380b030301d404401c95036a00d020016030070a803409c007841c01ea11010000070030706500650380301c1075015041c11000c3c104d24100d08030440c16201504020003055648202c1190000d811141c007240c1e10508182c0e0702d010880a40143e00320040c030038550402e0503070369404202203c15803030b11880c0ca21036100502c0845a00790004104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 832269244 1250 832267994 832267999
    0x2406031a070e1206040b180d0e040c032c03090303041e09060b0d09321b01080114010e1f0908070612050a0b030109050604030305060d1707050109020a17060105 70
    0x80350446802d250380e407001401c041d1400340614000f801f0303902c141019118440480d01900c134843c44006001d4000c4001f89606032203a42848088100c1a109109412810b10700e00c4101c950342d8064045518500c040d505421154007003002489517648007000280002c8c51110449001d00042c1d00911094900a411000815040850800042040d52705841e46851600320000c2c080c400c1c0e01d8162000e0005aa092058500040040d80100d10f2558031070071f1080007100790f4144520020460350110b2102c489940880c0c03aa00050003821540c510300681c0710010f051400c6203440d030f200090b44d03011020010b074908214140d083e0740d00ca41d115003a4002440400010804641009005410082c1d0000d118074030964503c0081d08066441d0003d10380741c0b10140082040001c2410b00e1a102e07241218258046801c20010a902e41001d403002c58245811504038544a400001055981d501940c000c0d1120b41d00e45000f02c01591b141d91a2100421078100c1c0380f0310002e05a030302c142c01c182c0c05131b01262 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 832270494 1250 832269244 832269259
    0xe010909030c0219080f07180b010f110c30060103050c13090c080109032007170c04050f07121823070f050a122406031a070e 55
    0x103a0080b0320491010350403104800252041000e03004c180509522003503181c0b186040300600007030085006001d80b00c407240f4038020b4150006012003500c0385448811700041002c2c00d9294460b100b040034601250308a01038446400d007080010300395542e0702d0b081800c3c02c1d55103810794015100e1110358541c4203201d00f0203410950b00d1501c0e90b80d194404d00001e0380c002e1108042c40d4100048550080c0107040d0f0101202030030548821186008020502c2c088011410315200c08040c8440480c450551b00c0310040100308141c2460a035085256000f010011103110303541c05003d00785ea5600407148100c049802c1002c1c14580380030024064403e1695110300d051502100300728080315141c0e11103005801c4001500d1001350189008c030345d18011980068a80107000300803030b242107000640c0d000c03641c0494031080000d4649003c481e1101c507100c00100048041101402860050020240107000d036000016520340c0c0c03500c503440a0f8184508170b1031074410020400442076008082c85c3c0b26007500751810b4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 832271744 1250 832270494 832270511
    0x6210209011802090619020609070b16060b0621010914060d05070503060703050108062211210313060e1503090a08070308060f01111209190e010e0109 66
    0x3aa0000c41030056404400c011420348411100e0350301281d41c1601c016000da50749203007102e04e001000d00c0d0030b021640180100c1011840d291000100351003940c46810086c0c0c6000d40da50040f0100c1c40342d2400884046481b44040030300c580d943e2018000c0a00c90007000a940c030308050300101d0f4282e05800800345180b0b01401c1d100c0c442c060b00e01e0198442d6081d1451841c03007015080840c40d0041b1540716941c0351107510100020103a164021504988024049542c02e07150307080c0d40c840c0c0b0424140030110f2081103c90070808901034030b00400241c0409008030a84111032060302403440300407060f2909550000901140d181c2080c04548010032061074049a8201e1060001301140c001403100118444088040f40818805100261600c0d41c00710041d55203503400c0c80c0242001400b00e802034488d070b1034503c6030010740d4040c9101c62103007066080940603007198000300310800d80107400300e241c0140480307025402801985c40c0c2c00300503010b8078900301490f600d042c090000f2410142c01242d00c0b241414001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 832272994 1250 832271744 832271749
    0x18080307170405032508060106050d2c070e010e161d130608011d061305030403080309150c0a05040501050306040f050406020c2803110f030d062102 65
    0x19612016408261107480721410035030750078940655000640d03d805600012445020454030b103e2030f583c1e40400340030516035525249600e542c400d12555000c40d00c1009080d191680700e030700c079000324003010300d0b401c01c000400400c003400b0802d03a40840f6541d40c80901c0a22410321003d224900508009070b0100c02c1d403502910450004400e60f0b00d00f002d026224103900c890a1709400c0424080341c000c0c003808012034001c041e10016100520480300603510704008110010517402001c01242d131900001d180075107820440c02044c0b450300e07100740c9150000303000100001e44002c00460140c006200200341c0c115045c444c88801010141445520480802ca008402ca03000810b81e02101c04c2401d0007a20b1790340702c00119020b800501e940402035031a00b0200010005544c8c050524004810304031341d031000c440360021004643c0d8032900c09003901c1302400741c40000c1c070450424002d070304500291480440984507551860300f142c0500121692075450500c008403d450505054024511900580c41855000b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 832274244 1250 832272994 832272997
    0x10c02210f030403020f0109030519081005060309010905100c140310060509273c0703090818010e01030c170403030b100e041b0807030b181501180803 66
    0xe09200700503000c800181454002d000030400a81000e0090043c0c1c0c0300342c94000c106501464203820300c0041480d1f941103091040b0f400502c6030b24145110034000e4102810000f90340c0001348000d15941d03c1c1c02140c000a001403111500c80b44003154003048840f00401c0c054481003900210405c0c1c1801071081116889240004c8012900c0600f041540d841c0440046000b00d40030610b4070340901c0c503514004040000c030391900c3e03100b0310601145003104900c10044100c222658800b0b00004280c0c0d03501030000100e40e504954014a10b0308002070101203507503034243c031600101400740c0807088e000800350003960451104c41803103809180400c00b003c3c090002900042c0c08035102078282001da4002020180250301540551030011300d171841d600020316000744910080c600c03050060f820440944052580d03408090003820b110303154007a50341d03101c81080340101880e8000c2ca9018105078034148810381500581c90046554087d0080724805010014240c11141c03201c17103480d51984402000b02500110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 832275494 1250 832274244 832274257
    0x18031323060f0732060f071b0314070c08070305010f02032403070308130501110114040219150c02011815140f030906160c08040b0f0c0d02010c0221 65
    0x50440c080e148004a049050811284d00e9091403a00040280d508940c00a403c070b21400c0400a041c0ca141d9800108441e1849800341c1009461110b400017000640030b00c500203004501401c03200e0601c0400c1d1150002054554442d40981c1c0203000140203105003030040c081108201c200542c40c50402d007881c6681d500008480181190828030980c219640a000c1c2100039a080603109403151040d0140c40d15030744444c414940407420881c0c1040000381d060082c1c41480009440003040313030b0390301c4c0c0a10201690009085a03c0c141c030503130210300d0b07001d0719040090755240d561b90604141d0083c40003400c0c202c0022107001c0d4090314104100301c0300b1400351010039108807918008001c012061411012401840c4009c00040c8000c401c001800c00300180042c03082c0c9144100c9401d8851210b41911010b0742210041c080290801c824007070350741c025005011135122050300c0c2c0d03d0900c014142c14106241060890010f03510380e0240d02074180c0c108568400510b80e084005540030383e181c43c0284500c2141d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 832276744 1250 832275494 832275503
    0x1a0901180f1509110f220b0d120507030305130b012105030d142805060f2d0301020f04030f050316240c0818031323060f07 54
    0x32094001049036400d1400015080c010092180b00c0f043c0c545881e09110070f00409010741c001c1c00340c00703c0600d000050a606240282000800e0189142040010303140c441d00d1240c00540e021040c000007600580c40b80140c1c440e0340d6440d5221440c5103001001d070f0702c02402601e001c0340c4048580c0c02080a640520341160107102200382c192100001484c1b40b09043c004c0908180808210180c6081c0950050319440344d6025034810513503541c454042c04000544122450055130703d191050b01480c551000b508602c004010300d0f08031000381c000503040c07800035403e0802482c985408840b5070303c10a00c0d0341032079002100203508040007610181524010b62001400004c4e00c0d403040b106200d420310858602c450b06440045030700350a07003000c4054007024485000801c81244214203110458031440710f25041c207940b501c0d801c3d10740e80c20350b00c41410f1030950061540400c12685405101d0400e10300b004120140ca40e41c010540103036069000300b40c200c0d1310341c05440200401003202c048071040300d800f00e610 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 832277994 1250 832276744 832276763
    0x50c0a031104150b04030c030c0603050c0a0810030212030903070b0c030d052e2315221e080c0319060f18021921031206031a090118 58
    0xc0f81001d070303802465016541800d400030b400300921804d11112010b0b24018000c5030038040c1e44100440490360101c8590007a0041442044001807050b403003a0b07002202130070262401034490b000680d165100f01d50403c1190f200094404e15805c0600614004000007030400b0304040130000c07119101c1c03064603103c8080c5070b40d950004102c1d140d454085400c84030415401d114a0410000e00301c2d68180c03d000b440e883c2410603c80c0c82130082000310a02801c0340c0941007484400100300030040c06d03080442001d40480c2c4d4030091540c5a02540b41c17000041607600b0b0300100944240715a113104040503008000d0715044104840919100040c2400c01c03081145000092240303a801e00e400200400701034880010b082c0080c1ca55880303c0c4600702140d49008503010589d5000030700b062901040c0c6c51040c4100c03041002c3c1d201c84c80d00041500c07181c407240a8181864070100091200c400c4400f1904125422800802054400750255048951010466000700040e04001e080d2100e0030390306034030042100300c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 832279244 1250 832277994 832278011
    0x30a0308191b0804031202130b0f09040c030b010e0a03120c02060d0609061a03100302060d0e0f06010915080309040b1f030902090606070b04080304060b0d0f050c0a031104 75
    0x41d510481c80c2d00b5009080d5222034582400080c1000d1003a04d064001900260070304003503c415108030b8038002c104460300c12510f03190984e8004103810441a0f0040340360148200c00132900c460003411a190203a07a0700040b800700040001d050b120542411601880030b580301840000d117000500000c0c0415418000d0600400748000f6140d0302c20038026021141c14108000f60501d003541000050b1081c181c8850344000d0319824010241c0802c031020015013000c01c0c0100003504184004160050301e0020100d07016007480c807001d24103990700d0002d1815038080e00c01040120a1441050404050480c00d003064503d05461180c0d41d00506410034401d44e0744110300d001c10b40c3d039a00444000303240000000c003815410302002d0002e000740541607009843c544e00040d9a03141c6401100d00460340182c4d0b8000030f40f04d545802e0300a400041003140c0d401c2c0d940c40310302042d60f1600c000001d9a44a0703501442d41c0340480c40c100d07040c24908034910340125001003041c80090b00c030901040424906803000146400c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 832280494 1250 832279244 832279291
    0x2041806060503011a0a050d1e030f0f0309030807030507110106080a02040f0213150c140d020d050405010f11010204080a1b050108130201081b030907081b090f0903070506070c060b030a0308 83
    0x25208260404011980c903272410405401012a89900c203650704c402c5840422000143c0c26107400e90300080001d41c0d07110026114034001e500c200c0c1c01c03d2461505003081801c0d8000c003030850300940c203c44203603841602c1802c01c52505005000c0f090250078815400c2c08640c009407c44905036021301e403640c14075495450481c61060320341c0851190450071089010001c00416515180001d0683d001030050040141704135004000b29012604181e44041240d9040d08084074203030521715002d092035400f00800602190100000c440107402090010144501801007203014160790303101c14140154601001043d50003c525140d0464080c2401d0880c2d44c0d503000c00f0b07410800c01d44595001c524001c001d10a00040001c4c0d604160349200c0d04640c1d5070458581d8240240c80281d081d9a40551480005100c10340d014195035000b0310454126400c002840d913035507040103403c44a09001030210200502480340343c0c00f9000001c4030a50181c480c0740303040d803001040b02c2e100030111551035149038040001c40c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 832281744 1250 832280494 832280513
    0x18010507050c041503031b170901030e120406120905070918020a0602030c0706110a030e010c1205120c07051c09030807051605030601120f02041806060503011a0a050d 73
    0x1481d008108020f84041404460901c10301070205400051440c80d4800d65440c0c40c600090f41c0c188c000f91b40c201d500d00200110174031544420303c814105511004035100c1303410f00700901c075243c2c0160f4000503115411f004004000c4a9081e41d0b00005504110810b4041030001c10320109540d0305110100341007048510340e01c04010001c00094200c1c500f040005503031035002c405031041ca2001c9098440b8580e6680086a02041441007002113801207000200028007a41c0307180c00c20b0f5018184032003000c01688888540e698071101050120340b0000380e50b141d00000c07980c2d03d544501b000e20340905040141d00c1d6240c1c2c443d001c00b01c941c00346158081080c20380780500706c480020b642c814001c03907a509a5241c4a40c40d0b854540303800500c2d01d030036480032a65140100d2203506940101008051a5000380c6800b03480e40034600081c2c4c2c0080e80c5855060250410850120a2030301856002c079040b46000141401c6420003103000300c5064084c1e501d5100d641e6601c0707a040484200b1240351590040070b04244451 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 832282994 1250 832281744 832281763
    0xd050709180911061305011d15030604060f09230702150402150706150807080a03140d050109240506120402120f060403031812051605010c020f01111801050705 70
    0x7181c4041800c48170700c1007060025007513680070307607514006814034809689a0750107103a1603a4454500020510758504c40781c0503642c4a100103002282d81035440303c0f02e0f8084c4000d0341042d503001d915104900f0740e01002d0190581c0045205000400794904504000e40b6034050344407000010740e661000c90199610009269003240b01c21200b01e0703540401e45440390060000340000010811a1500002c0f440404219a0100c98050010b03150355050341d42d04545669603460303c0009020180198010041540300f1503000c0c01852000103001c0c08810300c1500c1502c50010441d00c4c1f1050200c090101d40c890784151640d0800d0411600340710745544c0300160780105100320500c00b07403048a4059504e61000900c4074003590198170100b0000701401e0050201c000c503940302401c071410151040c40900c2c481e00050140300e1820300300300c0d00c40c41607079203060a40380000044e82c01a8040c003d84000c0780700a128000001c1c030000d0546191483e91321007040c143c243d1803489414400003184140038080e040c40f43d10b41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 832284244 1250 832282994 832282999
    0x8161106040b04170c0a05090405030705010c0509130b060901030903030e01230c04081e010e07080f0d0801053a151a0f09070c050f030d050709180911 66
    0x71550340b190b080600c1a0041e124512440c81080280055014081281484003001910181d00309061a050104112000c0e004075181c0c03004005c1f42000c90701c203201c0d6960610065540360390300d00a0700201302008540000300b111207032401000001d40d68a00b011204401000c0c00d0210319445030b81015030061000c40c9481d10b85e5400c050301200c49103075140300d15010070b140c40c241da29140c851242464643c050380c01401c10a44c4800e00003074044040111007a0b041c0381c500008203402a00e8461541803507415440010140d01c100c1400d10124410b03c5040344002d01840c102d030b42d40d0314120001d80c410202c2d14140004640c9a080c2044503c4100036000281d002d02c00111000d61807480d040d404c10054000c140c000501d0965840800381c1e80200b044094007008145002e40040301003001855400580003a0174051b80d48001c8001500c180503440140580074059a01d5550f000200411ba500c010115420484511001d2008020304411881c09441c091030000d03070b500c16454107000c0001080d50301503 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 832285494 1250 832284244 832284247
    0x20a0906112a041d0a060504060f0f0506010e030f100f2004050306010f0e181905010204091401030203060a0e01110c010c0201110f0403020913022115010308161106 72
    0x1200388040d10501181941c059908105010a030202c03480e104c140850104103540100c00030f080422501c2c2c010a4100b0f01841001448560508a14044071100e22600e50344030b44400c2008030b03960b0440d82c0071700c06040a4011b8400230318503180c02611070242c14050146280e0742c61605800d10311a40c80314210035400c4418000804128440420302d800c903101d100d01c20b02c21100007041c0800d80c003c0c0317003080b1001480d101d1003030f0302d6070071400c6010800401c407145c49200d100104003688080c03141d50b0001c0ca00540006940394101075040061b108000b1208062101c680700400041e14006285903010706c09900c0010740030581310005001d803003030552380302c001c1401144c01c00700c02e0f0041d800301000c3c10340e80d0002c02c050070134171410708614002e400c0000e4900100b800104094202060705071790141c2001c1f00c026800381d0341d42c0020750181c00c07151107013031031030400b07100c4442001c080000e540035600035100b482d015855a40c416a040c414496003440d82d605072a15481000030f90961043c1f008001403115 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 832286744 1250 832285494 832285543
    0x61508100905010b0705010507020d140a110313080705060306031213030f0b010603051003030f18090921020a050703030e030a050d0302091914010309031112040509060103020a090611 80
    0x140c15000744034260351951a080109803424000500bc08030540c040d01c1f81c01040d45c44111030102da41115a80c2c0c000d00c0581c4514644039079090006000301050002c15015080c20040101c0ca0301030380f60400c1c0e00902082041c0000317a64009008403c0c4400b08505a50390020004140d4800195510040c9a80c075609614400c10024802031410f888581d542005255181020b80074001c403644405004030318032098000c02030344070307010384076152680c0100703440034507940c403e50070450308651002c1c0c501040105a191690745207003003503040500144004c1409950a8560320344401c01440014181701091802010984052081302000343e004001d40ba0340c40c948100240180d4082e09a15200d54024003a40c2800004500c2800075070f403480c400c201c0d90410040c0198010000810240c0038014a0f55416107080000c124070180d2819014041b52294901002e211403403030040d111b64103150050000c0d10920342e00c56030100880d0618a0f1000400d484c000b8030500740307035108182c1c90503000c030320055 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 832287994 1250 832286744 832286759
    0x103030507020112090c03060f02090603011e0b040311060711060712020601080f033c04031106041404201b070b070506130201023d06150810090501 65
    0xa040000d000781c844e08001140c294101c81140c0b14440010300300101d1300824800f0400b10340c443c1c8519241801c0051a240c000c0700080c0300742d0026440026240001c281c03000d80418040d80d014010203001074258202800d41d554600c0404c0141c030a0703400b07060701080c50310038032911108010b44008060074283d641d80d000e040000820030a12061000b6204ea440001140180010300c0c41000711503001450401b80a050540c081c602c4068200c0200900d80c02d620715868018200003c50f00940b0a030705640d50314500d4000759001c1d058440a205074001d010400c480d50740c200120240e00001c890015031107002048900840e80c1020780090340c428003046816860b101125000714002e0090100c0d81000c0d590030700556a4032401d04003d01a411000214912840e9003224080003841401aa1030401d000e00c030710321040c025400841346000d0301002c3e040c841840c03942440100c1d10121b00900c0140e08050320042c400741004c90b041c1c100300c1c0340800284047c2c83c441060000d000014000d00055035119070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 832289244 1250 832287994 832287997
    0x60403081c0e0607120b0a0f0b030a15051c0516120507050409030203041a19030b1c11010e04020405120303011508040209010b030405100e030322020604121a01030305 73
    0xc0c0388489034582040e404200100083c581d01c10401980c1d500040700f854841c803c0a8440c0c600e00030f0301711083d5080400c2a090f582d0b4103a000d004440081616446d02040d0081038481c200012098101e10140a1095807a40404030b11084004030309840406007a2400500d005101046e21803145580302c00414191801c0040d014054020070841d411681c44408100c01c4582682008025134401c010030407864008003000000900500d480340e04080200f181c00c1101d42440381c410340000d9540d4501045440c1c0700500c0b04000341c610103680c0d06180607130f403001b5441c4a50041c81d414040d01200004207640c43d40c0440d009840040c1800d07041544646113250340b40c0007030050100b00c000051841c00307114800d000451040340c00a014584903441c0038001c00c07050340041d1003070b5030b14040d0814003480200140603045008004600450b901d02d00b82980b010b0780c0c07241600c0005102c81c0240d017400940d90310801d44090b40c460302d0611803d000281b074540410403912100d4901c01c4200e20000080c103404c40c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 832290494 1250 832289244 832289287
    0x1a1204150c03020315220c030603022701030b1003290106180608070e03011a010f0201020a050418180506070e0a03031d061626030c0f0906040308 64
    0x100c052040d00790310001502a804100d60006502c2c0a440740c821aa1500901280018a80d600c0140a80426145150984034403c50354001300b0f495920410450400622094050502802c44440c143c54030210941c1d022061001509a50741e000100d450f0303004000e103c02c01594401c032404006458013004800302c501c01422603d8003e0b1070000000c140313020b4413030b1030084441c05800040c501e0400724152a008005480181001507a1088081907102446909054071110084607101241007000400390886081035408690041c45403140d0310341c020043d1400d6500581612078101c034907800b501c00a010010100340340440f8009203206101012508038060a402e90f110800c18411000340040403115220080005900f040840009400e040c440c001020005090300e1800d60b5010100107100b520300e2040e40c07500e0400500213451038030a2500d22000307003440328103411854141c0d20001c480c0680110502c104500107088401640c82c0703c200d078048e5a018520685590701200c1400481e903111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 832291744 1250 832290494 832290533
    0x30224090f0309030d0507060b060309010209040b060c2d01090b070e0402041a0304060b0a06020309040b04090b0705070501090b0a0f0b09062b1203051608010605041a1204 75
    0xc207202000180080b0480341200000f40c010b1240080406088596134030481d81500d20680d5119104020b0340c0d200e0055000c2c0c6a1b6100160f1500d40071000c0200720703050500301500c5180b04000c0c02c2070b101c0012401e5014410070038001c0d0018050030508141c0030641c0b83c1c84482d19441d040d41e00d41001003a6040d03c1c02044143d881031160071201c402e00049100340c0c0181c05176041c2c0c541d00710f4450404d440080d0b234000e00c10f400c045060807510300400c0d84c034061303030308204096000420585082e08285c444c2d0200b000c0d0032541030000000b65210605480e4028007078400f0084005562401d02c00d003500070b118550b0381724100309248c0c0f9052010a008009c000704241000b414035805643c1407901041583c01703114010035110f00c0d01014036420b07545030003000000c00c07000d0004c0e15480106056449003074030000c03181c0300810039181c80c040c02002c208020780d4250a0004060051019503404429a4159210000586000c3c8221040c1c907540f800381c81e400846001441c010401003040284507900115401c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 832292994 1250 832291744 832291753
    0x19110f0301060206090307020a090e0c04151a07080904020a1115040201080a0e0721020d06020d06240509121c0906020714130612030806092203080403022409 69
    0x31030f188070f500c031f104029010b58418401401071101c00340c6548820a6800d4440c01c4400c0b801000300031800340c5e030030030791809901c4440f91800c0105806d01a18104c00d500c0e01203007145010010303900c0c8c1d0420b014548000d40900e0b40442d00c0c40a044c0500d0404001200403801ca800c0001d106107001c10060044408900094103440402c010700322a01460060b4000200500740c600c1c180b114840718010040c100c0003600c80b0014856004d80c0b030740716605565601880001d40d641107240803036019500f881e030100b8601808120100000c04001052409079099882c140d03a88102e81c400007020a918078a20184038002c1c803901d414440304041880500c80c0903926103044403562140b060380c0b91a05886124142141307940c4414040c641081c941d110642070341400992552a46817160303c031400c0b000120041031101042c055245070a8107039991000402e05900c040802d24040f840300002400c1005051100c2c1101007400c042c000c1c42030a400b0490020016440c0e51203c042e84c85580040e1401f1499009 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 832294244 1250 832292994 832293001
    0x15010807151b170d14010807050d0203060a0902061e0703031121060301092406120c05130e0d0c020a05030a11092a0c0c0306010e19110f0301060206 65
    0x8180c0c1d10b011010300038607203002020985803424018031040701e010b1600000c0102d001c00c000b541c0f0400314042c08034a40000719605284159150034a180c1002d07100300d140c0c40c1000016600007a000f580b02e90007000200301c4c207200d8030200e00640903030502d044142030903079020442c0340300c001c1c06418228000c0c1e80c01e00a0400d484d110140501c90085d142035202610002c3d0001c2c0c210303610143d50070200190000407105031607140e81c0d403a210707050b218010155901aa0a404101138000c850191005074480111429984d980b4203006007244546402841429224403100c98a603001c05100402401a83e1000b621440003d000c002c102c0004ca1040d604804085442c0c2000550b503900b42c0c0d400615511107039055810041d840900800f2580035101e0406120035903070038192056109003c0703111058271078488441c43c43c2090240e600c0c86020f680804010230041c80f83e919139030f80155100b0090410301d00041c84000140040303181c0044192400100018a1521540190b040301d035a94241c405a44 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 832295494 1250 832294244 832294247
    0xc0c020915030736050612010e0706080a090210031e0e10090c17030a030f0506090703020d11070c2103080c0d06210c05040b030715021501080715 64
    0x41d404401590998080701c01800a2041288220289410010850422410b10900c0c0341e00e4012905412140e507110001d210040c00c050342501d1120486000030300c26101c5008a65a07101003a02c1070314100041d40c0085000407806503c034000ea56009000142d400200407009130103000c3d40d03145008200074030380b4488500c96242c41484500c0c08031130094441c000f680250724001d00315005040d54681042030740040c2c0380d81250940c500303042c02480075684640070740d00c01408503003861000c0c86e0f142e0300745000c00800355622544a40d11122604005844445641504d801002c28955244080b4800108541030003c404900c0302150806035000310300c0040f1980b40705440801c540001e0101d02c450700814072462641e00540030042d82d03004000707811680d407200301d80944002e410001c48213485890004c140400a003000780605010b0303c0074003851980da00400d903910f1483c8181401720707070b600002c001071500c01e004500006044101c14042561600d03030640e25042584500c030501254040c41c01c224a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 832296744 1250 832295494 832295521
    0xb1f08071b15110c06010303020a15270303061706091e03030a09150504060914010c050901031112041b080109020d02060a090306050a060303261b04090c0c0209 70
    0x11680484904400e181030150840500a005180f4100742403c1c03101c0c2404090030049503000b14001c3d4010b100342240f0b07003052004944d454400030320321070070482c07181640c0101041d4103c201c0c880340402c00341c4d08101c2c00c04a00074042508480401240307022a15004440003500b60f0045190300b060b5000000002c864160f20008403c00304980c1d0410f00000308012120382c050810315000b4950f0f8500480e40341f0842040f928102da04481050785e5403e05d00c20702c40c00d400c0110440c4620002003022618084001c0d1683c0151291181055241d104030460200b280382130325000b20060790045c1181c1400c0c0781c403001510002c2108410107944603000520188140207007444e07660054101c2813800b6240c2c0901c016903010170013100510412a200000080c0c0c54130804d48900940b1400098132400d502c0e00408103002901400c0e0640510f001d800810300b01e1244d0039821502c1c9a55400a0f412241101149070042d5840040100d103054801e69605421030308081030240308907101c04d01c80d0f0300e0b548540c030032 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 832297994 1250 832296744 832296797
    0xf0106030b181c12020a030504140c0604090c0e040908040e1e01090b180718090209032805070806070305010504020a0c031404030204240b0c0a060b1f0807 68
    0x1d0f07000d4010b5800d21011980d250140c1c1c45607203004040c6411404c1d4000c00c0e6480b4001c1000020358817010007043c80260400801055221030207401c4007280b090006a50303004a001d04d070b02595a44250002e594050b082482e6501c20180050149101c17a040600702500b09200700640300d006400003c40d43c40007418000b000c41d81900410320a40d00300350061006000c013542064001e03100031110080c0400c6034a10901c604007a503502d0308040390520780120000381c554060465035005100c035403003955010502e060312120307031948090700c0708806000c2c071040f001a800c050018064590003240d59000800c0062041c0410f49041c0f0141e640e410a220813031268080f094001004c41c2c2c130080000703200e04a00c40b180900e64100c581032070385036000101119603102c09108902c0110002603240c81101c0d070031400070649032400314108047d400080741c0361804018000d0030321350303150002c1c0450b0355840b03038254a00030f20f42a1074a400d40f0066002c3c019210a6450030081210100c05803208081100c2454a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 832299244 1250 832297994 832298041
    0xc0610050f0307031a0c0c060a0e2103010b0306040908041e060e061b010b100201140703060b0f03060a09022a120f031b0c150c040518070e030f0106030b 67
    0x1178448114840b21a00585092503802082081c40e80216082086d5030180301c01900000f1140d018962203031602c2660302d0025010f04120944402c2c164680d0140c03411a0006c015495032552241c00080c001c01080c4d40c02002e02501003408030321815210b032006032400e070b00c0b840145100d40b0f6075002d444510090706259401081041014411103c060001102d44204400412026000790020701141d22100000005030f42d43e081e80c09584001c2610b0541104090800b04912400d060004441d4425140039007040200003003c2041511018903100041c07004c244115140d1090000c42d10000e0010401c4040c80400d180100b030010801244408004120b011114600024003100348199000240f41d0f00c1820060101c0780f0060350300b84001c03c3d1903442c82c40641080301c0300102e500103030500544210b0306504248801d200720340f2503000c08051900404200001c1d50350b000400c031403001a448965030180208038112100f50300540018069922440c5203c0250303851201c40c90500689040004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 832300494 1250 832299244 832299263
    0x1020715021803010c0f03050c0909010302010c110603011805150f010e0a0f0b0a0f0503010f0501080903070c0806150d0c031e060c02150901140f0a020c0610050f030703 74
    0x51400103a4000c020b440003034124060100c1140000a003140e01c0801003074081122404201d50107076042c810a41c0c09600191084d0400a606011a0b128601400002c0c1400082212941403100030751038a102d0010007400c05640c0c3d0703107904510b24000404c1030b9003c4003500740408038202000d0385c2001700e43c045001c0d02808080d901e4030011200200c45072100354100c10203010100e54403003400c51003006000c2000d0090750b03861401c0d6006018400d002070400421400303000606c05015a80d560a0485809107032282c00c50f10b400709a24194490303204020160381c042c2a0026820344041401841041c1c800e807280c4c0180074080600001300c0061600030b001040c5808140b0010301c100d500009508100003c005601e41c469940d075045500950010b409640401c031301a12283c40800440c3d03000000307200900c905807003200301021404014001100c0a2103003400907203500850b5064620300300754417080301c0041c20300340d0961410181d01c1c0507441c000c3c070084605135003904000070000102c1341d1024009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 832301744 1250 832300494 832300523
    0x607081323061804021312082a1f020408031b1b0117040303020f070503180109080a120e03120c060a060510030b0f0d060515150d0207060608030f0406090503010207 72
    0x29400f802c40086e03030900800303000c00d08040a50341d401c1c0240c400c00010f0b681d03c00d0840c200070803c03200c5d20002603150703054045281c0700d8400720f05400401552854a10740488800717032700703001e40100d420400c02480049004410f21114007400025900150140e0b13a070b007200641d01c1e90a40b145034030b0450106032001109100c40254000140e0301c54028900103003812491865024140d000c40c01c2a5000e0f0707c00b140300f250300c1c8a0f504840303000390401d003803d0916500d013000d05030b03c07080d000c98050b0000441c1c0481c2034080340980e1111441c07010080a0342c2640c0301d89100c1007582e400c0354000c90028840d003c0040c00801c0d25129500c247c0e40010490100711101404c01c5001c0e008580100d80c000800040300996511a0040119003511800700403e0610b07250b500340c0810200301d01c6c1c1920030201d0b04c1d8100303154501502202c404600e129805aa10b0340103080030005050654040c52052000083c01100a00b001000d0010f80303100781d50302010f06590300109400d070f0084104c00307000b0032266902d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 832302994 1250 832301744 832301749
    0xe130b0d030513030501111305030106120204050405012408070e01031e050a150e0607020604080a0f0c080c0f1b010806060d2003070311040e0606070813230618 70
    0x10b0320480c541e1103815040107440307942d294250b0f01c080701c9241c0d858401089040e91001e035088c5078805003c3c00d41c02044031620f04103841d03125285150001c0d00503640e51001c0f5080c014203402103031410001c481c10321440700f0b469003101d1603541c252140464134001d01c08041114511a000c0ca41265001041a001c003100d502c1000c45010050760101c40e94403424964a0000e03211004e204024180d402c8000303800c152102e02c081c10203600402001c2150007413402c00c0001800e43c41075414495103840c003503928403250402a11511130101014100c900003107141c00e203030400002c50002d00c41600040e076030401c02d46070641008511051000380070505072000a413450404030003a00454130380800205001024910040f0001418404204210b06c008100a85990180035201c0303d04a16824245031514200d01000b0342c081c01760029104100001d0840b0521000301c080e0f944590784401b5000d034044d542c1240e0618445201462414407950840340d6200c0c0c130340101130300c102d010000c104541e980820001c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 832304244 1250 832302994 832302997
    0x606010305100f031b09091709040b0414060406050604030b010303050a05070f11031216080c0307020a080109110d03020319050c0703150e030403030203070308040f120e130b0d0305 79
    0x303020714114120302c000900035402400c1600850003000d070007504800740555601c001d500341e0403208a02c0e0820541c080055105510007040000d80c402603610f8100d41c0d0001005031480c41c0f40541d010382460303425030740020702c01d100340c2c02441c08440810210360760303a06220490140d880b02404080c1d00780300400110b0301460040540c60000d160062512501d41e50352800004910b00c203a81004162052035000e003010404202009117048419050081c502030380740141c4404840107000c6980440e5803e50f0300340030001c0d5017200f80d00601170021540c9402250380200311f488401c0d0303510302e03404041c860716040074407220038450f8141e4003a61420483c03008404100c0c0034003100f001001800c01c40820507403401d001c10790146d440b48030f0068102d03001c8c10404040d691649404c0e103464004020400001c0d400004980c0c81c0d546c141001300703481d507031820305104000340b6030000f07081410501d150400302d40d4050000303190a001111602c002480302890b076000c0714501107220b0f030441c100c50850408203000c1d50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 832305494 1250 832304244 832304251
    0x15082a09010e0a052502030a0e0f06160f0204020712080115120b0a0e0c13080d0f0f0e1c1e020a0611011b0315060e010212160b09060601200606010305 66
    0x8181148146000b0400c900160308605c15100582011442007400703944075100810580044071040b551140e81030014a551141540f400010000c0368604005c00545948500d1007a800800440d1160382d030341008100c1c2000c4c0030750800000c25040000c10176072060010070401441a64034040c001c40720b85162030086c204031010590142c1c250b80300040b0041d050141301e1042ea80b1041c4541c0740c07105842551072001850f00988065044000c011450f6036010248001c0c10000d03103801c1d001c21515000c29104614a10302442d040780c20b10180200004001030540b11b0140700b01021285e403c841040300e00c6c04841103c00130b500c40a440401c210462040e0b8180d0fa12040040000903880c60380d280c440440048d9451384070209486400441d610f0b07030990705003c001c002c1400c00c2d11490104000003500c2d06121502c01c010344001095005e1400280e154503141c0f03e40c050644a8541083c80074181c1d0754500b00c691747d00207196486031781c43e220740903590142030900e0703240104840e441e1000158054070303006 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 832306744 1250 832305494 832305511
    0x110601120b061f1107060504081b060408070e0f01050409021e010302090406030609051504033e210a02060c090103150608041b0b090415082a09010e0a05 67
    0x1d000c40c0c0c1c1c0c440e507910140f10f214182500c6010340d1070580c1c480141040c407164008401d20006000c100081007011501807824031649003d82a211504030001d0424042d0703070080046449010300c0422510441e01045001d103003001400200d0380e0365941004107480c040900290040d80d07145c01740c0c2d40b039208040c80d00c2040360141005030901c10400301050407074100d035101703444c1c0f140c48170300b5981405828061030028407126107240c00c4c2c904d060389000d850020840c03880f940e9101d030351030142110300f0350424804200c0103004c0707161a848803d85c8850754500b0841003080c2c10000305402c07240f250a01004403484022a5000f500840e0ba5074542017000b50401ca060340d0506440d8141c881e101260708200401400c125182e040c0c0070b00302400c0040e01d50500003911220551210414041da01214065400101040f1004102c00c141508102e44171801e650000c15036208055204001c0c8180b442109103450b00700c40d05403a640c101804000780d0050a105548140e11b41c03201180c2d401c480c50b041541e20500d00f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 832307994 1250 832306744 832306759
    0xd02210d05041e061d06061f0e090a02031603020a0e090a020f0304050d0305060306060108010510030e160306180f020603090309031005060415080705040c0e0a15110601120b06 77
    0x2d2084110b2034100c0040211811540d400820140ca02c1e0005421940c6010700c0050202c2d01d007550100300b400000103413003008012640c0100d02081e209000d49d422180c001782ca419103508100c5c0031a0040e41091326815211000d86481d41b402c0b038824829a1100c0049640310910708213400240416400b000e029060381640070401d450f81c141403603001754003444c07142004042000b040c0301d00804483d13010b00018460780054045c0034440c1c1c0d0000e07055040d00c108407480d01202581100680c02007034401e0040d03445000c0c019640004200810052048a01621b01408043e6110a0421003800d540c1e00042050200707000090150801102035640910800101e0345891102400203161100d2010149506c544901c204106820030380684442d4650800f030004405003051001501c43c045400341b1400f46a4524a11031028030402626140b100301400805102e0f03112928458800741c0002094080303031340701001c50010031000518504a60000a0031010b40a103651541c04c4000060031f0a40c5c81480b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 832309244 1250 832307994 832308023
    0x721020405040e06010501090905010f06050f0c0d211b03050c271f08180325032021041e0302040c03020f070f03020a050a050d02210d0504 61
    0x850303204100b031010f40340c002003020b585410001080604540c00c007a81702410f1900400a03003943c600110b09580490910b152161180c001c02c0c1d01c1806282e45400d45445280c403030b052190b4000c04c18116107202c4540300382d84214138205003000d07030300b0f075400c441c0c10500c000b8450030540e4401e5000318ac200d4801003065213000561010b02851440d2030101c0030810f81d41d12018102843d02141c542c080204480706090109000e06015241441c000d040b0b6044c02c042801804401006004443c0b41d5031050081c0d01c0c2c0e49041007116041c45121510880c04600c0361800b92085854251200c1d0603000a60000d180310f10141554901c1030700d144102039040c0c482072201050f403015550b0404007070900a040e030900c65281d40108401d82d2900c2c0e100005140c4100329020380c00100c10122100c050300f0898140c51094189807ca10307118555030701506074050520b8000c02c000021429a01c01d0001d642195140c441111181251381c0e10408044200c850402811307170104060740ac865072042c01103038400317201031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 832310494 1250 832309244 832309249
    0xc0507081206030a05060709080c01260a0204050d0606030501150f0621050112030f1404031707171908060108041202011409010b1f0504120606080319170721020405 72
    0x5009403002e202042014200b40085c100070040c101a2b05000d10b0840d0402440100c010145440129140c410304c0d42180000c100880307a404540c0100700c0982001d48807411400c0504c001e0000e40030480b810b50030050142c40d14410000c5a0b0260340454800503900d5180c15019603d048052921030607941d0340c80000d445490303aa00c2043d00078602da410300c80301c000b036a2400030143c1c601c030842003050041040030114a042c003001601c042e00c0d8480c01000f6000041082c1040030b010b6034000802c2c241d9500400080d1941840203070040e68891440c490120030260800c0d501800c007150240e000400c00340010300030400140080c030f05540d4074000005c1d4010616a4224038600071581d68015030b4680c00c0d2154181840041c1041305007419407100000c0c001c0e83c900500503c960711529000c51001011481400003a03800100102440d104680d941c901401e40d01081c00714400c0320f1004250201d0f11645081b40000c2210b1207042150b903440b0303c000081a03403400041503588a41c540700d60a02011503540c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 832311744 1250 832310494 832310503
    0xe040515060a0e0d110f090705030a0209030313030c0e09010507080417091f0906021609023a0e0319050a022805011b120209060f070f02040c0507081206030a05 70
    0xe0703004585541d03900d0400d000f480980070706c1c081614010f000300c00c20400b406034040c0540390010f01c0b000015070b13624a081c1c0080e241d809490706101c004e2207040790000030008152507910446049514036491075541c00017041c00c844084400030049025203000500142d80d40e8070042c0382400040607039040c80f10341004142c121494140600d2051800c10602007000d410440000003414207100424644200006102d038a001600c11040c60a4012138030100c5c801406da888100808960001c0d801030015101ca40c0c1c2a040103402c400050f4940a05040e41000100488900f80e00140c54111040041c5a04581c940c2c41100c20078210f004500c1c488994030001080d142044043c100003030701e201e0090514600315561582c0b8040c13404031a629814841d6003200c082e00f500c0400301c10050b251145c0201062151080c12680c0d0418080000c8041c00c01c05030307032042c410b034600070380f8100404000340748299261700c2110340c050b15220051188600c0c1074080c40c141ca900070f0000e026111001e6007035031100e140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 832312994 1250 832311744 832311769
    0x51927270201082a0f0f0a0503041502030121171b010501060215160e09010b13151b0507030203011401030b07090e190b1507030e040515060a0e 63
    0x14891440c1805641c0c0c4510741030307000881000454102084098014808056030107a642161008034080c82d0820800d000e54000c0314105014654910007100001c00030781c8100e504903013030701c4800d2000150805910a90b81600d1414401900b100d07181c96450450701c0000d82c0480e00c2607415981c0040b5680072601805c03451a10116002c00c55030460502c0d400c0d924140c006070304547c014614541030340c2c20000b5140d0410944c006142d0220040c400403111070240401541d0050400c9000240c0884139200621203010b0718204140c2581c0c0790b621161050829404000c0003403500c0cc900c501354000b0b004401c0780366109070300301d540144d034a501090940740310711410001844118010801c2c00320001d040313540440c50385003620b1032500300b02800c43c0e482c00250010400c41d80002802c0c000010b258007010075828003c011404850240711450302c0c90b03001000c1100083e0005a20b0303a074504003802041d000d04030740d90340011610308407000d01c0056001001580100107943d03000302025194900300050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 832314244 1250 832312994 832313051
    0x9080c010923030a05070305070218180705131a0d0b010302030d1407060b01210509070f0506120606070c0f03230c041e0f06051927 58
    0x1d5410310303424070389084035000b0071440040180300d00a81008074044200d0b10903002d9424451388031450b0741003c440398010128000d42280444003c0d985102c1d030070182c0d610440281d000c00410300c50010744035883e84218440c40d90403039130424014800e0781e0185c1200c1407410a000841c0200c1c000d4100094003110403040a542440754000184190f09040c41038001e00800c504000e09210022106640c0038420050f000c2d0030b803603464128174202c0c4c1c0320b0340b40000010300e00720340d41c03404119082000d030040105031ba00c0c0700584103408000400340e010b64450f0342243c500130949414171600c1201a10784000041450764040303000c01200300000c43e800d1001c00a0040423082004660441c540650b11084098101c40c81d400140d0043c1c1800500154011050300c0503600490446142403051400083e140000c05065082c0380d000391644e01154000011601c0071100c0540003074081403500d01c582c0560141fa50700103007100040910013400400e00c1c0c2c81c02040f42c070000d000c03004403001c010510034100c01c2d040b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 832315494 1250 832314244 832314251
    0x50a02070201022107060506040207060c0210201603050412060903030b0607150f06150c050106060f0c03050c030f0d050604050f0907170109020a0816080d0504170109080c01 76
    0x1075503810400350200704484040034013003469041c4500c185000b1500d00418454075000028100e0b29550155180158400c0051001c40b41c0c541010b51164030240030000c0507807500a0321100407900b6040004423030107030040c592418013100611a01c5882c4076a00341c041c03107410800000d10000102d200ea85441c01800300107080f16039440c0080a4901c0701c0409440703042e082c44810081401d0319004081141181307000901e0092114034030000c0d00181c2d1001c0d030800c1000300c07540380365a0007850400c1c5251054008010341619010b00340da0b00c020825280000420320000a00028003400080c40004410402c803401c108008440d10742c280d2005150301d4510341c5910520800d0305140c00341503084204448400c08518004100e2035540d211449402a0784010010361190242d007035100d4031445401910042046c0c0e03d4081940d507610030044502802920b082d0300280203200031651843c60a003940e00d051910340380440031200c0280c0b003112025070f55a10107101002500074801084e0880d0400c0022 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 832316744 1250 832315494 832315507
    0x150f02041a0919171212010b1b190b13050c09040f05031321031e260f090c1c150515040b0102190320010c022b09031104020706050a02 59
    0xa0078241103a2072800e00034014170802e078280c80702007001b03410742d0a01e10485440d0050810111802c0000c00302d42030303403030042c414001e80d201c6403000c10480131402491845d015888a2001e0000100c3d40200600140c01c000030691f070900d040d01008d50401e01170b5044800340e000980721541150311101c5501006003074240c2c02c01124a050184982011800b61000100390460710003420b41511940034817043c1202c0e08100a1307aa005440d41400c0341600a500d6034501e90f102154100e0300c00c141c601000d141c0340318002501e120000130305410b9000000e0301d5540c2d4544811b00c8107100c081e1000e421161024000c808104038911031092910540101401404408076001400100d031550705856045400074120105040c440f540003c202c50350510385100958488150070341d1100030000a410654288803680e20241d500151010b1317100310140a0140108800280b03103005004041202c2c0403c50542c8200049000d10140200115015002500d452000d0b40c13010103c0e40102c404154030303507010411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 832317994 1250 832316744 832316789
    0x130602011413020108010506031f0305030405121b0f010c060905150c070309140a170303010315061202040b04180506100f03030819060909150f02041a0919 68
    0x1e407604458001041d0090004940000300362035014080d2030700405001001c80d420749204007500e0749040d40105a03100d00b90302d034644903469502500c00d541c460441503030304424410000c203034111004c00c1f2529602c81c000e603400c1440803d00030034141505019464080c140030914600445500502c1000941000d41030303001441512000070f05251aa90800d01541c00003d8000380000c0540310400d950040850004000410704640b64000845140390f2400211076000000040c5043c0c5c0d200d005485c4205050007504012555180b060b03401c051480341c00d0002600b4030350b00c4810340c8a005000480e00c034003200d490600015000808a4107988114208290101041c44507006440c41d401c950014a1468034010242e2402a210090a9900d42d841c50002030703090307100b0801800c80d0304090100d101700c0e080c082d0880a1825000180d9800d0400044001c1c510b8402c403801d40f50300100900c8004111880301b43c040c1c001400c40c5810455150000541c966041c48071401030480f410007240c03160601a5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 832319244 1250 832317994 832318031
    0xa1407082206020105090a06090c03051507080a020f04060305060a170706021c230910030501080c01020d050301121a01030609050f01050114130f0c081e010e0106110313060201 77
    0x4403a0031a41341001b480321001d030100d0356455540c0c0020b400b040b2089681810184500964401041d03071203200c10200001c48078581c02c2e03120310a1a21107450a0b038640d60404240d201d10184240d46d000c0400c424170100d4003941c012780c0c100c00003820b465402c13501e40c003c022a401201130404501c0d403100c002000350560400405402c0d41c00c4904885004c881d0a001810340c118513411080e40c040610310000640350080162070a04000903c580481002180068000d200a0044e082d09010382081f041103540002050740e44819103507070300c6145a2912001441156098908440881c0d8a004024074100e11320300c1f02d0b0285029000c005150b003040d1500a1030f155100c0c002030801d9043c2001001484018503040c200340d00c09580b0313100030200740001c4200401489900d45802894444c80160340390340b01121910a4003009000441c414a03c404414960310901c9107242070368981e801408014810f1815103410008501102c2c10600c00b0842d0b5502d4035202c1d00b003100146e40d1403003440044081303043c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 832320494 1250 832319244 832319249
    0x303020a1b080915121b0705030f030a11090a030b06010306093303201206071d0607080d09060608070b121e0402010c111203041a0a050a14070822 64
    0x41300d103240800184000d03910702c0c40281544003401d50103140360102c0f610b1808032030b0010b81c0803050b81d9803440d181c1d070603c00c2c0740c00a54130f15079028036080448660482d0030b403c03202d11384401016510000c1c916603c01311128001042d0b14101512920b000800c00b000e806000490703040d150700749000400e03900122a00d0600c0c41504510b60070f0901c1e0800c04101146652032000c075a90001443c80d225480105040f104414082000e91085030200030400c0c3d4043e606201c950500309800042030079501c00c02840303002e0048045c220810801034483d440e40c40380e000f101c45a05c60301010a056546800342401c0c004243d100c201c0380d80300041c19500e413981340c1d20342c660301c01ca100707032070141c01c0d403241a9048600b60010f10090511007201080070501086025010b42118010b0469405010310b060f01e46d140d800a2246240642c0d0020212599401c00d01c2038400341e0416540d82b5081680050701186c080c442681c4868019034100301500101d141c8500030322140c0070001352203820810a40c1d100c00c5100456 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 832321744 1250 832320494 832320529
    0x305030403060e0712120e090a020901080a050601090e090a05010c0906090603090c1e17030913020301050f01081b03010609050f01020a022412041101090806060303070303020a1b0809 80
    0x2180b06001c03800e07940c8005d5540607081070340b451000f103c0c402c050301c01240e04510b603580101e40e007041108826090300100040c0900b81d0fa07480725600c90705050400d4460580d0f0b2075010440c00401840300e110701d25540365019101c4411905c039200180c4600d421210b0226030500018a40c840920074140c00c12100c82c0200340074942007015800300d0720340303005801e41c030b01585c009a60a46401005441d8040340d0030050400380550140014003018401d941e64480107003240101490304001024a0061080d641224070190480311044c0c40386004541005000b0410388407401d19400b500c642c1c4142001450180c03c5646681000b00d00b0b100030804038441d25401d940c1190300011b0b0140060300e0380c0c0480707010b00c60a01960351003100c80100e80204d50282d50b010b14103d940140c100000c2c441d601d211440000300031f884881d1415102d44030180c40f0b9408580842c0c15a0007044207600091099000380720760742482c50900d8207a141c0000003c0e40e40c10707c407400e681106020a1510540c9492100c0582c02002c0c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 832322994 1250 832321744 832321753
    0x91203040e090a0f0303020f0706060603240e040f0f12080f0c03160807030f020304260c0d0e06070b0708010303080a020c1009060905030d1505010804020102031206040b03070305030403060e 83
    0x110351350508050700d6120020201500411180e548105181c143e80707005034000028401c0716207428000b03008042e110900001c0c54031590092003581c0d480c504100507070324001c50b030440c640d690f40c85010f0300512541e4101c400c040750362030300310105a0029603c400700c1c1c0140d0b25004541841086074000820241180d41c440e201002070040c0080413000c6c0f2022a0740c1420300c4102e40c0e071000e00540081c00d80c1000700e901c442c0000100010092000c000c480046020006124100d0300f245882c280340c0913036070170b011aa500c18105c0000c0b03203020740401c0e03514513802030001d40b03804542d40d60154001401e50b000720125070301c41c0040c410550400c54482d03110000d05021414445c898607015510303002080c207980801d035104e481c48180700c000e41103070621582104c11640c0e5115540139102c010138010300005418141c000010406600c1b4601450080da016030045003042014074141d601c0000281c0841c4d40a6600c01d00700886d61410320070303a001180200065902c2c3d914504201059501e0b42c48100000e401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 832324244 1250 832322994 832323013
    0x709121103150c07020904020111030c010510090c09060e0a051302030910021e130819172b0b150c1b010504060f021504080715050f061203091203040e09 67
    0xf481c1038850440e01111540c1c40c9440d14001614507101c03141803401c16000000d00c1200d680700c1508950b00502d60308404d85204d85e43c5425003c204c8920140c1c8000054803c642040070b60300c038260b010300c03006c2d004181c40d6603150b42c0d60004405159101ca009840c1d0303008030070082c42d0102030100f41c0c22901418815460f18456030030309014103151203031000510201140c10144000c0c0c1c40c10310030142c0b090404690b480800507094155101d01c2d40b10844184144030020381c11580c0b01c4007030b01c0181d01ca03c80c0303180300890002c5c2d0601c81001820b1803e5215a03a41098803415907078018a0900d01041c0750420350b445608100032401d0810489400b100300c00c00c1500e482143c1d0340b200480d42180c10307a2600100710101c0240890034120f81e81e05083e80e0640c0ba0042c40144039002c001007040300c3c41000810706600703012000205485c01200ea401e01c47c10304500040e002d0422072042d076410b448880940f032808074030000154911700d040614440c10760001c5014000004642a4030341c0001c0f2250040c40301d0074 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 832325494 1250 832324244 832324261
    0xf2a210f090715021e0a0203070f23030f0a030e1306050f0f03071d010620060705090109030209130204140f0403030f110a17060409051005070912110315 67
    0x5110388100f0090104040c420050300e40b0900940e13442d070001c4901000c00090300c0100c070f0351b01c00702d021043c1d20038000c90b8800170b8500a9106044c0850b40c0d50300031194000744c00c210207a081950302240d160140221040d20201900c00d2115202151003900d6504440040c081404842d82d883d80101008606d4980c05000c10781c0c4500310a40b00c2c01c82180c6500d800424140401d040032041d070720641d0340f805400c007108400609454028107803080c540d500480e000852140007100050149904081d4108030041070415205100034000c200060420307901c07880c1d0300d0b408605449800c0b2094804003100c400d01c8030462601d80140d5201d40c6d40e001619040742005460301c811404003400080c00d150344c3e028802049616038112000c4159044412912040c8410700a801c600c4400c03044100c9042e07020010b04149040c1c40f4210740580c0040003171502c108032418070401080050800414084030a1002030700003000340c184001c448c8070f452400304c20130408003854500101c0750680c03000b54100c0f00800c00c441 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 832326744 1250 832325494 832325503
    0x7091d010e101d0c040509010312080709261204060809010609150611070312030f200901050309150c130501050319050a060e07030c14030f2a210f09 65
    0x45000d0031403020720341351414803903100d200344d42c0019008100c00c0000000d0010000c502e0325424003e031507513183c9550301c08040b2203c0400c3e00403821030303c07280c407154032100b003c541c151001d00030f142c402c940c3d080031640050040b642240d80200c001a290a08205140d0002e0040800829200741d040c40626445890a0f0f40d440080c000e450030011000c4105030100700400c040c00085030010030b80100151b00820045c040e1106400109989003803810040601c103009551951100c08040b0003800c22100c1c4004603070a61020b00118018802c00c10703c2a04401400322990103030241c02c0c1c50b41e66481404100400204441d84124188031050041180d55190070748980c0459180080c00030b56a5a542d13241c2009040a0f003044130540c22840c10054110f4143c0d010700c40b001c61a0311845003000001c1001001f030b11080b01e00141d0400039070041080070712112052240600c480045003d60f0010100706500e41c1c00090030086242404801100140d51206400e40c00098611991a181c6840b866030f680d10f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 832327994 1250 832326744 832326779
    0x130311010c080115260601080916060c1103010606052206081504090b190609050c09010c050f0303040501230601170a020f04090c03141e07091d010e10 66
    0x203812080b450b50b040c0d486134000e0a404494851300304e0a2041c020180085e00c030301103c0383d5001c2050140400c00c4404000748019014a44500365a4410700704082200c0c0364040300802c071400e12076040b01c0d1b12103070b400303000d840e020b03048035603403140c0b00d00c01000d1140307c5100f111003100541d41f184200b806195400101107501820080862000c0b5005002080042000c00f801030300e041c2c802014041c030b42d912041c1540d602a198030702880701d56240c8000700b0031107106580c1c80704040410420008070394003800740109618040c9040c0d0307050039641c400860440d4030844048030241d540780c000d0600251080f9201e11100600540301c505850300c5070001e000c6203180300364802c041c1504800581070308011f4040307549040381a42e080f92543d55a0b0401e070050043c072144203003c030f801e01c7c0d500d1004425480e03540344641d0090f410899401c0820848000e4414094100010001c01f08004680011008000094200b440040c5a4950314144410078a140301a0172030b20032101007034080004079444082c030000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 832329244 1250 832327994 832328009
    0xf0c1005070f081e0a09090b270a0e1b031501061b1b0609030b061005070807150212040b0603030c0706180302040c052d030103060b0d0605130311010c0801 68
    0x4c0d1121108084004485001e54462100c0c0d0001000c0307800700da00240650440700c0300310742170002e04088810040c8800e070040f1828544055201e0070942d0b0340b203001701d05400c4880100e0000d01c1a551000103401c1c0840c01c000c002100e03841031413040042c1800c001d07c1c4502c1c0c442c001a00c0c004c0d41490700062204c4200d184074148814501042024032907408003041c40074150350220f00406031356a40190901c803040c44113a48411041e00040e50300c2c02c200100b940c14807100e9851500d4180f03e0359440920350800030050304d0300c40d81403960313500d000807510082107020840038480101d4509450030480450005040c240203400138403100442410003d030400c140c50060a00c01310419410080201c040d0a9600281d402400c00c40546816a0000020030003401c1c01040c0c4802c2c00c40e04400c1c0c8203600d8000b2103510242c40100b0041011560030381c48107000400c001c01034550180261134002c00d5038000e4400580115852904808054101400c1381c201c08418000b0b115226041e040941000c0c014821540c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 832330494 1250 832329244 832329247
    0x509010609060c0c150e03120a0507080a090b1201090e01110d02160c1508100303051c0b040905010204090608190b180a0804062a150204080f0c1005070f08 68
    0x4210882c41180017800500c1c01c9841c1e41580b05030010301c4a030490f441d5038003e0065031105070050150608a40c900401c45d00d4640c50060150381d28035182c0e00c100441750400140348000300e40641c103a0001c0c034654210fa020311380c0742d504001001d022286810003942d6268900000c612602004a0584405d2680d1101c016154070003601e03843c0742a620060000c180c00203403d008118695007844c0030304080016582c2154030783e220700740221211118000900410f200380103004101e5111035070101100081c000110341c101d001c1d0007040a84200700300848140e50045014084003a0310f10817100140310801c002c06403c25440c0000090307506828024000d146c1010014054400c1480c1443c420020781e03007140e8401c849800d000700c064010b4003802c4d0005500040e80011090000c02180700c00c811034200701d00c0c41206a1350703d20a0701e0aa1001e2204980334040091711140034041c601d80060b140c0042d103800c415650070045c0e2601001c0c0c0e00000d01c901804200007280303024100d4800c003603000040c2c1d07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 832331744 1250 832330494 832330517
    0x11806020c03040e0a0e16033203070c03050d140711040b102309093705010e01090203010317071505090c0108090d020c04020d0902190f050901060906 66
    0x10b410740c4201e40025407400020024030405d4140303644050001040d850030f0703800c10401e8442c1411005a248805800581c3c0030380d0040000b80c0481c1c640320303040b143e03000041c04903640b00344241c00d5400801e02a07511110b184820020303c4400d1006d0780f05c0300340310714080360304c1341d081c030301005083c0500c102c0901052004004206140c03604e034441618070303100404c0501035407030708100100900a00c0c0b506054101c420444070188001d000161034003440d000f08900da05641e02c5402d4118405c9915503010346002c10000c0440142401c0150039448004040210340c03903042c0301004d8404041a488040034600c10401000405c071000c500281d4030703ca0041c0d89030307103c2b078906024040400349091a02494602800c0c030a03002c10000c0c4420300640f0a032a500001d41c0d8220080707440e1200c00280c2070143c0c0081400141c0c0e460603600402c40892a2240000d558080d0f0300880ca00b0f4510502c0780071401d41d50302e0140860485a661140100011140c0e10f401d9814600d00400034110392240e070061010000f40c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 832332994 1250 832331744 832331767
    0x1061806110c06031f060c022d09100f0f0812070606091b021b0f041d0a060e0f030711040504410a1a0402121209100201180602 56
    0xa00c60314030b02c010925078981c01c2c40015414000c0070344007200d407211520f460010f4040d0140d1006a0103540080a5803034000c0080d080094110100e1115920480700045101c0c4603524403040902805403040094032403800c0c000ca200d40b0440540100301c1c010b82d81c88041048803400180301451902014003c2c1d150900c40c5409405443e0540000314250b080c0490044060f6048a08002d090b490390708440d9402c8650002c5110110b100c1c01042e00000c1986000000f410240c101046007011400080c40100f0641d0096040403420081115640c2c2c540c0c020300780e0302000b0405001f50300e42e00c00155241500c1076460031085080d2b01c0515006075100c030005010b00050141c80191300120703040010342d80740c9001007515080d41c038a4001c6108000102c40d5414860002604450954803404070105440d00c0060080250001002241d1080241d042d00c080c440b01030003581c5c0c1100110300c0ca04d845050356410040000c91104801c4216850600d0604a210030039070102e1b40c1a0f000140107943d030448004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 832334244 1250 832332994 832333003
    0x302240f0415030c0804020f120a050a0516060219150f090b0a0614030303190b030f07064e0905030306040b06040b030f06012d03050106180611 63
    0x50050100c01080c0000e02c600c90803442c0c402140d07903030b40400c620444034105a036280b90941e00a90410309607103503c5003908001e905003c248560908481d5000384960703800c0e1904803e000105c59075000004010040010090352401404c0c884c0041c016100d420140600c1e03c00704031300040d0042a0304030740c501907804103500c07044000c0c80c00d82052046a0399414076407408a02650280c000c2494440c00281c1184820312101c078a06000300a0751840d02da49500104185850b09018001642e85040b1526075038100000101517199402609402c3d141140280c0039510b0b6624a100c05110488c2c2e021460300d1105000550200f5840303800d01a450020f4a00d00551105141500d01442c2c44104014002e000014520035041124144102d401600074004240100e22680e160203405002140c82034650070710f040c1e40810306144c206c400c1e000885007502ea81c080102c0c1e54000485001d03100200f02d0f0305026150240c002410196003000d44600d442c00c50741800c2c4101340400220040011a0110602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 832335494 1250 832334244 832334257
    0x708060a05120d11010c0c0308060411070b1b0f0910200c0a050f0a030308190c0801261c0c120206100f0f2c0a0b040c09030224 56
    0x40140b404114120001c60380c40d009040b141c0c020810b142d030b182149a505026010540a4540c1c071801020b420303070303800c1da15030700d0141226621a0f01c0b641070720304080d1140060001c441c06190005250b003042c08014074014003903454820200d02c10041c1240c000300740000c0b01c80e1140c0944e41c0780b03002580b20300c003203c0c1035103205c0e03032020300d104886901580303102c000460100307001c821540d04030f00555078410031504984a04006400160301c200c2040428022407030b0503402401961148060640b8a480ca0122590080c143c800b08285800600c02000302025000c041c1080801803503401c10200e00b1241e6941c4555a0072442c440c11f080c600c241140b20f180b0700303d0a59800f0041c503541d9014840c0194075500d08584001d0820b5000000281c0c007440a0a200100c60010903034521070350600a00100c10482e002c0e03082c1000401c0b030390140c45004010352291082444140c0091040c1400c0208410384008102405c10820118002c0c00965100b1500d40035280b034a4025681c950340005404a440c000c44 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 832336744 1250 832335494 832335499
    0xb09030c0d1b050a18020f040815070e0103020909010b0f12040c080d05130504020904020c03160309120b0c09030f1507090f15030f020d06091409060705030708060a05 73
    0x8030400742040341e48506018900703981403003a003101c0c1d15101400440c8400f4070451011002c480c03100702035880c85a008001c0c100b0b0b20010140380585590b4440d207443c44600300a00301145000402c103d0359888102c8440914003468254034000604000441104041c001c03030903800c5000600480380e1038031030704a6851080035400c1869030302d481d0400605c0d050181c421400c00d4040c00d203240c1807851241c42280c420401120450081a0504044c04000e4204002e8160003e900304071241d02040c007000900800485070981c4a00d84003240307001000900c0b503a000164000725031049100144072043c4a81d80198002c0c299601c0303540e40c4000074500b034080c0071402214000c0d82031174074030824400c6290b4401c000b65140c1010307941d44c4103a0342d080c0c11070728031413100c42e4144425100d10f954825000f44480c99000c00c0302504103282d080400c81207503040d031301826199948074100340088600d85111070380f19000785c010300114544002e000d032251000030041c0041003820030000d08980c1d101032420f40a010003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 832337994 1250 832336744 832336759
    0x303180a090e010906061a03041e1709030c0f01020c0103021c0504030507061404030c0b0405070b1602120a11120f100c080f10061202040e040c050a08060609010b09030c 74
    0x160720205000781181c540503a42c81c0c1c06c0400105080c4200c9413046481e203948280c0074910380e80c60b11594108024910b00c0380c03040c01d1403100d05010620b01c10080c240080c640510613038450404e0101031800611034034550089070364280ea404140e80106003040c20500a00f009651104040c0c0c0c442d50940e82055401407552030001408245a0f0240c007804a080c843d441c1085000c3d000c4c4060300c012201120024000352008440b440010107014605400c5485a0102c981c200c1d16100c0e0010680c1010050302c100c07103a521a540190315100508038020200b10000e00300050141d280d8600c003103a00021a0702540c00320710034a034180d100704410007540103a441511210a950010880a80089400d007800100c2d003e01160568034585200c074000e02140021410603890804140d4a00351807010ba480340c680d091000003130701d1034501c00a42c483c51042c0d001d8011641801d04000704424207030412025a8400010001d0755158100351506684d0200d4038a900d5060314030003c1c0c80c040180c1449900000c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 832339244 1250 832337994 832338011
    0x903010f05040c120503040b0a0e090403030b130e070b130306024302040f140108030306011e02032203080a0905031207030512100b040f0602010c030504020303180a09 73
    0x3540e80c0007901880c850310003c0f9003256524002003200400d168080d0650b04100420044014060014001010a400c0c0700148281c25000110f8081c0215802e4010a8071180e403100a0b250128080100740403450003001a05d0b403036808a0b0f602c5460340070322600010300250040e041e5100f00081d10007168000b4055650701c0c2c4015800440060404120513414070a126041900d81c210020a42803480c80701c0c0740b00e01e140140c08000203007014041c444029a581c00b54011706495140b10039018000705001140e81e4201640010001c4400114450350340c00c4005150043c95404000c480c0358118580c684540e009503481031034501c2800f0f41c001080c0700130000d66041d209411050030310403150201c05542c404001c1c08802d030020301c00e070a070041c00a0b804110003490420014003081c1c000340c1400380c000700e0544494965549074050740000c41e0031510a0800c000301903090003004a0b00e60145018090380c00c1a6020a5890203080d460300710300312081d21b9000998840d0418000100030f0444103101014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 832340494 1250 832339244 832339271
    0x301140114061909060e01170a09032a02090a0e07030b1e13060f020a020c0402030c040e0c13050f0a0608091c051e07020906130b0d140c0a2405090301 66
    0x2010701c1948086112071846c80d4481d0f0160810314000801e040d1101417542c0c2d0403601800030001d05504800b4401d4100145017031080c02e881c50910090040c16600030b00109004001200c1c3e401003011407001c0c20909042ca002502003402c0d0200d0b0751003200741e00a52901055450303510562020311080ca2903110402800100303150283c16024003403102000218503000100e0164810041e035030340542e001c03801c032090301d040550007154804103a050302414980c4070f0004050146c1c0a40f03100003a5400481c0071105400c2c01a40d6400030041180d6100900c0740110103d00c0901c3d240c42017800740441c410004030150401e0000404441180d00e841e9041002c564014240d034220020080314044010010002001e881c0f04440c1d0198008095182c2e035034440d010000f903480840040810103403035052185103a180d1802cac000c400340c403480c08040c5002c00c03424030074540541001041d200ea8070000d000c20089841d0122103120f0040e5203e082d00e0b84e120000199010b05c1290700d026010340c64070322024983d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 832341744 1250 832340494 832340507
    0x50c03070c05121c0e0f090405160b270612040c06090b09060f0a05071a1503060720120412110111070b0a0c1a011403011401140619 58
    0x40c2e00c21551000c0450b040001d269641c40112648000c42d42c131030105041d4240142c0e2900ea414100501d9481c10f44007a0012030034a14040d50100c1d03035544500042c043c01d0306078050003000750000c030132524242032212000515084440100002c1407010801c01c894a4036801b04503410800090603004250030145007091440c409449200005100c5d140c4c04141115030408880781c4110040266052000340d0310441140e60000d1110750920004010340000545280f0362817800d07a1528a00702d015241c41d40e080c04603003101d0075070140b207500104100304050b40c0015204180440c41d120a038411404283c4040c42c1810303010700c0070500030010030009608541c1e0740a41171081d01c14500c0183c6a80524010355008240b0040101e650b00074190500001ca4500c000d414011458584269200f2258559105458801d010010406401d01c0140000da2941c5c0030f510300502c054000700050410f41d1000a200f1806002d031003d040402000c0c507640383c2c0c82e842030300c400364031084034420340c0b45030708030081c1a1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 832342994 1250 832341744 832341749
    0x70f17180a050d1409090615041802090a0906032a1211040b0904120c061506020a05010b06041d06130203070903050d0f120c03060b040b0403170c1903050c03070c 71
    0x5050010301d03680d1603005505540c0117076070103000c0c00d07a90303103034881040140494040e02c0d8090020034040012403140d00c01c0c034050008410034005980d2040e0001b0310010202607002014440d080030401c000259aa00d0708114130846440d46104034008002c1408880c1a0790340b151410741c00c040920820320101c2444101301c85001c0b6002c000171031844042c80f51001003110301820104406a500e000d080c02141407500c03042c410100000d08021305035000200d000280c005c800160320800104003001401d100320b9450040444034241890310340340801800c1c1d0503c0194201411411010882e81e4403100f01702c1c09003204403c030a54480c50607d07001813900c40d540c8401d64040c4500821040c1d0f080c00b64040c10015a520360300d950050a0b1115a100541140101803080580c2c904001603800309600152014001b01c88a6075955882c0d418a107200d44030070100340407401c00030440344000c42e0000a113090400c8400c01158003000ea070303040640d9180580c02c1d400000c1d0200144510400c034101800030103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 832344244 1250 832342994 832342997
    0x6010c021207151211070b07170c090405150604060309210c0213050c0d0c020a0f030f020c030f0304030f080f0d0c03050108061302010822050309010305070f17180a050d 74
    0x200c4614010602070305e00f0982250a610000c01500e00810306408250303a100656003807840407000c04203100b0003054804c5966103440d440101f20082c0918060140e41d03041440d051000b0351034a01c0000085107442984650741c01c0c199110080d00402290030510302e811004200d504400b030391404000f425048a800c0c08034880c1c0140c440503401c90301706d4400d542c003d550a02c007a60400c0c0c1d1190701c01005000401c440419886214005e00014071043c40083c290791096507550031480d080e1038040d280010300341040d8841e40041030354034240035002003034804503500502c0c0000e500d0b0301030610080b02d2182440c00340402c42d000501d0b010948a42d081401c44a000d42e40411550703030b80d54089a21900706880c3c8484020080c03c3d22000b43d0301c03030040f0a0700502c45a605201000040803844800141d01001710741c1d5400c003081010440d1380500c10382e40d010b2424246083e542d503005100400003180030343d11041166405020441000704507081a0041082000b2a00101c20358200790b41e450281010520 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 832345494 1250 832344244 832344257
    0x30b13021005030c0304060203100e15041b02031603140a030e070b120a15080a0309051915030510030206040810050109110a0302180402042603070b06010c02120715 72
    0x8030514400c0c003c49114840304118182540c81da9500c61010394000352503070b88401030342c04003c1a080002030102d03001c1ca042c0040c04412010280a01040d00d41c2d0011201c4c803401e004a000b51640e80100481e01020342000201e1001c2e202842e044c0c9588030b10300545030300280080344000c1003d82641c080c0740e003141c0721000c42e079105170340318115a0148900003300d80c03030100ca030001c1260303441c0c00d4202c4410380340c4052880035a907888101062806d00080b2040d400035100003020862420011811002030140040c051b68035401c01c0c000e62030030b00301e54a0344810540e50741c0c0003421202d0b8180c0c0d4071015590040c1110342d115500d641d10381e5036030700320441503112601c0e2038000208405c0a200382d188207030b0802e1099080c409000000c0d4029048026015505200424203c11640d0350780b0090000c1d2030400704000c140340c1941c5a1840340010010208a50390042140c0030200d540310440b80d500807000d180080780d41f10284003003040150071544030007103441130707203004100030511401d002d038461856a01d45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 832346744 1250 832345494 832345519
    0x61d09070e01060c1e1203090209010504050708040213110703030f0b0406140f010e0409050d14030403020c09060d02040608060901231b040e1005010e1e01080a06030b1302 75
    0x510441c0c1080c0f08003004244c41881e4600082c501c07030a418000d00c400c96500081c0c4110f51500d0000421540e01d01000035504c0d0140e0007189010155140501003c2d0381c204214a0803c0014142d1a4090000380c0b0580d1340c00800c142c4c215141c2c10009685040000b22504c487d06880c2c003901400c0041240c03010103040000f0401e55041c0751007107008503001c60200b19507042c015018004a80740030034201d4104803040c41040e1480d200e0b8022442d00030b00c0f5a0080040d02c00204000341223410441c3c031100902c10800910000c0f0354001408610418218ad000550f40c540e80700042c10b0b0481904029081400c1c03000009020382c011682c01d100746000703002071203071400c1c001036041d441c8446620510150f0030400410303c0700041407029603d140c2003c1d41145810780310480c01700c03600d5044510b00b1500e0001d900900442d6030111501c080c0e9081900d081450358000c1d07030907103545000c0d50700c0c90f8100038a07440010850500f075000340d002160007a0510451382800c4034081094500d028060b0b0251615501c02c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 832347994 1250 832346744 832346759
    0x20f01020a03091a091c121b060b2e11030f0d050907080a0c05040c030605030303070e1c06060e0711030a0305130206030a0209090c040b0f0d061d0907 66
    0x2040c09564107a40e5903d440e0f040c1300ca4054283c003500d214504190003848101401e85640c40ca248a5901c464071110281d6240c0c60f200d40035035608601541000a0104995042d030010b0012500a550000300410415100004203000039941c28910710f1480c042da01285030ba1114002d8522955415a5090566400c040712980c1e20310410031104440001002403000821203a40841d400000307103810f1307500c1c90b50307107c0d1101d1601c104003400340c13000c40d0002e00c100914505031180031180d0081d400c040c40a146050700080d16408020191414007110b440380c031050b60b407903e072140101424030010b90346141207414007100404950241071152100306000c01e07201406100440b0100031420700131403901030043c004402030400604640103122a540c01040140e940d080994403582051000589642440f0204410201d000d044001816003c100502c8400d032401c00301c880c3c1903220f1401580c1c501410145000070003499000800055002d00c01c4400595421020750060b508241110f4410b9104c080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 832349244 1250 832347994 832348003
    0x2070b1806010b0d0905120c07080c010c1709010e060d060501080109090c150c12050306030c0a050307150e0301021317030a23210105130e03072607060207020f0102 72
    0x1c000780e0039000c0c81130b0040380300d85820010b141132042050720000c0075141c85071340590700440115a0340303070480181805100c1c4100080c010080342441c250803110a41e4894050f815044c1c13241c440070010014480c02c46900406c5d06190307120340500780541d41c0d03454010000090050b80035060000c0c1e203170303400003c01060b5400761000440c2c10408000c04d00d03140c030135000e25070442000c109040c44624100d1720081145038000d155010359903110250b40780342c01d404043c10400e0050f035162240140d51014030050318002103100946800301e11b03000605001c400300340c1c3d0a01001654503410f600008607018151305d4180c000084400c22410a411101510344180c0c03280280364000c2c2c000f85813101002407400d1a2200c41607550b0740c000c1c26a140104040c5400b05140020901103002140000108280d040c0034026411014440303030704006694020140c10340300d114000014050f146440407000c20388250180812044075100c66007696403c6525056000e0340142d00142d104244141c0603100550021a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 832350494 1250 832349244 832349249
    0x403051b0714060a0224010e070804050a060e2d01150b07020103020a120906091704060504091a180a0b040c080414010617030712110a080904020d02070b180601 70
    0x1c5200b119021240c06014203038002018440452003000c10303813a050081c55064840c130604984044103150b040600203c11040c000e0841001c0196400400010a03c040f400014450b801000801c580c42c0c618096454010f2407103040c0c910b10160074294540740e400c2c048001001c6a290009c1c0152081203901066074500c6104210350900200a1000150701c40e600030021003145e4185070058503040008001207460a190450701c00d552000a039040c0084203614500c01c18045032040d1a25041070402802c40c01948102d081507038848901020420648100304800d50024001440c00c0b00e03040c00b2961000c806817402c40110380780400c518514107140c09445d03c0e0560360b84900381c81e5203039a030b00c1c40c0b40a540410342c04101d5594000100d2581316107507507084000c41c038074000e503100d144505147c0c1117000d594540070140010407100300b003484004540707451182e401a58003170b12940000003040c003034804c1000c1102c22034400a021020844400b000d54094800303114040382081c200081c00d03036501c50a0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 832351744 1250 832350494 832350509
    0x1e020f07050a05060d0b031e01020a090e1909140303070f0e04112704050a021206040603050a081e040b0c0d1112070f05030d050f0a0b010f050706140403051b07 70
    0x308940017611482c0d0308200341c03149003c2c04403050001e40c1038a4110400e8404000906a5000a005402e15500035409405450148004009030400344540c4189030000f4074200c0d50f55840d02108003d10086490801000724103000303490f81d03407a0080008110b0321081c166400481e0565501c80c00c03d081c280b080e1541282c0391110545002c58204170104404001c401d00003c0d000311460505903500d80f8018603004918405002d81c46070405224120321803c018406401036240c18401c0010401c0040d01054160300460640d079518084410882c406000d102c00c02d2884800003400500d01c0740c84001030488030611416920100284103040b19002c0c0403c58a07036055102881c40704000031800002c3c03844510861003680010613682e42d0b20305542148070100b2a00f40e8910070012009070701c000302980000004010454481b503500040c0140100410940401c0004a071050401c4510f501500e000c4a9012550211b8034041c60020551390200d049030310501070f41c081c408001100002c00340240c0307404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 832352994 1250 832351744 832351747
    0x301060515043b130f0825080d050c1306020601030c1d07030e0c040e33010308091309140d050c2a0913061112161e020f07050a0506 58
    0x112005400b40c164003804131074901c0450007060b0f00141e500da241202d03540c412401241c4030314062031100c1c01c0c08041c8003020700c0301c8a0744c2e010000142070fa504464510382c03103000001c5c0503101d0182025080c00b44540883c14440204400300300c098000800038102e0344a42449040f482d20b030910302c1d45001d01041c4040c40d1450300300202d140c29000c0e800c40d281d8003502100b00c5540801110018054480341c95000b011900408031132102c101c144801c030806209140324407001d800c83c60341c825094140512000e09900404110200180d03078610740c44480e4190140107214500050178410400e822180c0b41811621540b020042020300510039a005101e0040c040d004c50307140f0a641071100c818441008414a9107424030118030b80d240140c05004003103038214100801303064900541200c1818450740302c80501404500c0c468400e060f0800ea000b03810104c0c00240005000040d190104000c9000c180d4000c103409000bc450303400108600c0010803041204c150036541c00c00e120500c205c0d4059180c11420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 832354244 1250 832352994 832353089
    0x60a09020721180306050f060301090f0f150e0f0c1e1201020d0e0307051b060906280f0201051605030103030810120807050105070207051e030106051504 67
    0x1220312501012082d070f400c0c160100da06289402c0303100d01090300708885403a62170040c4409158118407456000b00154000c2041b5111621840c14044484000074044181c01c1c4604041041040c83c00018404000044c0000c10004804039212280b0310301402c0321380315501c20440309142211451546a940627004529038842000740450f4007805a202010380d902044145240e40b501d110b5400c0d920050700146031034044a181c518202007910404140307494804003134401c01d41d100421100302d0b01c4c0c1150590750300c800c410706c0c2801c03856801d519000d44007030b01d0b0b254031180e40e00248040c15132600d40d4002c10140e500c03428000b8142008103030600c0000e20500061000074003a00c032513030304442c1055040d10350559402858810103600101101c00600110314503081107403d0007410780003c4640003820b041d0b401c100116100684d0390707000d180b070038424001c8021542c9082d40404050304020307000902c010500d40d15080a98098802d990966501c60240b610200c1c0c6443c28100c1c02c0b036007000b2922500c0b0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 832355494 1250 832354244 832354283
    0xb13020415180b18120a030801060203030106051209010917090a24050a052512030b3613020307052b110d050d020d03060621020906070506060a090207 66
    0x404c840c2e00e07034107006400c1400303401541d1161101c2c0303540341c084401007040d4111443c005003404010f0b800342d0207642c03003400140036027a005801e0303c01c0094018850300c1d1640c6d0b011a601c3c05001ca50b4005064001082803e0300c130312100e00c00500e84a107098960588040d65208501d541714100d005005104101d176004245403882440100b0780324080e072502c9401c0801c00040c000ca0382201c071107145450780300ca864600030010f190b055503506074041c3c01c003007001c003040340c000c44c01c0e682001c0c5120041c242d041c802001220004420302d410a810f40c91091044e190120411106100f82d2005911070b21070000002410f10b8014820f80c25a688103100b4080a80e000c24a584480c40c12001102d801c820344010000c00d844d11070380d5145150040009084218034110083d080060280c080c80030503041041c240001500220030210805445000f0a410403415928000034011103506941c06a40000c4400030f004001684c203009500031a00001c42543e100a00e401324842e03000003c0c030041e60398480c0c0ea8000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 832356744 1250 832355494 832355497
    0x2030a050d090218090102041a0405030c22290d030c060506150c250b22080105010f15051e03040311060702030c0c1903080d0b13020415180b 62
    0x58405040c1481c003030f480c900120064101190070400aa6021808101080e42401c1a09000040d412000d14250610bc0400e03140c0802d000d4a40c010810092900850610302c4401c0c10b081840344400c0103c91080320024403a001101480c410f13111442c10510005d103081c1d84c070056039035172645038400454525a0340e070000d000c0051a007075001101a0014481c0c01c0e0b4400205016070085024056007076000d081008007682801004c01e00b00c42c004418802d000c03010007141d154408240b00d1410f04807924010302e000756000c1c1c003e05015420706000041183c1220904c8050f0f03080550301c030351604442601150580a8500c00f044211101080d031030a60702103030b0082d42c00c030b4003034908210b20f02d50000d0703924585a02612207000507400040c00d03005c0c1403018420b80008a60440d00a2a4034000348005c9100096078000a08a18400600c4010340c5c0c4403035110003c081c50140c030046070900a4800003000350000d00c62264031024800040001901c1103d03200444581954007408007424000e060006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 832357994 1250 832356744 832356761
    0x150c030406080c090a030627020f04020708071209053307140618190506220f03020304090b030309150c01090606081608060906010909030e0915030c0102030a050d 71
    0x118600b0404c205054441e2820040618099400802c0448200740341c007400300c81e0341d210b01c40c40e200d40e092400c00603913546141848440003100c026889410508181030144640d03200102564a0261a49621a0429180000c079542203075000d60701c49500560101030041c9184c0b80c50214280c01400310795034100d8005c0d1090381d000b0760b90f855079001c4c0e10380400d20b40758066480700240c101806035010029410440c10844100034520144449447c0c0c0d5040d41d00c40000d0000c1c1e4804501503092842d10100203405289541c00c40e04000c2c0c50501c40c140030307442e9817141c040d0803007060402d0804005814008100c66a40710054400380300b19002c445200665041a010030f43c01c2e54992529001050312030149602500e03d0001500c08090f225645219114083d4010b1043c0d410141c1080421040840c20318111791011201040411031032600300d56207440ca42c401903000b4421400c1c070201140341d007664089418140e040700e410034501e000683e41d81c0604600800051010402c10342042d9064020ba840e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 832359244 1250 832357994 832358011
    0x11040506010c0b0f0a0906020d060306060501020708100e21030907050108040803190605031f140615070809040507120b090c0717071a0910091505131202070302150c03040608 76
    0x122921b01e940c1d41c0b400c0e07910105a0030007081c0ca85c40300b071050008031721881000f040c09000400d2400c5c5840a00c42d06c2c2c0200e5031220851981e03c134180d40e680308051000c1c1402c0d81e0003040c1d0111851026000b081e180c2c00c20b5034010060704c5400804900d5501502081c0c3c01550007501c202e007141d0780c0d1044452042000c100c6060090345a6800080d10380301002141141c900d8009614503218682d050307c07049640c40128142d65120a100740801605c80294022048209540c05070352499142000070b094807480d600107803c94034100c1000111603005981401228a01030b040c41000340c150204681d50009071001050080300308403250002e8040e46081e40091000500a0300789425a2502d1980000a905d40700344070100b9410060302e2a01841a00f41001809108002c03403202c0f5110070b02550a64540900c0d07a5607600040750214003090f030f45084075a031200518061a411103c002d4813508244012805620007c4e4409101100c2100f5603010260304070007503051078074007682126660fc01034a800c2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 832360494 1250 832359244 832359251
    0x1a040305191215050301050a0209010f050711100e10030c0f030c031104030c1502010911040915060b090a0b160f1704090506010908160303120f0911040506010c0b0f0a 73
    0x1000b495902910f11000810250008024546418942075400040c2041d400c40d104005000d0240c0c0c001d015140d440708a860643d841d65000e1510240c5074007400401640b10006541d41d460980d230040707581c0b04a41c41a00e071150364205c0d11101350700382c1e8009038402001c501e03c030040c440d0980c403d6018100d0b1880310b10300455880e090380003601c01a4000d80007924101c42d080c03001d00c0120a0095800340c0000e20780300800880b02c0f2602c664a03003040e0701c0c0f002e61046448601401c1400000114800503034510502003065555071031901c1d0a59010964250184860210000e200707560350041d260031200703d0540c00740b00c03199503444c0940145611802c0700d2102c407682901401c0c5500314007910103850b031001c0005541c100f90001506c07688481d0b02441385030380f284000364034a040d441ca511089030346c5800e1009214040c0c484000103040903140c500141d0349018030741c00a02084800d0300181c05802d4408101944481004490001c00b90030050081c40d400d00100e50340900035000e09500841c02c18000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 832361744 1250 832360494 832360517
    0x6070809073209070f1d060a090303020616080a050709080307110306011401230906070b011a030103020d080d0b09040308100e071202090d050102161a04030519 70
    0x8200c8440c4000921400c0316003200d400300c0100b14000ba02041890881d01e0090615024500800b074404145440b001c1005107050115010b038201000d4404080092400c0c0c0c6403001d0640091084c1c400748030590042c0305007404502d0041c100036810704500c046942d1400e003603031425840800b03010050002c804000004000141c5420240040c1540512882c01d40e14000304004c2014546003045c0c0042409034803091b200041380c0c0e003203003a100e1084505c120f00c20303001e24150851942801110074003608002c000580300208458030303d0b400c0c181d80b103054602e2038480b4520113080e2580404d0000130340040d1840c0e00c51021542d040302800301c1c0c0100080109400450b070340818400c1c3d00981d0100c010a03218001d0048140c0c404030b016016252031000d50059107001c00004100c2c0d01005041c00300d0980c000b840388403544460071a0045160014005d650f00c2c0d018103000391005440724401d0f41c5090544040b0072041c001c1c100b02c2e500840e0995500703400d002d40b414100c0103040c0031900140034407400e86450b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 832362994 1250 832361744 832361759
    0x61419030512030901050c12150415180f0504030e091306110301030b070c05030313020a09060803090a09020f250c17120306102f0109120804050607080907 68
    0x100d1600b50600701415228100150400e0a4440242c410f080102d42840141c00d5a40c2d82d990481d0300035010200b0005e080408400316000f8612080d0407881d440c408940030a880c00600e4034940036140e1410f0410a0045840300082142c600f1b0f10010001501c2e056111003a01e005d440b0950014400c4440d2400c00c191540c2f110200ea200c0400c0700d200060200040052061403480c1d0340e84140c3c0b03410285003100351640e41a4603844000d1410042c18070000c000300540d140c03010788201a10602c4410052242c40c0c0314807a0342e981012103140d208128801d804500e00115001350b8003a40d044201150804850f22003203442d04044190044031214594001c2c0085074800c0c03820380041c81a07916045502035040e20f01d41c1810002800c8040540f020001e0040645858285007610b190601e020a00400c8000c003500f424035610010315941030212046505012040d400050442c0c8941c20032041103209102c04d0b03961100895000d8241e802c03103000601c40c5405140b440e40c0c0b101514060795030143c1c48041c0e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 832364244 1250 832362994 832363003
    0x6030403200109050d080109051b0a0c0b09100c05120712090f0b071202120105040e01020721020c09010e06091b0703020c0f0d02061c090209090606040f0614190305 72
    0x290b405170b006800c401c203001d030403a4580d805000c0d000e2050000745440d01c0b00c0851500783c0a082c907884ca400142c8500224401c400f0445280e81c800340311032141c10308100007175549040296034099140f0b03080e40308000741d024004550006901d90b0f0350004c079a40700741c415101b460f10701c500c030408141c45e20005c8000405c024203009460348600b084440b18104001c004040c03c000f5044442214410803c080f0544141144181100c80480d0040782d006142030310140640a50407000740a4a1a015047d94050580f6150079401040780d08440040c201e0100704031041c0002c0c03080f0315410404402280071410007504582c1c0c0b05442e41034a540c501429100d20080717600055050380142c104080358103c84c501241805075600c41298000c91045507030300014094400c442c44e1040d0b14524a0300e16070810100c2e04001809500200300303d40e03520b06180460b456510840c8c45510451400f03c1242c00052248520404e45007103461102c0c0c41040c800a102510f105c1c0752090f2200003910a0000c0054800c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 832365494 1250 832364244 832364261
    0x14012109080a080702010c05040803090603040515010f03120807080a051f0801060e06030318010810091404050d03050121050f0106081617060a0b0f21070e06060304032001 75
    0xd80742c030000d151201c4d0003800c46c4c000300103000410508100c10030418038004180c1d1103440d000c58070280da03500d46103403051604401484c2c2c180b049150f100005030a50108094800300c038001c03101c10061141e041d00849250404480c0400490000804034000740065401160321000030480c0310031400010340e00c028403402e1f55010580d035030f468900c24031000c0143c24400303400c4074054000318140612011802e0905e03004001260402145200280d0203090700100d0200411660400b08080070340c00c56982d03072103102110706940302c0c1b0508015810442c401e2040604940d03070783d076240c7d02d488003000351440341d040041d0080e14184288401c1d5189140c0a03c1003030001c0040b840100300405685d104655611031030740c0008181c3d9045030b00418540030106096a004017101e00008030942d4000c0040c0800c01488065900503020b80300b0b090a91403150021038444422000b10b8090a664010300c54881804454094000c58203201080021b80200e1450041310741200e010750400a03510000c3c0c3c219007161 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 832366744 1250 832365494 832365497
    0xa09061e06060221030c0a121a010f08092815050411030a1208100e0f0417090d080901020106080f070f0b04080a0f020609150c0714012109080a 63
    0x1001c041000e60b0f0100320191100f00200c84603059000c41140c080a0341c00000d0031081032540005400314041e00c2003e4400380040c40705010041d039980c0750103038101c450004a185012640080750156114014544588500c100308002d184885411842008a81c1241701c0124400401d20b18400068010820350232001c04030311000405203040c0c01c064000d07a42ea00022402030300034000e1400450200842c500c41d1080038100b0034070320703210300d0505010310449511003044440800c0601103044001f00c1c02c00d005500452180403034002e40c8000c2c1c40341c3e1203000d00c01039000340350320702da41c0000c3c1c103100c0074010b0000140000203060303a907801102d040050101444e00700740c0108a05000f500261464080036091852410341014104602076982c0ea69402c00030303110a1010092504540d610b400f16100410041c002e04d1101101240311541a000188400194000c80c800401c10780c1c407107111003900c10381c141c0d180342d00c1842c02d00fa20200d42501d4016a9004d40c1c0381d1000101040d5207100500120045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 832367994 1250 832366744 832366751
    0x20c10050604090818060405130f0c051815070b1e070c0c0b16080d060602120702061b0a051b180601092c01081606050306090a09061e 59
    0x2101002012603500920380340c46030b454009804007145070501900c64019103014000b100035136560000d4401d0140d5440300f40d1103c0c11102050314007005410040387c41d00f00304010311280c2407040013501d5a028001c1c0f4041504a0b4507000076092920014060300c0001500026203017920503111a2000ca004807145900301c15441710883d844030001704103079030014041c50000c0d000a420341d54200c3d1904503100b45941d8080100d82c41078040e11500e100781c071065001055541e540c0080ad0903101800d0b8034481c50300076028407064803440b4080c271001c59a400e68003c054902c0e240a200c0b03821180c00d0f90442d0400c46102d141080e900040003008958400c144203c00c4032404440d00080000e1b04100225400e4092000030500c40540d0b0400c21150550702c2d2048030600501900031056103014000040140ba120807a000241580703000c201c0341d2502c010f083d8405820f9032111401e540a20049d2a641e811060420000350708014540c1305c14039040c411440810440c00102e01203041440065003255490358 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 832369244 1250 832367994 832368013
    0x3160e06071a100b2b1b1b0b011202030c030f0f10060f060f05120c070b0115080f0601051201120204060b0c10090201050408010f05060a051518041d030309060f01080c150904020c 78
    0x403c103041101801c1a0340e403413a1f4203242c5548003440c40b1018841e841d41005200c008004641d018003c944004030041d0440f090007903140065135880c40ca07084040b03107900411030894001c454a001c0c140a07500c90404450121303141000854826084454030b004000080c0000e00030580522902e038000c0d0240d03a0030f103841c0c44080c103000e00000d2042e446034480c980c94442690401341c00401c0c06906c050355061540304d45d0788600040e9068070800501038400c40c5da80c0e0020030f40007504a8010300190007601c1c00c03c801c03612222515014410342070402c156904c00c840c900840c55054120407200c5206161203410304e982c1d00307201800d403a00c0000b480303c200e40343c0081142c541400c8120000030709003221113010044415184640910440180c22440a441a0084d0103500c40360071204240c4000d40001c140c60b47c01c0c01003e5145e1b0402c1d280e64900d4011980416580c007040d22059041e50650800361011130360000c200070252a410b46140500001482900d4082d035507407003e412401030f81c8010341049074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 832370494 1250 832369244 832369247
    0x3150f130506210616050d060315050a0605010914190e09011b0e0d020616051c020601180c0207090c0c060e01020f03160e06071a100b2b1b 61
    0x3e40c0501c980903082140300c240e116610006050f40c01200245074401c803440f40304012541881b800e051403030782c0350800c0790000412070105844281e00c00000002c01c01ca4582541c1c040c1aaa414450356002074207030301041c4846114010103202030707280104022030705100c0e111400c4034440c030356100f02210300902042103068103003030069521001e100d08084600e0001000e024022480380c40105008042c002d084004549400c0c0840c0d000c08044807214000c900c03507213003051b42e032000d54a41101c000051481a800d00d0b00018a4a060711400001c4003068103408410354000d2002c1c0171700c4030440c8a98280041c407046e8910480401390815901e400c807440311400c1c0b0f08133036001086035003c140c2c8104421500302d4640010750343c02044101d991407400070340000c00c8440c00d45000419922075000101030f02003086100500f010050f01d103850104a03aa03010b00c050003800e00c0c0c0f05018000400b0413003142074069078511046903100310100340e0846990250a1800c0f40c02452059605a500d43c41c0c02d450705 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 832371744 1250 832370494 832370509
    0xd060303200a0b130204020d0f02040f12030804030e031903050d06061e030e0f060a090b06032d011e050702010506060f090913140109020f01020c010503150f130506 72
    0x4101070000e19000310550780b14001e04000410032001041c195860000315946c0c0e030110344003041c1886040c40b80f403129030107040095119204580001d030030704000007103025140152140043e00340d12021000d654580382030f2415036044411540c036000b08241020345002a0050303100c4a80039030740d425203a03d03e0044440c03c80d4829044001400500040d00b0380b100c020ba503c080e20381c4094500402c00304000c2c00c07014a00000d160181d0b00e180039503070401240e41d00e1507002030403040c002c40c0d85113042c0d100d03c804d00d03844a07400114600c3d50341c440c00d00101550003240c514542000c40c04000144007200d0100780c10107104d9030f20300340d030a40d89401c14000350030750900442d07400c514125041450300d1b01040c0c0c000454421a900d0a014000c04000551603445180a00c00142d40000744840004601500c6c18001d00c1c91840c02c0380306d50020100144694400101d01d03461601c181c45003480c50b1185003040288021100c2c040340c2c00043c06003100006d8980c0c1011103801400100c000c10325090250400c01c0302c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 832372994 1250 832371744 832371797
    0xb071a072f07082e0501030206031b0f0703080a050a270c0f060c02031c05120a0e0328050901050f0c0c0312070c0b04080c12030d060303 60
    0x1041044015616032081109145066800c5030480040550300c081d02541094802e0344403403228000c3c181c2081d00703215041404007640940101e00c01600801d00704250407100c0c280400b82d0000b0040c800283c0112401c2c4071070455500c0650728038282143c0700c2c14503001d0f60010307004038000b41001c42800100d18041c05000e41041d2040d0301800010108500c0341500040b040905840c01000f644000500003a44800d202914114890b11042915408061b0907492940340490207407040958508045801d0007400b03030318018590b40c151401d071001c1170780740380c1e204045c3c03a8400ca507580300c41e102d42d4050108020242c403e4110000520204281004100041410040b80900c8070422200c0390a0f03070300108a03002d154101e80410703141c000042c0c01c0ca00c1c04d00c0c9910441d400d842112000d43c070322a030840103440b9144c4501110100c540c1c031000f24a859010324860241c840c3d1060700300710041e1400c203040300d0090070840100c07428005076900d24015681280d00035004201440c20b40c046902141e0844001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 832374100 1106 832372994 832372997
    0x5070b0718032a150513050604030b16051e0c011407081b1314130f050406110a020601090c020a06020417060603070614090103060b071a07 61
    0x8111070000315584441e040301d191030380000e83d00501d000c103407442a41505a0060030300f40a840c00c0d0803884405801d40082c0401080342c2d00c0320400f61004500900411185007000e1724035800d801400f000790010483c040100c41c002803200001030341c0449000710721580c0c40d80300e5901c050040501000f1455011600030520404903030109a59001d44010305240c00068503500360b000d03241c400c60903000e01140c8980c4082001e40c40800c00c8a0306258041c014410000482440c0c004441e01e4481c1502e407581d03200144030a01c00e00b8842d09002101c41b1151915020340702001a40c1c1d00014411000d00d15194216a1090ba20174041e10080a078031050a5403906d032107201e000028001c40d40824518460400015160703e000105042110b41030f86170480070300216020111140e010220641c140b588440d000030b104200342006008080c0190000303020303510741000c50002154041c00010 = true := by decide +kernel

theorem cover : BRFrame.Cov 832194244 832374100 := by
  have h0 := BRFrame.cov_init 832194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 832194244 ≤ n) (h2 : n < 832374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
