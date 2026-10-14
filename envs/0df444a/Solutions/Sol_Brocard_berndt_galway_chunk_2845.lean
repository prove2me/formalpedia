-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2845
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:54:53.743925+00:00
-- url     : https://prove2.me/submissions/ac2150b0-fd86-4c51-be3d-a7d608b27ebd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 511510791 ≤ n < 511690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 511512041 1250 511510791 511510801
    0xd18170c060c0a05040e130c15232229030a2301030305210f0f0a0e0d021f0b030d180302061603080f16030509160f060e010f08 56
    0x307000800c01031040f0f2a0007030405484070840c1d070038240181d4610380070f0b0580032011000d0241c0f6060403c0142718407900f50318440744d00340380030f420071450080502c00c1980212107200d041240740308803400c4c600c88218240340c00f261701d00814031051450141042c540380340b1515141a00210204480603460544040d00b180d88442109010b011003100c58a140c254203091031a030b01e1501660503003e1071003500c0e03150f103071100c02482c0e510740306030b000308140b00d0a06601845001121124800e4020350300c1c5a900c0c010382c1d165801c0401500700403881e0350251081958000d14240d0111f00841440c0d41000503044075082c106586042e50403c904440c1e064005150034501c59018400d0305026072003245d101a0403580e40c6d000551076800c603000030144a01101c03108801c041d8402d05080c0c0c0221543c1c08201c40341440b942d104015140101a241403565982c0440d282030b804101b82c0d560003254141c40500503072504081503e1000510440004c919070b08049030066020b0442c9860032655959042d03129603031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 511513291 1250 511512041 511512061
    0x80414160e04020a091514010c030c02010804021210020903060f070912030207050901090b01020c19090c03112d07151a040e060702100605030a02060a050d18170c06 72
    0xe44104d83c4414464000201002140034042041c42c103406803442c031518094100d5100703a20b241415040110029180c0c0c000b81e000304514229603028617103903e060f5141d1011070902100000316808521500c8041801c8400ea5001403407060801d4040c0c45941e199540c0b200510503003039490030041100c1502c240000c4209115501d41e0301d00a204840d03040381d58402194200354280c121000080d00c0f0400860303256010000c0750f034034580684240240b00d191032072415106500340110603602c0e4480c200c1c8031405e8400d40008e203040e03661011695940500c0c118000001103582100701e03a070b03a162001c1030800201d00061343d56941d0000d1402c0801d002012040b80208580c407071b550f0060a4510501e501750b02c81c1d12458401c200300c40018021418403180180c81c0818158100c07280e9801d0030414003644d240410800c00b03d55041e2425034640c1070504058945004a01d007000701c1a10341942050140e00400b101e0281c0b50240350115004105c4075100c00c00e0784505061081c00c1d0340040d0100d01c0c2295 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 511514541 1250 511513291 511513319
    0x90c010804230606120c010c020103020a1809050a0e1f021b0d120615120203040804052e0302181905040c0201020d061e030303020d02130608041416 65
    0x1204001d40600d0514107110810814081502e515440c2d02076000c1058904010340810f42c1030714010001d00c00e00c00302c000001d02001590200a04060b000300d035860f8140d00410901d0301c0290080c45903207189443e400500010301e8100c1d901d82c00c4508203895124940707004100800c846402070700329080c000c43e501c0200040d5001c1c3c50a01c400c8010100c0d401031000b000d1140e03180000244d583ca0822480021000d82030320380c242c000d0110071010107803030210325030820405c030804002c1110150300c0759540d00341071072a80616401075400c5a810b603001c81503071a4251726000c881c8540304844540004441f0228102d00803503040344406060004250043d140c003408040c2d802d0805510203a105442e00d0108007034545003c1a139000d42c1d000f1880c4000001640074107000741c4012100c516010320005940c000c106454031024003032540c000380480c410348a45c3c0450310f22a20b440f629001072651410300614070101110700340ca804401458a180000012520301920300389000b000d1086d90804100c1d6111307907 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 511515791 1250 511514541 511514543
    0x30603150103060219020f2a06040b04030302070807061709100e070302090c12041211160303030518030a03021b0d09061115130312060e100e090c010804 67
    0x31041920403000c040c41844418040e40c401ca501580303071101076054040214420b02154150340180c120312903201000110089008400f031041c542404d800c0b4083c03408490302c034440b9a045100054042400449180244101ca04ca5401c03640c04a07a1400156140ca4440c050000080e035121043e00070003070b80e00c0032150071487c2801540d000401d440005012140060a0101d4076013200d40200103601e041080c8690042108142e1072500086a60751a01000003d200030500c1e4044038000c40d02e50b01c9080c005407425103c1d0201c40c0013994802010300300c030482e488102c0002e030030200040c0751076001c100b000d0302c3c0c1d02000c4003d500740305002d0342c180d010303402c0000b00b80703541c2e0040b2581d1105041c1c01c10401d035900200b034a401071142e00b4480001c010042c2c80c046140c4c2544110351807100e8502d408021a800300c00c004012500340c03070500c0e0172203882c078082c0030301601681490b001060520780790f40c0c10f50098114400341940c2d44e5072036520300510042120207403095000b252110f0750303550003101050703841 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 511517041 1250 511515791 511515793
    0x100e0105101803030e10030501351f0501171b010314040606090e030304031d011e0305220203190206090a080703030f0e030606220e0a05010b040501051005030603 71
    0x894a5840c002e072040c50075881a0006100c40300d0300311300c038100000d610342a0300c1d65203414460f640c106a00400070803000b40c1c0403a041d1a04203000000344050030050482180d40c2400d444234682d0725182607441c0b1074100c610041003490300000058150400441c61550441000a03050810310f50f154a00010301c00b00c4451306068440002000c1c0c000d41d03004d1079200314070070040021002e04146140c02114200c0c2950013a41d4003c0081c4030200b50029070b110280c0d181d142d040e00c210042c001c0101c50042000e00342d1a049120400c0080807141c258102a108260101001d28076840150315804030f0308502e48081e41607001001224503000718103000310009030018040038600301010010442038803441c1e1020145800821003801010b6011400103200807561805100e4017560500103070306e8003c0035220f248100e012650300b0140e200c050309900b0510030034140411142c0e8600b040291295441d01b003c0718203528100c0c0d040807a2400380305d420f05842d4041c00b200300303201c01031105480d1644050035050f45 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 511518291 1250 511517041 511517057
    0x2009151908030d0f0b060a090e0601020c0d0303050711430611100203060f010c030c0602130305070f030305030609091912081305121812060f100e010510 67
    0x320720041004040058010400003025611000944102c85903440024411780b804c001c2140c405034003240d03503170a4420000300326140e0344541c00141d1034190499190b0b50070100f80d80480051641546c8064410750507612140c078900e500b00141500c4001c0142030600390607100811103282c00f0b0044081c400d0300540070300244000624500c4000082003503014400103400181307608090401404a407048148040c000d50860a00c0c0300090407800305900c4003410401629270420506200c0c8200c0342a90350051004c5542d0f48012030380002490550000351610300c80c49400050600c404040002143c0d01565080c0c110745441d8200f04002001070845003041c0324014891813150001e2000d07002c410300c110709152601d0005e2202030000c3c4030051601e6503440e001850400031601c08141d804440d1140c0d9a20383d5541d03007542c598881c10741003440e1160049424405a904a031000030384078050480c004101110755111101e00d50705c894107000e03c110440702900100818101840c002c5020501800c0001e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 511519541 1250 511518291 511518299
    0x3180f1e0a0503071b06020a20130609050709081c031113091505010e09060f0a031401020301060216120305030601050d0f06031110170907050d20091519 67
    0x491134001100940c2e1520311113034001800c6281d2605d80340180f00c180064070403c25291030b000a070302e00410f4000c045c0d0816000019603540e5665401c514501d13011002c20079a03803500582001400100d135081d000c0340012801095480307002030084080d0418606000f00d105170321108901030006014642480041401a0380b004900c1e8a24400901031070301c0000ba003014101714941034003940390301c613a050000c14920902c50392a030030401548100c2c281c81d000001341c20032000c540d503940b00d40c1c4003415201925540004508043d0001c2d41200e41d0f80d800c0352400214941c40082d80f01840c4103503c00b01458171182d0001030b0098002c1c5601000504181c0e041030310003102241564910540c20075000e0b5211014010031558400349002003d060340d4030500106d40c010702404401c480b424403241d0442c0100011541a030401454010344005810040340a08034076054800098860104034405443e003945802c6007001446240b240380c10312644580c1d41d000d80305002c0116070740d10316080c800c0000c44000c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 511520791 1250 511519541 511519543
    0xc020307021c02220209031606020a2402071a0618040b06060d180209071110050603120415080108010207080418270501060b0f1c060306060b03180f1e0a05 68
    0x6012608104d015a460040008240c00c2c250b180c401d0619054a40d58140900e42d070000f043c040c0194820382c00b0b8841c3c2408526403110100d40e64a4042c3c1c280000348140030805003848076100d84140e50b40c580106c0d103c2d4020070895a40e00181d000034203c21200082c0419a45a2580e40299000d07040da403504620144420a9911041d21500050b8100c1e08400450501c190740c203a2080d403910740a0004045141c1e100d4450100841e80c0c0b0859443e5400b28076541d0b02400007608029461494035604d507956600b01041c502c20406100101e241580001500b44040c0201d0311015849000c0a20306410b01c8070b8109075040b00040b40001d15a540b014020392003e001d82c01c0c042d10110040b142c0748126911b051402c0d40d229411001c070380401488000600c02c010001d59a180740e680f104c0340c403411b0520410704000c106a50000c0c0c40c8600b071000015046000c80b00960066440d148680000d40b00840802c0c0d0701c68140180b000c80303501441c8407164404022030300e900745014850a5541c1403120392103503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 511522041 1250 511520791 511520839
    0x30c151303080316170601021c0207050603010e0117030a0c0f150f05061c0b1b0c03040b0406170f010e060303070f080d0507081302062b090201030c020307021c02 71
    0x3420400e09601c105503410350814644181174103c03c40317400f1306241c5080000e445021354040c080301902c60b40140043c040c000c0c403019000d4440a8801e031384a60b51000c1004590a0070b20501100d0003101d036890b08904000f004644010102d9140c101d0108100d5a60110700c00c0d00724401da034008282001d4521501040c001c8070b040e03015082010070241804800c00c212031038500310310040607010034180f10011f4000320b591070b4000d9018004400382c2c00118140d401c03a10402d20001c1c07190200041c04203155090f0302c040c1065540c01d640b0101c8410303640f141c00c940d440c02607400c104036052520040100c402006240d0b54041c0e0040d080d42d040401a13a100826628607d0040710380f080c0c0415201401040741c42031540c00801d074905400c07039050460802c40441e0060001078090381001a00c0034002d00702d000855250215807181e8801d0080018060000b00903811049000a0804009500ea188001b0503102c40d250014402c3c030b0a802620301d84042440c2181040b60041d6080130302c031407002018040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 511523291 1250 511522041 511522051
    0xb070e0301090c0f1e120f0c1502161d0403030e010204080106050f030c01141632030315010c0618030903050706031802090a090206030a0f0b030c1513030803 69
    0x38021015050003c0743d0004c5440d030300180700c02a0004603000011644010300c00031100160040c0c45501d10905100c1d80c075204544020308071200d421400504003800c003102c070003da01d281c0c0c00d0342d0342c14080c0c940101040d4458443c071440d0f01c0e204142010500e00000110b03400c24400c0c1000214000c160320342c5826600158403c1a559554410400031400c080701c002c809900110b02511800000c80300207011180600312240c094000840c90044000c0445021489a81c00002041000840000e0b01003480c2451448540022110303004540720300b03000040c0c074025040d001c0d001d4418440440115154140d000303059070001e0300c4039418400412103540c286007050003987e80000351404e50804914150480d4000c40415251008000c0381d40344414029007407550440c1d1302003d64850300d1045001e000b514001030341c0401c000040c450800c009900203400000040c0e0b0070f10410460b00d04041e1a41800c03905c40341c110786110304520a40e41140020b045a042200c0d00308039564036500d9401042c4c10031a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 511524541 1250 511523291 511523303
    0x1103101a011b0206070305070c030209040c06030c020a230111120103021c050c011202090a142805010804170307210917030a060315020a1407030c0b070e030109 70
    0xc226002940d01c50700c18421140000420806203249601241ea984202c00c8003a04001020807170f8000c01000340080001103400408076011404c05051501c4ca100d400c1c400c0c0c0c1c0110340f8004501c00141c3c000320301690101e4002500090707113100a001e09030b40d019602d41c600021b540c5d038110140180200380c0648040010342140615640c1948144400a0402d03c442103150421410910000e01c2c0003a440000318000c3c0f81c403034000401001c6580103030150401d01a8006031a25001c1741c44034103410403030b14940048840500b82503c5044c841c0550382c0c006e01c6c2e0849009500401d00c4a135002d0f080c041c1d0000c0c4903031025103c0c0c03c0c081030507a502c1d400c05e6500ca40018840d0030483c1c6246120100c1140d03d01800300200035201e0b040d554800004110b4100304d9140ba03000c40051031281e442e40c000c40045800440b00c2d503401200032030f804001c4d4002000000415889202e0b4490340e070541c400c0e103281e5541904c901c01c100f0f01c00e0b181c0001d1824001c18440400c07a041614603c540c80c02e000c0c01c461288900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 511525791 1250 511524541 511524581
    0x60203180c030303090706030f060302060313150c050405190e070908061b07020d0203010b0d03111212070507021906030914030f07080f0904020403120908150103110310 74
    0x401050821151401c0300303120342d200b4024042c44110102d051000c45410b414001420310514050b500904102d0340701a502071404020400c00120143c01d4100340d51090107400002e00310140d00d64216900460640005007051105201504001c000f0514803074800e03040d0340d40d59a54901660f604041156030400040d50400104002241044055007006640010000342c000e01c1001180a001c6c881000e80b11b0480724900e80c080d9102944030f0703850b102c00030302030322424440e5003800341c210800c014420b034013441016210940e4200c0d02c025900311030240c1c0e45150b140d4441502c1110ba0750000c0d0070503644582c02040c2e0303180550100200400a081a0b01c0214050200341010600c1100003c4500010b400c10009030700500a00801c890805a01c10b0003562075200c80c11002e5124052514039a0b0402c0c40001c0110511040d0501d48540403081c1d500d60040e01e88581c00c0030b45641742184070403804017244006000054a2416078060201c001d02160040c3d106d01c500d08054410703e40b080d5200034400c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 511527041 1250 511525791 511525831
    0x50a050f01050603071409040204240f05041112040501150e09160b09150c010203130c14010504051203121009180209040b0907170102030708070c0507050108070c060203 74
    0xc2c0510b030707480358045002e03002039072038821841c55100c640880c203445441100001021592240d0111b00c08410003c4120034140c048090341c5041242d50090071103108008900081c4c41c0b820307001d43d48a140641c3c4001d0704080190702a040394000181044819540b94103906180200960b11280142181040e0750502c0c145440c000d4100360004580f41c030040d11240c01800b1040400003180c1650209a9203071192006410903100240100c1c100881994000014401d2551500c0d50b903516039030080d144013400c2d56484042c13075030150b22120018040780050208005901d070034296071900c2d80103241602c0c0341c0410141c1d144c1c80c05804550301c08403508844414001801c4a210f030411030070400c11035807155030168001035089030004100400301c110032000155005000e01c2100010601175000f40c0e0803511403503840b4040d401c1102c0002c0024640b0000a210300c0c03003000e9122003a0b8100004c4c00c0d20301c1c1440c00440d0005401016182408004814400007420510003940304d006c10043c03001854501c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 511528291 1250 511527041 511527043
    0xc120c0b070c031703070f05160605010e0108121306210f1a031504060b0a080a0c06080a0c23250215030c040608040f0b1e0c19120603050a050f 63
    0x201c131100040c021052007007105050300105e8000c10001c00342003031600c4500181e070107101e038a5607540050285042100008141c01d04c2c40c6064103984100301a12102142d00c0500071050080da01444105c4000d00c80810a0901641c0d4a400c01e10407011150f14002ca03c0e500d610a4641240c00c56501a0707503001001800f2103010300107511280105e02030400110f41e54150360083c50046c0003d0030700da9440c110920940d07a00500030300140854401d480f08101a4102801c034400d0702d10624010584081c00a943d003034040c4038012100c5819119015411a1400002807241d003124800c0507801082100080440c4581d80303442c3e05003564180c082e06000301e071050103120640f07030b010040825018000e001d003540c0c11906650079280c00d46030000095032242014103156202000c0a481c2c1a03035881808184081002d40c01d121684421080e0503e8582104605062140c885800305c2200d0003500521075910400311125000c0e16068003080d160303101d848031403e00210503011205540711032580511244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 511529541 1250 511528291 511528313
    0x80316030b0604120605060406080f0a150506010801030b1b1306020c040b22021e090f0907020d14131502060c0315120f06040b060a120c120c0b070c03 66
    0x20360700c10f03081034070380350102c610f100844900405c4541c9410000d000354442c1e41c4280d0041080c0c00407900070440405c001c84d25440881d006450202c20010000150702c80780c0a107501800c030681d50342c0b00e580c1ca15140c012004002401c200c1c402da0020b8070124210080102401c103544490519030b07401031514002a00c0c0030341c12201203016600300002c2c0d108a81e103080428a0000414403144105d06040031504003d1040303407030442c0d082a1424401c000c6440c0c03980500030051065072090245104c040130031071040b0381140c002c401a03002600b0401c445104000010901240402060408003145070304401c240b0141c00680c0f860b9000f003440d002c80d5034100021908250070018551560400c10340c81204522a03c95850003024001c4440c0707101c50b0708202001c0018601c2059031920b003440e140a001203103050300c0c0c0520940700c84c1d80104046005101c50806036600c0600001c2d41c0d4034095141c0c0030301c0310180b0203627907d01e44e083c00068000c003280d00410002c0d125a062011441c11883e05140e400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 511530791 1250 511529541 511529561
    0x60b0a0e06031501210f1a18010e060c13261203010b0405010302030c0d020c060a0506040b01050909070e060309030a1404050616230106091112040b040f08031603 71
    0x4103c00f0010400c002c501c0f20302c002c4015640b440301d0030055a40c100000a030301c180d000140310a032129281403090101c00340c840d0103141000c51100d1407882c1d50328450b00b62400f0303000c0d1000395004a0f0214031503100940c002c114400704d950034201c04690b50a02225001e1240f52541d0900c0741680840d01e9450040c452210843c022142c1d1a00715410503a40c1c014a02460003024103041d800800301c1d0b10070500000781d0b82c0f03202608109555460010740d0490303e030b420580d422031510f030806003c035505107050700620520f60410b940d06402e201c080c50421069100280c030420034001c0c5148448840d85a1000852103413081c1030003180c0d030f0710700e060004090044403074142110200510041c0b20030340e2090700711a00e419640400703c40c03003c81c9041c9040414101c6151070403285035800402214032040d00075600f100c0380d2950401c026100400c03002554402d5032440c903405240480042c3c0040d6601c1e50103508036018655001c01c055003642c480c4500d81c010380e4101c10300c0f4154617003c1e10302503050060000403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 511532041 1250 511530791 511530823
    0x120d050a0e210a120c03021b19080f07170c0d09062705060d06050f1206010e0901090f0614060d050d030e03090a090501050a0e01080a0807060b0a0e0603 67
    0x4004148211000e0715501a40c0c1c42d0a0b100000d5000e801c3d0b8815100c41e450380b5140d4108020500301c945000c1c00039803181d001c180104540e40041c80172154049582c1e0811128a615035240081e5903441e2082e40e1b00c03c2204002c0608240414408528070400c448500c1031071501243d920900c100d0f42c4da107014254070741841008000340007404015405405e800b5021100002c840c000c0f01c01c010000701484d480d402150f0400c4000c100c92482c0080c0d50005401c44000399094207510b80000144003000740e60b4105141940d010b28010800c03055452103095101c0701c1180005880d03401e5698801003011601d000ba100e0f203842d040203080015104c10301a03007204040300d0504a101d1941e0300d135511001c01d4445c2605041ea1070302c5018110806004480c00f1003002440a41540e840b00b4002c4014071007070003814000c000c042004038450103001e0641e41a0364800e002000260243e94401c0242d0f48401d20448035141c46009a001c3c98035200d8040014201080c0002c0562a00380113040ca0604c503515517542d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 511533291 1250 511532041 511532053
    0x8030f1e010b180f030f07090b1c08070c030f0602120c090a06110a21020705061804110d1a040507020a03140721030203070f0908100e120d050a0e 64
    0x2000340008480d80414210008252031003e5000294281404071899030540110100c1c6c104454012507180706071480c0410401006140d0703014004003180b400d03000307110768061150030344c0890f6240009d8100184610917000308191030741d891044840d0340d080b04030380680d004507100c0300343d80c0a140455406040e030103104c1c0c100188180010030000b400c0c07056000b4880c0039011074000000c00d102084400390000002c5540c51420345d0f0b0304042203808004440140210700d00404c181c60044125510480952a482d038922240002c001c02020060288811283c1c20444200801c809000381043d506052880c2d07213003040140144402c1d248014514405c54002c1514030000a40200581030480440c1090b07a458460300e00d0130301740c1408a48410f103885142039910003a8035038980c004510481c699075400441243c1c0c0c9070151017212041c0601607003504480715540c1e40d41000d43c17148186940c0070049442c0d401000c400300d8140c2c1c1c4040d02900c00300342c44a0800c00d02041c14091a40102d102e5801069 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 511534541 1250 511533291 511533299
    0x406060f0e0f030708150612030c070e220b0a1a030709020d0f02031008070509040b0604090318060c03090e0f0c03041109130b15010e010507020d08030f1e01 69
    0x65030000a018078400d08030010b501c200c0381c42c02c00504000d8a0f803513044401d00401c59801c48005e204c100d94840c810310140d440807a95807004070aa612000720039000740002410011329100583c0024600848091000117000000c400070000010480c02001380f08841c0c01c100580600382c49405440c0f648168544210311441d480018444085802010380143c840001c0341d03150001d000d0038561002d0150011050010540c2003640c07540860f0703101012505000d035035905002a91004880207000b440800c1e00040321818140c005404141c07007490160745894011404111103071494120f0070018140813400c01c10140c21000007005810100000c0b021460321008144d2103a50041554440000c080041313001c00441081504000d40001c004010515001001c2c00400220700c00942d600c6d41d01401007110036505080010510700107a5a0612100103040191080c0d23210700012a0410780c540150404110882c024500440700134019403100e040401c854207200684908829482c80c0ca180100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 511535791 1250 511534541 511534547
    0x80304060e07290d1109090a0c08010608060f150405120106181821030b0105090102060606130b0309010501080d1107142704031101090312090602041205010b0406060f 73
    0x6004900d00441442c1c64601d40b180168490080c101c00720411814100c005e03068902a0b0090f203000001aa080c0d03119945041441d01560990502c54000c9109c3e0801845140d20401903160f00080207001c0481003440d0001140300034000c1c64154000b104041018030281c50000304000708800c844000384002d40c1071030810041901c41c02040d00140740c1d80c1003400c910540d04038040c040700d40c20000346a400c07041d5240c503c60400e01c1010000019281c400c03a041c040d0b0141c0c1c103844440d001030340281165540d280c10700515074800100350100003010100000c4016050008620a07084800007260715403405c0049131401240007074100c140203440758540c10096001840500700e41d43c8031140c41c8049494008200c4840708200300d146800095901004450b40480e0554021071107540d03401403001d82490a0380c01c0b070303d04440050000300313010010141007501d608135000907030040c40018a0690f5600101098001014084885d651103500700c491500c0c142c0324050040100b802c0c082089046138a0007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 511537041 1250 511535791 511535819
    0x30f010c1d130f0605060d05040c091b0e120307140601090603080a0c110d0302030a14030610050702120a030c060609021e0706091707051225030219080304060e07 71
    0x4015050f9206012005803e6541002c0300903e400343c41d060345d401e4814034120140504940c1581d255450039800200c03c3c4092003002c1d1407003008807442021105003c130444a10350b8161980d68445002c061491490350144000c1c0341e40c51098038003600c9490441541400e000059000d012160702d080c0040003c6031107030f4219000f0700d10900c5c010440042c14500380c124521003480071a00300c40ba0f001c8410426400100404e0503080030f4a42c40d007018008416500c0a100450b020364010b0440d040c11110340f03005201801c289840200000414070010f66410b10b0078883c20810740028034041c0402c418004244104000fa05030070b4070648c03400200341c51802030f28141850950020700005045414020a6444514441d6000318080c0aa800b0566041d00c150417600c1c090f100c0d07028645852a25071034000031540010814654401a202c1190b40c0d0949820b1100c02902540500b00100c1003000b03c404400038460b1013003400a8903401d090418208a03130f14a003c2016a9101c00c0080c07000120144103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 511538291 1250 511537041 511537069
    0x306061807090333091e02040f0c0f3b0d0c184b0f02130e0702060c0c10020711030c0109030f02040f0902030f010c1d 52
    0x140394040e12807a03070880708408941d10203045800c120035441c4000c0203c07158100e0500f815814000d00a80900380303081181c142c010000c0c105d060b900d10507802d111b44051440b100c0c078001440001d10440c01400841518685150071001804c8000e0424665420220980320000b2102c5142c18403200f0000825050450361802480c1540c1c8015001d0956104145810380030ba1064102f40c660741d4916000051261a01141c240141008000c812803a264030506c014991101d0207070201c1085040d002001083c1580c03100002d500581c0302071030455050150340c940300000e100c01a503d10f2a080c4c1d0001e07441c4650004070b1003080359014071001c9c682c0000d8298101501c00e540603640e03580c404095140060307041402280b140081094000d00c9030407000d803403000d01c00303905669420040500450320710880340001001d10760110184405400c10354882c0700209500c10f000904044d690300041c1ca0608860360558150f9161038807201d460740e1003d40300441e051001e2106c0c41e6581d0a50000300c0300548400703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 511539541 1250 511538291 511538329
    0xb03090a020d240e0c011d120f0d02071a03010308070b0a060f1811030f07030b01022a1009050612040204090b10030b0705040b04060f1206080318030606 67
    0x7050106001c0080203a400242c01c0f8941000c2c103404030350403c006018070340e01060f40b0303008130390009040d0350044030b01541e1101e44610b0704150303c0d4000c040245440048292102e83c0c460400b00b2011440100005135034900c19030010074030f07580360001d0141c030000a54501109490144010400910000199048158442c02c0c00e5651790350f520f041d030024103296010b1480b814080c40000740c0e00d100794064071140810380c1c2c002d100140e10303521400460b10080d80d12625070480741c40021041c1c0d2190780545201501481543c44c0f000b04a14183c0322b0b0320901000e54007407403018110740440e151400300c56002c0031171800e0505c802480c010020f109030081c05101041903440400082c00c564444e4801c680c43c40e4072080704051401e2150300c02c04c1051740c0b40001c40f402040e090214007124010300503036081314000c00000785440d0411900302c802d0b0b03041d49800c0c0300340581c02e01c1c40b1031000c3c0d050094001404001d001140ca441c02c1c3e01c0c2d09001c0e01c501443c1580a5040181481110340b94400000e01a1084107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 511540791 1250 511539541 511539559
    0x31704030c050303010f14030a0c38030a0f050f0703090c15050307080a060509010909080c0109080c12120c0f0c060a0b100203090907030f0209030a080c070b03090a02 73
    0x208058039050031a100c002c090380000400400c1d918428003001d002c2d40d502c0c81e501c901031101e480516944001a41003e060110902d0040000b03071121825074140c9405000c0c00ca0b0000408410790400110400000c820803901208200c00605584206080002c4800d014819400c0a01c51400c200902a0000c0e042503120f0202ca003c0c022180c201c0310051042c2c1ca102c81c0c0140c144140140140c2042d0703144000075400c0030214860624038050901551380082c0781a919920744001c1200600004100b110944018014200251800e10802e1041d0303014510381a83c5912901100d03083c1907003101182c400000c01c2c0282411003498088159100f40c291b07005d56030b5803000e006044510301811030551294440c01c5c080280c42c0a498000f4940b2103002e594403040040000720aa803030b409903155158000c03c044000135442c5120360031030f07010500007000040c900707148500402d01304250380c4410382d40c920001500500d240b8081010000401c101c003041e070f00794107000c1d03103840e2642c9000d03c0103407262102e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 511542041 1250 511540791 511540793
    0x913091109070216051306030c0f0303110f030901030209010c020d030c151404080a09030f0813150c11012a0c12082b020403050c0f030303090d18080102040e011a07031704 75
    0x87d88804080c60f00300c180c4407203031070755070490b522a0740203030204030001401c0404098031098000303941407406126001550424100800440017504105611f504100c10084540c0261f141d90380000d06541c040d964100011480d1300b400c40d00a200b200b2401562440e1100b00581c0403c2212010b812030780c0103880a0344c43c800c08200f1200c80d88103400203020001245903801c10810082c0040031360280c0164401840c5541d4281900c1c8041142c405c0c8000c9041320344220005280301c3e880d002c00c620141407440c50790f040302e8400141030056503413140006414590200a00a107880c81c08000c0111f0b0b00c078a000c2c09100d554900c2107015102c01c00f0113a60300f441d5084040201040c502c0a0010062001c40d15141c1d20b0a00075501ca0f9075122842c050703103814501008034140072044900c920209070003801454000d0508032045c00d9032510360000d2800079580424010400c0c0005c00082c000d4030350364003140d411b05250b4401e00c036501e409050b9255040060360b0001c1e40040c11500340d41d8030505204003990725 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 511543291 1250 511542041 511542079
    0x11b05030709030f06021e0403120804080901050721020a05070806100b07420b0609100504030602070803180a170306130e071401091a091309110907021605 68
    0x3da2800c082401700140304403100101f4580030b842103038014446c903040c00d41441c0080d20302d00b8003500e000e032802408204408041d4024401052030714401d401684030f25281c00c4662480a0400c0051001a048550510f050107010022030025020b5031000c0d1a06040906022074144d00c20b108400c01c1c404003080c200140100c03002c0e030786501c030869090030940e8902034582e00d5003112160300d580060b0f03c05c24000030b4902040e2207001d140c5c0c00301501d1315150800c03c1c0e003080180c01d5080307900010007400700030210006020340003420800d84505941904c0381000800546400c43d69212126076a104e24241804a03540041861810001c0240c4c240d50741c0b182d6010500800740c04501480c024144403401007006e6001030a24111407824401e45155001c58004503116003a40c407485034685e00360b070a1542d440301c0300e40051007a500010107004a002c8104960026609041d500341c0380d14044040741e2155003001062030b070b440f020610107003c40d42c400c0c81040c0c218030603d0154500a10507158421883d46d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 511544541 1250 511543291 511543297
    0x306041505060306040c111b010306151d060405031b04050c18010c020409140d0e0f01020709051003020d060e390a080f01021c060602070306051b030108011b05030709030f0602 77
    0x810015507008e1320f03042c40b07450000d90034452001d0000c1e16041000a680c60040f40c2600c00051550320341c0c09840789a81b03106d81100c100400c080d80a0310030840043e10b40d4080180100449401c4601c032403000c40c1c40200001c8500081c243c1d42c100108001890f0010310403c003100340c004090034620034007401400810002c1c485000001c241041015090300c0000d000541180701c400c1e1030303840c0c1019801c0c00c000c0c0001d039002d080025015a10a82c010310036400c0c50780040754840d1110088402d010b0741d83d0002554490700d01350940d54150354015000c03040e24240461005004c03840400700380c044a00d00412540c8100381c1c0b0680e50321140e00305100c1d0550318244075100501803941198071100300c3d41c0c0342d58000e620140d41941407022b500c2c001445040c4a0050400f2200641c000d824902d20b191540c4021b404010000007207034041070061445c40f0022800796000e00b031694000103010840300415004100844146402e001c014410007011691100e40442a40e80c41a01e4070361038211440c00720040c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 511545791 1250 511544541 511544567
    0xd0c031803021e0a090c0905011110050c120703050c0d0209031e030909060904170c0307020d080306010f0905091305161203120c0504090203040f0f05030306041505060306040c 77
    0x420407030040701074040700344003480002804c5070f50b050081d0341c030340f085011900001908000301b590b500c02000700751701a40788c03d42000c3c0e804040d1035880c0e20300d10080048440c2203071104070f03c1e0740100301210000822246298400c0740383c10104070a0a001840020030701524081407072960300011011401e480510201c0d420004049051740c0e980d40540f42583c898100d11400750040d49181c000401d00d20702117155a00036504002204250b1200041e0380c85264003402c0355001d80d10080166000588480c000350103c5400789045c035840e414510001071154140101b00020803881440c02e10865032611003040d040003000222104101c0e0301e1500d40d05000f004000d00000900b207540004400d42d019503818142446680c454031011080b6407000b040b100020803000008800748418030400420380d00468000780520306072403408680da41d4030001480800e204803840e8201105000490402c0c3c0541900b44010b0315003404d0361030070a07000c15500c0c0030090185110356150350a4150650040003a00c1e042 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 511547041 1250 511545791 511545799
    0x110609100e011811030c0402030c07030503060d0c06030501060801050306040312051e0a02030103030f05070c0e060f090405010b0909012d0213030308041104052203050c0d0c11030d0c03180302 84
    0x83c4100c0c1c10200c0d1101e5618882c14041c0c0120b540040340d5140c60f2007100e00c03d180d10b017581d504040c1981c40480e410780005203015000009071903204c010502c047c0b8420f000340300d2541e01003002d41c1043c0d4018020f5006901c018020340c40a800e0200003a001034085c400300b02d000c1c500060719620103404031551161184120710544c1401d040c0094000c080d00158184d9010341c450054840203448103e0b464070540c10068010801148180400d00306041c400b0340008004161203007440320100010f030440130a031012501a07544100d0125581010721800c3e500007090320017009501c3c0000c3c600c2c4185c04941660b0984180880c1820422007442d40c1074602c03250900d40b0201a958580c0740c090280102944d003515400c44519a4881919250051621a59000c0e14030f07100d44030100c4400081610300007003202481018819072107000000c002d1041401c0199a400710241d05900702041c3d5003540000d154002e42043d00d14a40d10740c0c0100342601d03032613414541300c41c800300048503c080c5800705030030087d88 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 511548291 1250 511547041 511547081
    0xa020d02040902070620040e0a0b060c0f0601060f02120309010e0f1b0d0f060c1e200706080f18010f0906051003020306160c170a110609100e01 63
    0x1d11415901500005204800410a802c682c001c00c6611900000c010b4011403010001840711182c032508e00d41c1c201f0484880400d0150000c0001801a001110900f85076480818007080d1101c003000114010a0517091000380064115002910b5018014050401c1d280010104420382400d6000501c030301d0f100380a44130020210035225450b08085903000b58030b09032106401d101894894112829242e010940022a04955403050b024041070700d030a5041c030000c4032280403810501c007028580e8100a40c4c9041a45d03000d408003445644143c00212041e034428041445100d800c00f45d510b42004103c20300140c1641c03042160101215900040c00495007054541d0311038045580000f810680708120502150b42c8511001610070361910004e940b580c41800458109000c4036080104200b540c80c0147ca410000d44840401450380451140f80c6000001d103040324a61000241c070f004c2e442e60004d00b4a508195100a607240c2e0420f801200c001c1e61072925107032299095110075400c030700107005159 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 511549541 1250 511548291 511548299
    0x303070c021816200309040b060d09080c010c0311041a0c010e010204060e0409150c05040f0e160504030b0c0a0504030605100f0f05030303270735150a020d0204 70
    0x900d81d4000700300f500214840f06500d2003801140c815841040660340000c500740b1001404020150103140c040da900030004101242c010710181c0600441c180c0900720341e42e940d51000c0c54071800c40e280c0412910401d450304070346801d5101200c0c00c450480348103800c955001c0d03203441c0003480300b481001032110040d8038022020840d0401900a0001c8520680312a8107455502c024042600c0f6581002801d20310441c618409081c001d0344000e2a01041c0d207002420940c6400031029030951a0308002500e050f0141001801c15030b4450820382c140b96490002e007050f156607100d092108018098400801e00420011040d5109009483c000c54214405000d24101044400f4070501c01d402341030650382c02ca18011803c0d185680c212412518060700445c80c6580755085114646410a02104001000080100351410822188010300184e00c14030b00d004000c040d000d0501e03500803c0d041c20b6060407140c940d503403450118880d01616512850820503548600421009101c1c00500002031071010078042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 511550791 1250 511549541 511549561
    0x140604050d020a170c04050f07080a050912070302073803130614090607080709060302131203020d03180c0608061908030c01050c0f03010303050d0b03120c0d08090303070c0218 77
    0x702d00c1d40f201b950b0410480d151500c030204003080031216a40401d8164020441c884041d61145a100c0c2c0344405031200041c0c0d50310496041d510010040d0700580c402c102c140a02032201001302c1104c01d494003442d488021061408081080e4688820301120000c00022201d5511014901046600c004100031498822001e0b02032000152509106403080e440040c4c07100c0d0180300240e0162005840300c0c505280b4161046010303600000c2e0104d05da41d4414800100b0022611003890750300d1103600605151014160020121401d902e030729a03900034079240c04408075203504040c0d425a402031922454554074240826252140011000303900650030200180d111000f0002c1c01d0b1030070b0b00c10001e00190b200c1c0c1d082c0c1d01c0a030003581e0004000342000c10042002900510041420304003004020440385241c0001900780030490480241c1c00f003000a100c6070709882408800445115401c1015450800c0d15241d65070707000c000c0c416000e2080c5a0180343c00d5554800c56580c0304c4894400c40b1049241005081e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 511552041 1250 511550791 511550803
    0xd020309010e0c0901091d010c0f021912030f020702120303090d02010b090f100e13230a03030f1e0911090c09012303100303020601140604050d020a17 66
    0xc018551915411010001021591004001c00100001d00590a294a0800034003140325200c240c095000380041c0410b10a003d080c684c001c03641c40b0b060f51640b034120043c3c1010303150483d049504080e0013907a070004465110650341012689030000e226003c0108000003071081c400041d50260b5105400307205507000000940c8900007003020f030350031000c40c0c101c1a82030b1250003c005034046075400c001074103c1c0501218641c4144041d414001c103590750f80f60461800030135600d003100030800e070100701c0601072110074409030308200251490050f1042d03480161154000c0d00003c04141d20740031000040c084907080b807245090111185280e0b1203412402c0401444e040e00201d40402c002d00b0b2061070382c9060000c0500c0740b03001240d00c1c0c3c6062500001110109004c4401480b0074403941e00c65075a20740c1881c003441c07040301214401c0e0081c2d419820080d2070040140e04c803515040c0e041e60a0040754840c40f094408a0b08151050f140d0f0310300c03520008a440c090307504007010f450b001c04000c0f05120000224 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 511553291 1250 511552041 511552051
    0x2603150a170708011d2a10020d0e010914010e0402210103061a031e15040308040311010b0d08090a050315040606050d0314130509010f090f1a1c080d0203 67
    0x30000400408101107450791100d40d1010300e90031881142e402482d105460903401b50039042c001d03400c28500b50008840ca600d028140005901c003041d400c20303060300320030f1446411509082805107940740c5403801350076440002c1d0b0382d0b04005210f0050811521030350140d81d58000b000034024166800c0110f000881442440141c5071b050030404c0c0005403000700c2e000040583c48c00380260444200740c480100c1001c10070f0001090a1280e0f000e0812800060940c50f4000c0303120359241845801c02e414010440c001e17000625141c1c0e49064403100842d5941c82120090075884501c440d2503492000000c2d10715581c40d44000c6c0c00d4040c0c2b81d405500b28035805602445644a64000c0083c591a0307024050b1000c40c07410000c000c01c2c502c20b40c0710300780a003c1c030181c5a6480c502c50007800494580d404108920340c280e1281ca40c0e4040f00100380100304842c014240808000b100400580100c1d1070144640420024082d0080c22002e001c00c22a080c80d05001d250150840b590b103135910191700781040203501c1250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 511554541 1250 511553291 511553293
    0x20c010311040b12040c050604030609110109240302043b090d0e0f21011d211b070f080d09051c0b040f2603150a170708 53
    0x901109101c202209403815030300030040b15400d00c10b04800a0a0400e4050019a000803801000241d0360743e03420020005140700c0c40021403c020f907890f101d41140707500450941131002a8600344003414100d80c2034000000740d04008220f0701c00181d001c1d40240720f0360b00a5249800d5101403015200c001c0040320019102e0704200803071442000080c1c0c41c00314410350322603106802414000d140d035403250900285501004290340e0202000a002070045400108444c00f030981c09031007e80854000c0c032a0f0903a641d4031140321016050040e00140d1104480e991502040511341c1414041254041c00e640651050548005100c060803c2243c0d444071184154182460854030104603540c0100713111420304120307100d41c080b590078801000900700b021500b0458400c038501204002c40d401040e1702d0300650080d0030460380c1c201305080443e2001c000c1c0916080c3c41044005184080705003804807507018880c442c440c0409840440014010700c60b56000007220b01601641010340000819800c0481e100d0074 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 511555791 1250 511554541 511554551
    0x1a0423160206010e070f0815031b1e06030109050406090f030c1b0b03070c110d0c18020406120c090302303909190b0414071d10020c0103 60
    0x60005113a5034000c64901700050044c050340d1072202d000e40c0b00300d90881e8a1100210480075030304046494007041c03c04040346910a03401e1071469041440c00c4403e038107410700e010041c9880400205096200c10300c02c068080c0c1d6150005000d103e03055112001d22a417200303400b0614141e81c140240816944141500d010714588110010551400601340881b100741040c1d5056a0342c4910a5070350001101e000c0d54405011041e40c0a20350b00d000d89084141d203d6441118104d08200192035000006004050200d104000a0203040c4d0401e0924100502c1e4120100f11140140c1088941840591000b50001c4030702c0904071104421039401d0f4807188680c0801c0314820384207480155075040c0d02c500c0b0801c0440e01c0c0c0b8000b2000079a509801c2c0707000da0340f101c03004080c8442700c08204290000c40d410102000351500c5110080614010038500c048110b400f403140b40f40e440e0f40301914441c0942a1004d1086a2030304101c0002c40d61355038001180010034070868407030541d001948554405c03101e940000e06d48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 511557041 1250 511555791 511555799
    0x50307020f030403120f02100f02070312020a0221090d030804061a010905010c08160f05101a040f0f05041424070e0307120f12031a042316020601 64
    0x559040301c1c0c1008200d01003600a00b011b0310705411095000381180109040020819101e0003400e0f1050380003003006a80d40c10301d080003841c01d2031030003054511900401440280315400505d030542880c036041c00c608040464035030003c15210340e0650f140c01c804080030700c10606400181440c4075600548060000000c95009010b964102407100d40c08150924001c0c05154403030580702c8400c9105543d85c5144c10440c0d100c0e0380503c501e04804558040200c0d600c1c0e420407805100741c040c81109800d0034481071683c0b00000d12603044100c5c90f54050360ba00c502100d4412903030340000100400c07110080015003800d05156841d190f030028540320b217204051b060b05400b140841404e00c903040e0f60b6221002c03900c40c084200c66407048036152079810301c15001c01080308200300840c1710400707100381c4440f05a501145805200c14886084000501d0714014141951070100d1515440d000300842d8001884082da00c001480c070585045400500d4800030200208108009444000c1152980894070f2507a13031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 511558291 1250 511557041 511557043
    0x8010e010803190e03010221061503150f0a121a060f03030d02280908012901030f0f0216060f020a02032b0203090c090903160b06130c050307020f 64
    0x1800c4102c4080312406646074800364070a4131041d040c0c0000070005460100c030f074603066080d01082c00101043c0100303c0140515860200d100c0c0800c01e0042c170b5042c0c1540b5254511254103805107203402d0040803c00a003003460349da243c5020000d80f82210700e407005807502d811720140030300d42d81d01423140c40307038084004c58068503141490310041c140040082d40b805e41c001049801075081340d03402d8501c915828242d2710362002c0007000242d46c1d00180c0e5404000703a10b0500c0e80f80c01d44002280005115400b0880850f909008420070128001c0c20b0901142d4401c0b40d144131001401071010305a1040d201040d00f00c0c0b12220800c00f031490a014000502c10260900602e0040b03206400b04103015034000c01542080e103254815040c5002c403e020002c0074510b1340c1880e2400d9a108613007503141d94021000d109814941803640e240c1002165000310704104255803e8205003081e444050150302d081300004d400d031354981442c0385c100072200106021005881e100603000b50426038040025015411109100000c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 511559541 1250 511558291 511558297
    0x210f150b0f0702060f0f0703050d05010e1e091005010801020a030e0115030f03090506030a060312090803040b0f0702100801051e0303070b041109150a0801060f05010e030f060708010e010803 83
    0x140c110301c1185409a10303401c001c5070b030380b00610407034170a00c044c01541350400c540c2d006841c1980c06500c0e0180e4a03403240f2212000c4410503046441d0140d030710824008118010003000b81c0c5c40501c003542000360340b5802c5000349004e4501d1860031055003000004075914a041d0003070b01e12115a40c8050003030114590302d040c245c820410b03102240076610001003001c5120b0007246c094040c02030034403940241d105c5020a20b294011269020f80c151914001c1042168018414080c507443d450701c052900d0503c480d4540304e100e01e1242002c0d904002c0b5500c485069020100c84455038003c0c5010384211300310350080c00c40c80342413065034800c0d44204074240c040d90f03035502c015107071500083c091880d042660761703020b80340040078009540c1c03001c84060307907601c546410021502901210a0a4911b60340f05000c005025400750003150280c0d051081c1002013011885d0a141594401d00b440080001003201091070310703011190155251081000707100c000c5401c0030419060342c0841401b041960b8803881c6441e640d03c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 511560791 1250 511559541 511559557
    0x2190909141603021b0604030305011a0313020f010207050619020d0804050c0108041118090105070f0818160b0d0c03020a0e041104120b06030c03070e0403210f150b 72
    0x203440d00c0599030b4062090380104050101d0200c5a0810400c1140c401d1604d0811101100881d40c1c5100600c00c42c0c045440100d161100c1005242c81d40c035010141523203103140b0100003400f61034140c5480306980e0084c40420081d00d40502420b031103241d140c0c0c0d4003130b051030300f804200003500411403144502031141e0300c4503101d550008010540c0c3c0888000445844c01c1c001e1080c0d41c240882c003a00050780d9142c01c206250443c41c904440041c0c01c151412500f1154080c01c5401800642e0041c0380259410500d00d0354044600c5090b00c1c0d404040e900303c02e0410f41c400c503620b110400d6610300030516503a500b02502a89030025010400e0010803c400d030103d106008a001c040f071100b14081296182035040944120042000c042c2403e076104111161030400000c01c4840a107154108032007403c042019207001e04045000301074891510011446d800700103080030702040741000c045000b080001d02c84c0202807942075810000111014012001400d103003483c1d074000304607900005141d101c0d0006640d211 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 511562041 1250 511560791 511560811
    0xa030801030807080f0d09050114071b020f0d031206080304050904060b03010603060c02030408010f0b060a0818061501120c0801091805150f0109020a020c060309010219090914 77
    0xa41d0864407111401c1d044088102c410710420090341c2d00f104201400390a10501c414408a404529450f01ca800d4030f20011080480407042c0d000c020090f0b0780180c0161005040c00c2c00d07042100300034004180042c0380030140e5078214608039552401c141d401500005580d004041c200b00c0d00e40c95109035034403885140300e040e5200050101240100d151503002d08090b03003009000040141d604e035249401e4604c1c103800031003d0303000800d00b000032500170300500d02440324404041090700230040c002112402288800c07003c001000e40018140c10203043e0400d900c000c0c0a00720340e83c6141203081c103659000b031207042c14001141860801011443c501034124980c0c2c0c0c545030307561a603003440050f00040c802690300c00b10440040c0321807408664140284402107202e10084452803134a0056001e80e80c0701a070003003006610401401d06001c2c0d0215040c0040070046614540d00d490b80e148070750180c06201560180c0c0001c155180444a41001c1d400c0c0c21201798010a02074403080c1a855550301000301d07026515 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 511563291 1250 511562041 511562057
    0x423071707110c0f01110a0305130e10060302070305210711010e0d21050108030d0b0d0f0b040c03060e010501080f01020717070f08130f1505070212030f070f0209090a03 74
    0x684e03c0c0c68400200010018940360340b089045894203483c0528010003680480c8000520440303161403d1b0290020303080e0041c0505090504000400500380036204100403d5070105009080520070800c440142c20000400789032442211140c1800003401e60350342c004203010107001c0c4a86103040c01094144419600a04100146540243c50001c100402c40c054560380302d0b11103030305490034402c80d400381007a14000c6440340c3c0500f104804846d090f101c8180715008031144000010146071801e502240c2c401c40c00c46031a111850600312808041c0c1004103501d00302107000d1a00c6405501950490f00343e20121030404698211050803882844d0003d0f150300b4508130003602070004600180401d61041d00b45d08050700300c0b600c400045030040e04411000e2501440304000109051040c54003038540300c4200c0090031056040502184503800300280102040c441440c0f5030030051094070302859051001d90354034407151070240410002c444080348100c05000118544100015240c4841c0c1d5054441000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 511564541 1250 511563291 511563313
    0x14040915090c05060d09110f090103030516060204080102130918030e060708040806191103070c051e011410030f0318120f230c042307170711 62
    0x34003944041525902402c180010381e9071103000040c0181c8008400c00030700352800d0303d484100702045482107031140e60900e05407100355a60305805070450740e0608103107030744601c0c807058a08a0010200003030182032001c600040d0215042d00117040400304040c20154850b1158103d4040320b100100c4c0c1c0c0c9030280e0b580051f0000034020120015910340013464903042c00626542c80c070b0076a00035001100f041d000101072210b604c07000c01d0303004000507a01c0f01c240401035007508228030034040200402c0070001185084010f2107000c1c854220300514108001c0e02000000d0007080c042c3c1060b003007281118041200040301a1041c440c00d4040d03d81c058413040071666991402c54031806106880c1120402007040002e080070407400c000344040c0b14800302e20081f0302600300442040382c00e1028078804035280e1034910404001240300400701c80c1c102c900041340120f44a05100c11a40756582a01c07500300c0d0818851003e80100032a5288404a80d80c3c0d50290717600b50742128204034510b40c1d074030154001c5031120 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 511565791 1250 511564541 511564583
    0x9030a03090f021f09060203030606090418050d0504080d0e0d020108040305121509221401020c0f0c31092103050a0e0c010215100b030a0204140409 65
    0x1c094900816281031034040076000aa060306041c1c1d094502007490070942004030f900b24181100600701070001d1411403820b0303004904284962030b81c0380d2187d41d882d10a07040c60103540344403661031a0081c085500c1e4030500c400280880c2d0240c002da81e000c1c03242d4007000107524810300b0100114440909010184c215560040d17510480140c801c8007800828020030304d5801e5030790b41051007059852848090100c10505100201502904600c23804a044030340010791030119588800080c0c4c0a985080350700c49900b00b0500a0050041c00c0381d090003006100c8100c004001940a484001103070241484098840000584c0412952080c40620351924200e42c0344e5490341705240031401a0701d010714074030200c44240340c001da40020413030120703603180113101c0d6150b00da10860203410f151400800080d040240041d41e01e1005507414840c1511101c006840420381201000003041d030b0301c003601e40f6410800c1803000a50814001c080540c090320340d4407990f900d010b0290000c4150440a00c2800d0780d81c0c03d00d40c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 511567041 1250 511565791 511565801
    0x709020307051905030103030f030e03070b1b0a0e03060f010602123f090115030f0f0b041514060d120c020306070e0f0a0806061201090f0f060c0809030a03 68
    0x1400602c10240402c1c440303240142c201c2d0060501c90341c0c54070f590b91b0641c03030090b1001091400300b20401d4a0b00002403214800003085807a866042124017480740d5a00326504411184040c044514040105e440000640c00044101801238224152a000d50340c41649002880b02441000c00503440104500c42d010400701c0100b0740c202d1090f000d40c14140c1c00c2d008210078070044e041811001d51000174408551900c40c0c00c641d0b0000b02c940002d0004c1c030320103400f40c0361055080c000589920101540e44040140c045600c0c00b040341d201030512601c1c0341c2820001c0000160358410a1a40d05094001019004280c90710f4840d90b0000c1c0728801400c2c130f903119031419244071070181081c0403081440002582d0200606846003925a0360084030079120001d00070390303002110841d40100486030701404030310400f00f00c0c08e80c82803056400d2604d20b03040003191405001084030180c1500f4200c0840d009026280b11400c5009000d40c8051103880d0044008641c5440c048985510301c1c0c0091210601092283c2c02c2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 511568291 1250 511567041 511567051
    0x110d0804150509031f050a1b0e0f031504030f090503070e06011101050903130806040807020441090604110405190e010f050c0a1d060f13061107030507090203 69
    0x11450a0010f0350340460b261130001110b11526815045001c410390301280540b51b444040365005002c0a4507400e00b42581300309003940301003409940400c01145444002549401070300080c00c0b6511260700f00b0301704071141c10aa4041e40002c2000040c805583d020340c5442d0101c2d0340c003600900c4124940904400300303150190400341004001400481d05402c24007580b4000d285d000040c6641c0c00b20035002c640c9a1142e90b0110019800c10000c000101d201c07402640c02d40703a0140c40c089036040c0361290a0a6030a000040301c0758440d01008074005400840701e40300f5501801a181c1016034582d038035442d0356107078103d40003450b00600b030001403510b040c550021030304010112a03254400c2c003025440003d480b08041480181da560703040c4a080705042d40101500107118411180c81c081540100500840030b031080c5000203101a075850700c50340c9540080300c0c1c41e031242c00b50305500e494040e50041240400b40c4038100015106a810005411011942a040329070040003001c1140c44d00c00054042d41008207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 511569541 1250 511568291 511568297
    0x30c111203070e03150f0a2f120c04060909020403231e060901050114030703061a150903010e010b10110f0706020d03060b0306060a0c1b12110d080415 66
    0x203c051140d1410002c1c02055628062503516900d0100b0804007106402042d8041590505d9061048038001100317603980b0100b100488035400c00f01c0c8a2401c3d42c0d2007001c4006000500e0341c0200071250701001c01400c25500c4036550408802d5445074131009a01490001804a071484005031016940688040c22000c8100050311481440c0c40c04070100b50f1641000b6079542e80181c0704100d83c0200c2880350601520154160f1518038050001103540c8404500004020b5540c99a40380039110340004440300e0300100034824800c050355220801036903080400349500a40c00c0100440d03031000180103001038094043c02040e00c0040c642d00880303e0b6040803210324640d000e00080402003800610200000e4101a0020b003030b040c1c51220000c0840c2c05560041c0304007002807040c400d0668540049a4201c1002d02d0100844000c504100e100700354075610841d40886a0000028a400100114810140605066811100304000380290070981100042082d0410030003800020070310b50b140c40700781c500c2d45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 511570791 1250 511569541 511569557
    0xf07020406090e0a1b03050c011101020f030a06050117090c0112020d090b0919021302030a0b210d08061c17270f150a0c020414010501030c11120307 65
    0x680c0d80412500503c100140c030340c01050143d001c2c80503408080d44078a400281c03840400740355444541e15444840b111904200c2c0500207060710040c04d4040e5260200f840294a90324100508010010601c3d0300c18140481c07804a1041c0c072074408030400c07070f120702e0300c13200a003080e0301803480110307006502160f0a01e0980c0d400c0c025640c1c0000248120503c042c482c2c072003241182040c5803581d2800c48070102c034200301b0491045000c016151402c090281443c10030000d6100c0c0c07519010300300035101c920101604009151040a5510000581c0903244460031040d2480303100550030407284c00320111904c40d04829041000318403500d0040c400614103016540340031a10849041e13050440c1d103e181c80c00000343e008144000110303503401001c41004412240e40d42c181e54a00045048807100d10b118069000340030500c080b1481c0540000354540754010001c00681d42c040c803071040c07405020f0058030300103440c100710603860314080c032000d00c4240050001820400c281d480111a603910090600342000028 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 511572041 1250 511570791 511570799
    0x70513061227031b0c06030b0616030e011103130b0d020f03010603021801090602060a0f1e1a0409020a030b071209080a0e092a071202060f07030902060f07020406 71
    0x101e07210070724140b075504000c146000c142c2001001c08180c0c801603208030034031125040c00500f503804503104461160030082816400d078000129a070060920b03560501c0e250744400400c05034054042c0701c40341350988900c00c0b0944039881d220780d0fa00a040e80b4801b0240d440d0360502250300c09902901c0e100400f0100585010a05081c10744075400a07030115002c85c1c1c000c42d42004119040128068105080c6440140d4610340a0001d45d1904040d165070a4696556040d0814219542021169081100507442102001e1480c60000e0aa0310820100302e141c1c010030300b5451915001c1c41190a40003020304812074110b0310790351000c05015142c902404000504035250000b03e004214072039020303821060701c490040d040940054481d66045d44a0102d000421004d210b004c0320241c180c0d00002414000d007000c9007022082c6100301c14028054901c600c40d44406c840e40002c109100300c0c2d80708a40030064071103800c20b50070b5544030b110080d40610148004be01c6240d08201400b00c442c002000032840316a5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 511573291 1250 511572041 511572071
    0x120f02031c14090a090e1b010806010509191a0a0210091a0703061e030b0601020a200105040e0a0c1b0b1602100903121103040203060f0601120e010903080705130612 72
    0x4181b081800e00d0b0410b10050780c8400148a1510000030207080540705031820000007031280c82101d1800e0b21480e8100c00c0f0070700c0591103038503503009403e455101060700da055100e450980c1c0c005444450041c85044803410b050174540c003401440070f0784452201c014070071400e04070740f040d800100840201176070348100260744c0902a500c0441c82d0b000044203690b81d411070a0005541078001d101314103540c8030b02c02c02d0000451040320351240f0358506000c07818201000e401210603116560001400c04e9400c0c0600c1a850030903880028803c0540d00c40e5220b08010032907040011440140107842d48055000041c65815204000c80da0b255243c0305030384202d0030809500c02103481401c42030b4000780c0261080c0c15420314505c01d0b0a500c1280b011414214901580005d940d4000100a101450450b001161059025403800c0701284040403080c00342e500e040600728020b10348848198000344061380400d404070302490885802c85075000740108030354108a400d83c1c8501d8070344c014103081d80d0ba03003200c01e8000381 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 511574541 1250 511573291 511573301
    0x1e040e1606050306100513052403010311210307060f06080f0a030f090f1202030a0822060f02030d0504020102030409090308061003020f030103110a120f02031c14090a09 74
    0x3003142c9a160b01c0741001000e2001c0e10078003a840340107008040045444d440b294140500c100c1d001200d40000c0358810502d900a4480717104a11500120040004010040d4010121842c4c54081d6180101c031203064100001415184a1070004e42e0010001e0314086442604a0160f22601441c00318800340da480c2d02a03d8003000058036a11900000e00d1341c02010340c4680c001c0c880e0761003894040300035410401c02c5008016944100d0040315080b99042d0210344050065611041e00a00c0721521505d01c5003c0341c03140306003070300c00c46910045c00c500800c1c242e001342c2c425014400154001c60134891200c032460000c0c80040c0c42641548804c0c800000d20300094000c5019546c030070b40c1e442d40725051800038004076210a032011002e0500600404440900420580f411a60442403a8912115071008034260f00d445030080c80c0c40e00e02c0071075100c00303100f040d0310203c908600c2941140c140b0450440b040f0701e0038603540010000206d2400d4140340d1900103c1c06044805001001c0303000040c2e9508400341112 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 511575791 1250 511574541 511574549
    0x4030b09010213090b060a120612030207080706050a0504140a0317270d0b07110a0605010303080f0108070b0717070507050a09050c1207030e0124051e040e16 69
    0xa034000980220b580c00e80c40c0043c0c000c2c06554800d1144414060004100d4010718405000308110040c2044050120383c0000001b010382c080386800303030505810000d44902e118004c003503441c407601800107842441042220300c2e00c0b2040c2d449034105400d001d401c0540c2c0b90324064603640119a5000400843c204075103091441c4925030103150745080040500500030120043d040c201c110f4a2481e14054440e101d110401c07540c000a42d102c15a1f80c4d000c142d030440040b024504051050310844410440030717030300082c140c90003034450f0744481e030fa0013100049003002409000d109410048041000c0741d080300244c100c132885840d000c1030740384580b1460f401c0768004d41e9043e101d0b5840802c0c101300300c0c20401141d83c090031054900344500d00c0c01e0715002d2a00d1003807242c002c0d0700c00c41c1040001d04091180c0d100c44404448000248900503400128000d410355849a072075050125003800206450303c52441c8541c905080c00d041c000b44a08030402c0010104030101c0303511406102801c0000c0e40710104490050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 511577041 1250 511575791 511575793
    0x40519060c0807031125270b1503011e0504020a021c0203040b070b04030e15031501090503100f0513020306040609080909070f031406010c02090601140d02220f0b0f04030b09 76
    0x3840382c1350001d8080500030f03846101c10300d050307c125100c40403100801000000701e1483c0800c0546d032010201d0119845480c020341c11000100000c01c030081c0101100a01001c01050840d500c1c0d11801000100e00c500071010001d64451036400007041c074003100300c1008051030b00550b070030140d84480300001c60317000041c2181c2c0d5400c00fa04003c1056009500c500010030180d40030701130851541c6041480b403001403c004680500107150840d1680b10304890300c06842c018042d85d8a48403c400454003a00ba0900000940c50034100010503a04a00307041e041c107160000d0003055552039945078040100000142502c10310b5041103940d50b6070300c410102c0c134015040c90340d034504c40d030f00d000c03d000702241c00a024200d14070050400f031080036a4842c400c0c40203da0101c1c0c440c0c0c103603154000107a0f10590052480c0240c004081183c03d00120a41d0181c48021103032022039154603840c500c88102d49219000301c0021542840c4180200415803000d0170440100300076061410f902c0b61503010351240112460805 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 511578291 1250 511577041 511577083
    0x70c14012c031c110412050d080601051603030e12120106020c0a03080409021c060801060f090c050a08040c05090a05150406030510020a02071703040519060c08070311 73
    0x40e1440d000701d000102404040c42c2800c040406640c1e041c80d80d6405501c0701a283d03035511000f56240021103000b0702000c1102100c0303034030500d0f1103078a840032000558046144500040c05a50149013140c5580c12502d1507403840d20310381c0d41e0541c001c000401c10036480340311f1564a004210300c2c807070041880d0030b00c12032022503661414600a2600b501603451501803098a5000c100041081059a06850107030501584407401c0c01381281d03200b04030444641d59076080941c009030540041d170201e0150381750f100d9504881c3d0741f03920b90742054810800d40280003030001c0061892041c03050160542040c868240e50448680d118001000d0200588200600ca031b61813080c0301148420301540d00494a040e40e00f80002c0d4559280d1680300d0922030521b42c1e246400044d134940d154801d01c2184080d00008514103040068200d07241c0d03076504140605070003006003c25040741606140711500c1280c8541d600c0c0390202102d035855078013540220004801740010228405c440c00801e000d07603212600500c0d01c1d120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 511579541 1250 511578291 511578341
    0xa1d03070c080610030c0306050402030a170d2a0e01140c010b1002210a0504050a03060b1c0c06142503020d1b020d111003050603060f0f070c1401 64
    0x801c08030041e2540041440c01c3c1400c0000406d07400c41c9404407038000d00001020f603514004a41085100308000340134030044159500000c0310a00901401b80403020304101d450300d0540c80c6060075a5141602e81540450701d00d064000b485140188541c10041c50002032038051039406002a400c2458140c58a035100d00c5e00d01004d0404205900300c86500e44020701841640d610490110050a00108054480040e4000c40c0d24081e10441e001041c3c041c1080c410569617040c140000d090052815114010200d8039841034510b520a1503489034005551040413407400e00c045d910070b0200b5107089202e207000e0110460040014442c0103200070510003a251200141c42c0003402d000030010b001c0140240c15221203030307038000c001000078003c3d4165440081010b42d03041400260300201e5100e81c0c4140c0341d0500100b040da054002c00e0084109030101c07140f135107030040c1d95403003600c00b2140501e400f114140010030b004d124994060065005050700311446a142540c5030a4601004100d0052002c40803100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 511580791 1250 511579541 511579543
    0x605040f150201020c0a03051e0f030708060a0f06030b0a0b030903040909060f02030906102c130203191707030f0e121b12030f03190e01050a0509010c080705030a1d03070c08 76
    0x9089c1d0540c401c3c0d8604030030b0304401e0244e03000180552041068103000130380705071a4444070101402d000915a0a01580e400008000d85180e05d90103001c0d08482000281500140341a6402540d200007d141014102040c8000400c403051084d151036483d00d1030903c041856200031402215488061b00051074a1503d54140d030301d0580c0145c041600220240c1c03c0104d004140407105082c8140e20011604d41c2c40c01004901c06122010750b150140c00281c10744084208500704046100f140c001c401b0410b00c1c04110003901915801401003150f003491048464450641d031071500800510301ca0f4071807001301d4460b1030904040000304000c40d00041c140b40928144c0103490343e00c503080e0011490f084404001c255030340400340c1003203c035401c200009a50356800d80c000480318800f9100801003490112446009840180c0707089000354603041881103c0e0744107110b070512400f0740340c484611b1511400e2110300101464044040c640d258054080b4a143d0203000400d100d82c0940301074a505c90401a81c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 511582041 1250 511580791 511580827
    0x1202010b090705030a0c050702030709021207020a03050915070b0106020105150909250b030a020304120e0901051c05070312080108072420070e010605040f150201020c0a0305 76
    0x310344540100c4080010340c0d80d119044aa00029007100420b2100c0d08040586142c060090029450b0140c11008180401554090415254050800c9089444404059889505404002d8001ba00401140030141099800c08158806088400740340510545a2144a000030b03001280107075168418051b0200c1d403408600c07080e00088901202d036041404819a4440a40c3c4003810310780710450b0f442d0a100920180080108001d43e10251f5901e4503c401c40000d50048030200e800031005050a110740e48100385017840c14501901420f0180d083c0740801402c039039110504459010100d05850000d02d00703120040041d03128800e1041d0058070782d1005450141c05800c407001552050404100c00c00726842c543d0f01032013140d20f4988104550040460f445101c0d0412a05010078080d40b000c00b980001489a040310f22220040074666294281102d00c1d119601c180c106038020410140011100c0c0120084e4500090000500e0292400c4036a07050407408242940440c2c0d021601c202006c8031000b031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 511583291 1250 511582041 511582061
    0x10e0106050f030a020904020d0206070308100b040308090d050f070605120f09030a050a0c12020a050601060f050d0209040b090c0301030b010609120b0405012c1c090512100603120201 80
    0x242c004200121004a503403403021a8020303102c0d841910204080d5110b0700e01c2e42000b1071f00079101d02c0c0d0700c0249040140a0400503a410005840300b02000074050303915505640681c4c0e84460860f291090f20350070030804508110f401d0314030380200464036102c00f10811036000201095150181c0714a03004055100c226001809000c43c1c0a0490800c041c003500070007122640b151900740140c9448640000701c6290a0b00c0c0001047c0d441c1a601c4c60703400b15000501091414415030842c0d40c2070780c8905049641541da0220790011031000d0014005c0c0280d182c0142c41c1c030b41800381001500c4414200000c1c07d951003600c00100ca0700000005000b030080091026014245508000d008280f61403541c60340c007500b840001d8002501e00c408282042420f401c4440711441031000044081d001c080c0300a6544280b06100032203105080400703c441c0170400c000c8400400580301c40b01c02d40c0ca88000e114004101b10707000b4010b80601030103000240342510840010714002c10b01400400ea030340101a00f11644041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 511584541 1250 511583291 511583299
    0xb030606060f04031b05040606030b130b091302040908040b130602010501030305030a091b0e190603020f0d1a04030c03090603021c020f0d0504060c0e100518060417010e010605 77
    0x2010a03445041011901285e41c4180401c0070540d40c4402e0417101c0aa40c3c000390390281c100400007400c13075030542080c6800003044a034803212403d001600c078100c900c2c105440da00a49040c00190082c00443d8120294600160010407610400c2e503c00b01160f0040d048a54114401300e10790400c00c03003880220000c5c00c2c1d0b60000704601e5045807005041400014504000c8940322a00e000c1000303500e011201c84201ea8a01101310b141c0c8514032079401000489202c200c4824585000070340042038001c401c11039030082c001101840c01e640130b201400300b20783c40640c0e070b400c0c00324000d9400088100205100b42d000f9940c480781c1e640c0b00e01e03001385003881d150720500c101801480000c01c006200340000801c1d691140340140e40d040c005503144698010724003e000c00519010070003081c0b101c00d030440c2013041e11301da5070002d420010307108020040003540390300700001d602448441401c011090100036004402480c960411742da030300c0340b0a04c00018100c1030f071107079454100d03566418400740946070103000225 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 511585791 1250 511584541 511584547
    0xc2d03040303021b010e09040b1b130905071b03020c0102070608010e0612190b090f061905100308042d080a15022808070305040c120c090c030b03060606 67
    0x500c0013907646100c00184012000c015603c801c050b070003081481c1e05d10720301421844080c41c080c2400324036040f0440d00e00e81011071000304515078083c03d800b1106885816089822128100b0310700704028100182408240203c1240d0444421424440080140d100383c0c000c20b03190414000081c00c11801350310640502804c40c1c0148800180500d034694070070002d4941d00c2041c0760840180b480c103401282c1014160310030b41c50b46414001c1c0105d081c1d21130715400c01143c110500b80040c075a900e000441c0e0300d00d45c0e07051300d840014800394a6045250002d2505400340c2c00d198880e2142034060740680e1160300c003000d03401102104140314882c0aa400054044840340355840e140c0c4003071716012602c00c01816070070510040303201d600641d410b030344158138500202d070961070000300312140003203c1c968414040351030040010f030914801d028080c81a0341c00000d81c06400d181821581e42a42e84d9941200c0f407a40e80c0e880461170131400e00c0348a92036221607070701003001401d900c00d050422001070480b03070040c4820 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 511587041 1250 511585791 511585793
    0x230d14070f0813021212040602010f1a21010608060703090209061e0d03021e01060e160507170705150a06060c0203030415050d020d0902010e06071104020c030c2d030403 74
    0x101240781c446078050382c200010b10090031760541000000c120251ba078880100d0081000e41d0305601424415410403400c001d1020f40700741c0105503062500100340c2c0001c50f40c045071a6840348604030883d0301c810000100303016485c2c00710941012400c0b10f56400081d5180114025868089803245d0042c50507034455045840b050303004d0b001080c581c1021401061480c0c501800c05108001410740c0d10720204405154022044105001c0d04030b0340b1503034204000031070105030602f03289007130840da01d40c003a15854030b84281551541402030140180c6080c140c0240652004100240f00d0742c0480700c0d03820700003151454a580480b04449480d0003050400440038260001602d0001c1214141c1c1c2c0d402e800321070700c0101000300319110300c80d43d10301070781444c008034041d41d928400380c101e9101d0328400d0721348101c000100303000c1c03040ba0300400c040038051035010815110503040642c02400380000b0302c001d482c9018009001c0925228548280130889044180f00303544601d815460003010908242c0035610301869 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 511588291 1250 511587041 511587061
    0x9011704020a0b03070908070f080607050a0518060412150c030b0102060f060d0507080a051005070c0219090e07031e1a19061401020d020c01230d14070f08 68
    0x181c0182c5043c6507001011445c138502400c0140d008154003001c88902365103440308103c0d001c14a1240c050148201c00108031381c580075400740d490b00d0b00a680c0d0517040c50200e0942c01c0050030100e09060700024200000703d040050b00c54101c440038059a400d98040d003078070a181c801c6400a405613010103203030542050181e070340811000c0c0c21402441c0c1450032503c600e030000700c03050020389000380a489820780000700d090000c00d400d4a02800395080d524017800e2000021b0503a6021034000c400a42d4004401c001841d01200030346030f40d401c42d801c01c0303000ea40301c410702070880b900c3d042100d00d540c0c4480000c20401091402e0040303921004c0340d00c2c00c000c02590707807000810700f1006046a410407109d0000b40c080490354424110480614800b4040c20b5960111260401d041050490042c00f0f0b401407504070342d00000754071400e100b0603528010311007130a05400102660905014680940070010000341c0e01c010701888884d902407622540703541c24034400240440c1781d184000c0e428440420104075003592 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 511589541 1250 511588291 511588309
    0x203011505030912270a1203050d1407020c04150b0915210703140906010902090a051905031902090c1c05010e070905040e1002090114030108030901170402 68
    0x4150030856100d40720801071608200e0001305003480000c1c00b04c0d00000d5500300c03403040151401245800304110041500b80102ca0301140501d0b500e03412605255000a1702c18401001654081d20001400c100000e01500083c402070b40e411005a01c0600200101d00d0305c0d2090380c5090000401d20902c45250080035140380c054000011b101c0c1c015a0000c103041e07004981294503148007000c00160003000411049a01c04045c2c070050b0010f45425030301624026880303000350140d0401d600034600c981c070b80602c41c00a5403101e4801508601c0c0c8800000340c546698952241100120010280290400b400c0c10319200f804245001c207101400b18050141c1c460f0f000e401d400c0b610901c0215511040303075001d405540d9007020181029032508000180d4044d50f5083c09009070425510315540c0750f510b0f07003000300742c4801c60f80040203900000d03943d440707584c44d81c1d000307009002e018117000c08046c414a460007810b80099101d540c00c2c4e00001a450a0b40d81d00c101c1c60795403414620041f1595081903000305030051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 511590791 1250 511589541 511589579
    0x907090602010e07360501090501180b010e0f0109050a0e070806101706041d01051803070525030804090c02010f0606021005061c0f0b2212051306030504020f04020301 73
    0x208405c4032860031020461031308020090325000074440c03541c0d078040d9400188424820001324006500d0940c0d240001d500440c0f1800105940742444100c030f16040290640300307240c4031030500c0110703640007035141c840d01200130041082009007907013807a103282c0150034400c0062046100d42c8454042d1440941c01110715a01c1862480368001039645200115004207100b001d882c100301d21841d0007801c0039030150072040c45444d218100107a0801e090704107607924000c50000814035088200320388061800c1c1070242240006810a0340f03101c9580392030700d410b113074003d402003c2c4441c3c4900c0940c400613024000c5188040070703180e0401c026860171200948494240b89800b4150361104040780440e603551410301080c680c02c0411851030801c91400b031420a0381d070740c0100c4030220307424001881103031071502104142c1c862610580c2c2000c417940d82e10112001c2d011091050140501141c0c04100346294030b500034010b10345000615082c54010018442008541035100780d00420051203000810101c0e80440 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 511592041 1250 511590791 511590839
    0x150c02070b0d140127061a0906041208130f1214010603050106060306081b0f0904052a030c0307080c0f01050d05070807110303040308070f0c020907090602010e07 71
    0x103440192102010b0100f0700b9680c50070710494400869920520651031100c2c0d540b508481e24004601d03180401a00d040d803052944544080b6a525802041d0030000c0c10310300c0c00200210f1400380c545907450030403010300500351050640810b029400d08104043c9401401200058000e0f1600c2d0121a1221004620b0f0040c1a02c2e240c2d00c0f00c0200c520300350400e401a6620900034001c058079a0340080c01003240e03114448541c8210701ea50207400b40c02da0b21159414101600e0080c80140c3c203401e1024a040180088a007407040b5582d25801d81d185504001314040f50301d407108a10040d520415103070198005160b482900100710421040b1400641d1101080041d5070b003010b01c5001e100181c40c10b02036060320030711490411080010103540701c4a007508c5204103441c0d41a00340300c501e809035681d000c00c543c0200425074032004a0207040c0100480e540c0c51500b03140c5140000c42c2580444c001503000c2e506140811088042440103640a006002c603c5805400800300186014441c4c1e40300303c9013a00342800 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 511593291 1250 511592041 511592047
    0xc0304020d0501141612020c100902060f070809090606091305070e0a0f0503071208121902120105030f03070c0302102f0d08090a0201120b0a12150c02070b 68
    0x7044029002a1a000340003007052001e4030b0301c1741448800201e41003600d80090503114541c00d08010510135203c0d04e4208000410b0000240c40c041e0300103100c6403100703a030b1065007481104018103001d00201105807080307404a4903107400c60180640d5601c044c122610890341403080c14100d89500b030446a100561603004145078031080415540e40402c1c4049a030400000c00c008120030704518000d004640040e03007124a142d40d501402c80b0741c42c40340303c80140300d2001040307418005240c0305007503500050070001004a86100e0038850703040340e0100003070f07094940c4040d004101ca0b140a21508400031f4882002d5440d1008540d500d008480ca41c1c0002881010b4180c0c0c03451815100320000f01c14442401004c80c0810b05039041035039407200310045a0000d1084021494040748611415801451003800502104c0f01c546d0040d51045142d0111030800b654902d0310348801c0d610304a0b040002c0c40c1c8850200c0880070035040ca08202c039110f51800400c10b05003608040501c0e130000310401150000c0c0720f00c5031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 511594541 1250 511593291 511593293
    0xb15070c092d061a030105030c06040303081b09120a0c09020c0d030e03120906010e0606180d14010203190b06070209010e0a06090c270b0d020912100501050a0e0c0304020d 75
    0x401040f454120481d62190400b03e01c16002861004505817a0110200e6031010600c03002c10060344514040100000e03651000308401ca080b0740b40c1181c840f00801d6106060900c804082003c00c0d0610b8180c0d561648420340c0c141c14040f0401e080d5000e00130041e8254900070754104056990f0300100304000425949071449a6003280a0007a1000904100c40241007410300180650780c545081c05079806500002020840c6413800004481302c150b0855a018a2490410300b000721070081207005482030b00f65034080700e0341294284010751043c10441ca9030391020300c180400318119070a1008140c05804104600400359542c1d0790441e04603801d44940508966454101030050300c803a074801c0858504102856000b0740e0000d030400d072140c80c0302c5100d11200c83d00c040d003c0c50405c854810440021007c01240903040354903002400c003a20050b0100701c401c141e0541c0c05207803015002c1c58a0107641d541005000a06d004180326005150300b2a40000c68140103105805c07910029100a10558103884a44 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 511595791 1250 511594541 511594631
    0x506041e0504050c07050d050a0e040b0123041707080c0d081209010605040b011b030e030a0b09030310080a080405061b0a031e11030301050607060b15070c09 69
    0x1a0160001410030f0105040010300500e03550081c01045581c1c1c0106104490014400c00a542900d007080d600c00104090002c1880018043c842210741003224612507814070340440c2100d01418008545215525450144000c001c10320003461405150080c400c1049078020004015031840c004540d1a00f20b9940d80c0f40408061080340c03e400540c284407810080c40074019406031080f07907400c0d141849040411401126500f0b0b2404a00000400780a845404680f141507a07803011580a41200d5000721280c4031071007015004c440010302e942c000070400801c0364010300c141b0000d00413400144810001a5131300c102c180201e0207058003450000c02e070f141217007002c020310400041d8101c00b902d41c403154904008015035040281d0031201c0802403804200e81e88100118444050500c01a604590801082040c0c2c4c2d407111500740e81c0740b912041404840e81e152003a41112a8080b03088030340e00c48040c501400f801c440340d401707282c030503150019002c0c006a1843e0002d03040b900c90600c075010340400c08518 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 511597041 1250 511595791 511595849
    0x8220503210c1f06140904050d03052224020a02031b0309090103030203090f0604151202121303020105010e060603040f2103061a04140d051504060204090510050604 72
    0x105101d0211110342003c03030095000c1026a0203100403a04000b5020080c003c10031029100103000e680550740c0f90900d14800e03804107400c03500e4404515280881c01e2940300c51903100f08402e0721a49005010601c4111204003200130110040c40d0a42c240221001c02070340364002c901d800882d403212400d4201280b201030084441c10039004000b45c83c02c0d612820001d51b0303500034800b091b000300e00c0070a42c0502803070400c0958084522005488060314540801103c5009624002c020440d03000c3c0301c80040000c94803440b606c40c6002d051008150400e90030001e00307490041e071054039000503000500040361200d034103c0354425040072004a40003c1481c203041965440300d94103010124003040001e500d41c0c1508850100c400401c24485414281e00010040344954801d0b001019110703c02000c031800e01e401206480c5004009842c1458100c1c0c0d80a001210111401c4480d90303400601030241e02500d104044c1c211511303c091004850600e00800c016100302c0c050500600e100204601810b4040508 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 511598291 1250 511597041 511597063
    0x10504030e090c070c091a0d0203032b05040311150603060622050108010609110c030417030d0212070f03180b0a06051e0f010503040b1302060708220503210c 69
    0x74085d0f400d545000060003040200106000052807241c042c0c5d041c50410201c80e0020740080141d4600784d08481e01100c0070030300c0b0504441d1010905d42c7d68010742c00c90301c00c1901c41e90191306c9420f000101c0200c200c0c05c141412801685030403603442840b802d030f200014000d520880507507074045404e8000100504680c1201c1100c0140e905100c00403841c0c03030042d080a4101c802d10345092103003905a20410b50140191400b0f02d4495105000820035a40c245170501344490390b030800d8030700c1e00484200040030307a8010110580c10f4400a0300b4030400700d5000d8418041c044281c50100500c8114081c61051040f40044c060f01c0d4503405000f2500807203c1d0350084005040052030300c5100313602d000524000c0180000c05070302c079208854203200d4550241040307a10071f60703205000a22555541d900c400010403410401c0e6080003041c0311901c005140000204410f688015038804048600300d0301001048036500401c0c0203402c11501d21024213211070314460300f10051151283c680000b54103440c640303060014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 511599541 1250 511598291 511598303
    0x1606020306010c050f012c190804150e0a0b0c0d11030c0a0f0b0a05090303010603020a0903020607140c1f050c0a0b010605030108010501090903050901050307030902060426010504030e090c07 83
    0x2050704810003055100306001f01c40b0303074a1610078064100301000d009005e06a50310701741e0024200d20740204d00340f05042607200c2c4500c0d985030401e5107548500c0f4444000504200120391203001c1d000913480c251604400406036449114641450320258540350450101891306014004403015100350040c404d580f909148107080300c10204a504000c00707580c00c00354040e25080c4030304011681038020f602407a4030607900b02004506c0e69103401d404600a40c002c00c0c0364410080c41d80f901000694454009290040c000c80d0b040c5006515850700c00d0400e07100d0303014944601c100750b9200251343d05030000d00d40600e40d5818095210b101d030304402d505207100c10030000d105105e842c0000c10719607042800303581a01c0e0418001c00980e030320383c0022030480c0c040101c0139000c20b000b40034110640d8031640086501c920549000705d1001e9680d40400c0c850780140d00201c18510700311041111540c0f5954040244481c038500901480c10719850180416110600c40c501480c080000586180800411104200d034882 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 511600791 1250 511599541 511599553
    0x30b0603070903150b28031b050f0d1e05010e0703031701081204090218030a03020d1403150409050a0f0b0402010306080c0a1707030606080c01080106051606020306010c05 75
    0x804001d02c0c42815010480e0004200c1c80b40001c404898840c220031000064114000ba4a42026507080245040100d00e00406400350102c005039200ca008403d050425803c080440c0c00e080400ca030260700c95400501640d450f42810003c070303890007000100310b811842c0ca0100000300c0c1c14082d014148140340491240f00740d00b000010503070300030017003405054034000700d0f08241d80b1017072415140c1a50048100081c9d41c207010503c09424994020704814580d003200041441205010a007004201e20056015030800300c840c80c0020303001461110481c6442910500d1803910018814043c010384000c070740195075a0240e1000c00ac42080340100168100c0c11000c0c0f40742043c0362200241c441100d04a00003030901d03500050840c0001000318402c2001403c4030641420001d107a601200031046004407032150503000000328480e8070038030029050040180c0b840d400e01c2c40c0058405074060f40010704000041201d1610302122416a00496520072405a0b8a03201e007070048851014045003e01107002c0d070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 511602041 1250 511600791 511600801
    0xa0e09071b11041d03030609060607060c091e060915050c070f0f0510080703051b0705150609040210030207020310020c030a02010b0405101a070f0c18090c1401030b0603 74
    0x1c620102c8800c42164240894021003c007007140c00c20390a002404c030b6000b440441c0741c51419025003039105038060030f6141010300a4135010180c0714800c800b01c000c01c01011f001d00903241d0143d0710b012141c6032020709040306407400c50003c111015511881c401c0080741684903451314403070001c40790101d03040021070303007444d03100c44036810001214495402100f00c0d032100000c46081a10300310088510070746400310f00740d607294401ea001c0d1100600c000308171040f21004030071001041002c0c0c80018003c070010640400721610780140320300c3c080d0281d44145005410400103a07285030010301c03203da880c54003685409040c8042440c1042a043e420790031030011a001c109403c0c004060301601740254020700c03e1408034002d20080321001e68481d03412010701d00007405501120650881025003051066285c1801a02d40303d04691104074126a03261801004000e03040c443e1803101c826440c115810440e0301110381d15400d200301c00384148611403900c69504021607009070700404001d02c015010316520310300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 511603291 1250 511602041 511602053
    0x9070806031501050109170a141b0108070804020108090a020901060e09100e07120b0a06050a1b0c05061303120302070212070b030711010906110301090c03020408121b0a0309050909030a0e09071b 85
    0x44c031002b40e400d000d1880c00b800041d6105049040c003841c0640c5841c03420391680d0b00115080c050083c04000184070b00e4012a005858006809000b0202c40d40d4000803001c4a00030040300e0740000d04045000500304100740100b1078202d07030781508001d082c103090100e4540e920810019050525a00340c0c410327442a8009440380c1c00100502e0722110550b07610009000e003c40c001c1881981c440040c11680a810090146040000081440d032030181060f2420556a98601e215560001140c400090300880e8040c11404c08140f18640d140680c6d002c1c04200c3c4c00c2c140070b50480e02000744050f0070400c2200512040e0310003035001c900044c0d0440c00610100c3d81c0c0288080c40c0f6842032148050071840d08041160705442482901c099580c43e5010300140040600606100e400c07074100c5100d2046100400203183c84200000d017200d520940794851a00e00d403404002e0311b50001006401c16030070410508a1081d8058410344841c030b4100c0b100c403070360f45840030211243e1140c00c15410307140b44030341455014400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 511604541 1250 511603291 511603303
    0xa0e1305101a210604060b01050c01090c05030c120a060b0d02031e0601080d020304030f06060b0d090302010f0b03190c09090b090706020712030509060909070806031501050109170a14 80
    0x94260f500001a4800700c50410b074088441495112582190300401c2c00100e140d0080c01c0c0f00c13074052404c1e6041c00c4240c80c50508590080d0340803188020a8141046542000d01c564078480c00100d072521050718620758440e4481e451500000e08041c1e8034103c40c10f9a9850388185154160080c003194402d415240c0307480d0840c0c4013501c85035107a10855000283c030720760005214995901650155003094a95610b407805008450b0742100c0381c9440f00c1020502240403c080c04080950742c0010822941604000c2d007100d260301d02e07030386046040201440b501d403030014034031003c0030b003405000740690b10a0808100021f0103802030325585040030307040c2003400038040c103140c00380502c017060703c902c10750f80d183c140d80e503030b0142c40703043c000c2c002c06002c600102c0c9c0145c0142180c15806000185403680a40009000030811501c2e500440c0000c0180704040c02c0400102d002680110050300b0103504180019140f41c00522411403020f054402c4035014890a102c160b040710340c8440341100186176030002e9600c680b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 511605791 1250 511604541 511604591
    0x30106031406250507020d060e01020f0a090657020102070b0a02210f1c0b010903050c040b0118030605010e090a0b070c020102031201060504140a0e130510 68
    0x15083c0800340380c0d4228000303d44003203a080d9203030303903183c04000d03070030f12030308100009003940c041e41d41c0c076052511448207000415601402d8010681e844102040250104085070802c80820003250070701c580340ca4104901e503910312001c03a0782102c5080038099518803030f2008035540d06502c04c200b280040d00e680b130801c2030984a20036000c0e0340d460340c1c940b200c20619006041c1403c0059004120100704200c203041c4124104480304400c078549440d004641c510b0f0781c0900c644101d5500046012a01c4030704500c110844003c0920340b1162041c95030b1a0182d940d0034031210f19101d0b6907a2803080306240e000741417820f4a26003461451a2041d52410480028003091080406011540c0c0024114000c00b1464038415544019902d10303030388400508407072800a5030b60403415840b08214041d0406581c50741240288403c3d56100d940d175003000d0f00300140707070500d00f00e860182e03c07046018003490700c680103050740c8510402580303a071804103800c0030f9281002c10307100c0c0b28165260003480e0400c44025040d1402c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 511607041 1250 511605791 511605811
    0x91c3e06070f0c05040f020f090607140703050618160303032c030d140705070b06130207051b010f080105130908030702070302030c0d031e0908010213180b010207060806030106031406 80
    0x7840048150700b099101d1692302e0074a582080201800e2803074203902404c03030036000d2031a81e02010981a0401d00c1d00a0740d40080e11268408010080041000400300c800100d6901c01741155541076a0f994443d594240030003400c1c1911124510040346c00020416100c12801c003030300c05203000000f01284ca0b940410322205885040820141c1d2034080e10b0121030103807a80e540d4207031400d003c0d602d415041210142800e60b0101f140018030b00341c00e4050000d42071440c0100c01800e00b42809000b00d1341c107002442500c50600c031824010100c656000203055045401c2912200b100c108071200040080c50100d40c003c001c1c400210034407404036400200102901d20a4003101c1c05400240e0030004a5014880c000300042c49401d01000100b01e5960b40030707041f00c0c0d2800c2000b00242c48482c80c6081e600940041c0c0b4260b4011182044100f42d80aa01601031500c8001000050f1241000039201c000398000e8005020130706004c5400c41d00d00b540160002e5800240811544107103045964840c1e0041c5c035400e1603 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 511608291 1250 511607041 511607051
    0x9030c032d0c0c15050301140414070305090601141809070b0c0d27060c03020c0a1211040908040e130507091a040b03030d0b06091c3e06070f0c0504 65
    0x109001400d15003003404045d281c80d41160300c1e00c840080b003c00c8482001d504103840d004002d004040c500c44581c00b8a4136900d0124640ca0034035003040c0703414016030100c145040e8503001c15035142c0b40e1950341c420022042110000540c1c0c0d07520503c0c6052078541c8000160903000800385009540401c0140510055984d0030002011080103984a09034038000303569403420305941080254060615442841d101c1c1c010f4500d030710188400140d10401d107500c2003130280c44945402c1e04000416018104442041310708020150315601d40350704601071400351142003025a800306448119105800300410b034880708a41c91a034030b80400700060f020004818070301480e19850040c10340b4090085030842c00e8050011410704800710b045034050203048001c0d58104100700300e900119164041c0c0d0380121129200c4101e20845546040c1b0f1000030b600010301400781001d080450103001c42960b54181092031401c801801c13000d040000c8044c45031041c01001054142d540504010301d654444088941c221400c001e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 511609541 1250 511608291 511608299
    0x60b03060a020c12090f040b031e010b011709031b070306020408031306170c0a1103070503090f0102030406080606070804080102270102031c05100e0f040b0a09030c032d0c0c 76
    0xa00d60060405c9540e010f503403803229041d10b081c20703030080510360302c000d08542107100c0c8411074003541200c4145c545034694440004014a50b000040c2e984040e00604000b541032401d048166200d01a0340013000782c20020700e103011002d040800560015640100e03045580e40d580f8000141c8d00d602005c0c0250003165102d100040c3d06015400031170301d01090349050000c0d9960f0030341c15101e550000145400b4041401504154910100081c0c540c40344180c0085598040a5042120180380d0213103245c11940200405d00000b94004403507070f00641c00740c1c0d440303465075124070313081040b4083c40d04034200741d40c400304031040140b200c40500b8421004180020010400d20401280c403841040009250364951000005441206512055010004407514600140c4030140d000c0120390507114011083c0118042c8410300500413402c68122044140030403c0245031781c0c015000300391400014060124001300d0070300c0381040d00345480740d8035480d41c400d098407503c15001038030000050100303480400007160b0201d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 511610791 1250 511609541 511609573
    0x91008011a070b0f0a110f0304050105010909150203060609060a02010b091f0e0408040306060e0a0b0f0f09150405010609090515060f0a0314070504080d0c021507060b03060a020c 78
    0x15500a030407030380030340440d5221903001c4010728000e001962000da50300c8001c603079880c69031b02900340e0101c40000d855481c10581801802d4407010303006034029a2410418000284485d00d1624090b096114003607281c3d9101c0000501c2d41c0102002c258001c00d00040a02d400da0303066014048030102214681072948a90100c00300a1401c19010400340314280410301a07100403280c00c0ea44a0710031500549016140eaa82000f50f070a80ea00646920080c03a040c00741c0304502d030054010420054401d40c0e41c08029000140c05d580901c41c401c0d011324180302c04503019000400b00c81d00c0841c405002807006503941c21000705400d04034840c4a00b1a468000441c034020240c200d051840c0000608643c1440e019030642d003501d0388801d002c072061565075000c62800741030b0481e000384140300c43d0300c0707941d192442d158132036003030420909050b8100000d0380c3d0014016510340a410203000c00561940380c0720031292600341d000705038041c2c02607814400c0400300000158203800916005030f050050301d8208010213044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 511612041 1250 511610791 511610797
    0x10303031a0102071211030312071e080703050a090204092109030c031407171c02011401180b03030d0f060e04050705130f020316090f030201090509070203091008011a 73
    0x81d40140c109500c10040010485110b0030300794043d4243c10449526000040e186601c5801060b440c00320000030808010340207046206690304203840042d040000d03034030050034910b009045c203062542d2280400d5064259505c07041e901d99000c0e004001d002d109007880742264120042c0038000c0c4010388050400e183c80b402d80407040381e078031201c0c0c60314080c00c50351403012141034413110039003611508900041104801d011b1441c04503c0a003c0d081c21411407c3e04074031070386071000301429a0f050a0500c801c2c2c210514815046410007031031600121130100042c0f0141c90021110359140c40003040c5158109a40d43c0b114440100c00001003022a42e030341d400041545048401404603040114104014148507070300c4040340e100755500085121440580004a8105a89000c251035070f007040548402c2c0c20488500180c0003101404805902e140e000803e614581e0203658040d4a42c44c01103003e02d40204240d4031804e00040080c2d00c2403043c018010500e48092058542c1e10303403500c4001204040c00390031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 511613291 1250 511612041 511612091
    0x105060f010c081b030c161d0906160306050307080c09010e06030d050913140415020412080f0f1605010f050402010f051b0607050d0506040225060b06030f01030303 72
    0x9024185002d8803840080101981ca0310213060008115840101d0b4040c4441c074041c080c1c1c8501402c0050410481464010740f041110010300076603000d0004a00001030b04c0c0303502c041d042c0242c160b440500841240580b55651103660140709981000c00d100c00e011030a0307040e400041c1c0354009144e0f81c400c1b4800c0060000d039101a016001918844903d0740b2440003840c140070b026080e096015502c00b04002103818060791940400780d0402071004000700c00400700484000300300c0c19401c00381006026070a85104031381c001c00380600020b40c04a0068404141d0300c128100e913003010340723074070406100320030101c10008100c685520b4007580107440f50061181d0f0380160b070103946070790005505280640b440c2c0e0040070307076182c00036200b50a102003000411400340b19020036034803181c03110444420b14094a0024080600c51030061100d0390707402c44444085d1024150400c10120000c8140c20f00c00020300c14007075000d41020002081181c1c2c01007040196048034420341e0100010001144814113062460b01e0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 511614541 1250 511613291 511613303
    0xb072d2c09070e09070c02091e1519060c17031005040f15141201060b0702011808010903090e0609040213050c09120a0c060f05070308270105060f010c 66
    0x2000340041d0a201601c154440d03403900b00440b610140000162100d10304541c4d9a0005100c0c030030400842c10001203031604001c4103c620780c9400b50700c803a600c00f05000186200203500005a01c41c15550b14804149001100c4402140c4a01c3d2a2840206840c01c21002030340d09100e020420b5a40c2c071820421240300ba4600b040c0207400701d06110820010b011010009060241c03211901078160300350100c1000180307030084c5518020b820700024484a1200912003c44a034580030f000c00c44101000121000f40354240f0702021003248c2c410050f1038002694100359540d43c41c0c12528020190882e100006484844040108554443d41000913002c41110001d4110b074420441c3c14050400b03800103904400160f1105080000c03010200303059540107005d4000d241d0180d00a14188100710180802820051134071701155400950f000d00281301e4504d006041159170340000304040903e0441c1d20340300d00d0030003200605114410506003e0001a00c40910880714814801d20701d40c082c081c5295404d611030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 511615791 1250 511614541 511614617
    0x913050c10090e0a0b0f041a0f0a0f06090e010e0106020c19090c050403060509070503031902010b0603010602011a03010c09030f050309180a05071701030b072d 70
    0x8007880034600e440d45809007030103200e08010808942041e04244507110851001500e41c0d403000802c00340b2100707180007030701580c079100320609403036070502080401b1031003035501c1c4002603502408284091400d600c034403550205014045034080d4804902400c41d241402140c03646c0e600d03007a501c5000e440038852080540d20840d448050390070007981114001009104101110b6501c00100003504c0807503100900080f00098107000b0000e05101d09074100103800700030200c06042c400481c1c0c1e20712601c5800702c4040e504002d00c03901c45100350804403040c01c000d001640c480d6035031140079000c3c0441c0780141f622030a00c030382c0020060805104040040da4107588501100d1301d191289030340c419400000340c0315400108a41c1c8165103500300b20440110f002e640c0040d007454149043d004558010f0038080800150340c5202e059500748941080c1904d41001400c00c080d120600142d521a0300301c842020600c1d04000300001070003038000d6107091141d15480d0045c008100403203501c5040c1c580d03400010415114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 511617041 1250 511615791 511615813
    0x309010509160e091c03060f1502060403110109060c030f0c17010b07030203090901171c050403080a0e1305060148050304030605190b1003050c09090108060105091305 73
    0x81e01100d904141d041050368113003112030145046114a217143c000100e502d4810130801c4886101921000384031113030040320043c03030141d402521140c02602c003804210228054090700703c003c0d8414804164080720801044000d000094042c190300145034214034503001d5054001b60252403000b00040200c580190b0700d07801c1030022629904503800c15021440709204201281d210f554880d400b030041b242e448440c0007243c0b14071525191065a80040c0c0504840d442503000703802105036001c0d20f80c007600c1c070f40d00c0d4160300b00704681807100c0101255000b81d510000f001204031a03407021f80a01c4080e80c886021841c1020340c03c102d50089281072103201b9001030715140c2c20300700b81e21050496500e55094117584409440e91495900140c00c2070380c04681d69001e04c41c3d40d414401c01c421280c50450410301c60314010380009a42418040180c80c1451344400000d4822007030601121040d22000380480c009586078090552360b06400d00419001d01c88083c08180d03030200e1488014250f580c46001001a5949e07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 511618291 1250 511617041 511617059
    0x1706040308150a0f0302030d020d0e270a050f0601020a0b0a0207170c0105240d02120102091c0c08060f0a0905100f0b0312040f0902071a0903030901050916 68
    0x40221030042c500540140c0070307a4403900c1490043ca40040702d02d64403419401003500749461801a20b0666010104000c10342c0d42180640c1084039040303035035440700800301010880840146d0070b00c070304011004c000c0112402c5250f1010740507518048a00c00d0a58035800160b94425140e01c0141c00106c1d4840000c86415030307074000340f40c41481151103940b2404854642030f0356411070740041e18181d45805c10031650f00010400303402c0c01038021444032010f4510202141d08003103600c0380039010b8950380c108405168400d404860181101400c00c0d160103201030034442e10780c0e06468048420f03041104000800240004509003c0c500d0141d07040180c0d11480341d042c004001c02c4004032810302420503003008900062290801540c118100441d40f40c403c03a0415040002541040070548014402480300800111505050390510240142d4910050030501f004410f503101045000c0c000c18100034081202201850290482c64001e1240b82c5070a544140c803240c0800311143d42c680791280401c81012 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 511619541 1250 511618291 511618307
    0x703061401050409020c030405060a0203120708160305040c08061f0509070921050d03062607062f15010902030603060c16020415080c090c030c0c190309060917060403 73
    0x700c241b040780d103400d5680b40420349a803c900300d088007680002c600a841c1c10420034016500c030070340703242010440c900000c0c045600411800f10a04142c4d8400000723041013910014500600205d008a4525181c003809864a00d49880ea94521034098280001038600f0700c18443d40c005d20380c80d165140802d05101862019880401220b02c414107014103503004210b0610543c89008170300d030340124000d8102400c1130001e048444100780d41126030154140b0b00800400c55205440c840e180160400010350b9011103d031034110781d0782450007580020440d41c12000034201031107002c0b40b156400e1581e682c4520304102d0004030f8071103805800060000c0c010b81d03480c0e070051202d40011103186554080c1d58002c5000c4500d04038008540710704000e0144090b80741000a00418201210540e07085d1904c944100c045000c0a000d0022007032020803480d01e4124144074949007803e5040740800c0c00ba0307030741c24010000690340c891040440c809a0011505190002d500c40041302903e00030803c0761610342e070498400c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 511620791 1250 511619541 511619557
    0xf0d05090d0215040f0303030212010501050a120b0d0503030c18030f0a080a03020d020304050601080c100219020d050f0705041505060a0c15020403050c1c1a0c04030b010608070306140105040902 85
    0x101d41000017141c140400154a40654001c3c2e5006803140c2640310000703440d07241038008a05101003401420042941b0854080244840100200303640d08a040403441780b004c5210014040d010220420211601d4800608040342c2c009410000100c1580103040d2035007030790785d1028015003000c201080030640385401231501410600e401450011a0710f202002c076007003510b08880503000040100002001044440000001207410704038030207030810043c0d900c00e80340ca02c1e529501425441c00055585d64040c144005070040d05a46d0309402001103503450380300b14003502c0e12031482c080021024814100b0700c0c10a41d10b000e4209807400400b00c9040d1034030800100c00311203503000f44202400c060301c54000307440103511500c020700ea203080340c100300f01c0b507180094044aa83d00300c48440d2004502c030702d0801c03e1003456902d03803507038140c40301c0ba07030400a44902e4202a154080034400000c1080d1b02a04082c4180c001d9a0104421601c480c4605081e0f84101c20640c0000e0301030200f400004c94944c0100012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 511622041 1250 511620791 511620829
    0x601091b0827010b040b15070609060b030604030906021209061210091a010e09100e09011107200a032d0c08030a1112120c0702030a050f0d05090d02 65
    0x60380c640e041076030001d202c41d4514902071351512001c0b01d080c2420300550303c44100842d003190b50801310303030040015401220303030103400345407590300d18014088203501c101c9191102405481c86407400d810003a1100c07025101d41c1c4010b22030481141f00700400507040c0e070f0701a034005002e14940f0030b14807560000c2070307005090300c071842400301000070f20501d80d842101960400f4076042c03d118000240003502d501402e050041c061a42c600c10070420045c100c00c2d032015601c10f208419030549401102500600d018200c28500100010350320b01403064102a2020300ea008045030317208842003c040c0402c8c00b41501c4014101d0140c003040c00042c1043c01c0b0b003180107041410115074803250f162110340002d61035038450304040e0000512842c030380b984507128081300c84481c0024440c0500b00c2c400d43e001442106c5403c01042207000104841000c82c00c201c526080e0000d0071984850030b02e04007603442c1d03606c290361038019102c0d0460021846000301c081d10302c0b03040010f00558200070140c0a1080f4210864804011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 511623291 1250 511622041 511622071
    0x41202012018030a14010b0a03080a03180602130302121c110f06010e1008030708030a090303110c0d030507020d0c141507020a0201030f06380412050601091b08 70
    0x1241c504000c040c0c050303401450348032217100015001071b00b11044c00e65258082d5a15501c00e002040340c5104840801b1800d250001d49016081c2c0c50603401c6900b8034004110714000500f0901105884560009a90085551803a0740f15040340217030765001c0c8a03407500d4100303042c1a904031800340181300c0c00038140003540c280c80c05800580126810030f00c0036002407016625400500446042d082d001902615018000b1407408203180c070b80c03d1580c00010715640016417507020340300825100b0b0b040346400b00500c50100d626285d00c18402d90700c50080c0688000040d1800d80042e071524030000b80141c0000c1c83c0c1c2c07207406048030b99440d02c01d952520b41c5165401131017241c460a003400324110b402c0b44141e50940c041d000352003d61000500b5071313110070054803d00381170035410302012030240c0f0f1078642d240c00701000d00100900f10480f011b011502850315800e10a01180020700300c0c0d0b0362454001610702c204141e910b82e81e01c5404500031902e140460080702070450035618051802104150342001d202515020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 511624541 1250 511623291 511623337
    0x5220b1f02010e01110301060503190204050a0e04110114091302131203020f06040b0105060c070503120d0f06030b010611010f0914010f1103060d0312140412020120 72
    0x1114411602203040180e5480a2034100000d081c842c1504481e84d03100c4e910b285500d010320042550002400310a180040f94001c44182c141c2a41181d005044c040c1c0300000090307031344010700704110044801340d903940240034035104650b1203030b400c080e22079409a000600b0052203400340310103051080591070302154200201150b00c054540008c0c01010741c03d140700080c0a407450000d043c42c0f409540941150b20000038040025640042035056520540700c89803500110101907140c0081c0d50302041d010300032030202032111744334480105030354501000306100c41140c000b4000c003200c103070b440007411052000e0010b01c0094810f03682d01c0308c030f501410b0020822012251410007210074100003100c220101c9415210005001c1c0183c0d0070590102e002040041229810b019903880000c0101e4410204030540d841014000c560381c9407901c1c1105010402a10550740742c6050758410b03039007912910307800000008214414051040038020251003008070240c0c06200310026080038000380c0c14802c0c1001910 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 511625791 1250 511624541 511624579
    0x3122503060e07020708031b011e0c0f020c0a0603091b090e0123010504181a06010e09060d080a030f050f091501060e04270b060112090c0e090c1c030905220b 69
    0x41c1000ad045480040c682040603005000075210660340d0065402004c0010741d00d80e21561941c00300c40c2c2034140400c00503550300d00415007044402c07882110810440c07001c905005035610650020342900b0081220399591103035031400181850115003107218101c01840381d03051070f8101c2c010038600d05119250240c1c072680d4520041e8910b11402d22900c603c94204265507a108540900880c0d056401112904000c00400c00c00003807104060414030780000e0000d0040e01c82e5002711150301c2c094804119a0804002800e9080c1068034402c3d040d02c10040310720401030108500a04882054603520a0b1048043c244005045001c11189a640e02c068950300c02a0b013044480c00340c94442c1203201501e01c0d010700058038400e0740080e588192440c02201174000b40901705c040c001d80300d981d100409030b1390f20b9007901c0340b40040c101c0d0001d40161524000c80320781400c5c403d5000040c2e12a4a4061519440c0c0051110446040c100e01c1e0f00218080d8142d1301c01d010590040c101c9400160041c12200901d4640c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 511627041 1250 511625791 511625831
    0x705041a0931031d0a2414040f030c080303010e340c03170601020a08030405012403210806010f020106030b0c04031509030203122503060e07020708031b01 68
    0x140c001c103444c03812100c008000c07100020082074040301c42000c00c90a125a0303038000d41024101400b101c41090a60051030702030000b0804012074403c90a039a0350b104e2060349101c8010344812680031818640209103120301200382ca050361300000d4204016031b02c0601036800040c1038110b0034440364005a000c00302000c041000ea059040b0f54940d901c0ca01541e2400a10044106a001504038494000d100c180ea9001c01c41c144c2c80d5030020710701034407034980d070405500620300d0044000003415540070310046c001c60022000112400750304000110201070f644480384600d11107103007001529100000d401507001b003450031100c50082c800083c40315144d41c0c1d05408024141c072180252403012608101b0030113094492150341c003c40c0014007079505035a40281da68060700154130096220800000c107041804c071a1444940329044445407981c50a5070702500420ba40d000e801c10b10042900040c00341800041d400003110b02c0340008510781611200760000e112058660041c25540b45c0c111580300c0802554a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 511628291 1250 511627041 511627043
    0xe041802010210110306010c0c051905240d090c080708071706101701020d140603010b0406050303040605091807181211010503090c0a140f09190f0906020304050705041a0931 76
    0x141d440c070305003840100207041c01031048500c0780c40370101c944402010450b007601d81100c0307840c0002c6031643c846c4c51b0079200300d501500400d1162180038000034a5820005e000001c44001894624403000d2102c3c24540f03440c4126076010001d0000c5c0b800b00074040e072028100599082e40310005040401d44c1428005030f406000b010707403103804800c2c10720803503150a104180090340704440402c145454000841e03181e0180d880b4000c24400d02103030141064440380100011800f50b01c00101d854901184040c1c45040c0c10356095080c015841e40102d00883c040600900c181c0d0400c46141d22817540000440b4154802418003880e40502901025551907000c418006003828404498108441406001c40112042242c030311904e0070500380710042103200351400e045294041301003400d8008040f8400981401440104030500c00020441405070201e002015a03d007110107000f5107481d50880110760315681c0700075500800b450301040520160810b1070301c0c2d800c80d0404414400c5880108003140801c03c201c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 511629541 1250 511628291 511628329
    0xe060910031a04150b03040c05030303100914060310051807060806040e0d08011505090a1d0f060f0f1923030303100e04030e041802010210110306010c0c05 68
    0x81441100c072040c28440d04501c420b950400c48502c02c4d900e001e980d20340f0762003902c043c6880040880c0c107000309402d06101400340075045950b28240034802a002d044203120340404d0600e0000d58007204c4c2504158280200c100800515200985002c01e6009101c0074100d154091800d100f41c04241c0e4040c00240028200e64840c04a0f42ca8002c0c24001a204180d81810664010400002040342c00c01a0b540c152202b520480f102642c80240c182d48920543d104564090900040058940901542c1c0544038040114103c4261120800c040308454240d4016502590382500b10303169003003048603414042c80050001c8103100c007101e94421045501c1d002041d03080c0c502c440c422119000311f0901a2040c0081d00298514030740781c0340f616240314045c041d491a096006c00420f0034075210790307810320721410010020018210882000020700d6000e03a4124054000e0358040300c501d001300d1040840603401d07450350070300e10b03030340d0000442c0e001e01070b002d080743c041103022000705036511000b41696101030400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 511630791 1250 511629541 511629551
    0x510030917041d0f16090803030c07034a04050103031e08040515090c1e030d03050c07060e0a060e0d080f090703080c03090415030605010501050f09010e06091003 71
    0x400202101c061960442c160707656403c090007043e801041d03546078000910361000c1c5000c071540000b241caa51041d480034202c0d02c4080b050058588580c0002c2028611070303100d1161181e031b010920240c110f41783c1c61903005070002580b03000c100d080c0f004558502c7c03d1001040c5012001980c002400c50740281c106400054480740c00490450381c82000640c1c214480c10000803502e001d030703035480d61203210a44003007890740312101141c010101008030301d4040000400b010b030040e11075158220460f0f144500188a03110300f4000707000d220f0281c071400c1e00506403a440309103480d48075142e00e0050500c10155007458400c41030400f02250683c4104c0d1700900e10707040507010403403840b400144400005816911aa50f105041c00081900001e02d04c048076031068115403072300b0010006070305501a0f12029608281414417000080c40a2448402500d224400c1000182d0300c600044549000d800a40840c00904100244883d80560325110b043d00c402004140703041151008112200c4810f402840803a85603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 511632041 1250 511630791 511630799
    0x907170c130b04031a0f010603020a03061205100c0f0203090d11220b1f031a181008010b130b0303040308160210030b0f1c06060b040906050118051003091704 69
    0xb03500c0315110b1004221440506e00304404240042d020600c200303000c0c19400640c0322150b50180d0402402425001c4081840790b41c0d5050064039007012200b46101c030383c5041a0030300741c40d0140c04003104041c46980118200321525041c81154440c6c41016104001000301780380301903866009034010300d21409e19a80b48403820036410f00640f0f03000035185109168020340c1c40785844204c481c141665149203000b1610f005404444107039081250662034102c20300202d820038503100c19800600a136400300325030f1050303555404a942200c0300d409a10f9480703000d44007404400c54007030f004160443d1006040d2864150f49990340d0429521400e41000c22100500f00c0c0700a500c1e14061084c01c05c807503800c0a015501c65400054503900500303800d5445000f2110011003001202c0e0780c880c1030305510040030403c4945030a41c46002d60400d103d40c40c2000d040c46408602c07035114006c403403801c011070190300e114142004c0800615045181001e42015960122080490800f1310070440f20340405440726603507810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 511633291 1250 511632041 511632053
    0x8030307090f140d0b0a09080c0d090504230c0c0d0306080c030705210703150b0a080a08040b0307120603030e0f06040b19020f0d03060608060907170c130b0403 70
    0x140d980680309a6104030003d0085441d450090544541d205114150554036004030301700070049030303c0107840b460b0b01094040e01a040000c1e0598400c1075915615500c07692481080243c07001c0006410039810943c05a4540505045155030040d403e0000f0904010320f401c2c4e024540254841e102c0f00203a00c032007017080100018880007042c2c10040e03014040791070404000c5101684640300100c0464450b6502c42001c000c00e020010145078480c001082c18000e1509500207030a8181e1030900c900d08901300001d0f60348000034003040003980402c202c0c1c2428504074a1503000d0b00300401c480e051001c1094680d18139a2507102d08000303503210352141c1100c94040340c1403004ca1101c035801240a40d0b02000248800c00070707541510320312680000324400d0545100e204908140c5200901426441086401c0c002140c1540100090301c505036501e24503692141c00b003045811081c0e45600200d00211040000961079840c010381c044420400c103803400c802d10009204210a43d444407100b580045400d20400031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 511634541 1250 511633291 511633319
    0x1e060308190221092d01050f090a1706310f0803190f020f0f0a0c02091306110712110c1809010605010c170901120f05040204241e0803030709 62
    0x242c15440d48942c0d0000c028441100d1917101c1c140c9043c02004240303000852110300490b80e01c030310040c000c4085a5035882450201155600010416002e4040042e20154400000e032a405da0344194401c2c804810171070aa1030000551002d4807904040c011404c003140c008002940a40042c8103401800d4030070781c1410048400340d450040300c2c1401000304190000c0742c0c8041d1a030450f4062079456071303500811001c1c1d450480d850802034000b80c1707440811031281c0d806290300c2c54882c00b80d0814001803c00c403554620300d2213003000007400d0402e0b01c0e51800440d40305d5100c0c241032461480450315581c0c241000100c00c03030b495209a1440045980411018100a00401c8004e107000e080c401380d0312616035510048401b4540105203081004206100c440e031240741d1402ca042210101000501106060403000e81001c45099008505000305084549211056018810460003001e1600c40c10300c2d290300800402030b1460b5100c1c14409502081405080c002103010711040d441d000c41051501a150108103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 511635791 1250 511634541 511634569
    0x4050c01020d020c120f2d010203070801030f030e0415030507050904080a110c210d0815010c06110c0c0108010603140a0e011d011e06030819022109 65
    0x24100584400c0d0094000035440c00d6240112440145e0007002907403146417003c0d44250b44020700c0780e001c032800c0b44031641c80045802201041c00801c01c680012540c0e00781e01c001d0780d1020020365100f004101080601441e005128401d00e05807a025a040d80000c05868100328820110f0020f01d000700100f042c2041510000c01080c0c0f0121402c0c40c060320780c00e24a0255620705414403040e4110b801d99000c090000e074500201c01841a000b51004d410443e034101505004824036200c0e00a000918500038500c2521070760344101d9103000800b845c001112003282c80041180e01c7c54940500035076280480e00a010704212100062901c8000c48000610503030b4107034800024103280c80c03c4214030000f001d00d1b06501528040c2d000c210b85404021882c010603100d081001007500e5050403010f26041900284442d0640c65901035071074081e010090100d5406200c024040e540c04c12072211424052442c082041c103080c0107071048040e0036410309808009502448000c0000020040901e00d0701400681540c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 511637041 1250 511635791 511635793
    0x2061204110406060c0f0f02120f01020310090902030c010f0c0b1f17030703080c0702031b09100503100f0b0307030308070212160f0c09020f090a091e050a020d110304050c0102 77
    0xc0107454603606c0d411b0800c241d014214042080f178403410754840b1401c00700484909001c842c410111500a035000390404d940d50180e49c2215031000034609164040c42d964240c004018003035000d0b258005480303404881d400501403200c115140404078030b03024000c0d4422141d882e1161003212001c0c0e800c0e007044901d900031001189a4407003034000c102001050f500c0056041c2021541c54484060640807070052001c002e60501c100121641e0480b0034004414048009881510b0241c48000250210340a180901d43e055403040600151b40c00303942d0002007040b510a400011402c001002003400e00b0700750703081600411034090600c103400c1da040080e4100403031126006820300c00b8005410b02d101c0c0c890740000c0c00784110038120b40240720310b20700b007540104031f5411b045541d810391100c007010315086110400d00c10100303664002070003a02805030b51500d803503441382460074070448041c1d40000c010190503542c0c580c4d0b0038072809510020030300c03070b1400d0010506034194681c80c040c03034075918220320800001c0c11 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 511638291 1250 511637041 511637057
    0x30c0c030601120f05120309030d05010f061713020a0303022503020d330e06010510141305090403031d0c01050405040e010e0105040317180c06070206120411040606 72
    0x10081d070407040320541c3c0d4030080c462884c00d01070520340d14280c010542c3c1c0c294503000009000c194600000100300b40d055600062047e030b079a0b149041504421445a00049003090308003100040610103219400300181409039445011500803490340700284e0000c8000d41c2c80581c0c1d6020382c030241d492181941c00710601c4007000f181554003040c0b14018196001f010183c400d60030111076955241e850042404031101c40480000400e03070000035100200c14002103004000001c10780381000600341e078200e000342c0c07a81390381e00402044201c15a0300030b100304800180744941c04034503a950500f281e80154009d039000306043d54014404d402404822030483c00036800707040030303c0b800d03600700041da821900c080b0b40c0040e10515620003280075124000c1c0596541d4600380c1000205500300355030510b80f1501d5100a103455440001000100c101070081c1004d0703030b0000001183c14038100c8010072100b44041c01d41d1382808080c9400b58000081070b00c00b110407041040300d002940c200b520039440206158900a58 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 511639541 1250 511638291 511638299
    0x1142215051803090a03020103020c0316060b120a0c050909030c0d39151d0607140a02060412052203020324060d06110a050703030b01090b090907021c02030c0c030601 73
    0x86801741031100a040c15004110051170190510079240346d045000b50585501d2141c1c5403040080111051148c400c8001921b141c2c00380318000f9140d12019400840c6050007800d000801010000007402e03080284010446111007040600c440c1840040d25250b5401c0c6070042e10319070704c080d460280125514010403c00342c1b01c0400089440310901d4005c4051580200c0c1d1070b0041c0003030800424000010321240c01e19905041d00001d0030b5205103106d9480c0640b40070919031811140c4a955040001030f8408400304010aa00c0da441201152007802d0440c544000103c44a044078800b203001079402854903801c00c103600781440500342619006101d4041d5118401805c120740001420540c080c20742ea01c201420030080b94041c1c40e1070303a55030012a490769000000100184c1c0048070803400a424000007900307650040c2d40010507208210012800c3c4046c1c0d0b0b0610a41d000020224000c40c881e9244980c80c3d00c07103507801e00002c0f0410754051680c2e48003502682e03290640015110307003c0e502200c0100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 511640791 1250 511639541 511639549
    0x40201020d0806121603060606030e030304030509060d1d15070f12020903030f0406031410060e0109150203040512060f1902130f0e090114221505180309 67
    0x100075072580c1001d548a495900c007041814135801a281c41c02e104d501d518609441940f0b000c0b000b12407103101c0610009071514021820380700d0401c1b6240c843e42c418400700d0700103400351010b0f08002401524650401c0072110000c2d00380c80403e80e581e2803407450304a00b4810440c0502200072090280c0ca0340045905200c1c400801100341046a00300300503a9000303095440080f50100c2e00e400743c004040b87c1d00c07210080d5103c0c000383d0052082c800480c5c9801d0004114030820500c1500c07410b08000c0042400340707484000c2c1c0391404080d500ca810400c0e640000300320070400459402c60200301754021500e1718141000c0c428601400c81c400b00b16070f400042045126601d00403070079404051800e12071350b02d1450524903800f9009501d002002c040d600c0c0804980102101d150108079a1f004101d0000c03526048600c90032960b10814105010003541d0002c0c82c0140c00b41c400005400d4203900014000c10b40740c80d030788110b2107500c803001051074a610501038640ca40300c00183c0072a1140019516001c0058005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 511642041 1250 511640791 511640803
    0x806091b01140c010606030605090a060b120421030204080c010c120c02130501080c101d06090a03170306040501060f020a172205120a03091a09100e0a060804020102 72
    0x3090400c9104030b040c500320469982540c0481d101c9074000d1151544a09014003e8080c50141c05d00070003c1100180b040308484c001d0301d00b203591882e03445150503102c10202482440050064810b203622540c05902180c034101d8101c408a0799a80040e11241000a400d0411214010140c100100c5258000104e00420211500e40c141400c002c0c6c00c09445201068010320381d0b8500e11141c0c2d01d0074000003000c010200300d46511a008541e8003401659111065916810010b90b0301e521078505802d130025400e045000b0322828000802c4449096500e54500e4020300e0141c00c8184402c03804000d200c0030341054040d4502518003814000d03e9036050003c02941e5050220340a810390590880c1468500c8110045079520300c1c5114840c00800400c800c9050b0850642c82028050b07090300d08031304400c6c031002c5031422845605980321200a4070380009102d092001249113a0064000c00c4200c082d980e17800702c03820041d0201d4036203524041c404001c0003500d040d664080b90a0202401c00c010050780d021403c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 511643291 1250 511642041 511642093
    0x80d0513051e030703030c02090105010c081e2b0513020102060403080a1b0c0309090612060230010306050615030a2a031e09080a0c051203040606080609 67
    0x405000b02111080d890005241c00341c405400d8022000c000c020300d58840480c0c05d8032070094410a105076a6080115a459000c5501508840080c0803190f0440c2400481e5071340c10501c0741219050050141d602500c6a518001d0680502c1c44440380030603507040390081540c4031074040030070000301d42c054001070740b11440200f0003401c01126800040c0c40328090350040c51501c030180210700d026222094060100c843c00c041c15800b0800805000900c996580140e0060705c0f80c483c10310b00c02188079521394000c0c4d00000c400465002c9c10412500005a42001300402d49280d028894819491418280e003219009070030b460060f000304203c80205401d06013280d03006424090001110815003d100c0c5c3c207410040b04c0c03504800040601010344e15855001b031400240340c868050410150500c01d4400c459000c94010501706050240c015864003d2402489860050058034013415060011b91010f0740211000c55045541c0c510621110308100103e0383d002e0700e614014051188401e18001001c0c0c0c4d2100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 511644541 1250 511643291 511643299
    0x81b031006060503130c03050601120b06090601020d050d061d010312110607260a0219030e070e04080d15090b0402120c030a0207060f090201030e2116050f07080d051305 74
    0x280010820803e0720380351b0000d603000310a48100f56101c1c0225010840b02d07100c1580e14902c0d14010034280d01d010200140507260503002001c890a05440c00d440d150804a030b5400c00d0380d951000050b0411860100558440f08117545000641c11491304855048030404500708220a059211001c060000341d029004641d03424082041400d513100b030308031103010f0781800d4001c0d04100c00740800001d991b0041c06c80104594020100800010b100b102220751500e00e415150b4800d4504103c0f10025120aa8119000d81c0140b450510030300204070942e8400080310a03103902703c00c005c0124000a11462044000490782503150403000d10f804816044060021001c144000010a031458510b5044410303182c0d0280e418000302c40018408001000b441c401039010074104030f07640402e40c0c0c02061414030040c50346c103504a140c00300300881c0425040301c400360441004010506020403401c100c5541454100001021454280b0079601d0520300c82252034070600809005400d0340440c240740c1d400a8074010f0b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 511645791 1250 511644541 511644571
    0x20303040503091e040903080106260f130c03080301030c09050610030c020f0a0312180f0b040302010930020c0a0308160204060b031e0403090e040c081b031006060503 73
    0x40402c2c1442a503500132a58040d1a04900c00101908514424101c504c5516001c11100102c0d50b0030304900007030f0342070400807105000018450642e00c0c4c500381e0886120b60300d0b0840d01e04655280283c00c00f071a0421340d0480801f100404c1000a40368000f030203400104401d0246041c004042841200702504031000c0c5502e8400301c04100c0c1c030030040588400d03158070494121030301d0b509018214000b085042220b80d07007401d5480c1c101d0800c0f08007082c840c50740942084220701c49500e404e201c903c0090021001c55485104550228000c00c52007940ca0302841100107000a04950404010341c00c10a400d0554101003040d0300319580d003602000c1200e800a1186a0341c02806814600d040003100000b0b40c03182c5484000b05100c002d42018501c503103440031a00006054001c60001c0c0741c1011500100003d44481060204011001f406600240302c2c001201050b0780f102e4011303060803c544411a0400d080030040700e0076240801c8800d00b0388281483c00c105071400c0060052042c03200802030040d00c0218 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 511647041 1250 511645791 511645819
    0x1403041d18030a09050a090e03030606160b0a0e0c010206010b0a050f0c0334020d1104091406060f0d0b0f0c041502060105040606031a120f011505010f02030304050309 73
    0x20515028100032180e0030b42c2e50310341d80a24040d01a100d540a83c5010b40c28804c030228659010748602004404000c00035419a90380004000e4580d101d0440054100400b6145c0800966040032041c0641c4000c007022032261004c03070005107041c1030107070300604560182d8010041d405e0072070b04841c0c80b18958079110381d0700d00c1480c016240b5841902b01906c0381e413000203400e251040015450840040507007a12040294144a07071800425038020b004e0f61110a01c0504c0002900c1040c84002d10343c0c0150010500c01c0568881c40200c450090046407540c02c404200700c0320380b9145855031601c60088035142121412030b101c4201c0c2c00d2006000022552403a0b000c14407000032032050310010300c5410360850032809400710094440d02c0070b00ca200e0080b820610081201c90080c00785a210500c040c00f801421000e0300104405400d141034698154000c981c0411440d42e800e00680220345541c0c050800310030702e014001058480c8005a07001150810310a11000810100454421a60482d01c044c446024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 511648291 1250 511647041 511647061
    0x9030702010e270f01051002060c040501030207060b060a18060504080a0204020702030a020d150609021c0f0b0a0821030f04060504150903030506030c04020f070305030a24031403041d 80
    0x800700d080d98080305000100040070400801c61810f80307105a85501f04028040310503645c4100a4031161401d40b4240018001e651080d4003902d0224000da80c007040c81c1580c0d002095196100300e05284c0014010075102c14040038800e1120010086407a01629092601d00302580300c9540340c00c021301c03450b000034000080d03640421108401c40e800601c08500313000f261812901900112102c01102e60500ea00001d12200d28400e48640700d000114401e03100086000c1ca0009155184445800700e94601c0c2c1a4125140c04002e10040d20724a40181901011202031a000c60495584944081c030100b080003005050030f141ca0790000da000f0340100f281d8550745411a414403000b00095902c1b89001d03548410300da81a00058003c0e9810344c00c2c0c0e0565603444090206911880b5541c0401d00c80400005000922905c001c40e40411041000a01940c0340e108036a01c213000921044114117405a06100303020040684031408074040009501c1d161410051817006d14003d410340d0070050b107040004000c159 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 511649541 1250 511648291 511648339
    0x1b0f021809060a0b010f0f03020304060f050c0405090a06060e1504080102070305070b09060106020601150908070f051e090402010807020a0f03081006030621050a06090b0f09030702010e 81
    0x11100158560038034010701490764985085404143c100d04114184526500501c007030503805640d40d4030714508152821054010f548050030480341aa82c40c440003d82c012544542c074000c84810b801942c1e9103240c1410441d19120151549480600d06007007005241d80145403400038010903200020500100824411140a182c2c02215154000100042015071100080442c0c40c4035010342c4000791a08900950744003001d02403074002da0321020062104d4413049151440158940c5440c02001d6110701030039007040f5480e80306e5076107902210b00c280711900c2c0c211103281e1034090b2030b0350088004200c40d00240313101c01c2c0544060305020b5010b011035646807007800010300f519001041c0740b284c0096450000c00d503160072640c0710f214100d41040812170354442d00a280c00c40d24194500c2c40c88000d212520100816a85421030b010301c41e0b80040340002e141c0c0d0048400c42d074000c2c00d0b100301e98a0503c10200d0074000007405c50180390020410b640050385c00c40009545524180c0307800500e0001c111144400700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 511650791 1250 511649541 511649569
    0x161a04051f0207032a1d0708090c03070f0e13050d03020a0302071a0406060504110717120708060f0619030f02090301060e04050c06031605030703020f0f18011b0f02 72
    0x44450040090f0542040c41c820240c00304000b80d81c05c0d156850b0442da880c41c518001100300c00c86248085000705101d4100c01d50070010030b90584010a000100092034081c0951081c00088203a01c000c00c0310541015a45501070360f81500c02c0d42e051780710340d01d03962159480c0042c03000380f507400b04000c40002d1081e41600c82580e802200d000f5a8550302032240002881103030201d480f64240031012607181094019a0149000003403400d09001203940c424855500807503e62200600030701031401c0384000020303928059661900c036100b883c18018203100000104807903c900a510410003951032580000505841c0e80031071400240c1c44402c000004060f101d9808640e5140d0300f4608042a842590662540503600c50400c41d81c104034000244200b9020886802404114150400c1c089074007a80086038440241d1800525140b010001c629058200501c000c0f1440008241101c0b40703188044060000300c002d00317002c0e000840398010742074600c0001300010481c411015045086480c5c1000d845401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 511652041 1250 511650791 511650803
    0x30a06050a060c060501140114090f061209010e0307150510030210021b09011d1e04061409011a12030c070815010b12040201080601050c161a04051f020703 68
    0xc1691075400403d080c001c1036040e00c400c0c1c41c03c40002110307415612807660740c41041e1940381ca400c00c01d09102d030130b58100400b1150071143c0c02103a4103440d80d44134000c04504031008032080c81402c16499590854030310503100500d80d03104110071001b054a19400c40c61007803851002064603a0303500641d101194070765100035006150321845408458001ca030450003c8128440701c00080c0d189010803d00c1002881140120003426401d540003c1d14035600940c400ba960300c2c104a189405c125156200034100c40540f27910341e498220304001844140c5040c2c0200d0044024440c4032040507070307040115201d451080c0b150f40c101130070800310541481a2024425404103440d2926611100c4a40311143c43d100c078170311942418008280d113211082600c1d581e8002e0312043c0010b90f12a801501d01e00c40241010741484028400d02d400076104010003078003030404c580a0400e40f0300d806204a46414001c00c3d0344e15045041c4401d001584458a640e03a410b4076001a40e041007429a1042e0f0822240e904081c2071 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 511653291 1250 511652041 511652059
    0x120d0c02010b1003052a0406030c0c0f05031207020c1e131b2705010305100b03040f0b0a20030601110d0e150405030d0e040f0c030506100e0d08030a0605 67
    0x40c584e00765002d184225485400a5103c5180d00111480c12a403401240c0c54050140070900c4132074400c1e40000c01100c1942005408140c00b5114240c0c9558045001c07241079000140846c0705158030748146d60800400c1c0002c0449540d80e00000e030000100e1100c00000350f82c0c50580070710f10303030b01c54441da54030b07281080c42003107250070601d50884500601d044903004142d425103804105030382c0c48a0f08a00044032040f0f0700c0c040341410300442c040c0c0805003503210803509024005c560398004c80002c45c001c621031038258041d00d2080c40c00413008407006240300c074130714a8a007201620108034010000480204136201c3c1d92990340d0070060f203800c4407820a056030343c403840c0310141450340c100c10341055048044681c2440c07480072801c0540244224081c581d01904002c105500c07042c0240c3c12294440c00091021038010b001e41d040e0340441b0396040710f1030b0000361030b50700340310881c18003807601c04040c466490a81c0c1440b079030902141100505000041101000200003200e102140c0d1111000d018010104a4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 511654541 1250 511653291 511653319
    0x10c082b020a030501030c080705150d090206180301200a05070602160507140607081b010902040213090b0409030504050d03110a03050a02150106080601030e1923120d0c02010b 77
    0x4020f10313003404100c4400d4200c010106c0e400c0800a80c0c0d204442c40140f6060404c1d40c1841203a1490b040010b1302c00960347c90b0f69110340142d4400c00a0562049403003683c444000740345c410035003903a14940700311b02581003416142c049031244004a81400a03a42001c65442c0210f142c03060080c814041880700110034503501c1d008008000c50b011040360702d00c1e902c003825002c05400f08216407240040c01010031808114005070000f030102030004648130f4900014440407143c02003000c0e41e100703d41070b8241107081d400622031980d142c4214034540406480c10030514000c0e603006040c501c51401140d208211010340442054410f418a0403180d1142c0c040e140034903c1403502070090f030491147e02004d8000ca100440359a0704e60b0b40c02c60f048555070f03030703070301d84035898003c0158000c0081409480160090300c8901e002640903403a0107a60910850b001c0701c2c00030ba401851400e400c0b0142c0707110182d8002c031400c0103000d410070060380c07c840404c2500080380d14002c0416030042000510454000ba64050707104 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 511655791 1250 511654541 511654547
    0x4090501030b07080702031321020a180c03090b150d060e0703031707020d18030c08030a0e010f0206040b0c07020d0609060b0a180c090b03090f0705010c082b020a 71
    0x1501450f4243c5070350040c1c1d11001300aa03140d000d80c022880030f07111b2580e0200490f4102c0000408079110811400c8104a070f5600464215401034000703520000b10407130b0a12600e0041c0c45003001e02e9526203420001c00f92107071749072864500c0251041e004060301180302003807179840d61218249564811001c01225024035020754440c1ca461005a020900c420420108800803280e02c5200b560a6400360144096403c01a20800c14101001d07034500d81d03034003000c4001070041c0500805000403400960321100014401445140504c2c0064108507070b030706888030300380d40000302e45401c03c1d0712503c00c60305e83e5035448082c0300c1409085d8000c2d40c0700e00310040f800c0a00c07685034407140003940901e500b8000030042d05d041c000b108040d0300c01d40102450b000c49a00284180341d101005400443c500102048d80e9941c0f00708464105a522514a800c941c41e0150518010492100180400c1c03d01203154201521307180034500421040540441c0007018a09014a070b040081281c6900c49804640b40d5480d40002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 511657041 1250 511655791 511655813
    0x13060e010206010b0301030b1816030302060f060a08060a0207111309170408030d0b06130b1315050f1e180906030f0604020112060803041206050a0b030d050703050409050103 76
    0x2903025005000001c81c0c1584a0310849050740d4000e4041030540c1c40e82032040e0f612001c000c90010607800345010441042440c48501c80c0254025401803100c1d0402c0d078120102104054906032044901484c00c002c03960340411320603441405030b00c0041e11102141400038a135000d5009444e40920700c201e1600c145030480d4002402e06015880c1e081b98020446210603861141c1d0281c464598418040c9940d0170210350088040100041c00c420300305074100034080d00192154004919401002c50703007405442c40360418800400007518440301456003038034043c00a12441d2a5a0a031141c0001d04003003050154410707840f44007d0b036407950ba0342c0c407428200f207082c0a003500d001c81c0308010001c08200b807481c0000d20076988846140241440791556070042d154030340100034562489459100c00114410103002901c01020124142140c56a00d072910008640c0000c01c182c0c4503d1814004034003948000883c00d03ea00c10718140340341c1d20301a60409071107034050766110784c40709400c11001004200c414aa8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 511658291 1250 511657041 511657067
    0x304090c11010b04091113110d0509100203100501050d090b10061211030a022203050604060b030a0506070815031218060a140702041b0305090d05040501080a111306 72
    0x300709491400f0200300c169407525102a00036802c502d0083c900b031412103016004071350100d00000f24030038070001c04071440c0c01401d40008040c0c3c0d02e07010010b40550600c150f0220418031801180781d483c0411544221024030f0003098104240850740c0400c10380c04d40d00c100740301c0b80c000f00c00e44035500e003258030303140880000d0052400140b13110303415031840c81070350140c008407002e0000541e0969a6120b0b500f0700a40104034010303031180802c64102031071124000a140a14002d102818075860b003420318100760703901c0000c107a000b940500c0d089008200089106604001d079450214040c0d113500800d80d4510003c00c00c40b43e07142c000c070030300b0740d1150181100401c40d41405440040d00310000e04100440e500680c100c0344045018600401007104000b0001c01507507100a0001030144461090304200600718101200032a070307140f0502c020761004000e00021107403145041481c0c5824800006d0801902030102d908c55030700c41d4200d031040300d08a41a24081100e01c0315800d030f0030340c1c1c2e40e00c000e10119420076 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 511659541 1250 511658291 511658293
    0xf1404050705100909150e09062205060601111606020f0f03090109120609060903030504060b03030301080d03051812071e17070c030c0b121312110304090c11 69
    0x80020b8039051910101c180744109840b0071980520340560031001e0301c01c456611072481111000414056540c3c3c2040d806044034000404551812910b00401c10401000c50101600c1108a94001620003d83c40b030303002c0002c1c030b0003440d990007085509103050841a079483d40c11503d14008640282d000424030b1101600c0f0044a03881e400b195070b0b8540781e02c180e0240c10300046006000344001c03400b011040e440140316600020307034050346444101c1100c09409040b40041d480700c00307120034000103014464241d181140518699490a109030355544000c104410926880d0301c00200550b081d41b02040007030b544a000c0e078400d0002c1c0d51800801e64000101250300981a1030048007440d40400d00007400c40e48248c241d604480041a410400c3d0042c080844075100020004030014103180d04180040c4200e40d111900c1340c007000031000305071130001c0004000448100c6c180b40418150284003a0045280c10080c18080f56203001030b0561080340c008426075820710f004202d1499001a5201390303c08008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 511660791 1250 511659541 511659553
    0x12020d0b03160302100c140102030c1803071514040506220e0709230a17010c05030c0d0504020a1703040509010b0c06010e0703090606080601060905010c080409020d0f140405 76
    0x102d00c07084540d107000103500031240c4407000c0c151501818800100c42d000f001030703042d00c00205825509990049460703101810010070103001d8416052030740c00020304d00700c0c0980121820001100b03050090f260030f04082015101c0082c0000f1038400444018104c003800541da501d00d40c8040300c90541a4000c02000402d54080000b2900c810416803409025140e80d0850b203203181020040c0d150b075506001d400905c8055404a02c250340740f6803101c0060100c880c02104218030240ca603402c441e41c1c0d507241c0c42480410030800004400c42c2d0b04980745e02d8004c403400581911140013181200400f078200540c84031541c119011121307000009802100d4044032400016a00c1c1c0390180c078140285000c0090640c00766005110020000c015658001c600c1d150000d5902c98544642040c0c3c1c58907400940280c11250050014a5100d080b1001800017820010048102c90b0781c3d0300c00901c55072082004155011582d03115480c200d410030700303803104442000d00074410080b161083c6c4000996084a1600c900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 511662041 1250 511660791 511660813
    0x50304170d0519110607020706030e010b010203090d0602040e10092313020301150f1a040501021c03060e1e060f0102070302091902040b030702010507050702060f090112020d0b03 78
    0x24400403a03060340e80c0c0d150512202d00e0000030340781c1c400690300c01442074130b00003680131402c1042864440d102c141c2c0200203440c0b601c00040c0817070b40c2d035001c4080642d04110000d103099070000100c0b42c0c0550142e5003011210303101e051810003030040d81c0103a002982c841082c454181285403840c03080d508031071001c01407130082c0980701e43c03000c0a940001004501580000300e281c0400425000c04500240020404420f4a00d4143d19852180c008a6900451400900a5035945203940b44900e0340e8100301703464070382003c001075515801350b0007243c5803118580700710315994400d0304450024150415001c07402d06181211842c02001401c2d001000c1ea581c1c000104e5520b0545180c801e40741068026001903411502032080740c000061003420b499503102d024400390b040a00c014030033090303101f140c9600d034100050001d003950700c054425010003100f88451009696a0400c6408200843da240ea80c0c424018006a88841a28403a074aa0f24400304032080b95841e160408824400304505881c1e00c9085 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 511663291 1250 511662041 511662043
    0xe0106021c030b1003020714241b0405090a1407030c11010b06040b07030309050a03020c12060405070902030a0902100e010e01140a030203090a0f120e1806060310030506010305030417 80
    0xc0a0300305640500040445044c59004c0c3d801004410300800c00c2000103415149403030718205505c662012030340c01004060761501c0a10398099008240c80c0396915140c092140c04590070302581c041c4520889843d0040380b2012019413154005440e21400c480305882c01060203002459085810300114614042c002023041c81131284002c0f0200050825040600b0188040301d5500120821010b050359821204042041003208170001c9129900600c01140c0b15010302c03101c5002802c0307040c415803003003080c0070000e40b02260203000d49100101c01a01c5c1d903640340748280a0030b00002c029410079002c118120b03e9035800358a00c0078420742038a5070601841480011155080000c2ca4080c6c2c070740d014400b0f40c10140c46a00115041098802102c0501c0019282d040007822680d00c1201d4040349154070300a01c541141002040300802c031020f105041514030580c1091070000c2030603214240001c005095100c03c407a00300c001c3c54000c4112244c071b603100e06d8003940d01e81c480d00461802c49188420840a148 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 511664541 1250 511663291 511663301
    0x1104090c021c050903031e0c01060512120d23040309152c060d02030f0f130f1407030602040e0a0c091e0e0c030f06031618060e0106021c03 61
    0x5001c2e1107141c0015071040b02111036070019442d10780d01d400704024203070718040851008400003488600481e070b0307102d580e08850700f11081c07640b0190003254001c900101011780461120380d14580300c0309440da5024100c0c03001004000104000401162607940000f014060840161045102e41c0310100790548880801a9120700e110043d0700280c3c4c4c03901006465040102d0b0a80325000c000d82034580c5044500000700941c0204900d611040d50100411400e1690400f00340c1d001400050502c140742059980d4454041c145003000d0002c50f40c0c1c03101d05041011007007440605140500a44803941c2e101d1900c80080c0d0f216200d07203503902100703401103940d141da54030400c00d5003082900c81940c030601e0f24000200103580c04e6007288020010000005074162800c690a10510540030115a02c0c90501e003e41500480640064025401a1010030300d1740d103280300e800c0135a0500c2c2070001c004580b8500e42800380c2925041848502d00040c000907001e034000440c08480d02140211403100b201c408070850880b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 511665791 1250 511664541 511664563
    0xd03080f15030d1119050a0c06090f2108030c04090b0a050303070b1b0d060618080606130f09050718110d05060402070f0b0109180b150d05011104090c02 67
    0x70f04403d220303140050003943d408503441d01c41c5081d210700710f00b126001711203010b408109a4240c4c0190f80c0a40401c400c003000f210140c41d90b420404815414406192480d18a034050f621500e0010303070b43d0a00b10b0b0040c450400b01680d00014040d03032450104402e9003640c11510410b0803607401c10360121101d00d0600206c10030741e41c01900075424102240c80303d0031201000748c40c201807050224804002c030040a0001d100005004074041085407500800401c0d881d0b16059070403400d0b140314018004488080f0b0800c0d00130108444403800d0642c0d450f070305402001041d401408592404c0020000c00c00c010032080100e40754108002000310101d0346440955207500715128848004010030740550240350300c0706030001c00250005082203440c0e40c440302e00c0588550103450241345180100300040440c014444c0d034068040c03200e0600d03103a070750391705400c04d001070860014600741c044400b500c1e881d06220700490a400400920901075581103540c05035001e0301640180038100b030f4102e0340741c0f800001d400d1010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 511667041 1250 511665791 511665793
    0x110a0909050d0305281401060e18070314090f070b070803010302090c0705030c07080712030206190b0904060903021c080f04060f0c030f060e09070e0a06050d03080f1503 74
    0x40010001d08070f00503c801020310035516041c000c0ca0200340b080b0311406000b010030000c009521340500801c1032030b40205a00c01c1041200c141c0841c041d0b600e8000c800120f00f0300e2942d54800f5620390903410b802400c5032200c1800800032010803c0000c91000030300d1b0322040407000c10364006d9034913030301590524030440c0c002400d0300c10104010801802d01e211316641c46420fa015041c1802d079144d0f5041d007541c0c0054040d801c517a03c03001081c81146814018540185041c1c100940e0364201603402940b107600050003d00c180c52156414074050510b41c01200340e00c9001407480545161901d003d000800062205400610900d000000c00c41c64602e80342440e40c0260300c0707450165450300d648052482d0024400c0b00c2c0c0c142c4540b80c006914003e03009001c070b0302d41c0680340410f80c24460040d00040b83c58075440800c540407510103000c0c04e100c0c041000015144460755501c5941c3e10311080202404d0f556129580260b220050b41083c943d011031528050800c145a55402e074403a0201d84040c60300b100c03102641 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 511668291 1250 511667041 511667053
    0x5030606010c150f020f070302010b22020d0b060403080a020615090a0b01120f06050f3f0d050306011205010303050a1d0907051c0203160509030c0409110a090905 71
    0x440c00c10854001000c02180c0c0104090944101210580c0c204d0303640c0706c90315080481d143c02015028014112004c1d000d541400d8140d0110303543c0404600741e80c454000715580002c800c05601000d80000310700600240c161a03440c0e98a00c0d280020b42d2003000c051006000c5ca40201303035154012031840d0b4a10000810389440b84e103c0740c42000007007000665140c14416030f4030041c07480344e81c0c80c020702d0b45016556900054082c60101485131f2200400d10092140c08181610044200e000440c81c0d402001d040d510030029000c0720820b00c043c860b402101c1c40c04d20901d00d8928000358003e000718415102a81d4030a0000120340c800c0c4240c0d0020701005021a2003441420341c0a440341c0454108041c01d036503802c1c072003135024020904110342550004001600001c4002c020701101001a141c81c4406d5001c503d10314250003c60784c0049100302020801034000b50140240e5400c226044036018010700070000d801d924034090342c4140002e00554010b0300c0c01c00000403202403500c80e102c1070030381003000b800d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 511669541 1250 511668291 511668293
    0xd0c1707050c040c0c020406140312120a05040f060f0506040621081303060e0f010b10170712020c0c01030b03190809060f07030c1a010b0d1a120109020a05030606010c 73
    0x4060402c04e203c040401c440460111301581e21809070740002c2c00800100c0d90f2458040050600341801c218445020810821038050142150004140c0c00892541d0010301900ca615040301071236403040b80038018a00f003c4492401c039001c2d034405800f405003110f04120103561407000b01040d140321360500010101001d12038000c55800c100820802c0f01500318258116160b0f031307070001251801c0070a070640d0f170702940c3d081001580900ca40c4803084d42c120303090240c990031450001c0c82d105039500078107a00000034000c20182d41c0102c0c81c08030030380c11046e001e43d1070b643d49003991a035800011400c4d0b800139007000150041402c000c25661540304074040981c0b041c1059481d080404d0b03001e400980d820040411010480b002c0c880041c100a0384a41d1f5000d286800030300b8100445030340c4102e00c441e1401c0da000100442d858240495104050303030f860109142013000000b000c03041ca4081601e400c8000c0c0241a08040380c190b00a0300d01d50b20869076a030b000c98441084c1f5688203802c80394503000c690340696402c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 511670791 1250 511669541 511669549
    0x5010503041401110f0430321b0a06020c04020c070f0303020a0c0504060608010e09070f0f090624110a05011d0606030a020f0609010e030d0c1707050c 66
    0x501c03421034a00012940c25100151104194400701c01e100641201080920042081500d0100c40700803503400e01c50f10282c0604400c9001c001444004c0c05909525548200e58502102901c941081c054481d880140000e10181d144c0c0274a042c010100281c000030110945001c7c00c20380c051300d00560061101000c000103000c002d500107043c25070240b1685074005000030304202d211001e10f00c2a03010740030289562504140040d03544d01b21502c242d003400340511007241d00021040c115081d5481c030500c1a00c8005481d410605540c204010b0340505d144040365500f400d034201c1c0d003101c5074500c0412045940b801e00d4592180141d002030b030b00c8086041d48440040c41110303c0c010400303500d01510307407565441e41d809003101c2e412512400038140c40444003051884c01e0290a5204a0950242a40310f049500048811300600c540611561021804480c82d034450106503490810143c00c0303640d07001d9000b002a1000e1030010040701d0030420442d030300c0030f1612064280c620b096070142c010014014000c0c104 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 511672041 1250 511670791 511670813
    0x312021c120902150301091401081506040c0c20030d0903170703050c100906180b0601050c010b09010914060307212f0f0109030b0604050c0c0f01061e0501050304 71
    0x184c0e400019a0f0b460031a20506000960003844807070340015031507541c49104400b07000168010403041d0089c08103540201542c404c0c5a9020104a400240c00e00800c20142c64a1403072080180c801842c42203482e0044014615041125904804445e141c0c1c0b10880202e40310070301800700034a05001e0300381c4d4801c03103880c2c10003400203284241020703810b14881c00d0000b8905940d41d1003041842c0d403140d0b110000d01a151050025104862000040791031290700c0300c456000b03002e8201c5040290005014148100c29441004460700c000c00d51074055035144800d502900101c0d024002141a19004c01c01514001601c50102c5054403070440d80d00d400f40441104c0d01a015a05a81c14058034943d0441000700104101c03040d08200d1800120809280034008103043c0bc02c222814406016428004103000602d00c65005d00200c1d0041002c0e5aa0308810010780107108244a052158112510f1459810741000c0150b54101d010601136608180b00c1c8c80d005c40281c070803170740480c8d0100041000300c1e4603010343c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 511673291 1250 511672041 511672043
    0x516080c0f0409020d0302010c09050604080d0c15020705030904140f040609030201091a0f0c0a0c0215040803030f010314010c1b1406070203070c0b0304021c0510060312021c1209 78
    0x6001061900480e1045c10322043c02c500503503503455503283c50358114013003002074801640d05c0360920341489202c59031203003c10001411b000c0c0e050034010030000c01144000d08e804d2702c1007095480f03003941d203402c0c2e40d00c0e042614a02c0c1300b6030401718080b44180300d44011920412591043c11219103680d140d0a000b00500e18081c2d045548454900c0082554018520720040300d10310501030324034040b509086c4031400500019140f000801050a2641e4000149080a5011680902d02d90302c900c066148030321032640320b8009030202004201404980003c900e04890164440c2c44040324020324881c00c8400790780d14240030030f8030000540d03d8411003405186e84c2d648520800829550407915503460104112080030050b440061000204030001c010b0f00010103072965902c4c118201580095100c550a501c900c2c442041e1301c2d501c1c0c0500104000c00007160508180802680b5121309084c5c120340002c01c9440702500c145400448610000c3c1e0680c2036801e0203580f2000c6d11240c00140c14040c0c180100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 511674541 1250 511673291 511673299
    0x41d030405100e180105090a0603020306061203130906050102070602030a051c0905060f06030d030b0d0303020a021507030929010b031504020f040e011a12100815040516080c0f 77
    0x310254240ca40d000b0f100d03405031090302d138034449625103400c022403420300600c2d445c001414191300b00010b131070000d0303800d800c420b04884880510480203480c42c903500402d010440d400502800002e02a00d2550000e03054070000e130300b80c58032a92914016641d920070342209400003202000040800c50079071101141c14080b6000226220b409915818902201030700d11000c00c0132240244444d5180801103000c01198604083c4504001e03600081e4040812080107414540c001410014281c803e00034402081c1a035140801c4500702800010000c010a5000706c41c400012501015a02d00c0c0c50381024107000034202000050b828800504110f40018002c1e201d072080085070f0300c1282d9164005000f11b80103c611040d122032078880501c41c084410b9100e03a600103190382c0c1c55040709060100b12040008184412211902c50414807580500c0b2544180700c54042c0d1041c2000d10342d4910f02050080d8060411980c0200c412495003651410610400d50702d40e00c400340c00415400c08413850070700408028 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 511675791 1250 511674541 511674557
    0x4030b0c07081605010b0901080c06041503060f060c03090b090904110f030a0f120302032217041e06020601080703060b040207020402040b1e0307050702120a0507090605041d03040510 80
    0x643c0002d65010b41d840101c0703c603511850b20507441d007070081c0d03018010f01d014070041414140000c0420050710440c0910389208022881d94a8558000d400020003041100803901c0c2c0a981d42c02d0040421881c0b400c2100001c000d01e80c00189003080c0000d4408040f4001c10080c8161030716510142c40550103401c0b260441030381d1282241d56039051001082050048100b031050407ea03103000340009c0801c0307005c00d0a140c81801030000ba043d808102c0601ca0074900d41c4004080142d0800c50084144152280702c03400c0d00040104013241c0741c0d000751840030812802c85201c16102d88090380ca814090240d14680da010084c10004a04240c0003814071042c0a40014900410358000c41c1c00d130382c055008060400000200e4203031040e8212030300040840d004400d6030860a20030030080c0300d4420f0003000f038494041c00c400781d00e00e0682406900c0aa950000448a2503030744c480d401d10240600d40302e001d208030301d480502414102d02d02c0100750340c03e0300351000c1c618140c2000100001c1395400360031001000046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 511677041 1250 511675791 511675807
    0x103020108010e07092103020f01090f08030a06080703060f0b03070501020606012615010207060306180c0e181509040c17031e0304060c05090d030f210510080304030b0c0708 76
    0x240d06604491442c184003c444852601f00a884e10003028860780c400c3c0e242c6621800401d141c20030354a40381e070b4042140d603525145c4d4000b07440a004a50840011800b890000100304029548039200b5562001d405201c02d44408040540f188103902c035050258010000155003580b0a00c46546941960070300c40542035078a808007210004101c81a400114840c0c81010303003503804015071802040546000d000203401c29500e00c4600c9203409500c00da898440c81d0050615000b290880304088015200c840c040082035420192000251000382c0d001144094103840c41c10800501d80c171480d0800481e40285140502941140340e4403400a003560205105180241580702d0500c8406511002c02d90b840303041a0410074107c80c4000c0300002406802c0000345056100d8680d4070040d0b0b03402d42800ba0150490b040261180c009407201841c513607041082032406625150300083c0201245509071290319112103000e6928440c2c0c0c0006400f00210b4400100c4031040f4000400c06140725480d8a0300304001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 511678291 1250 511677041 511677059
    0x4090b160c0c0305060f091615090302181b07020102151e04050a05060705210910140411030a0b0a0903020c1003020d0b010f050d020d09210212030103020108010e0709 73
    0xb1034208480d142c04c00c07000d12222420040f1110780254286003e490205448910120b4444040c8284040c0203100c0304002c1a560140203140001e54001e080d4560f0016490130004900d4801c072640b03400442c01504441150b5202001d40702850350603001025040c0300038000c02c1659038000c0c03288040c1d00d035081031142440e0210103558001c9110703000411001c18289005424203000a060318100082400000858601d922011201c2c0705480c01c0000c040c0c640d1192a0700f48100043d00ca80b03043d040c00000d40b1810b891104039407045001c2c0f010907013035255107000c140c0c59600d51580500206003000101d8000b12181e417119201a03c680116142d43e032242001c80c502000c0c4250340d001281c1d0104000400c0e8815010301c41c01d0203024641000d100000c400007804a0155922846480b54007003500d40405020f51701a4140f96004180c103d8070a0b034074143d1a1150003801c10250050045407841500d61010b4030559043c0d0b0b5058513001c0e180d13030030903150801c4400010315040402404880014582f41 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 511679541 1250 511678291 511678313
    0xc01120219020a03080a05040c1e0503060108070807050a050607140f0a0c05040518030307030b40020304020d030309031b260c0c060901050d051306050604090b160c 72
    0x2101c1e030064882200c0307601340544448001425070042508110800000513007001e2240c050380e81c156414640c11044004d04a50540e1075001590036100d01c90010031440000119071017150004030450790b02603250001d00001510314802c0e141c0003031080c40158000354009002543c4401b002c4101c1301400d100031142032804884040c1600d6007441040c050000c0d04060040c540d01c1000507040718465001312840341d0b620700c801000b07801010b54171007113140d00780c0c0ca8040c0c20060b1145034040c00d0202d031440340e4100003012402110b030201d0764605601d291415460003940c0c0700f26002040b0740785120303903034078241d01900030035100320704006941000c140c0c641400c000011410340034040c800702d1074040c0d1606880d440344107900910201c000340300c80724614200190811151303100b038940760307190380850006030b03420b009419842c2c010504203000c01001060142e11041c0d120b0190005210070b031513086c10b000031500030b0344028056012080009043c03c810b410038a40c4201d49281401d140c0c5015110203000d84 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 511680791 1250 511679541 511679587
    0x4050607080c1c0e100804030206040206161505101e091a1801030309050d11270702030c0606010c2a0f1d0c091c02030703350405030c011202 62
    0x5040300740d4414140c14036170b900c039901e140b0745e040c03100183c1090f4802943d55900100000d100310030014503002c1908280340c441c0341d15944a5081c00c2d000c280d0001100c00303084100c2c3d0b48142c0107140e40c400030f044445401c0002d1401b40034180d6280b40c5040c4107203040134168403c040815000d007116400400d459000346801c030810354404904541d410f40c9801004140e840e03201c20702c22200205480d0100303001424400c8815411070303019080c0d81d06030b04406041242e403200c280c0010748450802c500a03402000615010f009001503507001d0752500300542c1e61f030b100c21801424008807504c1c110a40440c25072500d04d114149480b541250341d883e00e800d0041003e03904600c03411070342108215620131000388226008070100c840181044901008524942c136075034010319841c08400a41002d5450a1004601450300212648140d01c0b1071025109000704480c0d00ba1440d4411000340500d43c81410103840070b07541e0007009000070000040046540c0c141035072a50f200d80f942040303041d14038080c0350540507400f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 511682041 1250 511680791 511680797
    0x809060a02010906051f1e0b12180316030302090f040e0d0e0f0603060915060301060906020d02011e0e15040c0303080f060105040e1f0303080a1104050607080c1c 71
    0x4940d030b140240c05c5e01d0019141d60300c940032418032081c03142e50110b0b0440075607a00c21082d504004081c00311081e2003401c3c0e403005025600020b640c4000c07581c1056141d106204030380b44c40d02010f14100a2076503902c0b130512040340d00c0303911801c0600000d1080d00100314104009054407a0100f40b040003e040302d881905c021015400a0b4000c02c607a0f8100a4400308004d0031180e141111003568046907240c4402024548500c0031b900020b911401140c400c0d07401140040c0c01551650b07100c0b070b8050510f22a60269101501c10b8000d0850350074414092058030342825038900103c41d025900020142c40240c4c0311052600404500c034006004881c90030344154001e101c80d0800a01e1410060140b000141102c5512600041000550790b000004c8808403220042c0300e402e030b9510a02d50f5001200b11150840c907418440074004145035122551034090754803600204001c5c1d11a45488480b80304620440750410700c14800c00700481c4c0d000000e441c18544a070103031031115200f48402491440d60317100e47c0000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 511683291 1250 511682041 511682051
    0x90203010e16080c041107060510171b03240c070f05161a0301030b04060e030a030b03010b0f030c1021050a060e010506070f0c090e03030406050f13030c0809060a0201 73
    0x140c00c810091504c201c04159810481da402d0543c880300640f29820b406800c00d603c9501160100010500c42c0004202c400010107030141001c00301c41d210203501d21102054003420081640c94a000302c5d101d030500142c041944c4504084415401e504000101030390307501c040c02e1001754003041d03802c402000803071b02c200f000d00402c503070b00c800080f8407101c03942080110f218001c0391044201c0e00b01d402c5034192900f0107800905030380c8914004010b005d080201d51024003012440d402c101e038264001c7d17410360b04118000e0010300460024014000c00001c42503130700d40e00512020003a41003a01101c1c20001c1c861801d46408008090b55009000560a03004da8041c0d50300d0401000d00031a12448020702004a034988165141c000002c1041c040d03004007070701c0c500354454550104440c010f003000c0100b10342c030000d000d50b200c214526900c82d0011101500c0c1c181c24000014500c201c00500360b44640ea40c0740b403c500f1850a034a007143c1d2140554000ca502840c00c00c0105002e6031154041d00d0418416400070078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 511684541 1250 511683291 511683299
    0x905130b041b0c11031e060f01090b03030901050c0c040e1507210b1909061706040302070b07030e04060e01030636020d020a2904060c0204090203010e16 67
    0x100c41c02c556006039815030301401d07800c14542c0280c04200c03454001e400f002d586080c81c400281064003e10240c0084407040c1810549014080b0f0028840d1aa00413049007aa0781c403103c0c0c209941c080341305c09a041d002003002d000d0b01d40c0120301030908005082d040f1030000050b980820100c40400070008816030021982000c640d08401c5441d40c030801038684103107401405902a0b04620b40809404c1ea81612403c0494060b100c0503038801c0c0c02080c44542200842c0d5801c0190010300403400340241038201c014241070f02040000d81180119450343c014017803503161803841040c07500903017400c50400100c03140300103450380c40d402000060b00c690704640c0100d526516048048070129040004290001d0490b8080442e02d40c1c803a0000d803042d09442c0380001054030010780c514a2481009500c0148448040b9003600c044041010b101c811404041880100324490541400b48e4400d0100189211407510014149078112a00c0341d031003c1c0000c1381210000c1050b0b0b042c11000308503400c034081c03640350400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 511685791 1250 511684541 511684549
    0x6150f0f04082b020705010f05130608100b090607081c020f090f03150f060a1a030402041508100f090807030806010f0315092403050c03060a140a0c0905130b 69
    0x50390741c80461901241d02c0c50f400034081e484256030300c50503060004900002c0051401081140d660304d2441042080c695141c200c0a0220315040e2680790200500302e0000c44d0304950b9008580081200801c0e00e070601c0d400d65100ca2080c0e1107840c640300c118601250070350b20401d0a002a00300f501442a600d134450b586d860902c920001018030091196001712910350041640300d034000e8006c941da803200c034096900d4901080c2c41e200b4030f40c00020300f078024450301242c01d40b8110265010b00d200f00e03410b01c8441e01c0907210f01c900c0b0109025500d11900080422140d007045548100031002c9a400c011030b804017540c58282607600440c500358085030700541080740039a4030144550a1140c0d908040241c00c0070a140c220341c08405015420b2642e40ea0059000c540e21001900848202c2404240e20301c0f40c1c40303262085e101d00c44101424001c0c8078072030211307101701c4140c016000d031110100030640155a0340c50f440c03006001c05e521200c0034004449004180c3c0c2e15940344204145000b11408141c0c040b0010604c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 511687041 1250 511685791 511685833
    0x60c0c0a170d0c0c1e05010e0d020a0b0a0608030307030f0b090a140c042102030c03070807031506061b0c0302090106030e0c10270b0a0c1a06150f0f0408 67
    0x43c4041000c1c80310a6000078038060180f2032084940d1050070f62080007841d14030f00511003240d215000d8807444180c103254550000301c00110780d201d0380e1311030355948501d11100700360755160003100c099030014000100002e210f03600400350020281000f00b020b1942901140d12080e081c1e6a40c1103203a1a80c000300720006203001131a03080b41005c0c14031440c3c189080316034601c05407160032020b000c0001c81040c1c400d5560810891200d5140101a94425030380c420740c071a9106100e200441d808246090382440c004602d10032032003100c007251a424003a014198110500905542040718242d02c10100440543c65508046020700400d031000201a0322040390117143c18010100036201d100140041d4049560206135444407401318004039459018020f02c943c0b491006800c044258100865a030b4002c691110480c0101e03800703202c00841c00d0038980001010300c03000b00c0b07c01d40c104640b800042500301e900ca00500305c1c1d4040040060030491300480a18080e40182c0c0034a00c26480344500380c801a5603803540c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 511688291 1250 511687041 511687061
    0x30f0301230d020a0501140408060a02031608070206072f06060a0807030210210f050f01051e060307051606020c0708240c0d2912060c0c0a170d 63
    0x50280d0840d82d5a00150303101c0d04a0003000c1c10400804426554024144191400340041c5800d0703654614100c0c0a28009400449004601400c0440e409244500880e80240290b81c1c0d540a40800c0c0c0d030f141010f4840003103504d019206000040c0c51100c160400003884002880600007a2a960404204000c01c1022641101c1d03250b030400001000182c1d1045600601c406980c180841798841c0c1050750501d49000200598030203041c151081024000d0b5440144200701546840c07195903250703410b0146a05210420303a42d00300942040c0000351400c2c0d0b010350307413009540c0f81ca00d2514840030912040d2948a40d411280c040d0040303040108840140b0401026081107030007854501c44104012080031851211030b4a9071000202044141d03281c034044a40181c0541c4050003291060402848100c8121070544252440d50341041c8140c42c011521880c202c1c00540200780d5901c582d000450540c2c04424900c50314030524104100103408841c84064184030340452588070300991402500751281605 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 511689541 1250 511688291 511688299
    0xc0c0b0c2d040f03080a03111c09111c0b250c02040f0606080604140108280f2003010501050109030807050a1e03030b101e02030f030123 60
    0x40c5045104580c00080110801101c0364075120740480501c032028881e98000c03c8400240410110a02201e10002c142004403580c2c10070120808441031002d03801515001c020140084141000221580c1c1025101500900710407030390302034110000300d840711110a10701e000d10203101104240121002c2082e80604130410f659082041c507040c50728080c506800c040700f1f004c014135842c070a5444903488030051400e00982040090b0306c0c5c4c0b1028202c18412034101c0d04c994100300394101d0481013600c1460403601e81600801d140550611207400d81068102d03c2190495110b2401010421803010002c0c0340e0301545000b109100c000c003d1400c100c2c1f0551000b40a40c0c1403100400040e680404003008a981000c0d10f1a00d42e9414500b007030600c0c2c191000940010400d4a1303012910907000b500b621000d100303442c02c2100284203000e01540c442641d80b49000300d004110410800080ba01460b04003000f6403040c0e1b850640991030080190b082078121410350710504201c1c180c1140e022011401c0444115 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 511690647 1106 511689541 511689547
    0x1504030c08040b1611010905130b03010e011113090507080402330a0207060207031109060109080609100507020610170a050709090303050601051c021c0c0c0b0c 70
    0x1c0e10545810005c218200c1c882d6024103118030850304080d0800044840e0303c060300004098040e01c96030503548529824801310020b2040030031343e14580301d07401e0b102c428102c5a080c045801c0e801000300076140c202403004158025919a07489a8100c0c5c00c44103c0c90396251010303a0340c0c90f06041d1045035400d0006101043d0380741c000741544a541d9801c90340c4903030356031108036134803002c0b440040c040445110140c1a11300b40741c0100c507400708060600c81c0d0003d9a0f81c2c50540f45c1a0308444814154202c00c102014403913003402081d41019591004140908050000294000041c468045201c582e450007952188042c06580644c0707401000f52007150390344040c3d09029102c4510f00301c001a18200c0050240d600960540744405444507465084801000ea0507009500a0015028600f240c61380d01c3e01074012070043d120280700780c1e034405d00c2c00030052a00802c0d40c0cbc00501070080c4501c041c = true := by decide +kernel

theorem cover : BRFrame.Cov 511510791 511690647 := by
  have h0 := BRFrame.cov_init 511510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 511510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 511510791 ≤ n) (h2 : n < 511690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
