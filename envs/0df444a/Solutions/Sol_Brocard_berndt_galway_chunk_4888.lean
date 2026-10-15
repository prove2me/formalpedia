-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4888
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:03:31.605199+00:00
-- url     : https://prove2.me/submissions/53a4753c-fca3-451f-96db-6537c105c3ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 878956834 ≤ n < 879136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 878958084 1250 878956834 878956861
    0x40201080c03130201110a06230703060509040609150f091b031a0a1116111f0509031204030f051b03030403081b1c030606020c0a140d050a0b04110306 66
    0x20f0003410701c24445100609007004210700c03000700e5400502804081c80a0300306c450140303500146241a0022030000c92907250083c010354040c2d034409054400c5907900c41e00e40f003001d0804508140c81e40800ea2a028509611070302070400003201c0c107080030500003503e15140c105502d6410311550a180c0a800074000224500c01e107a801181c104480b240589400502074018800514042c000007070004002080b403064603910312085020340e4400d1000c801541c1404000000c008240d40164640e42d0041840390088016142c44c0002900302c96040340c1455056141e507001d90425114401040300d40010410200400d008610b0304c51a4241c1094160012942d24080d50100411190001c607a01c03004110241803c030040d1080300890303407a07030164000c058180030804c00c0c04000905240c00401c0c007500000c0d0300d085011000e4800310300b091800c20f00c442c8289282c0003469008040d2108800030500c2008410082030161b841c03040c50381081c0c41c1c0010303c80c5003201420702a402040c2000041c410021 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 878959334 1250 878958084 878958121
    0x2415030b030604122d1b030206010905190e011401050a031101140903160812090901120606050904150b040606080f041103030d0914060417220e040201080c03 69
    0xf8440c0c4400080d05509960b148001da02c5d0000140300c10a4002540c0450700070071811144544600c9030b103c00201c5440c111504004000d00540c0c42031004000449007544495804031062003c84d00b0291200350040c152018085060344980d102c0030b20100e40c00201902c0760061000300c0e001c484003865991070b5010842102011814011406105440c094114003140c0d0405030080c1130f83c0ca0907100c886901070514040c0078041003072180b203407454040036400080b0303038030640000c180f000c90343e00c0c0c042e48805045030200120b40d000c0c0c990000146649034600300c01d014034419262034501c07580c0d212640c0300b110300e00c20311288201d04014040141e13540040b070700c5070403042d400d80da030340036030b4031410b0241003020750340310b07482e0980f100003201d00c90b28172943c0c04200003a220315200059055017000c2142e070307a802600c02a040c0d07200c600a01643d5030300c0c02c00500120384000c201c0d000c0c035840c1c00001c09803144c03580d11440f5168082d4040104660744185159400b070794031501329084d070801101100d130414100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 878960584 1250 878959334 878959343
    0x131103032d1606090204110f0c06070504140d14030406021e030310060c0204110a11011b0813110d03030905010e070303120b130f061a030f07050d2415030b030604 71
    0x200c2c4ca0005640340c9800c007091103085d103c2c00507030b070f81c204602c0e510580d4000b50307150701c1030b014442c08610f65034880c60481e07085030b084050740721801280f581007180141031140211035012514600e51000002030002d807000340941d801800c003602035100c058521495130150714503940c00170420030001d00a004001016030303620745040c0019000f184040780c004c1051500c954407203500421103030b4045911118035400006c00c40000c0c0070000002030341d030503100f04030301d100c2c00400e070780c02c0c00200381c0a80700c148601c4a40c0500d40c491140d040d200c0110352003d030780c2a42600069141c038100700034410240155000030110900408000c2d00c0c40d10300411218854283c001c2c0741703444041c1010555100c0c0340d4081c00c0165120100540001400104010049840362404104081c0780c11100a010a410b0f248921159600203005641c1d451048810b0342c0910b6414000070740c0d801c1059901560401d50031548a170b03410b240503040c0d00b0201103c011044680c0100209800c200c44070070307152000f0442c103030400e500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 878961834 1250 878960584 878960591
    0xd1e0309030c0f111201180f05150c070c0e070e041a04050a0e0610080c010806210a030216050f10140705010b0f04020a08131103032d1606 61
    0x80d24046507403100d2044060b00c5800020010020b0240710716800e49030900403a100c0040b0420181c0302401c0c0c075800e0022487c0680001c03800c002107008040820b825038420b20946469407080102c00b0001c000075a100506600041040001c2010b4a103840001e440040c1c035403071061070301c00401410294443c04440c081c544400351080b0701d060441d800c3d482c0c840000c10901c118600031903828003d14503103050148070310510f8085011404000090019201da89024000a4105070300544020f100a0841500480f00c141d56a07682887c80c06801c0180750700b84054503a40500d400c00030f261201017100711040c0401e02d07004020315601c403a43d002c0d400c1400c0d10015072110b680001680e44204610b169200d114000070180704100c41940040550b103811610000407182d084140720481c010340860704045644038000c13441e242950700079140c5991040350100d202c121a100800c0c01d5800c038401d4080840a90b02d0441190814042c0412160440703d50742400d082541d040e040b040c02003000c0207090a582d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 878963084 1250 878961834 878961851
    0x10f0207241514040c0e090c130f170f06060612040510060b0c01180837090905180a0311010b0604030f110a1a090409020406090606020d1e03 62
    0x400d42c00007205065402c500c0c911042d990071640700d00038940c2ca0060b124600d0806100c4d00980600c418802d60303d0302601204a42d540c0d408210358942c0040008903013100c100c0340c0090a69222038004010f8908400c00038405924009218a80b5000050f0750300c0d241c00c0b03a81001060344510f019a15107840c0004044881d13240c5080c1282042c0d00c10800c604403600340100842d004c03508100400501062600810881c4e1403a20800d06038104034030010f0680004000d4001d8016086076070ba803440804100760402a40c03490314260044615044a0000c9103229408008030225882416440140107038405074003404044866100c03034030ac450040500c2410f4078107450000c002d60005043e0782c0c01503d0542e50354bc4a007400c2074620409032085415280b141d11011150501c42e0040b021590ba15005269807400d02d98807080b00d400004003c0d82003644d40c58842c015030340f81d004003002004003d01c002640380c00c12200900b403440c010741942c14801031010200034070455030f18018011b441071400040025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 878964334 1250 878963084 878963153
    0x30c070c051008061005120114040219030e0d0201050c0d0207050708070605041410091a0d05010b070209090a030503060405040c0302040c0305180a030905041508070b03010503010f0207 81
    0x30081c0d0441e94000c5606114040c0140e00710969500501044a200d0412950343d10112014410002000700f64500d00c5c0042218228800103903021003c000c00140c144541d5030101e003240004500f503003001980b200040002c0302010f01100020200c988000d00c071520b03080c580441d0320700c034502e012441a98009484c40901c401441481d016002da0000d8605040e51420005d2841d0000c2c050104602c0041d443e4412528040366841c00c104801d45403007091030301e403843c8421a40700808000354545402c1220f603841506601c41c10780a80f02c054000d544404041c010b0000038a401003c540850740511381043c0401d401c6421380341c1c40070040b90081200c2e0b603145490002541c13135600003074106080a0180000300c1c0c054101c54404d56000656100f040950895903980c3c10f2240c4025021480030201441075007031940182d125404101c0b0003007051907540320214500340055000d80194800072005111618081c0615001c40455850640c10061b80c1d4a9200d4040307501b131014800001d5a2081f8007130071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 878965584 1250 878964334 878964353
    0xb16060b0a0f03020f0d080315100c02011e02192402120c0309010207060f020a1806230403050f06010602010609061503050601030b0613140405010812030a06080a080403060f0c05030c07 81
    0x166018518a40f6410054261707009c0c4e407441d030640c0b4400e1a0000d00d05600354445d000120f41e0076016510100d402c5100240409071858031024a02140114181d005080c03004158400415209040072001000302041c0c0d21402ca526112202c10f2600400064000286040031036070004180c0040594039203490100a00912a03054010703d42030030300202d0000c1e00c4566000d85484041d41d2900108084405095400d0741c450303018150210728400c80699112401c2e0459022684c9940f855030314154407030b01d450380742140012922855510007030062110030f03070a01415006145000050103604d0070410a5102c1c103a05803201c100300360759400018150381c132070b4212100700c6070023405a65540f64480c7d0400c41c0c2c0e030703c64003d40c0c1006440340d000c40340e80d0506202d82030407100e003d0081c2c019840d040f00807841039803010f08401991070702d80c000400e20a0341805002e42a0340b01c1d039031040e0f9503032451409800b5038003140901e200013484c101c00d0f50030260700001126844041e800c1069600d130060710b000d1400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 878966834 1250 878965584 878965609
    0x1f05120709090c080c0a061b02210f0f01020405030c090717010e06012007051c05071409060f0901050907110105160315140d0201090b16060b0a0f03020f 67
    0x211030030207030080240407818481c40700356021342c1c090f02c92010084080c08500401c0703210359000140c8000680304001c5803002c19400c0188028200d01c2070b00f860030070720345070340c4810900b648507504501c0d0248510a000c120700076411748039500a5051515080000352a0f48001d101c0780d0141e100c410003d81003600c0362450700a8180350301d00c80001c0303503110007131b00c3c104038011145d032070108152222103518004401e20161840b1802d10060081504250078070010440006007006032003031410b60303039000481c1070040c20050403050b0750840b0403030005003c001c01100c018006c80d004d03070342580815070f0a860b01c20340181501c0c0261000e4006890700b03c0b0031a0344104070007080415529190a01541c1415207080c25100d280c1c55505201c03940d0b00e01c801180710345052040c01c25940001091070707810b08042082520f041d00504051907095903c6078000d07140d84c0074001403880c2003c076025803020801948070b0746142600a4030259a0182450000400c040c0c8070301020b8030a20903a40c16900940c0d41d881a000b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 878968084 1250 878966834 878966849
    0x6010f06030f1103040c0e070e130917070f0c15020a1403090a030803010302040f0506180406020d020d0c08090313170a050a08131d061c0606080a020103051f051207 72
    0x4d607440c150078450000f550034022481d1010066000c502d803e4460303070111440780c1c0e00a02c2010710030401201c460041c61100c108070740011390001000440702c4294060403000f80102000d0901d03003558503058014181541100200002e04661002c80e079a00044d100c944603840500c00082c403041d0040c503461401034505490313002110303443c08000c120a410185049038404e0318240401003d130b00a80040d4ac004445c80e039000011809240c240703c002e460415041401854010f00d02080003580f00b0580c0e1050b140380514649915007220f130303182d020782c1043c4e0280d50440030b941031a40303401f0505174101452042c20300140e28200c0ca800d0351481070095801c640e41c800704607402c1c8221840c003188542c00c070044030003c1c20b040c0c0c280000d18032a1040008070002000c410101c0340d40e41c8000300882103414503100c400395021b61040c05d00007103480c49884c010301201801002c00c0c0ca201d00c001002c2d280020645403d118440b006801c902010f501d0038025105c00f1a0b08401c41241045910701d440c034594000360 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 878969334 1250 878968084 878968087
    0x20030a02031e10060506090d030c0b0c03091e0303060409170c07051908030a0804030e030111030126060403270b0301260606091b0f0d0506010206010f06030f11 70
    0x154000702d860840d00064101806550038002e0000c900302c01c40c0e02d107218a0350002c05c00c01160420340b03002070030f01c501280701c0d0401019002c0c0540720f181c06100d04898800303c1410000034010005820410008030b40154421001544180020a5143e00019244c01d01854584200008110440b01a80c105450072104262100520301c0b059a94400c58810a40295110202010002407014030041a07038922401540b03043ca4060741284c1b01000208244c0c10080c2100c08080e0643c0d081c0225a411704c542c000d02e80d200e504000d6004540110b15468122038880d000e211324000c48045550b5600c107406062a4002c0041d450112314800c1c00c1000c508100c004a80d4040344d200d00302c4010f1810b03180540e100c840002c0e5002350041c07104c00710302d144c001241e001030001034041c9440c0b680031754270521228480c1079802c040e6034658001d4000c5603c80d4608140400e034441100c100f8401c0a600010906c003c20042d4940040d820707102c81140030b290300b0180c81c3c409203020f6074560b80041519a1407820002d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 878970584 1250 878969334 878969353
    0x4020903030f0f1905040b070b0c0d091a070c0b0c03040f02210d05040b09090709091a1f0c060209010e150712051306110a06060f080106080102030420030a0203 70
    0x2001d942c414100510044d0070a403101d281c940c03107030b0180d80a0701d01407500c061070700741591118444403400510f61000004c04108586030200c1c02e0140d040c0700d0303104100d129032003a0740c2c52010510710b000420b10020080024820408113110307522040e04001a03d200b1a0780303032511304000d64004984131010350480071500700401200c009050b038000420741394046c1e41001d056401d017200c65108511606403006428000c2944510b00030250b6908040300d4149540010795a941010540d10301c1542039642680891807034800307041c0380c07519070a424510004241441603400c0003403d00c01c10440081e20290307000c52031081c00c1e40991100403200400601545100c013004601c00b040c1d42c48244111454071441440600c01c42c007680940d070007031034054040b120060414000f1950f01600012925140c4194034400d40803031154400e04002e094a6180b0011140c00d003d00346003074904941c44905280e20400400020540d5880e14550100014140308130000b14900080d00e05110f80c3c10103907242c002d00c0c000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 878971834 1250 878970584 878970607
    0x61f03061806020c030711031204090c09050a0602030405030f030a0207030b0a090f11040e0c01020c0f010c15090201020706020309030c0f040e0f06101d04030c080c011a01110307030e04020903030f 86
    0x10b0b0008511421101d0b04845054048c1078540d01c020311300b40b840c80400c0c0400d200b074142a400056018065142842c40a65254005100756402d94407020242c0c000050034091030500340040201c100d034040082d483c0440300c10700203690f11440d120103080c9a961b1404074000c0c100c0c0e50400c940d06a00705070308800840160900420086480d50124420b51810011520320345000ca900d07500c1001c141c01603c100c04d50081480354618030b000b0018100805032348020002480d5036941c035080400d40000003000c0c4c249100292400103113070805825507006210703405040d80d00081d60b55500801740c4030103144071a2003021a0250060f4560b10940c0e0007021402c3d000301c003000a13207920424080404110300d5540d0741014081588400400c5205250040001e0100703025021045941d48281800b600c0c044c424901e00d82101c0d140c034605008180c2c840e51040750ba6910140303030034070510801c0c060b43c500096a90007501c1c412451003070601454020403412003940d8148103541420b02151040b5980b0801c2400303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 878973084 1250 878971834 878971837
    0x130c02030a08180604110310020309010b0102071a1912050406050a1b140a180f050307090605092701020f030f01080604050a0807050a020a17061f03061806020c03 71
    0x12440002200e10000820b000782203810f0030241d40066014140644035600c8480031505101c151542610802448091030360701ca100452098540301c000140c0343d00040002800c020059101c0103514030070420403c61040401c04940c4800380c0c1107254001d0044906080c1d4101c101301c000840e00f84c0c0340008100901806400c124844d15007000104080001070f204400e503041007091400006641160040100034110001c1070103480c3d034108444005071003c401004640b440d000b010a50300c10031001c112604080002e403020303000341740003844114100400b04081d41c0300144117040c1030740400034140404103102400105201a4030081d5502c440400300e2605503803055034840444103080000151252011503100c5c01994458040c0c00201000d071145002030300010415925800398174200310060381c0368415980144050151820000e13a1106d5043c2060b000803c10741001e19044240710b40000703c4900c1a0070b0300d44c4154002641000800c0b038004410315920300500d020300c00150303400702000000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 878974334 1250 878973084 878973097
    0x327060506090a11220b07031101052203051605010e01290d080d11041409060d0506010b0a031121090d05040302040e19030905040b0901050d0b06130c0203 68
    0x84070b614440d159500050121028804e410030311402c107210041c006065216610668421400a0301426031200c0c907000d03050b0311103c2c3c203c01007655492101c840520a015086d4000040b162010224068000d00c1000721041c110003010410000790714403001c0540680342c411650801d000300712020105d1082802460350031103940342010441e1280502c40120000d0301c09420001d00b10711040029659541d1840c0c008440807001c0030303210300c2c085814184110250000f0641c0d200c440201039284d80502100344005416213000c2d81818242c1c0011a000103201411170340c001164070742e2030141100c02c82c020020343c0300100c2255000541c20b4402c5246241d00d20801082c2080b0b10800e4642100f881c2da81d1186025034008a8002e2000704054605a40916040c1a004041d2080e268070b0080c840d401300380104040340490207d0905010790b060520400030300700002c1d0303a0081320b54103140c00280b10a0382c8140c010035008080f000191681c541c0c080030a03440503500030900410182580182d125000320 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 878975584 1250 878974334 878974339
    0x507030c090803030405100c050c10060302010801140f1207090e070f0b04240e0904060e0c06070f020d1103100905060a0c0c0609050c1201150501020c0306070327060506 74
    0x80c000b08801d407000c01200d0040e0351144c018038104041d600341d28003400a4180d00400d1040a00c01c00c4416a824406a0301106000c00c00150b900d085100141412106030445035000105889660306501c54100746a1010012210251a121071104051426450390480444103003030034501c58034003900051040c1903458002030034055548030311035003d042c0528402c24020121107107600ca074844034003455400c0884c0514122809201007004908032070b0055030210340c81541c0304044140104140701d649942d4208032499440c1030125102d6080b2100c000c01c0c080c1c0301e07105602c0b9000800c401d0001411004802400b0f446d800341009100d032000304007140044d1018041c8000240d0f40710300394420341c1a200041e0300d6140f02d00d80315489090003403030041c03021280e070300c110840021995144d011a88441c0b8000001050101205a420000e11003d40c400360640d0b200d17242c5090f2980d00403541d150300064030f160000b01110600f0070052003400d031070820345000000d0140f900a010150300014840c0f50706 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 878976834 1250 878975584 878975597
    0x72408061c061b0e0114070510050c03090d051e030603070305060403020a0c0603092a0f09020405031603230102040308070308090c150a030b060d060e070810050901170f010507030c 79
    0x1010f0705440e1220b0604440d40000e442960a8100304031003030250076040e0140b011508844240c00320402220b0055070032810844d4003200f00501d42604100070000168a071400b03074200003121018075156003c20212a500d5500400028200d84081200707a00a6411400b01d501d1801c0034100613407910162402500d0303000c9000b41c0441c68900a0264944040e480805014240b804400002500c0c1862101c1138071408000710001d0210390107a01d503806000e644400503583d910f0607003094a022801c03002201030130800034040010401c582a00f10300c2c2e152140000200c080e25002c02d900a20803a04014090f2602141280c103150b406400c1d2889400301c10119042c5500440400c140070f1001c40317150786d24907000c2106154481c425044400c0140016001c0c41c2000b11030501c0200781e03041c0b40c11a074100010070080201c000d9112405a40000012050346c0d2481d00701008a0740e000c40c140107242d0348072035a400c0c10780403c0c810000c516084c6148002041103023070020004000d08000004030001650 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 878978084 1250 878976834 878976881
    0x512012a08010b0405090402010503090f1e010e0105010e07050705070b0406180501112d0703080c0606120d1803061e0c030b030616140a02060108072408061c06 70
    0x3c0c0c0211001d40390001d14454450b940c550044405138002481900d450248d01084034070480e0030000d0300102c3c68a500c0c6480031b40c400c10312050860303094080c1da0401c0d07810f1200410250000150719500481c079031030050368500b0a0b0030414607015041d8085120f00c1c000080010360303550701c09514020746444507a01da11140c5d80e9801140e070020214071000b2160450300c40d88032001e4802400060661031151080c500340040541d541c1021000c1d031050700c2070701c0009400d561117034042c0b000540c42041222140b615048043c40c59030346c2c9078207581b40e4042c0b190580014032960030120003a801103034846d00a10548100c201710f12a504a42201343c1c00c42070800c012071030554000e008100c9110360180c01004c1680d43e580e842c404071501c02d022101403044210003c070342c07444c50784c0041800501d50f400400f01549003040151800100da0300030500e8008000d44914040032055002c0410016880c1000f22501e9041c000703913040354060702d003d04a81503013540700300300261070b0410b2403111940500042400ea = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 878979334 1250 878978084 878978099
    0x33171c030504080d1a060408060f0709031a190c0f080108071d040809060304052506090b0d0b060c0c03120304020906100c29060a030c0512012a0801 65
    0x2181603600408880050111802c45051a84581c03170a04490121010701c08a5102050940e40150008a03081c1c101c2c0003084541c24840e41c1e1a070700300c011482d10581262842e211110705034021340800d00e17408899000b05945810340141b910006800000410550810760300292052080c4160300c400710304481c0c00000d0f009008250318003100c680002c0792000d65010215288126001070080360030000a00000480d9295075010318491842600200024840507116641031241000707030010959038140203010460384030744808121356185258a032620302c54201c0402800c541c0a24a801c5080411103001d400800241d00c004144190140c2e0f04140d030030300803004248030454010f5000301c0300c1d20118030715007000e0047c1e4405000500d810030480300701d5a26400e00c13000580107000e1610010340032510802e581c0171041e410803c2114040c440f286140d4402241501601c50140b0840ba507030035140e00b030502074000075150a40c0c40c8111402030a030b001004086e000800c21030000515420012030341c42d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 878980584 1250 878979334 878979341
    0x1200a120e06010515040801050403050403020307090504051b040b0d03031506021902012316030e030309031b010c080c061510080c0f2101170133171c03 67
    0x400107005403265a0814007030001c1c00b44152826501100c0400002418180a02c0354501545c0b281c3d44240e5214618010103181042c81d80241c0c036610f10705000d100020703400003600c2d100c0300c4451401107101b01220f0005401041e0204c0c3c074036001903140714000c08056169001383c0741039030109825488513860b403400b240e5074004480703240e0040c41015542405903000341140c40b41c4400d0403940718051504105140342c1034016050318051001038000034030400d900310085031410f980580c001e600307001410300001d0fa00e451500d03d03460510325805d114611030b4030030305402080c0c6420204480d03803104560300031545d904040340e04401f4400480e03042a6940743c04210303100081115a18a06580c951001480f0b140e404401031140a820800c07001c05400a00c2544c0d2030300d0840c010010b41030750315240c80c10084020741c080f22404c607490860850000040c5a2021142d0b060401000c01100c0007403071010030100982c0c020245c1d01102c0040303140b000b51300281c03441030781140106118042100b1007060301035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 878981834 1250 878980584 878980601
    0xd06290907031e09060209100c050105062706031c1125140d141c0305010b1608090d23060c0f0c0c040203070306050a050a0b03071101200a12 62
    0x3030001001210f041c200c5540010b114140100310051131300d00240d0000320281458207000c2c0205910020020600c4401c1c80364a5020784103542e203a43e03201070000c020503604011020b00c801551503e01145441e102049850034030781240c0e581104820304104060319150003401484114400c1084014032150000d4500141b40100010f00481c1c5042c110000d20b08140d110031150809541c90f040c0b404541d02c901000706d201a41c80140c5a81c07000b0b1070401d40840c0840c80364000b80b5090400400040a204086540200307580c070700240c0ca250145020a11303031050310001d5500031000550703a000d110b01d015240d4072040ca10350350309a51080b1070018176100c3c00c080b41c18190f1403006010704680380300d1901c01020141e50100035903200d1400c241c0010f00701e80058442100081d0755450903c000c2c2400540032020340412181461210310b410b24055152000926010403c4518098403440e840c007500038520003401c40741307007075203005801b84850855004080b641e00010f8402500407600c4002c0d200c0c4054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 878983084 1250 878981834 878981861
    0x9100602030a1b0b0f0a1a060901050702011202030c03010f09050402060301030308090a051b04060801020702060301031e0f03050d1406030a0b090f0f0d02070614090d0629090703 78
    0x381510584152034038112000c42440d01c000f407040b5500001c1060074128840d040c4201034101c035091100c803440403201c020800c40101c90a41d82c4031013181d5101c400765025004246010380e5100e44510040340c010180190207200907001000307121403e00d441018606903030658401e6891190340308044000d030b50059401a400c044100010300100784200b81d11903001403040c0407168810b45580e1110f161041300fa0b400400f51001c43c400718070754500341c0103203402009024000c0d818108a600010701501c0184002080000c6140700703100786100000c184d0150540000300206100c042e41400303009680b20b0f101d6011550b144c4100b107034864529003003550013244054010b001c001c0041d95a203000200180050005101300d000044216008010148104407150041e001d04d08001c0347c081e1a0800310f40080c3c050200e405003602d801c00d00c6c5000d0f80c2c14006d04584454041482e8203280000340b80500c80200000c00c00e00b0b404001100c1200c00b80c80c104410341d81c0a5041c0c3e12075404400711026030503500d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 878984334 1250 878983084 878983087
    0x111b1020120604091209061d010207090b01030605030a1103010605010c1509050c03330405120a031b030c0801051207270504121e1e0e03060c04050910060203 69
    0x1d060104022032264440307009031000540080c0c68807618005080400e45000244200400380080742d84041c1c0c10480c108103041c1d5850440310b07400043d4461000340182c000c1590780300440c0c84582c5c032036000301d00182005410380d043c103112800c0181c107480380100d125000390b080620000710b9510610805060320340103010b0b245c660300b40ca00f01202402c0c83d20310650300c0d4440ea054000981c0c0d000c2c0100f100b0050300f604032002c4c501c1d40403602c2180010441504081215480804c400f05601080c140f040c0e4001e00141076565101c1c40c0d041e1300424660458030013600380041c02c2810190141c4c0900c8660b9600c0d12030407140ea0781d4404001071810781c2c0d01c2050850b00400d404204155400302c4000c4048000c1c000e4280c0d403c45000400c0840d102140e040d40d4092400c0350f070ba80c2ca00d401211996480381e120046545a4113854030182030064141000e50220416a02001c41700384200fa42c0842c80c44001c0503502d40f800e10405900254202d402000e103d0701a41c0e002c1403840d140c5140181c201d494540107103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 878985584 1250 878984334 878984347
    0xc0a0e010306200906090301090c17060912091212030a06050f030a02030c10030b0303030901230f060114071401060602240601110f33060f04111b1020 66
    0x311858001740d1103e45c0540d03da10395003000403841d401d03200160900e01c01c0cbd1080c904826600ca0710303024018140128607004034098090340f030b038558110741c898402950b2410720543c26402040c5071000007011079140304408400e000d0840d0faaa0094400c440c0100e4040030140c005e101016120409020025850f0b8030004109420703003089445420740c01c2081c10002190300020000c2030555102f2211100c0e41d075942c007519100c190321415006502e40c108640201c080c5481201c034003421102411107810300c80c2c000502d4940c469101c040324000c6600490402c0c0343c28404950501802c280d000f40b1015003c1d00c169070000004200300354040c54151010044607889400041d1801d04c41d80b140303151940642c1c003010442d01c01c02c000c2e082c0341c4240c64214001000c1e014150700e8131880225074003035080401105210a9689081404d900100f01300d400080c0d1000c1035041c07600c54410281c000706820a5021500c610210219000c107005641520901c848101c1040403050b045420181c05814003060180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 878986834 1250 878985584 878985589
    0x21306260a02040503030c03070b070503040b060d0f0602130510020307030905041d1f1d1f061d0906070905030a03030c120204141807050711030c0a0e0103062009 71
    0x22608011075500c010b1805456901081c11948034040202c100d078000100c420401010302200b0394050300d5854203070f003107041540d5441c083c04009494584509030308007500c410700c601c503501c100445611440c215500d0f10b0a000c10042c5090074468903200b46050700c050700b0b01c1400030045902181d41641c3c2e26034814200402c010052007030280c1c001941381010303540d20025004014450b940300c03a952800d8440032804003640243c40c8000242c030400b5905010841225400003055200d940c03045074409040b03c81500208004c200b40e40c003c0c0780c008042e102117180e1072000303910280121805e034256203036950340c0315007a100400540b07c0c068040c1d010312900c1c0c2c08248240c1c411507074071046150620300d5031007942d642000e98100c0c5e08335401c1604030040740304c01454500c9810304000c90003030100042c0d1500319006410b9000e41600074003490a0025032489641d820722080006440091110b41465200c8180614404090104079002031508000c03100005d001040001d440403840419890641d29806 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 878988084 1250 878986834 878986907
    0x307020a03080c0d111b070308040b09130203011202120105070915022119031e090204020c010e030309070f0819060f0905030a0e0a0302060f1b010906021306 69
    0x2d4900c114003403212000c5465030303004841c180c81c220740e602525001040f5182024045106d610700b0b043d448000700300001405002502c0498540d881c04503207401c5403001007140c0c0510044146101c1c3d00c00400403c41d42c440d1fa81c040d204900030b070384000c03000d106200c2180c01ca402c2544c0c49400304900304002c00c61350680710400c05134000c451040e1a8814031003540152403030305050300040201c41c00316a900a0040380c9241a00004040c9801d1002c03141100340316880880410455144a84801c40d110541d102ca40407100100b0090000b040350041c001c41c00b41c0c403500b041d51921054029002c0019005600324241e41c141c8075003101a04000e00e01c840354000301d0b0322442c4221109600c9240400740c0038a20f100d0284060301071000303180d40d17400300b101c020305041414407003a1240d00108024009a25103209590303050304000c501c1a40c0d0040c00011784202c590b001120041c540c20109036500300511500582400b20608851040e040c0d00c4881c141d61100c2a000000c40c614a42d40480150300c0c0c0c1c642 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 878989334 1250 878988084 878988091
    0xf0905070512010e07080a230c040305150a060806160f1b11040c0207060905040c3f0203060904030c03031d0f070b25052e050a020307020a0308 63
    0x81142c40c1c200c4908500010603001da01140f0f003050300f1800c2200664100058660288007403000b040382d6500125400c05001c858510000d49624410020780f9520100342128040d50300202141e0031454004109145400110741c0700c544942028400284504001502d078040c003220172225041940440080340d055441000c00e40421101b21551120b11469140d00060a4003500403000310f03601c1d240500040d104000e4000085510100013003107074582c825004000c0c2e03502120045501c6181c15022500302daa0040c0d00c030030751740c202040c1100103003d4501c3e1083c03c0042c0203401605c0044964024101c3c04110786094000d010b85001400007846092204100c91003801c1c0000c0035211600c0a18946042540100d01613008032110402007d00304580001402021489485c122000d032052050b001000301510080000030440c1040100078008604602c460104265007032060006502201804080d6400803514045c04120301d0800e90089a00c1002540c0003000d402c052a6002c649071035004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 878990584 1250 878989334 878989337
    0x705040b0306042d11030f03040503151f060801031703070f08040606080f15060a03082a030a1d150315040219090602060f040f0b070315080f070902040f090507 70
    0x580010400d80d8404c0e0008041c0c01500c100140d031065005040c0781c145c1d01c036044019a8002c0c0700c10446943c1c0081c19110100080082c404140ca420a547c2ca000d480202030041031000f10001203020b075840381d00f99040303038044e6a0415a08480100030303101440700b95690000116000c1112150501408560340c0083c41003400096040d40d4409460624035401d181c10602d40122501c11322004a110000340c015008850550000b880d59403402414800c0c090001e501c164900c08506208841a99040501c503550701500da40ba01f600030000c02c00003500c414001348003041c9000105a081c1401003207409401220b06502c0c0d519045161306510303c0c2c400005502640030800308045640310944201e510f82d840e1030309000c50f42010300290806500602c1c04c0c0c05071588504101c081450f100703540e100365030040c2450619484600c1b045014000c0d90183c04540760000310000740900000850002e40e401140980d5031403a1220400c8099104505ca021003c1095000c01e01440405601403504003269 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 878991834 1250 878990584 878990633
    0x5070b03060d0516170f07092310031202011802040b13090b0915040b0609040204141018020a050405100512041104050c0304200319060e0705040b030604 67
    0x640e41c81c0fa140c0400380141e801049814072040000b100f100306410030202d07960340a40300c00c16103803d425503111000d100700079540340c6541a25040c9104400c9a0b14500404413202200e0710302044030301540c42e55440100c0700c000d046100354410354410b220742030442c883c99800000d01c6901d6000c01002c3d00702c40540b20b921282c98842c00d0255801489554020343c0300d451110f00c107142c264009070501c1101816061490980c0082200151801d040594404000c460007440fa89403400030a00900d86884501d10b10b8030788405101e40c80e62655410812107004061035150b802c005091402030b40954034100300451010321060203540f8056200b94464211440d10a05001c00303550390030300c4504151403d03a904244030361b031704070a0304080c012540e116044030502441c5003040d5035103010f1031540e4000c2c05025032840213402c500b0750382440700301e01c816505031221056500a040140c0101814030050501d48550800000e550404d80140041224003c014100c1541c0315201c21140540e0341c100c0e42c150400d03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 878993084 1250 878991834 878991859
    0x91302100e01111e1c0207090e01020f0307020a0210021b0409060f1b0305010f0501090905250203040e011e0b1e0703120b04060515090d0f0f12030905070b0306 70
    0x1020030140700c031581389200496940ca4105102030030000031082c40e010524546a050080680010705141243d140352000140c502480c06d00500a0041d00b40300303030801c4400024041c3c001d0340050803640c880d000316810310210314520170903651100d0405260000c1c0c8071011031f08ac55031619a00c08005107029040c0890f040c104030020104603803000c98025280303000c0c8445204845e900d40b1074580900400c04254521a00b401c00180003116a0b02c00d2041c102d0711440000d800c0700c4800181c1c44a1403054261001348401c808020f900e981043c09000d00f0040203a000040c01041402e1114200b501c14410350400781c02d1030496a40c1d5441160316009511560103160284c483c0c900091403005d02030b90b45c4a40c10303501401d20f00306441070149654811401e0100600803641c1d000c0150a114010705002592024218080343c8149041c00001c1e00c8503052030106018410303c0049401c8043c45a0038212000e10710305003c0d000c03540303050710241980d44088028401041c11074002e603080765005010302050300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 878994334 1250 878993084 878993117
    0x5101211031b0c030f0f1908090f0c06221d1012110111070b03040c030c15021b120d020f0f010218041104080a030c02091302100e01 58
    0xd01110040c0c010000000c01c0200b0a1081071400300c034070303182c0100740386840d00360541c0c260782c4c0c0107450038500c4813840013030313421141e036080e1007202c0d1040e8141503c0240300b09a500040c0c05036100700c07401466030040c030000d980303040c80100e43c003070464030002d12207810200203c841c0207a145209070b004500751a0030f580442c0a00d0310100d030100506e0807481040c450724001484c1020088c0a41c4908211404014030300d0005e0001100001184004c0c64010344071114403244910b020820380c4450b18450f030003c1070100380803a40054005903402000440162680c88a140e00082039044007840140c1240751507034038030342c0c0303404482e0707104034005108001c0340100f52041800d101d02100d8107030142c2c1c003140744e801c0240c40510061a46084404c000c50403c001c5c0340300201c02d11045101d00d807107070343c0e60b640c1c0e003140c03e180c1000c2c5c0d400b4049410480d803201d403940c41e025102a116003009d900c04d01d10800042d0340c10403050003c00c2100d5002d081c51201118100c0169200741159907058140040114090001c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 878995584 1250 878994334 878994341
    0xc032711040e0a0819080708040b07120903030222030b0c09040902120607090b1c020c030c1203091612060e0a0206031005130905031c0f0f0b28051012 66
    0x1e40540c0d000b594682c0700103c207103051011504030005011014041102c03c64203c403c103a03105400104c030001580d0350107001c33261114074135403100c212498203603000c0505a059015101010000e0108000701500c0c403880c003400901c5100003052108440001840e20701140c0c05000301e180d0113400070a070008141c0c00600d1400c81030742109207943c005010000c1c2a580090000010298034103c5454640103400c581c103c8010800e490f03c0c55500002c100780421810000c40b00c0140030700c01510411644160021944d0b030054072014800c0c85290b080484400f0104102402c0340c07000024103048030842d40d6954081c0c00a000c004446000b04112880980ca50500451140b1003428140b0a114207100810180070440840041201c0c5003c101c0d10000c2c5000044035a9914401046004203d60320301c0d850140608008440c8242d0802c2c03003021040603903801c00147c418045850942142d00100a2030030480401e0300121804a0358104020500340152017050f40c10103403501c000d0000c140d90b07021054 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 878996834 1250 878995584 878995603
    0x70b070311010f0b100e030f0a0503040602070b0412060e2b1d030c040506030a1713080a05101d0726060f04080f07060f0c032711040e 59
    0xc1007030051101c01e5581d080c8101c0000159110b02005840880004036070b100d0011082c0400b40700c210030040b86207940070070881c01070044400c101d82c000d000d03500e803140e12504030340301e80b801502c0740c0f050200c1c0300c1c0311000a0700c084d100140000300360b21550f501c0c0c0300003401049410071600e0003404074030720583c0161100d0199140040c0348400340780c1d00100c8000c2040035912800d200d030108000510215a6020070690100201114045601c1c0c9854001904080e2030400051081640c4413000d00034108550180942a044c8402c00c141c09031742d007107616160072035800c00074800e0304482c40350001803000754041c001c1182000180c2100141241209280c8121600452030407100e040040b42d0040070710391900382261740d42e0301514450400020910840d5000340004050311400316842c90008030302001d8801840c8c00c10024018031a1840c201001004601c103da400642400403101640107594034180c8207a06420002030008103a0326a060340f0070024031803691180c1c840e858202502002c100c030205 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 878998084 1250 878996834 878996837
    0xc0307050c03070b0403080910020c121506010c030206160905060a020601180905030a0c0f060614030d05040b0d05100b040e0106080603010b100c060902190303080c0f1b070b0703 78
    0x1a0741c01c205071800d80e056000c40c00c051810002480083d40c003600b60342003814242e034030803c0750000f400c0581c00c0c0064002456003003000d1440c4038a03440b40005040301da909030700054000c69266400115110441410050050792040002c60f452540058460405806600d044002981c8440c0001d84960011030340300016880400103005000c5441c48031500303c10400300400c000e000b00c0d5030710fa0301c90085c1c0682409109041c607a5a00f400380140018142e00e62009080000944031410034100c2132041880c0f500920826440034101c5008900312030544000c1d01d041814804c008501501a21008100c0b06079003600180c006040320500014002401208207842d0f655030402600800b400002041c03a40300c1d0703060102042c110b8580b80c0100c22461500d1401450b1050700d03040130005000b1194009402000c6507000000b1f00319403c0f04001035034800d0761030a2903a220040040c03a00c0c014200c2c0300240d05400c0040351015101e4019584128503c60700b6518020f0751600040400c3e00b2a000680 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 878999334 1250 878998084 878998093
    0xd1b09090e01051b07030309080f040905090f1009050f0a08090111011e0b190602060115020a0c0608090a0501020c0c010f0206090c2407291306020a050c030705 70
    0x10010038a80107181118210300e000b00318034586601100c0e580c400b0107101e511100b0300015900c0501d8441d800400c2c03282d4120840a5455000e54490311b40d075445486603140039031503d030110720300c41d10100e1403080d800740d914000c00e0152906000c4000401105004958031301c01c2d054900504d10341800f030340700b0450203000000e440c3c2d032441d8009000c002d10140048ac1503450252244d08040da44200080c0700d154050740050b5548a10000c1800c3d0007150013294081d030040750001a1346a4009282130580b101c1c1d500c00e0b80c510800183c00c0e6a45c501050f402003200c50350100c280700441c1320708952070b801080a400c8400c00301d161f855140c01c90f40088686480754011041c20740055800002c010b10248081c030091640b454504c0846440da40e00700704092003000d6040384001321100b6900c1c00b000010300d0750035403540c80e1481d00d0600e5030880079045154062184040d04074008031247d1420744500101a1410350b101c085030b850400a43c402c4c100744050100500c514000f181c4104064030b0994801c10041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 879000584 1250 878999334 878999339
    0x1507030201050105091006140409090f1713050f030a080403030e0306010b2b1122080105040c120c150f08010905090a020d08040e04030503010e011d0c0d1b09 69
    0x1d0079114141c20850261a03260103010032601d100714074134129240b80c13400c16203801c4506a00c1e0914810b0f43d02040503142050100028080004980ca42503441007940790b0075142404072000a41c0122003080940d030303444d11030401c100d0078090011403490900500344c0707034416030b9076407510700d29000fa41040e0006004080d4054107030404108040c05400003584050a00c1c800125080380318400700c042215030250600705291412a40d0480c00220480300802d5444054400300104022801c1040390342254004100040343c0d28103105541c0102c0d0000411031640703081840da085920900c0401301e888040d550360004881c0690080160031840655882c1102c1414940040580d00d06800000030b01340351805202c0301600014aa0703030620350540d0341d641c1c54245402e1240a0b402181e011050160703d15040004240e03002005505840c95203003d46207698036042008858040700310071560380c42442c5c012643e0383e58031101400c2104014200880c404c071054805a801d0759a000046c1d000ca507821005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 879001834 1250 879000584 879000587
    0x1602090c07060506041a010309050c2110020c12130b030a020304021f021b010306090501080618010203090c060c0c150a1b0b0c030711011e06050405070903020f0f150703 74
    0x355600294211420b108011b081400720309a00a0a6141810315a0760a954001c00600380710701e0341600c030010030b284050307408002001143c000d080403255041c002c21002c000001070303078401d441e903141c00c0d0b0006010781a00c005003030251740d00950700d181c0a8000303040d0011b02d001084004600c04d10005d01c1c056200d060910600480c040f8032506070195225030015031280741d5000800c6100407210030360f003811800550f0300590050105410074800b55081c580041401c03080060f1080c01550f000b01501e01352403880e609e8900301c0c007003aa41a85150401b00c1c40c03114034a0030304042c150f10129070090701d102049400000e4540300c400c41100c404048041889284181c20100c0003500988080c490444c1c0389041d580c494602c80300138003841040c80e010002c240464440c0c500360200c3c80041c0c008000340d0029000301c20340da0188803078081e0b030380d81040c20110352402c0c213010303950080c80b640d10345000c00c500315030030042c2421101d4126030308000e00300f4520030307155160201120101ca1a64690350b890149090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 879003084 1250 879001834 879001841
    0x60e0102031c021312020f0103020a03150e0708010b030103030e010507110d0303060f08070303080f040f0f1a100509060112020f0d0510090207150c180e0f010504110a051602090c0706 80
    0x120310501c48203800c0c4170140c0c5070300d1b120f80c01c202e80c2464011f94807a420603007034000b00061503400c00c0c0c1c1d135004100070540d0b1104c0400140a81c0c0c0c182c0f1000000da03a10044801144002d0000030005400c40d644001294020405070100030300ca2034944104500c81e0011800c0340a40500c1a40000d85495082103900104c13140d0b003026091090142c1100c40c03e645020340542c2004d4000044000305800007818000250140e5000703e41c00303094a13400701440d040000e2410303901c101c00380020b440d00e070103d034003d1007603082841211805000c08105940d024010b542c100704616030071040c0d503000c02c08840110300d10f400a06440204650002d4a030400f413900d00b560341d05540000540390310410014001c47e01c51104220901d00004000c105004565403c480c602000c14040c000c1003141c22000c6030030310101078103900c141c900c1e0a80a42903a62201048299910301c82000c420043c00c002110817148944020700c40c200610648940e440d925501044050408481204800c88045074400801c080b500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 879004334 1250 879003084 879003089
    0x1415070e2b02030f1f140f09010e01050a2408060f1b0403060e1c0807030903090e0403090609270c031b0f020d08040c060e0102031c0213 60
    0x40c050105280a4011614014118185040d003508081d041c844556000040812035a4090169900754400400580d6941104071908103050500c1d400500000042d202d600d0050000e00c2d981d66441d2030b0403103e81c82058010b0302d031210a5480e040000342895003406550301031011101c000641114501c1200e1418001c10720b00f91080040407000c0010a1001030f000d0b41048000c1054445070302e41004c00c00742c10b0f9504e683c101181d00e0210700041800a81c2c0c3c071140c0a20b008005548074400001109900d107030f010948500819210b00c08500d5440c40380e0b10080d181442414071044047d19120140e02241048030120000b030f104403810301580e6030040e02000180500c041c0d081004c01c02c00c0e80709500c481b0900d030407054265070340700784c1111620a03000701100c2060744240f58078000700441c0c010041c5810903400d1003d441400069054140f1034010184580d40050345c0c5551760b428160100d4100c44404030460461200b4800e0440c0c000002c4104004169030b5800180d4504044080011000c0703541d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 879005584 1250 879004334 879004337
    0x906091212050c1801020312040308150409020a03080a05220503010c0f05030103032a2604050f06070c0b03070c03120e0d11010f09050c0306010902190c030c141507 72
    0x40d0038418682e1115080e14401004c07000211050454000100e207035008a0100810030722010090000b0f05800c00803150080710b00d0002c0c514401c07080418070046d00e02c540c0307000790405d28580c1c040000c6420030340075082ea54440d00e1700d5468100d41410301c4841c00042d545205006804020801961809114001414190b420b020392412100500680b80d80014400038082c020140051085181c021304084e110501040e4014005121420000880146901422010800a035222580c1038107082610201c0342d004002e2900451900301b40b00464012030350480c1e110500003c0410203210070005141304400d20740e998803080c012414001c090400d01d200000c04146050381c1e45907600c00203e84a070302c1c4240d9084c4440820011403c003401800201094001c061030306c840da404104001c40c1205101804500725010340e40c07a02da0034400c9108464070b409607e0290b04283c607156014810311000d442c081c0c2007a0101e04100d0703c0d104100700b6203400c00c0303040390043d8030b0080d0b43c11441411540c018415 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 879006834 1250 879005584 879005591
    0x3030e0607020d0c0b090313060518010e031f11030c0d0501050d110d050c03010f09060605060a0503061002070806040f06140408040b13180203100909020d0b0601030906091212 77
    0x20002604d8050100c42c058604c540d290006002c002c1d00b00115001990030b810400b650660f40d01c00103205400092240d9004100d105034600e4a62040f01040c04903003005010b44440d00e01700780500410140c2d001d103014000d803170307c290009501c0503201451152a07d00f40003a9a000000610011100140c02c414031507081d00d41e606002c07540031040c2c0410364006030b45001c240c28041c20418980303603840c401142c0c158280492004042465080b4900661180704d040c0300236074582003000b6040c0115440800050408d100190045c030f0a4050014010a1030054681e8a03444580301030500d007040380c054409511410710001000301e075129000f110303c00804a1803a0382001e540f00700f1140324521684601c094080780d981c01d005095002000100001c0c0a00000c5900710411100690400c8800d202d003a01005000035591001c6d01500712026402880203520503410f0340d425650030005400541003669400300240007070391600c03882c2c2456000d503104000300042148010030a03412641090f81d41c41c02c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 879008084 1250 879006834 879006853
    0x601060c03050f0705330c0d0216060f23091c090b0c060103032d03020a0c02210d17011a1c0605040b0619030906060f0303030e060702 59
    0x248104588015035042c503102c0d64074080112504198050b400c40030f8924011a00c4070603083d60f00300c030489030002c0740d030041e541494903150b143c00710b5003011078100c01155001c2081040382901a4014110312802c1c401c00226001c2c907441d05004c42d00031071561070380c0540d60b00c91841c42c0c404a8680c000c48205103018010181781c00c0d0b02c099200c030b0200c540001106565031b41034294034018140a00030b446000707512030700c0c0e17141d07680c03080d03610700e020300c000d402282691020f004c50710803100341d03800c2000b42c86007402e401c11400300d8101e000354030590410040064104000c00117030b5524040703500180e0480460740c00c01e002509000e0070700701058603440c14042e440015002c180030001c1d0082c110361408001c4800f0740000c00e00300c586845081950300020070178510854000034a80d001a05a44003030700c00300034407007207202881f200b407044440800d48650850311404806101e90003e141031b92160501103051039590003081030419440e00103c000c40e032202c0c2404080d0340304003d0f240d4484400d100500702c205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 879009334 1250 879008084 879008087
    0x4060306051f0e1201020c0109210f080c1c09050312012709050109060e1608060112150621020102010b0d0f02060304080f0301060e10030519180501060602060117060106 74
    0x3000c002e00d4600031070b04c3e903c1c1000c00711000e6042da0042e90000e4000d129940061922684c2000300e454142440001c0560710940c0320302c9041c801d141c8102c26101d0001d82c0e2108800301d41c0c240c1103a22503c00d02c0c2c81d102c1c0440c0c8031800602540c100248120000c54940c1204407411440150507000a2000c4035409807104181da6411203590782101c0702240007400c031095051550140ca40450080c014601340301c40c1c1110700d0000150301c010002d900344c0007808140c54a00315030700c0d80400c2c03140d108044240329a090100d0542c1005071040100f40900080440e6207a000302c580c030342c84e100080d0b51358685200f10015540c082c0552030520b2801c841c0310400b1045548c580c1035003900100c1c044d0082c003011000808000ca40821200c0c00f01110000d29120342c0d50781c0c402000141100501400f404c0140720300c4d0308050090007000d005200c2c0720017100c1a00143c00301c2c40300401810003510783c13030040c0030079401c041603081c4100805400d031a03015002c0c541c100705250340c0c18a45100c820025034001e500400819 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 879010584 1250 879009334 879009347
    0x1d030a11010230160c0f1a040501120b120f1006050a05130c020a08040f0303030e03070b01090b0d06020f1b07080c01030209060702090a0504110303070b0114060f04060306051f 77
    0x4240e4946164803013220180da500c00c0c0c00c811000078000c0c103583c480850030681145052048900d1051400e0900284813034003e20b81c012840307500d003c520102651814803c09810001b818840a00008141d50031000303414503044a21405060a800140344400c620f0081d00451020b402c0a850906115242c50003280d014503258682051080c0d8841030706509920138056400c4c065003201195460382e848422440700c3c40e08510003100401d261021180840c41c8c0841607504141c2c1000401d0728507840c148016014000c10210b8030390014000001c5800a400c5102610001c1c402c0841992205e00030083c401058110340b210700c107c7d51004004002d00a0005114500c049082ca405a04c844208011541d40c5c0110b9000a5010750716601700b00d03041d000d1b42e0140344031718014042c2010030702ca007806240d00da106254025200d03200e04030041c02160001c2d1443c00c440d4501426040c03605203d51504c410b1500030f038000c00006902c5480802441c5407240e840070b103c2281100031818440c110ba80035182 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 879011834 1250 879010584 879010663
    0xc0c140612071107030c062615030f031c0e0c1f09030c090c09060311040e1302030f0a12020115060305132001031401060f1d030a110102 60
    0x1e090300400000c0400d07100c0e034624090803612004865003039890f840d0402e04d480e52402202c001a500c00822840400003409a5420b480b010362510710035280c5032a44419030002280e085e030940700340382007800401420070007440018000400c04468018500800f8181e8898001c0d203181c0394000d000c031010701d0350391801280491065810710b168110700300d078094810186946c000380c44010461030000c2d07a12840d810031015a48560307100228548c40e20416021200b03d01c2c850049aa02444240b02c0c41c40c030056210380100100c003100205018580c0000d1030154114001d46094200620a00c10811140b00a03038200c10140001e1002a406408030500c07618688901e0f410507803030301e000c21050701110a510a00c1600503514208400000b0303120040e01100c4581036002900d0b103008a130004040d2600d49058611960716500c85a0828100311019105800f85109031520010310070f00948d8100b00c3d0014643c030450041e09a10403d41c006070811142600344126030440c8110340e680d0b03218045480c4003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 879013084 1250 879011834 879011857
    0x1502040b0913110a030504060c020d02030a0509030106091a180609070807110607110d030b06040603020703050d0e060f090c180a06032f03071809210c0c1406 69
    0xa141c6860b0307001c0703000740501140705100c4680028004000980c1a045107200754007440d018024a845000201ea842468200c4000160002d008800840b84a000240100c030030003000400d940d511241040116520104c107a942e440c035402c09106641005070400d4020300c064803050099241980200d20750020041c2444100710242000415183c01203d000c08100841c0302183c0040c0381814002d048420b40121901640c810002c0b01054148070380200102c03090058841420140f03803d4040d406504a440120103101081c81034160140c11485140d00f0340c074800c4000c20803410028070464404402512050041c0c11104110400303441c2d5108103554070b0012001d15031281d8134111004000d01c0c590700000c1c007480c00525503001200d01c401c0c00c0701141c2980500100c0002800c810143c1d40c2140b40f0034100b003c0c9010b58080d00c001c5c802e07489000828018814140c4c0207241c10300c1e40d8050001040031034041076500100c2c03801d01904076a040c0241409a000d2451052401d00240c82070144110258 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 879014334 1250 879013084 879013099
    0xa05041401051902010c09120507031e081813061421010614031e0d050f0d0905100b040203220203010b12031c020a09060e03070e131502040b09 63
    0x81103900c200101c0f42c01c03a40141c00c1d10032424107408000e0103090404044130014a030041c020802102211007807808651140c01018000c1c55a555003000090582000f000005106c0c180c2000c280f20714000c04c0d14400d01ea40d4020b07004416801c00041202c5d1900d54011585040e80c02e0152030a44d00741412005021180c4401e40b40345600c001003159030043c0b00b21850750034218000b8603240c82d501410141c0b0411070585a0414200c040c0c9a5074440c40d0134800e000b903200709504a60140070310000d01151000031003080c80c24080140402c103035000084212101d40c0007401040d0103a030716100c0c1c5022940215000d501e542400451091070324100c010841c40805189540d6086540c03d51100c1ba40300300140080700d0b2001c0103035405440740c0202800a001110302100325824614603c2103480e110043c1c0c41e81c810321410480c0440d6020081c1800c50f4042c442d02c00c0c0891103840300c3c00040c2c814030a09a20009444d407625055110051214229802d5070040c03105200d1000720400350717294080c0642d40c80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 879015584 1250 879014334 879014369
    0x3211e0f060f090b010e030105040b010e0705220e16140d060518160302070b1314101505011706010804020d0602030408090117060d020103050a02040b0f040905010501050a0504 77
    0x180108580d40c4012942e026010300001c000d126508111841042621400007034240c2505140c00d944003250028084c005980050040b03241076408a5040401850150304002c1d400c420801c0c42d0100c0c913100c0c0d9400052400c2000701d0002007800c15840300c136010080c61050248107025054015207001a9803d21000c254480e1114140c0e00c200018030006250095044c032405110800a409131004000400d400008845242c000e00844020b6648441c04101555075101031001c0e594400c07c0c12503100ca440c0401455007403041101c0625900c1f400000204103900f031900b0480d4030b205c5e9000506011610350308a01008c10700010380d41c0400c003030a143e0216030b600d1001030504c00050070003e05030340c4040240403e110030580541582542030304c411440d4035142444442496003187c05c00d81c441411400f0321700652090308070a07006845881c1c0541000e4803000180082c1c2c1104003040c4081c140407400f008410414010300c0c0c0180070a0803d6403400f100580c004210f8400c5000d191080344000461 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 879016834 1250 879015584 879015611
    0x706091a060111340f05181302010309020f040c020706020c010c0b01050613080a11010801090509031b030d09080d060b040f0b16020904080c120405030a0b10080a03211e 74
    0x15040751461500b280003005e07128400c0d000da8040c28041d0900903031524815400f400782c03a449443c05601c8a0680800202040d8011009090f114504a800c41d103100c60011030b9460340c0c01000301100032130b006482d0180c180080246800d860b1080c0c28100100711420502044071041c1090544006951465661005255102950855510244442c850950b00c40c05104500e4104482103000366a40348079a66941044015110259440f4506800030095007920407070082905400580c2502030b80d0a141072a0440402c484045400780c40c0800b0012310003a0a815500c0b910300a0482591003030305142c20204d00e001068064010000031a10003e140110b21820540e002c040a5004080d0301503440d19141c134060030341102e03000c44a0351154031403400c2070300680001d0310b041d140090014810401c040c2c8070002c200d100a40f84105400104c10701242141c0184200320010740251149230300300c1c1d11048650180610404800080f034a020007413182109402e61103211000c100c0e10204026048122 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 879018084 1250 879016834 879016903
    0x240f1122050d0c0807060306050a1202220f0b18160504230f03060403020c010e0f04090605061905030d03050a020909070207051801030b060d05030706091a060111 71
    0x802540070051044102c20050f1146080064034039010503201c9580c0c0c2e440082d01980d50718019564040e828820500005400303d0085084c40d00081940c41c50847c40e14070601ea004100c0004c6004a031035408804410b08580545490758200751400182140d00c0f445481075507034050400c0c500720301d0607400d001c03038144030310700b23503800340c410030407600b103280b0603141a203040b0425401505d00032111500074907528500841e0b12072089130541c014059050415004442422103c00190307030200101a02001ca83c440348141018103200d9000001c15040030400c001e804049159540c0d5580c00c0d60206001c0ca48010a410022090508002c0364a0700e49802c45e001a000d00b0100b41d42141207d42009540e681c00140312045130400d540c00c151110803074201000001e424040a40004074020100d0034038106007100059040c0036406890a0401c0c40c0d5405007618045602600c409040076140f04500c198206540c2d0088001d003031140000610002c0e50b61a2100c1410f0701c111255580203500702c0030310252 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 879019334 1250 879018084 879018089
    0x1b030b01020d23361003091109100b040330170a09060e1507090506160311061302100c030834020102130b070519030c240f1122 56
    0x1ca0000e28441c0d220940645200d80540c803845000317003680044545011f0b225082105400c0b0300303010315800702842801100b40c0c020381602d01c2d04001240025200c42c4090182010710f124a0240600c0d080d044a0300280c02030010801b864007084d982d9100a845e00402008170030100071039003ca45903250550900108075940d1702812844c01c111512450800201e410802e10110380c010300d00c40e8032400b504440c0100903010f1260844800c004804450f04400d030f03002c080174460b15201e000c114680800c1800c0890039110107001c4450001c0b20421842e020030301d11400111898104e100240a03107000b829190094003140002800c0d52038402d42c45050049030742d03503203403800c641300d040c55020000034000e511101a54081082c42400840e106004104444030650000c0040010705480c5041c10182e40c1d03200411020300c081c0b000500002a4910b40f051001c2c1c06540440c04a240101e807800180e440203002d9100c2c0a00d007003002c400d40020314081d50014130103455900c0d40380d81c2200c03440300b07200741c01c0c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 879020584 1250 879019334 879019387
    0x305060d020409030305040215040609060e12120301150e210a06020c0c030c100906050309160909031206060518060403050604060917070b15041b030b01020d23 70
    0x83c0c1400d054150b0846401144252150013a8110410501c0b4160085004610024500030410401148038504d424500580100020341004101c09400c3c41c1400c81818a18402404001000303640740320744042c0070200440c02d05000030b404110020780c00c0340c50000c03517540c0d002144558181c410001c0284001055000104541c1c4401c035895099036003066002040c46482000c038540c078182480da089090411045e25070340d80ca142029401d454540000300102d84520481100550f1840c101d000c40c401403011410009010703900c0d090007040b0030440492a80d0050500b0300820480381e001c0704941c100c1c480d400e02400811b000c40c0018a06101d41e0f48060b11a2155106001c140109640100f079110312502030450b506110b141c0d2201c1b5401140400b0384601b0480000442410305040d244182c64401000094252151508030081c03035940000c0000080e6144078803460340d6010802da01900300181809041510003008003040e10104010084c0e01000115002c05508003816860311041c1e401d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 879021834 1250 879020584 879020591
    0x914130f0209070513050d0206032d1e0c031317090307030b0f090a052d030703030f0e19080f091503040b01050906030d030b130c05041a0f0301060305060d0204 70
    0x80c42c030051141d04100b0800034210b17540080000e4511700741c040700ca007940c0e01500080c00c5a03582c8182c00c000700901420b44001c101c00041c00d985c0700b8030703031004030380700e445014111b06000e080c682044250301c10060603110600b030b040061042c00c0c2d900c01854a41554850400c0784c1e01440c52030410160f0040340b5005805208010010003000108407443d4400c0340303408541c094a41d500142203a0301c071040e01010b003194010340c40e107045100c0003030090025203404c903001c01d6065407104511440d5600000703044c0c0001e540d070418180400802d001d01c010307641b102d200911213002c9148410035400501c2c600140813140000d060b141401c4120140c400c0140000c01c10803c0d2502d0340ca20f1201c651040320210f403071200f01c1c00040b41780e150000303d240c0500c0001e0002c000c2d8100e800d00540c001c0281c1c0004d20392260181c025074240748894000c007001c0111540d20b5503100c1d40f910090082ca0803040ca44826504030078080c216a900706981030302e045804515021416444d050007280e03040d40c5500001e50000d0a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 879023084 1250 879021834 879021841
    0xe1810020f04080111210405070e0103050a03021b0105161401060303020d0f091802030415020a0f02070e09060f190609050106120b0609150c0706180914130f0209 71
    0x181e01010704201c42451000740f00f201d9002c0001106031180c854403421910074003881c3e000c800300c98400c2c0341d40319109204039041113403111517645411000340e0084a5543c402c0001c48201036050000418410394411103000d190f050304006060360140040a00d1000c03c0700481c4030138403030106461559000c41030000c0001e151682802500d41d410154034102284994103c42e81c8544925250001c45500600394071840360083c2144e000b951000e003050b1070400c0c0300c4200d01070a10b4180f00906120796940c40300c148410484801904081c0d05034030640041d41030341c0030000b06039404110740b540443c01c00001241955a001c0d0094118001000702c0d180c5440c0c07a0008c100041e0039840181030340c4103915010251449100a0720a50f105000c1a940010007800341091600b0410040d40c8503040c1c101c045414420341441c0b0a140455682c041c0c2c0c0000c900030144200c0b000000f00391000303807441e09003e02c24030102c603400302e04000c0b0292201c0405240c12500708144102d00790100d40241d4010800006402e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 879024334 1250 879023084 879023107
    0xf06090506011706010e130f0203014706090d050a0309090b0f0d060b15030c0a031b05041511060f06030c030c0325080f0102070b0c040e181002 63
    0xa0090050f00d507201c4064169442071040060814101c40c190309034560030f65034528003841e032a148aa008c842c600f84081503d00103070385c01c0c019842a403102400b690009021081460b000c81c2540542c62104036800c00301822400c284601c002c1d071172500b550407a03540d01017030001c07072650211a1009450740c000c0c02000810994840000011251006401c1c04a4140e0b00c080200710401022030b180d015081200c41400550302da00110014907000300080c00ca1484001010456842252000c00441c00061040e490540610030258404422808401c591800400140c070314461400344901800d170070540f081441e4800c5001c48400300000c0d05039992401e100e4444402c18038141c2e8214864003e5044040311414000340c8101090710040081c900c1202c092010300007120092401c1d02c11a41d84080894030180800c8104c032148116000107a031b614082c24901d2550300050850340720710204000c2000642060300103550850019021030410500344424989003403004800059072a0002c0755144c01035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 879025584 1250 879024334 879024343
    0x1106120708070306050a0803090108100b0a0c1e020a090203060f120d020f0d17090a121823010302210a060501020708070602031c0b03060a0f1503110d0f060905 70
    0x300300c03e8a041c0425038485040000e8006d00740141d803401e034801c1c0144040781d80304048154002040c843c081802d152a1104200c0e580e01c01040000410059000803007040300c02550801c100045015401000b801030b80010520601c6200300740740183c0100108825956050380c0d131010f0b02e8010b1031f43c101c0203c034420140c0c031a0b0554407610054040c00c040d1102c220008500b01d2200b1420755500880e040c940e1880d1400d07080042d0180c5020700c03901c480f50000480d180010003441d0100c5e26580004e0b5205100e441e551040364001c01c04451005030312a07694607440000745000a0300b42005a22203004d440305000c01401303040c0b0400901800b40074404005803030f42c8401e01344d510a9007134130306c060303100e01031a41e960406124900040e481080351a8000741c010910a4580010000114101d0200300c0060715045007520b140700050359801800c240c405142c03092144240701031141d69000e5103152950b072003900da58105140620494100c8030104541001003803045984500300304543c0815040041e5030703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 879026834 1250 879025584 879025591
    0xc0c080105010909060b101e020a1a0108120403080f090f04050a0221130b180609030a1209020f011b05150103050f071505090414160e0414041106120708 67
    0x501c3c41d1002c05419410016036400d00303410180c031350108d004244050301e0010b44210f0348980450045c1001c0100156040c3c1c0343e240800c40c1c8902c155800e5040c04003450030240503587c54100844104010000100740c0800c1d41e490303a01000003207847e03d414401142c0250080c1f00ea00394000d1a000400038103040707650180036408180211410101c413100c68255004c2c0d01651100c0049920307504010010340b502d44202e40c818440541d04106540240e00940f40c24401d480c03459003500080303510001340303070301500303000802c000748800f8001e61043c0c3d00414041c1c100b01c00f01c0f07410006540151b40103c4110000700300c05642c8a02241c0c8105e90743e8032a160010001e002c00c07101d0340140320243c010070400103007020035213002d1700c070410050358122010b5074107a000108980e009515000e000109070303113405189100c0c1013052104e05c1086c3c8000d5000700400b02d180041c40c4640c0c5024402d804200d090340056510a9102180305d18a030403d60004549020f40c660002181903039408002402d07a12003902c500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 879028084 1250 879026834 879026843
    0x60201050c04050904060c0c1211150c0703230c010506032b0c1e0506040b09010c17060a090203100f29030703060f0b0702090a0c0801060c0c080105010909 68
    0x29446181c103490052045105055010b0f1007500445c0c0401c00640c000d18055510341061381501c5000d0b5941c0e85468642031011001c216158940150348070180507400413004014622941450581c681e024580500b02000e010001e210110024100d60302e01d512031500c6020400700e845027500304403c6e000e4001122028081c3c01140d00f06051841f1150030681c6001501685840c24a8680e00c1220500155070017980c403010200c01d101074948817141c8003050300f800344024200c0d03403a09003003480310780502900f816141c0c2e02d0141d000b034800b544641c18401540c080c1c10110310640380c02000402c0303030035a5000741650310720001c14003410130182170814044a121460107141243d1700c1c1c43c000080c44884012401402c007240000e80b8440d00c160055601903d83c1c10002140760711401c1540350800503803c405070303d000028110066180802c0255407051654809100f00c0c55402002003a0384010321946090090100300070007002038808140303025181c0107000b00015030b9560b81400280058030ba0590307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 879029334 1250 879028084 879028091
    0x3060b060301140111030d020313121701061d04020310080d23070f0f0606140303040f0b031b0a0c031d010f0503090f2401210b15120106060201 63
    0x50150a000c000d89048440e0f0380360ba20150010600191020485040116068003041002245000d0340340b0245008528a518900c3c6500062424039042c03200c40c01c06809104010000c000c520040c0000e1605550311807a118513001810040c0c00c42e025404017410b58000d0000c01081b06030311060b804035040740d0302d69044422269048a0a4400010480c881c903590608210039800d513100321f8001b0014584905948011016240c031003840020324039030300701c4d011610fa150070440c00c000e04c0c042407010070003200030b146004d140100e41e21072079286100e1011416808400540300c030710390000d51040c84028140391a503902c4048002000464454011000300d64159241c000320109012410f58509060f11030035000203811009440c107400040034040c840c0300c0c607802000b000c041030140102002c440da006405005108501402c0140f0503000007009014000304105104840d03800801695001004040d10b86c840c409405500d1030144034060708500e458402c4040954150702503011601c2550080 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 879030584 1250 879029334 879029351
    0x50606091003150b1507030e040c210c0c0210080f16020606190f0e060405090c0307090525050c0d031a0111030403060c170108011404030c020312130306 67
    0x180800c001c0c0e030001a0140d210f0702d14642c03001d0501e600031002100001c0001e0048144001c9010490b442030900b20001043c40d004100d2900303050050204013412800c1001e076000348080e480c01c04400a0080005c5c90f501c0f054103880c0c0700e000d0782c1d400c3c001c15009412211500e6084a01a020180a4509080403410900022030503843d41070b4a8148465550203404d40f51241010402c0c5840c0c26070300306a29607c280300c00103000e04900c1c0e2020090040505c9040c40b4540581040112180140803402503008181c6000c0d0301e60700420340105440c4810000951a04d030308541c601d4421460b921803088408a412160b8408e170043c0c0a000c48a0494086641d208802d00c0c0840a80e10061540141c0320040c44c400030440d8010420841b20420441c00c903800d0513542d0310f600c1c09850840c0743c0040460240031140d08261402c46150f405420301400a008400b8003003250f0702d202d54010300140400090940359011590b0600c842044c1c880b1074082591110b100a07180d03004940c142c4021120a031400141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 879031834 1250 879030584 879030601
    0x4030b1305120304020a03062310060e0607050d14090607030507140c010e220c0c0c0e01060e090c1201080607031d1509160915050103151a0f0705060609 67
    0x40300e00c1240c5c040d1000340d01902c0c50350f030840900070198800400d40580b2040c03200d081591000039101d07400c40c00e00c20121500c0d00e5005801394010340c807034500071001002010089400011601c00042c182e01d4003902050f03640c4484841c9000303810130164440f4000414109160307100010308009801500322200c0d011041114680c0c8200308841070b03000c9040180c5054591428500018018419102ea10b05000303003108644100c400e0450910045900c801d60341d000d0060281700c0038050405100c5440e0b4030b50500074058508040403914510030005180003803a440d5014090301d19115409211a14950b101e00e045a11100200e401400080c42c0641140c10503c503a84002c42c0c2c4008040640411201c0e51600051003030020100c0103184602c24040208591188110380107080840000401c4c24420411607004a0194801d504060a2003403400c0315041400e00e450845a801243c100c0100a40c0300806043c05203000c0340c0d40800740400c0010071701102040e0380f07100d950115400c65065403103a48 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 879033084 1250 879031834 879031837
    0x30c0503090c090601030e01060806150105041a1602060a091a040605070f030c14060115030204180915061d01060512040807030306050a031b05010e0d03030f0204030b130512 76
    0x9200180b9400640606054140f40c0e6080b50001d0040c58081041e0b040e03800745c5401e41d4100d40c060080d69000000700b10b2209218a400c4861035000d103403031854545000f00d042107a0305540c0b2051104c80b4001042d04132001c600c540c0141250340949030700c0c1c0701d101014004e010016179110f0351030350420407201104004c101004940075a402c580b036040c20100705031104bc8502c14807080803001d0144005e1540040381000110f8a14041800010141c82d810090f00c0c490000c00e0f400400706040c014403040c0400d0b00440c1e0945600d81203210000707900c140b00d0400f11460030a404040c10a640b07464404103900a0035503841d01094980100b240251341e0300d08007119948101102c0a28208901c4041030019107248000c0c010f06019150105080e500c80002a20601d050b500840f1904401100b6500d010291150784000f05424280032240b2000030004c0394110035000002030070555102d6140c00d100880742c0c1503501031904041d8250307036454a801400e5412000c42803e441c3c0c0e00c00d903130b103101c070f00b140c50300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 879034334 1250 879033084 879033091
    0xc0907030c12360609051f06050d080307021e0a060b0603061008100506030c0307080a111b10060305031209030f040e07031b030f0b0904171c1a01030c0503 68
    0x50800c12401c42c00210300700e26009074030410040814455400f0040340650094019590042c0003400050034450030200a03c0f01500d529110309060107000c10440d0b680c200e0080e04a90420b54555407a0f5901d42d040f403d03c1203e00c0c407007040c41c10080c0c54451401e400144100100c5c0700e00410003131000c840003040b100740401c40d5101e42c401c101010214085129908503500907013031121030850702d922800025400d4104541c404400f0234003004002c5006da00c814126005181e28004015041c1070003c4071130940310b80c800382c0f02485d801e601400c144410821508840c0307100400200100c9490746070080d1694800040814400c06000c00729103083e9000c0201e030440c00031310101620b801c1c0f42c544140c2800e02d0040055052655541c501c11030381012026485c0e40003202d90300091318981409001040710b00c20756245014240d42c3d0304010001d10341108060f807411030035001039258404c00c0c0c141c0b64a86005903209040da4107100342480701d07442810501d0500c0609880034880081030100480c4c2600049 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 879035584 1250 879034334 879034361
    0x90c0e0d3906030902010212030109290d060518070e1e01180c050c033403120207020a0f0b120a0228021e07081b0901090e0c0907030c12 60
    0x21041040581c3c081d0344001051031060040c3d1b42d00300644041042e02d0342090303001c2d118442c0c888041d030790103424111180a94030701d818400340c81084150082400402c10007801812aa44c40e000300d5000d8050300c0c00403a6000044088074216505c03108101c0c1d11020564201502140d50400070f20712002d13001695040e94100e20405003000d6124074140d01a10030300c500c020030b100042202c103001c1c2c1011b100a1061130800010440c0040302e50304a14007a2107561202030302d481c102c0c00104002503110725944540802c100004d45c48540c5400010410111a884012001415080000d00400c2e46000d41041040e01c8507040d440c0c0d07900c0b42c110b0141e11a00701c07005540340100d8400410501c0c440d0a03801600d119204480c030440305090000080c4891080c0f4210f076601045003044100300c10031250150f40c0045840118002c1d00c0008641d50180c10700921064580304c040082e0421802c03c41e20015810044c4902544e0a0040c00075006140f000d00c4100010341001d000c00c5d00c2040d82c058101041d205 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 879036834 1250 879035584 879035693
    0x50f07030b070c1b080f07060201020c030a030213090504050d080f040c0512070b0f07110d03080414120a0302040602060603070f06030f0902040c0306051008060a090c0e0d 75
    0x1040803c4500000c0010102c800c0000c0c039281e000781d08038055080c0b020300640e500074400c80d10549840c9150401d264081c3c0c0c11a030041000c0144000d002c429a22000807506001d0f80750380485008a51090b0150804513000e0f01d00b03001c101c2400307000a603107001900c803901c552000d52107140754802d102c43d0840c1e014140000b080300810550804c403101c000345072074a0b0192507580b40c4400d11f00e91660711039034401d2002d03039010410400380441d8040c1842d1450003100c0c1124007102130369000c1e0442500810251036800302081c0d0050407030b02400364840c007240c1010895134464228901800039041405007030f0052080e07400003581c40c240000c5c80e40c00e80e03054105100c00103103081d50441c0075088103000400c1254542e0008001a1258050702d4860310503a00e0102c0c0450400091004040b00285030074100424030090004603240d423810101603400c42200411407040c4420b00b81d40d40841c0000c210341002c20f4000c0141800011288103a07442940f56000d0f000344850001ea090010000c2041a0580031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 879038084 1250 879036834 879036841
    0x130509031c0b09010605031b13091d06010e011409240f0d0507031214191b06050a060602160510020c12150c040e06090a0f020a0c050f07030b 62
    0x14480d00703206490800d4a0007040b03218661003c294261000c0c2c0c84240860300220a0002094107203025030203103071496909a003840d1002c0070b1042030100d00d10900b1015659260203107a1044100b00c2c6003d40d030441c2c02143d003156900c1250540c130460900c0f903e1105004100502510300d00b48600d11b025902941106112440101200c0e2003856485803081e88040100d6103283e8585038600b501e81c481d4040d0001d828000c0c0385060650450300032450700d60400c00c0f52480b05900e10117460030345141d0710303841d00e484aa00c5480003003980d0041144000a00300c04006007800c08001d12500120f200b41d09840f810300c2825995503040c0c0c0e42e0321988854040380780d0200018032a0f0306080b041e803e440541441100e02d00091580442d500303543c2e480401a841e0806100000305520a040d03a90300107108202c480e01d01454000e90007105140540304a10645030800400c0c1b00c00740b42d0b04800c8110048020865840702e007e007019141e8110580c040f6040d000f19400306007a4440800c2100442c0d0304441e42010700ea4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 879039334 1250 879038084 879038107
    0x6041104021902010915150605030910050a020d0606020c060409150e180106122d060f0b0a0504020708040314030d0218090a0c020d0e18040804030213050903 69
    0x41040100a03046a0300740800b00c041c00502402c9101c0ca9500d030000500d4010b40d007002c402d03102c1514101000d45040842c402c1c6000b038401c0f0b4841c1110090300c1c0468517915004605403c0c81000110080305505103400e00000c0314403580202489100c02101300300455807a203080e80c4980b00c48450a902c118103100402000c0764580001d922208441c004800300c580381d40b0345000881040c3c0f02d40001d42e010406032070075a1024451035004e4440c1c00c140c1c8510420703507941d90540b080c100220381815041805800030110780c0f440c403000c0e29a4400c4c4d084c0826110045084d0050120401c000e00c03503200e040e000643e5003840e1086420081e0048401858581541c0302d030b0f41c034074001c41c100c0321051004000b401140d40051002e0480c501450300d800b011804994100200c10002070b243d500268030304440400d05c0c84d0000b455124600f0780d420140c081c401f00d240003031205401c041885450005210030842000300303200051003564401c403011500e40c00308800300c20458000700e2b900c2019030f008112514021 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 879040584 1250 879039334 879039353
    0xf06040c0e060f160b0f012310030c180602030310090b0607080705030d060306050132010e0111030d060609061404030f080d020d050406180209060d03030e060c090406050405090604 79
    0xc00e0b48501442c4c1c01c0442eaa110203441004540d20020324000d0030041c407205031004841ca4401010448040c00d15054500003042d4800241e01c000c00d265440c9500291103005036405000b04450f00c25504c861270f82e442d0065140e50003287c100140681040340800c0c694030784d108618910402410316410420140d0300c03980c0381e6002d8038090728207100902540f5003940301401a80c0166220f81d601180c00c0d403400b0300304401d003441c0081121081c4c080c00d00085440d00001d0010703140b580241f80030700020410b40016681c40c00340464460301408001340501009556810540866107aa90782c885041c1e545c144c211401d441c2c010708400081070400c000c1000c924a424880480ca005034003441c90a400d0b030700c401d8100e80c0080710741c2194030345030001c020a10030366108404061a001e000c44001e200c0d198001034802e400284040d01c15006074030f0300c005142c82540b10080c441100400c55400e403d0004040385030740c2040380410300c240e0605a0100d00c03424203000741406298950001c0945844d81d9035440c400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 879041834 1250 879040584 879040597
    0x70f050c190b031e0108010603050d0e061204062702090903190825171807180b031603050606100f050901170718140a061b05060f06040c0e060f 63
    0x410040d0262000355441300c000e90381c003d040c01c1000040d094503510b030481c24080c04203110300500107503c40c0d0001540300c0701c04449101d240708400710310955903460b26800510410014584c034190003035440b20103408480c50108990f0080705c851806907078220800b682e80c4105003407480b621031949541c407141400741450541180c3c101c441e0b001c03200620f40140380382150030108840018660440183d8502c034200503a034104041e0351504079030103118404255134008600c11080c041040105030b80c80c1500c01d50016104c00d04c01400d80710407030304c440102d0700d400403d4001980c0d18098003010800520b844000d094901c2c007540c5030034030f480302415415280c50300030051640c1405034a038060442c180303a00385102d120786181c1d1982c2c10707144d90300c03010680d501205810100c00305100c0c4003010856901d440611048a040f40340001d42032040001c262500d40149000808502c141c2e0240080d0300d0341e40001034460301058804111481c03008608840c0799141030a03558004c50100400c01655071800c3c0203011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 879043084 1250 879041834 879041851
    0x50309060711030a0c03032d050c07170a05070801150e0c070501090605100f08030f091507080405100804020108180a05030c060a06081209091506070f050c190b03 71
    0x10b8041600120342044603640d4100c84030032072902d0600405070845154420007004c0e46184410001546200d415214003402d118140300300032802c1045a01e082211401805103110004058101ca0346940d50781c04450404440500034030340c001c943d140381441501c800c42198020400c10925240f0501c10494011b040482c070388000f0031403030340400c109009502580d8442c03000000e0314a84070741ca2050b0500a600015018074051004202041000041c1d0300d2104400e51100e50780e41304030002074140180803603040340b010f10224850f403e014400c0007402c2102d80030f0300c504e40c0b50034060004550420048500a0201f0003940200c0c2d4044840c2e08260101d241000442d04803018545803189590000b040c41c082c285c0c040301c100284191580102401000900300406508030400d40c1c02c5020b016048142c2e004210300e030002140c1d0f0800742061032614a0103844955207120341d0910340c2d490015004160340500c5509000d1105040056511244505103100c2c03201c01401e01c0035070b601039400605241d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 879044334 1250 879043084 879043103
    0xc020918010e0607020705030a050a060c0507150f0f0b180a0b040213180204240e040e0a20010e010309020a0801060e07030e060c03060d170d02120c04030503090607 72
    0xd144480901ca010841c4038a40001e148500d0303c0b110007490050301d5000540603401640219000440000e0f41d0000d00364844c20100e41c01104500032a154002c1c144050010074500d48110304042c1942d222200100b0342540c18003032020804140070681d188103040c1a00001100c85065454a01385010f6410a015132008140a941c40d0005016030f008040e451002906207401000b2950380410040d07119015000254201440c04004800c40300b0700f000000965540e102000c5800d41c400c00f00b100040000a004105d5219243c40e42940d901c030242084075601c03651600192020610033b0540300200059403608a0b41c1c04138030045007d000f403168126004100701c00003103001c070003c3c001e00c0050b005504e1400443d2904040c014281c0321044507843d2603030055000c0c8030049500780c4c00c0303da0014003550120203c0342c0c285000c502c2080c2c9103030258071007a00480d40c040d40a8050300140314240110340700c601d03e1340f1480b031188803900c2588801421070b8020010303507440d424001c019060440c068903801 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 879045584 1250 879044334 879044371
    0xf090a0b04020f0a0e0301110a0c081912052406090a170f0607050406080114031e030c1e21071a04150c0c140f0a050f1c0c0209 56
    0x10140d03001a203076030100c1c400114284c03035042d45c82401c90340e0303a0000310028040c1030b140e001d80081a129003091381d010001e99160b403109100c0e81000322003000c500c02140301c2840160080c01880030305040382005081d81000041128504240c03408004400c9410500b0000481c4604000303c56112040803a00425004c0000a00642d04e407210750084660101502c1085034a040762420980d00400d4030307061001c10701c410b1024a03401a24141540c4182100d40c40b02812403001030314190780500140000394030401c841c6a030000c00300103800707450b001c4002c803281109000000ba8201e0303010100400544d1184c140c452507007281503074441d07541d01340ca80400d280c01e070380751600c0350a80d0f0301c11034000024004c03a040c4000c010a808111001d450a80010804d088183c0f00003403000d001e100340035210821300e140c00d110281d0148100e5800b2400c0c4c40c02c8441c1140300b858182e0b02c512001c0d0054a15000e411003002d500c0f007041000c4c0c0511101603407416a0741d4881d13800c001044402030238481118550b00c428 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 879046834 1250 879045584 879045589
    0xe0c0901060f0c022d06040b0a1b0f0c03050d020d080c03150306040c140d03020a020d060b03150109060b130603150e070503060906010914120a081b060a0504020f090a0b 74
    0x4a00000e5881c5141076000407003050000380f25003031704604a01807601004100701d043d0464065600e000c1c10380c039140c0c130910301c0051800000310114102400d01002072280c1b80402c0704400c1404102ea203d02c0544020021070081a612001c5410345400840d84003030014181d00c001300011540840741107901851141c01034080b07480e0540454048541d50f640702c800340702d5000c0c6100780b210501b0701160300c4420303240f41c1d581c003d45503c40400c0003406040d1002281040000e150015007640c0000f604075400c1d084192403110b0041c03801e1155040c01840c0c030001040c10040d03035044070f0941d914a0200e006003441c142080300284200310100b10f280040110200300400054100c500034812595032540342d060035810800540c5020301150f0601405840c20406120b05d926612110a030071144441050070b200ca20a0a0180b4024020480c4000041c0594150b600645141640c500c2c002103910769a10100303d103044a10648000c0d51100f4642100f8500346040c1d001150b1200b8204004220121000003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 879048084 1250 879046834 879046849
    0x2090a0e091009081e090d0201080613110a08060405010303170403170c030a0b031b06130e0106180608060310020a110708010b040f1e0c0908120d0e0c0901060f0c02 72
    0x4a4031681d001422210b117888078540c200000c0304000030345250862410000d0b0a00700b03985002810301c0312020005141d96a00654120b82e030104031001e004c0340b03000181d092110342c829030100001c83c0b44500490a02d042c14807415050703030383c036460701a04000f01540801403250001c10403030410184806000d03c1c00004a611030086038409810b540302d040032000d0100759080f0303a0b04a806640050400140801e0707070071240307107554010b840155031000c003401040303485540c54002d584000044400014059801040d01d1032440c40100500d44141c0c880d14202e0307445400b0f0303d00365816031021007591002c1c140c070742c000c001484c11800c0207600341c05014899424505140d100e01840d1359580c04004460a01c0e004203102c05206400400c01485a441e8040303034480c4101c0c0034000c0581e144008900c0345d0040820502130000300003101d240d40d18000d10903240350f100c3c0150b00d00d51418040055203040000030f0000a241e401041c00509a0a00f4030844070800f6040c841010801808841005a280c100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 879049334 1250 879048084 879048101
    0x12010b15160308090a14010b0f0409230a02030a0c030b060307080703020411070210080a1b12020d0b0d0c0315020f09010f14070b0f06010908030f0a0201150e04020307060302090a0e0910 81
    0x418a1642c5d4001c02a20f10100641940903d04007000000050801200cc51b01c25400000900e05505450800d80c07420307081800c000c2d05441121544414001c2084210041f64441c800b1b4000c1581d5038418192900c1e030300e00c2001e5480c0d104240030b00051130241c11000c90360307401f03460361801c05009800007100803004117000d101064800d024080005403902602d424250100da03440d15640c142c0c00000c2980d001c8507040b00c0032940c0801c00c2035140149810444854400030040b054007541400c00b00220905444101c0d24001e050740400300351140c50094901c481000c071140e6041005490040d503114408a850714104400d102c140141e00601102800b03006014808400d01d0b0728208001c2009450b0141007941031201c8107008002d80000041121020701171218400d171510442401039016080b5030b040200d58001c001004907550100c5010749205900850441e81029500c1c0d0080c0c08038480c0c1603125400c6800d40000340a945006c2011940144800c4201e0300c0003d1102610303c01c031100c0c17a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 879050584 1250 879049334 879049373
    0xf0506062b0b090c1b0105060d0f02040603050607050a030c0801030804060c02041103090c0111010b1011010b030709140703140a0e10110306030d08070c061a12010b15160308090a 78
    0xc90390350031080749003030554099500b1701d008000758100302c00042c0241c0e80380c1e58000c0c0f600b03400c000d1000854440380c000b94003e40e1b00100311046810410400380445e00308641080002e403404101200a13440b43d04418100ca0300155210725150030064100d0702c2085101d4241c1c0c005032102d640c031a0060561008600c226018006045a00c44842c0014110811a09103a5681e0b041c045001d1a03a603c001c0036260460310742c185030860380800d40d1709a014101c000c407050340c5400b40c200e00144009594200706070b01c0324000005400f80d41c0d1520154215241d10710086055002c420001d41ca01e40c807a880500302d400d91408840a80c140d6a01d51000e8070302c41c1c800101d0921300402408541d04003045502d0000069003400602890b00034001000000e031110081c0c0607a4940a2048044100c1520800e8038200644000486015400e12a010b0a104c15200307001c0d202100760840840075810a641042d0151480c00e125502036440c06c07519030300040e00c04011405510050300014118410b118402400c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 879051834 1250 879050584 879050587
    0x150219060b13090206120907081501061103031b09031f0b03070b03041a060d0506070207030309060509011e020309060310260c01030507120e010f0506062b0b090c 71
    0x9000600801c21042d80c80040802e08105812005a031800f054403103101c0082111200c03a07403561045860500c00d035020b800a8001c8a48140f4001c1080b50158140c0c0c80030303220040d51102c804103c640d42d100886403404645602d03000c036400d108030309009240001d802421a0075040b020119400452001419954840d950b99201100381c20148003500c000c1480d0b8186038154034003a01c60000e10130b5018440400845248001401559242000c8103a16006011205185442d690103951001c083c0000c2d000b2134010080040c62070700c11411075000030410381d50030300411440620a20060031031110b810a6020a009543c0152901c0c0042d5101d69259142c4822440c40d0007812041249105d092001c9904034111200051400007150100c40714203103000a03050344c03050f008998038050040d013080b0b02401d10158100111054001d4911504655401c0060341c50301c0d41041120b02c207503400c1c1ca41c041080c44076501903a11808503014514160140444d04420440000350781080c126a8049417100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 879053084 1250 879051834 879051851
    0x4150201091b06090905041703181507090522020f0703320a0e04050a02093f0106091b02010f3b010e0d0f03090c15021906 54
    0x200c0301e003140c0b40c6500c2620420b14050501c14020b0200c5618050244020703281c8001c1010040328001c911100c00138680100e8a82c01c25004861141c400c800d515000d6200d24139941290b21620b000250090000d91108904a03250030306000e01c0900c28007a080003541013118107440300840340020090480140c18955a81080f0f24000d400e0540012a1000044104c1204244c5862a010f14400041c3c22180c5c82e4852115500803114503481408071500030741405c0921106a41a80290502d010212400d85135600040394003d184401c044240c00b080700c0880d82e10f004062018a41c2d24404a640c0003c9046519140904140e0303145043d813241d1140c000301e840c035405e6030a00c1551030b600c120360f005210360b0010b44100210b50341c880c0c40341410850054111482d50441c1c0a89190302548900280700340380aa0314416180c081d02c92280020a401601040c8414481c0c454800c0003503000801c5100c050900309240c080c0300c00b51005405504c0740f40100002102180386080340d131392044801062460 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 879054334 1250 879053084 879053093
    0x60e0c0901090c090311060910030621080d0c020708060f0414010e07030318030c0f031a070c0b060604030209040b060139030e060406030e0129150415020109 69
    0xc8164000c82419103451882000f059100001004607504400300a030742040f03500024080388035060200e648140007158150407660035170841da00b2034140801c1c11054441d540c4a450345612064001042808200105400c20440780d0008940c191203104a40a950b1500241841c011083d10050201001c2c00200b0007040111182034461301c00990081c000701030f6440d0300996135515808020103120409030200c00d403040c0131000d00000c0d6004906a14525a01c00c4a00c60640340c9002c240d41c1d1507110070046855070b140f070349680d0096000c0c1e92102a150b405442d8000b40325000b070f05041d40444200320000c0540d0310518041d0149000d02c030300c0b24150511000241c075044542003034003990120301c1e5030380320000078aa00c18070070b140d1440c5195a024695103403c641d0060100e56a07640107102050228000e9850740c8407080004a10000b0014840c100d40c14203c0d1542a18500000d07000c0000c0d002d107641813140905c0c0e9014454119a420240c80d0140c1114040881a003d00140e544803408000d01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 879055584 1250 879054334 879054349
    0x50a2907030b13060302010f110c0409110f09060604120c0e04080a03061a0703080a15030818011d0d030c05010e16091a10110a0308040201110d081302040603060e0c 72
    0x8071011401304612895580084c015910208003681442101d000c240c01840c014424a100c00c40010320805c41036040d0300d06800700850741c0200030301621213809502440d007400080d060241038000c100c2414a0b2400110300660024510202c0348042908000181081141c861030b02a901c142e00d1661103c520960047c210740441c2c0c01072030741c0c0034480003540c0c01e07188007800c0b6040150189049080e46d9034081a510140413078484140781c0300018100001800402400760105404514540100c90b50810045400408a84145030031690000f405c411a10700202104907040c42424030903c00c03090703030712003601b110080c442d0440d198000000500940d20040c0d0000c6c00340600e4582001841c1c5208610240d40122210607409084d1710303030518552a01a2400303102007044501100c079a0049032070010000817003980c040780402c81d0700c404042d00071340101e40e4061003052030340c03203035241d41c1d41109101c1c140d41c032148180c0e001a036500d000300c00314801d4003e00320010a01401400d02d6042c0b1020300444 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 879056834 1250 879055584 879055609
    0xc010203250804023303010f080706022a1309050607170f0a0c05040f08031201050414040b0c0903010e010e12070f02130615090f080a050a2907030b 65
    0x2c00c08035000f00401a61008040704213404240d03072944c610100c001e55141c070f80d010840240d40d070810101c0000b41840d0806100070a4900308010385825664070403043c0c0e42c903c0f0440c03151011441d40c402038174110203090900340503050f00401107184202199101d00480d48509016111a007205041110580d08480c61440d40403450740c6011103440c20303004092010300003030200140d1680b01c110f0540300b51b2080040d940500441c00e0030a03881596015240d0303907039101e000ca180b24071035001c0000803285803e200b0550b08130940c22000d00b542d070341c565074000015002000150403d04c00d10504001e80c40034454500c07002801400001d40c0700800c48407a1400c00b001c615001e007038100300b26410020b0307580150301000d43d81c1aa00c01c000403819041e803070003901d000d821083d20b40e501040d18039040350b130040c029421100850100002542c54081450f10b5513503101000d00320340e00c045000700000f40889604288a000a4070843c0e00a41e281c02d403210b0302f0029182840041d131901d880700081c1c640350426584 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 879058084 1250 879056834 879056837
    0x270b010807062102040e0c0d140c0d0b0402190215010e010302060a0f0c02060d050f0105061305011101110307050d050c03060a0303050c1608150c0c061b0c01020325 72
    0x100d4580305006002c0700801565001050f1181e14111515501341c05580c041c080c5403011030102e2914007640282d50b080701c04140156420b294140c8040003150310264015090f258490b450002c0b043d1204015021400c8001d402a500f000f995110715400b000a0079002c403258081d09a00100b0a02c2d054500f2068018856030010300c0300400069860204a41d40114a070903d80341110303014500303848003504010080d4000000085814003110180d0105224200d00d0700c0c02d0909980340d000348907450080c250a080a6001a03501b48425030151700c2a503100a26400041548800c405407803c2540090740d5034000f003000424a20030085e2540241540190350f0840303582107150007400101000b45600c00981440700000300994840000c0c480c070041c8813001c03010000702e141c0d1140341942c3c5081c0314140c002e010031480c004c11035100c2c00308100c8900c003100310000d01103501d42d1480c003500b9510110703013060700080401404646000c20300143d84104d803003a1040000d160401da4603c03041c0802d510000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 879059334 1250 879058084 879058093
    0xa09051e030c070b0f3c0702010219031b08040506120f07050f030a020904180524040c03110141030403020a2402030c0a020f0d0207090c03270b0108 65
    0x60358108458160b440c0b00610303000058a1480c10032070f180040712900d070303142081d10300054800340c10210b0703000420347e0a1003a422a4203040317030130741c8020380031086000c02000101c45a50704041060343c0c8091894090003110000c1c1b5050b03507100010b00c60b03800100400581181c0c8400c2007a07810720228055032041450600394a42070254072003131042d1000410351030b5420350101d044000c90300c540d4050020ba060b02d07035044120354001c0c180030b43c1d9000703040002a0310003180045034003a0010003111601460340701d0040030340a411540c0d45c14200b01d0318451345040200184486803008194042c0c2030a010b49559014120880b60031030f500400980072030880e40040400903c40025800a0b6540503540c218003c810140d50030b00340d80c0c2c0e0100540405108541c008000d0118405049009040341807054003220303035142c041c0d1701e0507880380e444090b0500942c0105100b040045402e13004900d250030b0351f1070001240601285210b2009000d04d06c0c0c40721441140c0d911a080121045480303015000b00e20040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 879060584 1250 879059334 879059347
    0x24090706080c0d1805100b030601051c06090501020c062409150909010b040e15160c030309031b240203010f06110703060507051815030a09051e030c070b 67
    0x82c824410410350f14040c60391010945541c04207104007810040c0d0010640c0c91014503440006c0140034188000c070321a0003910000141458461000030f00301c0f03190520042400f000e9120744000b412801c00588055400304041040e14000b440f64601c600442048000d00128045040803c1d195015031203006052000034007400c4484808003076030713110048819987d03d58404504034003402000510340d8000c2e080048141c1c0c541000300d41c503486014640fa000c1f0f070b00d5644105107110304000d1050304010496206203c008a440303600705842c0c8a010303081c01c650029020122005961044005aaa0301a040c000c0c014031303481c80714044105c0207030590079411941003d090011815444c0319420610030700d40590382c2c16680511804005540002d0200140e281c08040a04654080320580f0380108024080520500d4905810806540d20184103420356031070b80706a000901400c007003510700e8800c00740c07140042051090f1071040540060003454440e50b0308102d0624180107908018450501440b03030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 879061834 1250 879060584 879060601
    0x6020111090a050d03090806091e0a0209060d0602041e030209090616050c0703050601120c0602010e070e0a0e010c031a040b0d03050a09080321012106020307022409070608 75
    0x90741c00844070b50354502c4c8240b6080c0c070720401c42d0f40802294000c480c05c1111400340460201e90031140220310303032160100d404801d502d40782c01032301c02940010804041602410082d0300c0701c6601e4800d000040c50070f51030b000703603d0a1641180c00c0381c14a008502091046003802d220721500000c400f0010211030401895400d5800c00014030030041040105005e413240c4020009030008580100c150760382540c491180d2a0440c0c0d41030029030b94024000f200107841c500c14800c490400c4a241c014103c1c181c2041220000144054641d4951a0700c0d00e0542c4201c50f020b11443c0044122903d000a40c40c0c000c100001e0801c41200c095481246804281182901ea00780400440d0794146406c2d0341da20059803040e1012100c50701704001502c004513100030617188045407010b1a000c5c040714000c44da80daa038440d400c03009819060b400e10002501c410f1000880035000741d40c00080130b00586521080d04416081d03019161000701c84441c0b00107060100c0740c00140103500240c10549010b201c10301d44010f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 879063084 1250 879061834 879061849
    0x1d0f0109061119140d150303020d020d0e1309291003081207090806090609120a0c03031a0312040519030b2202090c0d0507020d091806030206030c03010602011109 71
    0x40030f0341800b011220070201400041c00300c1d036031103460480410004051807001c011445e01808110090711880c0c141d036031b143d4000078100c41104000d81d100c0790f0801e000810700000a075200040d201c2c8544a21500300055169042c50036800005030008003158540e0029003000800901701d58070740c16940c0400c0c408120b080c0101c1d140068980c0a6034031a44075902c0c00c407012251079014a0007405070000380605d4003000304031300380180860301c100c81d42105260f10522891007004001c0c03001c18600400500024040d800a0166403200305203895490b143c1e201090800050f592003650016002900f4407141c0b801020090104400150000c1218151750310b000d069040070b884c1803543c403841d540aa4010404403400c42c100307030b400340c1641451308200c511044980c005516011205040500045125100043c16030581038a03903217001c035036440c24903081c0c0071035222401200001d8a40e42c0100c056211180118082c00b041813445540f90701d0844000d0845603210080b401c0040c0c01c00c80e24440342d0742c0c0074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 879064334 1250 879063084 879063127
    0x5070e01050a031112040f11030c0d110a0801020414030f06040c060507080c0706050304060c081015050d02070f0308010801090f080a0e10020601050f0913061d0f01090611 75
    0x80c0080c1d81580c440b1015440e00408503e42c0018a17000c00304000c0000034a480e001040c46051003001c4a4200c204064503660902030980d0045801d001c1003011500803a00c60881c11030180c0525035590700d844d042e600307a074083c0d0001c580c100991030001c8c003035040400800010f140d803400944028181039a581d4000a942d00c603400c100007002c1008402d011f11078040f60b141c070072140700f00d6444503910720000d0500e40080b07c09441d028582100303130306418010045203100e4210352044d001142c1c149440c0c031201c0d5000161400c2040418041c200203240188020060b450141d146003080c61070f07520b4001c1c040801600030401a17410410084001610303201c0281c0d446900445254860041c0c0c40c0407070742460008940c80c0d02004c4101700d444410b0700422414103840013a1303065004040203c080c070450b10340540700650414000403044001c18401d5014294401404200c0c4218142144813246030050034403014416035901c410007020013145100d0041c0d24014281d9032401c03d95940e43e045603005030302 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 879065584 1250 879064334 879064337
    0x10b0f040905060a0c121404020a090203040b0c0f160b06031c0f050d090b1519030201020a1209150201060815090d0e0a12060603060c0203030603030714150a0f05070e01050a 76
    0x5e820740c0401d240111012031440000785001c2045034250600700c0c0030103000380c8040c1d005242d02640811200c0d914021a0300c91a004540c03168113480c1d8243c0c8031304a620540100c0c1e0143c00c02d000a031814840c80790320141c00c50080300c6a6105080c800308040c24640c1001076101d600e6444851080c00541111342e41c0c1003214142040c40e294020b119030100030f82200071005180081e00320030001c0c0c25149038802c0c1094070303054070085110800c4008400c2070749401c4c000130f0301507446106d00d2030000d1480740e494155011507152800551799141e40f81507050103c82100000350751100814040a181000010a005a610290740c030030f0610070a000d40700d408a1411000308682900c1404094440c0b0b51503400901702c8084802500c403441c2000e0005000c10f020490b021820718080c0f288440c400826240a600010041c5103042e01e1503031a0141c00409008601203130043c8082540c50746088000c41e4442c1c80071890101d40d290300d4000c0700044560040a020034045610b80303581c0c0f140d903c081a1034040405 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 879066834 1250 879065584 879065591
    0xc030606020607080c040e16140f070206090409081215030c090f090708030406031a0904032a0b0a02071a07090902220f0e0a0e0309011d03010509010b0f040905060a 72
    0x255900306006210b560054225045402c041c803020700004002d0f5032030317004d0301c2d501c280c030000d8270040740540741c850055403c1e1880428056403001d031400f94020000700c4030040c400a0075980b159076403111030b0081c14038032100e8901c220070440044200f00d1405850b080c12000381c100100f04e07c00042e617100d0081c0119000216060028010a60400003000944103103000c41c2d846580e140c20003001381440030002c1040f8828241c1503102030030460714481c0107540c991103c03000c0803d01182c0d40003106890003180b40c101c0c00301e0382020200b024005a80d000b01e100c2480076a454849061070348100c05204240c8294500e62002c00c0902d0398009403032000e4400e05c3c5e1001d650b0714003041140e40007815020644180f100c1c0130b1400180c41c00c4007031143e0200c44d00180c0d110690780e00c4000070812a044d010301e1707a60f0b9410810000c0ca4075031084d52440080301c10360102800d00144080841c3c2100d00850b491516030f9941c210718000c07850600c0c7c030740b60031100840b02170180c5641c41e40c51a80358903026201030300c41030301c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 879068084 1250 879066834 879066841
    0x111b01050103080318030c1e01060e090703030e0a030c0906170a05120c0a080d0903450b030a061a09030a060b0d15151a03060108040311070b0301090c03060602060708 73
    0x405101f100c48407520f0038100c0340007c1c0b01d084219007034040500d800703081c0d40c40c1c07003000200e0428509a661003a40100c002d0041c076440c0d900c6c10303214500a2810301e58020540500030001036884100d10015000c07070302c000a078043c14410f02021a4800a540c0a101d07401400c03043d00142d4000340c2032034020700e5260a10303181c84142a925182c00c8010b40010001000480c0403031b4041202d40c8803012aa01030707070340c017039100e04e5408000b0070005401c01c442d928000428101c0158103880d86880d020001c08280c1c141441e41d0310800319000d500152a00b202036511031504002074001050009440360340c96001501e01084c100001c6d6031078030042da00920b819140d140d80b9400b0f58072076100340d2969821400200081d9040301c4013000500e0202840754508407084004136a004200c05019141150000094a1a120794006580c0420f0040c1300703c0420812001001c009582400100014144480c14a440c0d5050860140c291000c54000008043c036094080110a41c0098000d4100c074150904100a40303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 879069334 1250 879068084 879068131
    0x70f09200c0d18090905010f0506090403051e1b010b010215060a1a0f0a02100e030720030106031b14060c06040f03031b0819060f090c02070306111b010501030803 71
    0x185071340102d904038500034001083c000c06420200c0d00422a4104102d180d42e88020801854826903002e800218184015400c20918291f40484504042803050400308000440c17240011b204d07000c0926a51030300d818a041e540c0401088440b01904814a0028600107001c00d040007aa8482c803440780310b09940d001e90b400c5d40c0e0012102c61200340d048280d565400b25202039580c9034459a40c4d44810f01e05107c0058144003c000d5842050f400001400d004490100d0600b40300045681c04e81d05541e2040000000b6034280d4103148404000130851050310301d0302c00c1041059100015235400f4540c2000340001d02200411002d81c01580241c14008400b12400e0850041200e60988c03075111154450500c0c802d9001410345115188904140600c800840a039905841c03041c426141046000101070204900301d41040f00214070901c115030b40c0d281e4903180d5205030f400c1c03100040c0000800003403445445e0100701c561003104681078000c0c403280d45107544070011488010a480c01c404020320703100c206031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 879070584 1250 879069334 879069377
    0x12010506221107030302130b1c05093a020304050f091e011206050c09181f0b0a0e0307030c0302060315180f06040c021e070f09200c0d 59
    0x361020b0380040d1101c50524026000707500c080850303810340f807c0760400110b07450004111045000d901e06800c040192800c000405000040c2200b0068094040400d21440c0781b002d1000303070030840b202c1c02030180356118550f0103100680b418803011504108010300031900c540030b8044940383c05503001c4100fa52400c0002e9420b40720f10161203103501c4000b0001030700c08100ba5070201000d0082d58200312035152000780038058403d06e5599600008001c0600d1400300281c489140e20040f41400061044044407032110441074075084400d40c03420101c3c042d1a001da0058200b04e1030b00055004040c00c0d8103585604851200a120007449150000009903091242010b00600f244000e03102c540e00c0364444410700001e003030442d20f500c07d280b001c200003410b910341030003a4000ca42d00c54014200003802898044055400c400d22809035100788400021116031080918000f8907200c0b83c002944050301c2278403604003011154418140501340044203d0240c045800c4060320914180305c0001d82c040d0310902d803407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 879071834 1250 879070584 879070601
    0x9140402091e070f02060a02360310020705010b15071119080a0605150a05150705060f01081606090b030702070f09140c180603190c05091201050622 65
    0x8580b0316060100c0300b50800c0c2c0198071049541c09880c12075a400c1450401c82c0180d128894100f0400385000001100616490b80b803841c094203035610514100740800e10340514142099801c0341d0004d5101c091000a109000c038242045820002c0303201032281c0680a0b02605070043c03d210100071500c5403a58503d002000c64103001071000449076660218140c030344003200815140c190034407000410140c00d20045100d05040240100422420181070060250100f0740e031200c215010030204002c00c2080190300c1c4500320010301906c02d9810550300b5810032000708907103484010b41c0281403116642101d80c16060710b139140c0c6410744958492004928040b099448050103403140c1a020031101e42940007400001d203620010401a210301040122520800810180362000244142614901003004540100c48030890704401500500c031541200c50002041c07010820000c3c1030000d6041912004840820ba030008204600c0c050000c03078555003072400d081031424841ca04000401013198816150b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 879073084 1250 879071834 879071881
    0x31215030d0305010e0a060510050a1b0f031b080702091e010312020f0304050303031f03050105070c02010e0618010f17090c04061e05040207062a090914040209 70
    0x1c0e040700c8040081c009140030700411040320012800540003a8540c0144000c642000d8646452410a0941101c450300408090740420184403940802e4440c40402200b8250144040e040149542e1074040c004c044108403115103404007a03007003030101d0100802d03a41c0c19901910140000ea48080c10003042c3e803010a01c003000c4404820000c0b00b401503190301c882e00d01d035285d000c070303002e40341c040007070b10303580e00840c0f044540c15401000000c001074090303400a1aa0030103504a4455140c584d81c4a500751030040354160300080040c40348400f55a03018083d90300f516400d075006860302c014981c2842d4040320048460781442101c1d00d00d152114410300100f4126200400707480e90f6400c1031b542c8140c4809280004a02c42c500b8008082900020ba101d80c1c5030801c602c08403841c05070703d031a0912010790802e132016180f1035920350503080460f01e1003080f54041d20181000000c00403e6510144c070a015a42045040616041e502c007072100040d00f40a800680440f140c00d61aa552400d5120032022fa143c04c14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 879074334 1250 879073084 879073093
    0x20a0329011710031112011b08010515030103150209100806150408031603020c0a0906030203122a03040510021e0111070314071e1a160e0a0e150a050604030503121503 73
    0x82a41e04d40020218501103540c172040700342d8be260200202c150b894510205945010001000020509444004010366158002d4107114140c00006d1448511040381004520200100030461030300c004007008030b0b443d003403c1c103040030b044c0304000350350303000d80211f02940060b2482c0980925000b017010b00900313080104407281064540d850031001c1c001c02c0c8000c80c080c2c0300388070700500c0006456050340c2039101d0300c1040069041d8454024020f0211074008410240402c2102165a849801c0c510003100d50716001081e20320a5841074000001e101c00009809034508001c0c0490302d9811030880d0003094040ca0990300342c00507202c08140e03a01c60480010020b042d0a1203c5c002090880031081505000d90501217032026038006085000c0b81c02c5403200801d901c146409115140941103a05d100d0383d0292400c400036845080e00c08410b5819950018084841001c1c490350703280c0905110060001503030002e0034a4611355449139a0300500703400c00d07655001c02d800580b60048140b400410000c0c002d0480707 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 879075584 1250 879074334 879074351
    0x3031e0510060905030a0305031f0503060c0c0c01020115060509010512070905120304080d08041b08070807080c09060409050307120c030305090c0f04020a032901171003111201 77
    0x60300001c0540704000108805600000d0149400f04807030031141c0c0c040d20746925542e141140b03540d9050b60804890707800084c0b80408110303074508004807441407110b4401d81d550740188440c96480d05a074040780c1d504680c10200143c08910b614240780c0c04488403400d00548800c00900180d60328018110522015031090301004051903010782070000700c940654210242070441c00245480b8032460041c0541a4031810440c8107152180550a074810b00a17044841c6c26502c5240c0540114030715400300c40d45034400322040c00034201c00c5c011240100724801c0245101c0c3c0360800403e1801078004e091601c00c581e6003441d002800424011103142d103600900c40852800e0202020b481e00d070640c1416000030f46031400041a840c800034621101c0c80d0028155401c980b040d400704400380d40443c010030201511544a50030154502032024485010302000f41c0e0000360040c001001512031564a1601801d4001800985c40c040200b0360240c2c0d400c040c900c802e620540c00231580000c4502c072181e00da5840d00010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 879076834 1250 879075584 879075601
    0x142205070311060702030a0614060924040e151801020c0c0d1e0b04150501031e02040609150302030f0601380403140d020c1309050a050a080a092103031e05 68
    0x10703c502c01c9da2071081c2d000360b2101c000b03006100000300c800c418035041c04d1a450150702c01c65840d110fa070386401000880d043c80c940c0d01c842d00b00340d2165507502c100321151041c41909401000300d00140d0085034000c608210620040c03a50350b00d00c0401543c00b0703c814241010900115203094007078442038601841d8865181d10f48001c1460080390705a41c8103070344c1484c50b40c0c000b0040c02442e040301e40022035462a8505420006001c400f0f0341c030120303445903590340d0004001d2014020254003035400b010401e00035146005160600340e10700b22070040c40d00038000501c005d00c111041c001809100500e883c0d440030848034500301e103071141d088405a150000c6400003c00130402c0e84008648140c20076684040c0380500c0a0b40e4a81020202c0c03039209440320f0b1083c09c1d82065600113080b030750043c000c61f04104441c0d210746d410580502c0b41a1580b0900003582410070b40c00128600080c444541a00341000803076145031807488920200404154070740401202e00f0340d10305500303001c071104510100b0060502140c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 879078084 1250 879076834 879076841
    0x160305060f06010903020a060531030209090c0a06120e01110a0e0102010e06070c0515010b09031614010c081308030c0c0a050a05150c01142205070311060702030a06 72
    0x11164110303500c1c400042c2855104084038000c0740e602400c103107046030801d101640d894104400c3d400046402c0315840e000c42100c00007030046d5200b03554100050307034150700512102900c01450450a40e020140010007500c9941c0f0031002c45e080340c50035080800e100d043e503d0240c40c440c61410041d40c200240d0101e0b1020200041400c0c2c1110b845a5881c0030764003005a0a030360480303880140c036403c000006040796000d0502c8214440c415030a540e000410050318459102003a0801c101c00c92011444c0748480c2804c11a24560151003a00c241003680b5100900c100304494140160410403048088410801c1000554010540450b100a42c86407a0094240e90fa0000015094107100c0d0205414407030400c0d21121040e01d5000c0c0000c0b8032103042100384068084070024402c88850308000d407070800d030740030320132010604000c03055150f1030308000a51107145603a80c1d10090701d2441c540100b00001c0c0b00090380c00220390b40100950340c40256003001482c0d90040c88400394140c02403c803d002081050390 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 879079334 1250 879078084 879078091
    0xd020d1a030a03020c0103180602041508010e01080c0f010903051504020112020c030301210510020c0705090c030f0403140a1e03050c0d090c0f0b0703091a0405090916030506 76
    0x240391031038500d10002010798034a518540600580c20903c01c0340c440c0c0d407080e08119845440b81c0d40101d44107105503075040032a801944000600d4100b1400845c0f0244d10103251401080744e1803020103154100990300c0c0d102d014851105104040d441148078141e40517030004002184c10005560341c020901490706038401007210101d001480540c6603610140c5240b0035a820012060015401c40e82442c41942544285040200581501d00c0c81400021820005d035039011030030060141e2641079441c1c00c075280c141d007070300314502c40c110140421002d1101c41060740d0b403106031300e500107034a6280e0b81016039840e6040728526944103000240c4080c125044485142e44407019407100d1741d401900e48044007118010390702440458402c012000e100070302070300300e90700182c01062600e580da41d62303469054000f07071b15a2024006100100c0d40c0c005164000e0383d160000c2003694a16850f5941800981c041361149001c0c40e4812440712000c034000000c1045045251050301486420260f12410296aa240100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 879080584 1250 879079334 879079361
    0x2120601021005130b18010e0318042304020a08010e03090a0e010b31140f04050f19110f090a0b0405060d0c0519051c1a0f03030d020d 59
    0x1d07a42c440c082c1c002d40c03140d01e10500002e1801c109071609951840c070075200c05013240c0a6480c6092190a01600030322810221146010086560720b81d80401c54035503e00c0e1060b036901c1140b0340180300c29054001c41390001041400c446150fa260340702d200080b658032103600f180c4210b41c038026820a14010010042c55600e80444101c10f28a07920b003141807155100740500b201c40e50080c085803001100030311032034003440b130301c003400d140c14401d48485201512401d0744000d18100c040014200b0320300308a440074100b03a00c181c0d0103004a03e490f03288d8041c040d4000c0c06070400e41031391100070800348140f581b014112090001495940d5103035035030004503e811100455102d042a8400040d440385c04804603070450704058500ba04040080440c2401800307040c884078180542049600c000005210500c01c0e1310410792596a1100c42c1c900d4403501d180003d1a0749032102d8070f4104444080b00e800001c550801d00100c03604400303900f110010034110f016240c17448400c40d0001c15000788440071904583c6078507a81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 879081834 1250 879080584 879080593
    0x1704090b0906030a03030e0f12040302040614010c020f010309020411040302090130060e15040b0105040e0a02040e0a0c030c03120507080702040b0f13020d0e0304030b0106030507120212060102 84
    0xa003400c01c060703200c094441a034503501c00410440000e010b90400783d800b0041806480c84980545107042c10401d4039100591042d0001805204502e42440748501406040407440030b412942c1c5d001800c2a9000d00020744036101c40300b462080c0340e1181d00013041e45c503400351007804400b10081c800350031034105010403441a2544c40011480c0203110f0500c1c016480118030171120800d0110550741403849041d4140c5070a901e90500030f601c110100040411102d489070110094501130030715024050060700418030460800303203000c600c4a0001548501a0b40481b0000341520f261090985000028800201070384500e041c008248025032900c1c5040300d00410300805015206030048516110340c070f000504840e000d2010a01604180e0300c10301e001400940303114902541d000006000c800d0740b1040104180d00003d22070325035542400b6100710003150b907000794103107401c0d596503540007901406010304055541c000581c5040c841c2503409080110f42d5802c55032600801f50201c0e40c4442102d032903025214 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 879083084 1250 879081834 879081851
    0x3060f0a02040b0c061b090603040b060a031406040201110106060509130213060c1416031e0203161a0f040303080c04051908150907060f031103010e010f080a03080f04030309170409 79
    0x11b800100d6080010040081f45036030740e0b66580049041015040c290082c06108011000032091000070030803200e00d9006100d2858184001841d062500b00c40c18030503410200d04211070350b0808191010300c44100e443c0c1d40d0048a218080000b4090a60f0141244a80c000e0025081c0c4e040072400e0229030085c008181405038681c1002e030b0303a040c080e007008046005004100003243c1f40f42c8038182070b0000d2240e1032002894980000c2c1c83c184050003001030380c840490b002c00008540694a02160110303180040c05c1808401c2d040103603005510002d07050255120000700784c514070031300b2900078020061170a00e00c4041105424203108040c0100449803040103803203400c0c285440110f40c8940d180d07400502c040b508045007282c0070022000c1440901d900d4210708404420041c0203107020b42200140101603602d04a40f1010341d109903840104c05e604030f4103400d030200e03600c0410b16a008207404c0540c0e0503500d0341e2a0450003420f040202038182e0303070070000c1040251070340c100070070807260700340701c14001c042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 879084334 1250 879083084 879083131
    0x30509100f0804060b040e0a0b01170c060d0209031213090b0f0a0513060e0f101203023a03050f0105030705010c020d11060705060115030b03060f0a02040b0c06 70
    0x261100011010840b44800680080c01d1038004540c04140580003081003144802d10900d07100e883c3c1011203085042da0300502c02055100f00c05500312420600910318a54040301080c0e4902c12101d421200c280c0018000905460030000d08001d44000780320290b0300e031248140c3c0e004a000c2401855840c50070a81c580d04c50b803410300301c48005000006d1105041c2c0b0300e00b0042104a0101c00d104012040d142c540003d103841d103810445119800d0f0f001489518a000300c186007410a05800441240203403d040502080c1c3c0007a110803d44c1360f0101005d210240038a50444440d000c80c41b401040e0400002e0b0300805916400282c0901c1030100801d0160740c0300c000301038542415010b000e001a20380e80300784000d441d1900209940c2030045481001c14810311000ca140750b4880541901d00e41c0c00f8000400c500800180300e801c00801c3c82c9000c014066501c0002500d407540a042260204040d40c0450498002a411100100b10800403180d88090741d20701c164803032004a502883c02c7c01c590202d400b100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 879085584 1250 879084334 879084347
    0xc0b0703050c0306040510180e0d020a0309032d1505100815060f0d0f031b1a06030f0709090302070e0f0c07150c0504050429010309150903050910 64
    0x2c400c0e20301e00509565900081c04000d25000300059610310444000007001c1241c1100b0740c1c00140000c1000c03420b6041d0004061400b91001294000c41d80b001d4160380c080782c4c1c0805004141c03a400101c4040903030f242c6180f100030290440d034004804403591950020010424050600105155818000b0303540b00c1e4401c510096881c42480e545401012183d0300c4041903000d0305a004c50010081d001030004100401d40d4550034100459401d034600c030300c0d201415000400008000c08026802d6031150880d60381192240f443c002a500c1c101c46e01022454580e004d114040b03599221408444016a0b29450310780500001201500075004500d00410200c1442c840d840c803c1c48001504140d81e0ae40004c0c115132588842400e94000c03804048107046044a0f004d80505480280d54654403107050200b00002c4460071810b103608500103180032400e1100386000401128001d007000a55000b10341000320101d2040c003510421185803100d514201500031010740461901541c056040900704076059a00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 879086834 1250 879085584 879085591
    0x40605060a120e1c0206010b192f010516020a02091b040305010f06061409090403030b040e030304060f2906070f08030a2f16050a0209070c0b070305 65
    0x848010404010070900501055141032015040011540c5000c8411810a41c4a0354002030f180401070b08400304503810044940940154440907162900c02c3c070076510329201141148040c8682401d2001250815404820640c48020a13003882d80c135550500c2d5000b401c044520f150200790540c000302601e8030020340005100ea01406200c43c0d910b4040d075420361031140e130703080082c0d4503810080400040c50a02544d6500c03460b4400104060b801c002001c3c00c202120b03a22003501d00c030305001581d020381d5110585a0050b4050400180d50f14a01c00441c004c1e0201075112030030303884000244010005960700c20129502c00c10000c21002103204071400c0c040700c034002a048038485a039240c6a00346028001845054130480309013800c51143d0f80da0743c2094008482c42d05040d0303910300c002103460055600035502e000211003625100c2aa804903000c0324022416100041c0007424900c20803c00c00308140703494550010708a0003180781c1440014580c2c0e00198003146c040301d030744000c00d00450190048500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 879088084 1250 879086834 879086839
    0x703060e010c1b050a020d0b01051e031f0e010606090e060a0e01060e031c17010b0c031e090a0b0a1d0105071e02092a040f03021005070c23040605 64
    0x10101e9510110310141c0c00100152014015a4001700050b80c8240c9080c100520540c000c43c3c080d80b42804000481c0c901414556107951441c1c581426550701091503800303804030b00000c05070704125484c210010540c04459000540ca400404a01c85404c00c4180707080b0b0f90b820030141615030f41c610502000420301d1142a06c1440c401005102c0c140c0500040c8034115406002c503001c00b01c143c05181c0007480070b016150041980c86400c04207403100300c9007250143c038921006914003629155826540d100d8002c0034101114510091003000c00340c1d004460f0116002410307840c800340c035440711180300e600044400c00800c2c403150b080d0300c41509c427440d103060005050715032908118950315445624030b4410f403202c000c0d408200717100c001030340c6000c281402519440114007142c000250502c201620302000140c0048061104210700d82c003142026090342e0341981c0c448151420386105440c0d034010081c0040c41050b80c108042100c3c00e80186098045c00304054040b07610720f00320148001c80701540070751078 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 879089334 1250 879088084 879088097
    0x3150901270c0203190c0c0f15020f03041509090606032a02120306040f1103091504120c14031801121a0639010507110c10051207020703060e010c 64
    0x1001000405002200c81e50750502409031840c82e51f0350080483c1a4000f440007441743c10342400445c48502c40045d0001560009103841c400f052aa00d03502d000324420710300340200380303035101c4580f92003459101c0c0144810202480200c1d00e44030b000c3c01808982c90100e030721610103485640103002d85914601c01aa250700944140d04540940386030a40c0300505d840c1d000b41e190400701c68000f5a51060013214034061104646030304000400302c0c2002520400890b1680702c40c000d02c40806d503042a48a141d00d405c0c18104180011481c0220014110350301c03450260101203080d00c5503421828800d00c40e98030036a141104d0308500d400c000126041411107500750684001c051178070303042c401c2c01031058900c0204507078441c1d20410184a040e03181c031503845074600107201c841c0c00e281809001e26a0082e0242c10101c001c1412081ca41d41e0f00c01ca4000e4491280080e40400e411a5024408603950010014443c100c1c514101002942e030b0502403108890301454403005025166061080c1c82c5440010341d1a203 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 879090584 1250 879089334 879089347
    0x303040303141b0d0815040603110402030411030a03020c18070e2404030c031703010501050a050f070b01120b090f030702040e010209060a0c060e01090f02040203150901270c0203 78
    0x10080c90708124030119810044035000183d088007081404240ca0050303a542c4501d140c6044070007403401d0509074450085081041c04d0000403003440c0c001d841d00c502641c0042e200d0359581868a6071700540200f240d00b41c05a00e500000b89580400c9100080e8810343d180d80004420050280001c07100301c85480000d195078400c07140c14905901d10040c03260640a07420058401e020142c81154065802200c018000e22405c01c01c0000060051841107010701620f070556140c940080e00511a0200d44800c0100001c1c10b00c250b041584180c450380341d004980340050390307195501c0c2400244481d40944001c65410300090100709c0000700000b4001c80540990705100169007070001820600d0358501d0195001c0c0021201e54035904090400c0c0e02c0159070354503030381c010b81c14500d085441070812821281d040814134404038020100812001d40e066400581c2c0365914840c04080400c0389600a034498241400000c2c041078030240c1d1040110703144d150341050703d6403802c03075011140c000c502d4101503041030105 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 879091834 1250 879090584 879090617
    0x80c070b341e051c1709030901020a080f040b0301030b0703051003050d050c03040902130f090c090b03060d020d1103190b0f04140106030c0e151809010b090c030a0b0303040303 77
    0x103400c0d10303500c41d408642c4c91201c1d003041c0d000440d41c03000524002030f034484c00722441d00608511a64002055002640c6400c0704880000e442c0e40c98824064106800040c131a0240401502140d0007001c1021390710703481e941c4914041e04080000d42e0200d000a0610f40030071900605104680c003241d6108000700b81001c501441554240c0200c40c240041d400301740000101203080f40028400c042c3d0720250050007070300b08080e040400e4690382100c041ea1b86046405e80c505d6070415242c4060311107c0a60f01c6e140c0d621200081c0c80c04515150081d0030204481c0c1100800080c2810303903e01c0d90080381560b18500c0308801c1c3d205038540114018040644001c0824920b40d007400c551504140500004600001040d000c40e0039988280d2007141c074440d443c03504120503003da80280380c0100b0210b0803090b4020180d0300040102c0300031990b031081c114000c40420341c1e08100354440103501901a1107048545400e04400445810440c4e83c0480e00c4c4c1015141c00d0b0718a008801c80d001d032076164451119980743d00c00c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 879093084 1250 879091834 879091883
    0x30c05011d09091504290f011214030d15140105030a09111809010609020f1921061a030f130516290f0403080c070b34 52
    0x801c3c0080e001d00d13101c2482c01c0c500110424410744c01803402040300000f400d61800924003440d2203108803e031503400e203c030303445c400008030381101c03500c0c400392003102c1c91070400d8100d2a0049000360001c1c4000158150a002103030401400b202c0305841d1050019951f05003181614120b07a42240010000c20005500403402e41c0409031042c0101d0010b0702d605032140c041506134003080c288110103113a0804020800c8800d02841000e03004040e020741c1045401c0e0101c0d03409000b5a0500b180c01d02090441101c1944102c40781d0002084030300d2561030072400541c80500600b80c2e80039650103903d0452604000002e0002100d0043c68800b80c160060f58869140e41c030381e001c02800c02c40e84c0c2d00034400500303d159043d001240242000314050710700982591540440421640942403d600003800034400c0b011550040c0c07012a83c10998460b5503680701051141001e587c0e4014400900d03000c0341c03011321640082030014120440c1d81e0405400c844d4203a811110744000c0d0380c02400c01c5011044889070529505 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 879094334 1250 879093084 879093091
    0xb031e0705091b040b0712022406040f1104060306080d08060108090a12050c060702070b090105070602040e0109151a03180a14030c0111040b19020a05010e07030c05011d09 75
    0x1620a041c1200d40e01d8500041c0d1203a40f081e012058081b80741303424480c2505c0051441007a43c0000d0402d51491000c0b201400192940f441000c090320001800e180c6907900007400844c1410001c000a1502c41c07049040342e0414010040000e26111004c602070b000042c4482886089865503501c507682c400044444c0500100301d16254050b080010700001c014000c690000c0c1c07625242d150f01d42021420350307407803c14010f00e0300c011944000c1c0b080103182c250108071032160b82d0a180c155503032162420007002921403580240d038200c1c4284000200e0080d40e0340b00c1005c80c400807442c51130040e66480710131054114005a0140c0705002c10208510001441c500e403080081030041c0c03914031110341c8854411400d0600401d030a9000041c3c150b0311803500380701b5250100c80c81d10001d4103207810141411258010740001c0c09205044600c41e001c00350081020320314441d481802880000b0300c0d140607e40310203661008860200301ca58002c40c2c039602581c00d00000c5114802d440b20b0000820040201a58000c2d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 879095584 1250 879094334 879094351
    0xc0e06060c0102040609090b180a020a1b0510291306120f0213060b090f21033f0a18050a050607170f0601120f0b031e070509 55
    0x20009007103500c07400c0c006800100110b0f2203603400b9034905041c0d0416202d002613140d01c00e000390f401c4c080004070000c03001c98000d024188010f84414108505031508003030469607030313107080300c100c044410404002142002c89000390000c0c0b011601424000b500038482c5004699000d044002523400360920500d0700c034503d03212800200d001b80e42d0b510100700741d2a03030607419100011581f00580540c24006213200e50018003d004002482c54207a0f10306182c0111109540304092856035011a0b5480c0307043c5102e80d0103c81c10000b031000c07a18040a6036540005815041c04d86c841d8a10307103000d007400c45001440d08242c2040004065600300c1c22a05070300c010842c044803a40c0f041100149c4e41c1e04403013503030480e201e100140183d140740c0c2442842e04000070200b00802c03001e1480541c080d80c113540c95640150610100140c0d60329102e005880c0310140c0942c503c0c07414a414801c1c101d0303c44c10b0b001040d81a906805a41055031200580300d50000c0c031444018190340008410052070500c403616590004c0790 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 879096834 1250 879095584 879095587
    0x8010f0506010804031407080307020303090d140403150902032a010906050409091406070918021806030a0906050c07020118080715020309130c1716031109101110090c0e0606 76
    0x1e0f23a5913110180c1050700c074400140d1000c41040300c0310504000e00c01d00c1c9502810300b00409103100d04407403118822800b005028070f8004a000840c41e060b900701c844685d90040076507403003211008005d203043c08007104010b007580c4425048009540585110000d9a405913100e41c81c00c1e00342403070140540003543c0102c5452003103d2684408001c21b000e1240240d40704e03501e07800013a24016a424400154046201209104005a680d030524400b00c0c011203030030903214983c5a40d00c1d014500c00410000740301800d868104000c02101c900300e60028650f261003600c1b080ca5000f6080d07000c1c010000320740608c1c90158481c40060111041e0361400c0c0a0407002c17807045a00d000c0280e40403690407989104254001511002105074513600110200129104e44d14103085905d0b21050074441c1446402082051591310080030060380849001c43d00385440c060111030226610400060030040c56001d5050140603103110740c0808c02c8a402400005a0000c1502c1011410310021500c00300c0d0140642e03501a40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 879098084 1250 879096834 879096847
    0xc1612080304141516030c08102606070305160512041e1a0403030b150d0908091f03180f020f0f0306040804090c0903150c050408070f08010f05060108040314 69
    0x60035800620a1844071007681a61083d0040a410741c1c00706400d140521942500f0050a00d48030508007084500c20f962800787d00d00f00001090f058403c40c0b0900484bc000c440130410712030307050f400480c040d1481144034041034120708001c6840380600e20303100901c85465008074010454250b20700d620b1043c20200d070b440f0074006544004188089540307104101401e00200300505405203e140352080c01502d0340b40c40c7e15100302054032944034605207404415561408902031011036070a5900700a4003810f50b40340754284680070031010204141e00000203003441202d15040340140c01c1ca12059038480c01c0488040c605500304040441918400764101e1034165072001c1d1760f070b01088054002c1c0d0050061a40d100c0c28421090241c07424056018144011848104001016807018045074a0407072000651810002c000b2240361040d80c1c0722a050f4442c1d07040c0490b00702c103100020011541130900070001404040c9080041d60021645070f804143e00c440001d020a0003441203243c2c68a131404080d28100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 879099334 1250 879098084 879098113
    0x120303090204110d15141005070c12030203090301151d04020f040504080a2601090209240c07051c0b09190308090d0c0512090a0504020c161208030414 66
    0x100080407032030700c8617114200302c25a4111003c005003d0039a04030301e040003410000104080001c0c1071104420080c00050301d50030700241c18103a02c080c01c1e4447c00d0700ca20b003480d0709000713540350454500326129510304000c501d44004025041030481e5181901945103460307001030187e844a005000b030360030180e851001d07080760b40d561080c14861303881403580644490209200070100782c051020210035801100f1003105540c90f0328041411205041c1000d81e4501008000c64a603481031980400788034103120110001c088400f005e0f01c0d072140700c8422240626503401c00c00105c0700b00d80c1132000b1300101255500c070104500302d18060303000f40164102c42031160301042e000921105c0c900168001004502440305c103031818400480c05a0061800074040074035900c0d41519200300032001d800d54400010314184607240d00c1c1d210401003c4c000c108640f11030001c000326031140c50000d02c40000b100e2411000c00d40300090078994842682005000d070071039661740e45524809142c1c24244da041d1044402c000c0218 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 879100584 1250 879099334 879099337
    0x51201090501050c07140309130504023c040216031413080a060615080a0b010905030f060703060815010e0c04050303070f0204050604020a0c080906041805041b12030309020411 77
    0x20484040410342e914111b0030402111220b038070078506150010829074003603075507052000ca04e0003504040000c483c0c80b5480000d641c0400728020000000000040c4403151041200368038400c0040076032074228032100740400049200381441803900c40c85890a460100c3d2142c035403851809040034801d49000041d1a00341034400d07155005240c923511940896040001901504006103081d82e8108070003040640301403c104401009944040e0399400a1075031a0703c0b401c200e0000380710240907240c00c0c1c50861031181d00c540c411582074010900700b03c000103d4520000305120003c600c02d02040c183d0742450796605e80000007401501c4401070901001c10266401c0c0020443c20784941b41000458101c0d205003c1501c0300140103e105501c180900c004c0281c0009400500d80ea000041c41c1d41d40c010039002580038000c81e04004800c061000307005e05400c4456000318016801050400718800034000f0140c05030700f841c0104421100d60204c0c180019000350829010244024400709004820a4101c84507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 879101834 1250 879100584 879100591
    0x110303010f09180f0b07030b27010f081b010309020a0909060f1802060906131214030703052205041a18060f0d050c0405011508070e090105120109050105 67
    0x324203a040c82002140100e1207980e040800a61441e1440c4802d504c42e40c00b200c084610141c5110701280000701403c0c82540000301c0b04000824100458131010107600f5207030002026404030b1070407000081149544008414103c400c3c00300185101e100300410425000e03000246d81d4141a02d0304074940040e80d42c000b0200140c2100c201c0004c212416003080c90940300b030b079051484010324040010341c206d05800c440c07a0200388c040e03071070682d00d50700c0380007003503442c46803480b40c414001004101148030624041081c0290380503a0a51b0303a064403080909440703222345800100070401c00c004070a540f00e110403101e140040109400080260f49001245c00e44503641d0041000e282e02d4091928035250400d00f40140f518501e907034500510f07168000c2040d000241a00780e1181400700046c40030810200841486200090130502103565281c641c650703064988000e050128008400095100d031065800a43c142002051902d041c0d02e4172040c0103900c56901c008851a54890741c4d001c000c5103007401641d01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 879103084 1250 879101834 879101849
    0xf190c15120c09080c0105070f020d080a1d01120c0507050a150f2022090c0f02060603120c0102040e01150e030708030a080c070614070f020d080a0c11030301 69
    0x150340740c00c184100c04550110415a003442040d48090100100010381e0420340d40c000c0c01e08940e0342c03005003403215031101c120800031340c8040a8000c21042224400c0170703006488090f180d05003103144180d001c030800856170061500090554035020003041c3c85030844680c101e21422b20358580304075500c6460411051103c240c909901e001d000f8500410b840c4514043e040c1090401c0224601c5958900300141c01e822441f60020000306546040c6da01003c0116464281d114000100c940c7e00d81c802d038090107001c1e20100200e1103500030012414000700b00c4610580f0010f01400c500006500851410380102c1b6200c00c00759820320010883c0212020007501038000c1c2640900481c2a01c0c1d001014811004049402034204403410468100b00009032018003500e410510342996440c2650061401092000382c001428240042070016022880d01d006031210760710550030b40a1300c0810b80e65030822400383c1d4001040c0b071002520082030b075806100300580a107099070071042540d0941c0c0ca113405c2030b0132221 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 879104334 1250 879103084 879103097
    0x7081309050a0c1b08030c0906130f0f060509092a1b07061e030b03030d02070f1b06050a0509192c0c041e0906060509120f190c15 57
    0x4100790031848080d000002203040d081c80b07204c0ca6550501c0c40c04040c4c1550003480004c603111506175105819030700c0c2d5010480203800002d80d65a9055402800da1060a1043e820340c000458864400c1e000ca8005440240012b22191104503070340b50030002d00e10105900c2c9140104d10100281400000c1c480c0f070310f00100341d82030380e8801000d25041c40607540c0404103104881442c1805464a1102180c410610b41400200c514150001ca070451007007031002d14500d84005100300410410040e42241c09014900030310201da589100540e0080d0180901d002040b000c0c4603400304a4400c0340140340c101d0340a44a003d403807500046004d0300010300d80003400c1b03802c0491400704402c50072110b000c0c81038100c42000c1c0700c2418100000310051280c0d019601d0505041d0aa090034150088201801802440307810001942c0d590b9000705543c10402d0030324414070295882821100c0c00168144a05000c040030340901d240f0a40b00e086500c81e05101114a080d160b10b00103181c40310300c551690b410020782c4505 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 879105584 1250 879104334 879104351
    0x30806030a082a0d080f0712060f090b10051e090d0302070510030c0e010f11100b0112050f0a0b0a09050f0a1b020616022a0a05090c07081309050a 64
    0x7116075909501000b00c4c0d10210081a4850384a100c9540062460840880c3ea4031030712400c4a00003040400704401900701040090401d143d0003d440440b03030070940801c030380200ca00c1082090300200000b000018001e000600d03500480c2119000f0103220405428a4884004041000c0766101c900c160056041104200242d06140c88504800344c00b510b01085460b03015003000e00503d8040038a10704210f186800da4140701e0040d0695641c18488408071404800326104c490090102d03450300358000350090352800c50000720360040304d00580c1400004100c650760605401c0c003e15582c801103034800703031180b0001501251031050b18005c100e003003003065440c60031030828415600200b0105880b003e02000b100a026408200e44e600810400000056001622800c83c0b030400c0781c24100c1800c100321020b555020300c004d1030030403100a040e41d01c0f01040360b030b54041041d40e80c41101d1070503074003000f000200005000d03000140444500351090a0086e5141c1a43c282200c0c011580500c0c4a9555001c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 879106834 1250 879105584 879105637
    0x1080c030601020607030c12060e0f0723180d12020f030721021c020d090b030c03041416080705040c02060f1302010c0f080304020f0906010507060f1808040f050109030f030806030a08 80
    0x10360780001e09040c000c61240071080d403503003507003c804001a40014045000240c07a40741050010b8004002000d29040e21607900b018044510040400c6000d88102d009800012a01000382ea070559044010361141840455c4244d1850320f03110495402c600400d0074200607014060072610034646294010081d601007050302074002d68294101c0344950500340300f0070000b5258082200e900513400300302e0744c03d0b04010380c4980c0c1c80c164544407060341d0345000c0b42000c100440000b450b8270464104440c1400310000c442003c6e41c840c02c05130394510b0b082c0ad0480000780c083e0f4003844040900c07803043c580601280c1580d255001e841c0f0000d90101da0340392000080c0015440c24450440701d1000403139500301075040400010303065208288009018a442d00101d1801400a07030022050b0004100020b003400120700d0841c02c43c0e032090081c002141e06040d000324455100f101c0d800d0640b41d1001d1a182000d050b62810b941010004203400d80c54070944500c2000a4180303009026041d42c05c800303410400e03100204 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 879108084 1250 879106834 879106861
    0x6180e160207060203120c0d0902060c011e0606090506130e071d040b2803140109030909061404020f0903010e0d03060b0f03040602160b130201080c030601020607030c12060e 76
    0x7049013190b000340b00500e00384061070089500415500003039591003d0882010300904400e96000e9801400030480710114001900032091000d280100e030150b0350b100700d1941d0103e4805010725800a5418442802682003180045c0080388441c1307512a44150380716003c51450400b15003060000350100031800307000b1540101c2d2041c010088406021020001d0003040c044040e24400f43c11900a0500030340e40d114400c0104000745400580c44040505000b405502034504401c044001030014240050101e1540c468a41501c907110000303c40320880c0010000a03400040d0702003100c0e1000c20448819a4003407160520080c0d2181c05007076008410032000c1c003116030660043c00c00c020200458400102c041c01203d501c03c3c1d2200c401038854072502c100089181031940001c0c4604400780c00e100310091090b5180c41a240700f40c2e1000c55547e51203c580d6864081500c540c0d026a1011000c034040900940202d1449030b1207140c14010034504680c480250740d425400492a00404e00a00800358809507 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 879109334 1250 879108084 879108089
    0x90c080307050c1311040e01290d0507030609140a050a020a0203040b1b070315200912010b031002071109010605040b030a0b040f020a030b1906180e160207 68
    0x1440c01c0c00016100c05807580070604480380f2811404110084040040d404140280a07403030083c0d07180c40d11481c514100141c2801007260990084421a040c2d521200940888840319044c550608401a144202400e8003521540c28507803296004036002c0700e03a203d2882c04500c040780151130340c00c06102400c21503401429a0451038010030441d0314194001045400321000d4a40e150360341d9030b03040ba8045520f4078400a0070100d0003482da0000c24051000b505081e202d089403410020f05103003040500c3c1c55040c103400040581400c1c420b00281d841c01501c00090b01c11040000b040c0f26940c030300020309110402001603c85a40890400d06000103c030f02603185020640e1901c1c0b1075410007102800b14044d911940b0503d000000000c3d16418054001c40e020003006001804080400340c03242000c0e401c100c0703030303280001e18000100d0203a01e440c4800a820080c01d04104614904100c4100c0e8100300e0a84501d07042c104106000500055000e6480d1041c041c041c15604890b00d0718000038103090381075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 879110584 1250 879109334 879109349
    0x720010903030c03230604241401030506012001060902030117010e0a0f022710030212060f0a020721020604030219200d02040c05030115031b0809031c090c 68
    0x9440f22190112070f034a10700c1201140c60501017590360304000070040c25441c010360008520080b408451103955110315800c0c0d404100443c140032024130011000c650b421600580010384501d843d2101d110305081c0c0d42880c5030301034000b00e01e294980c4000c10686e4003c0e4482e14885100341801c075201c16003071107210079101d00343c40901803005161f10f0742e43d054941110041d1044402d280a104510310f092030041c522480e1100c0303810f1600d8080d142454140d82407000780d00505c58000c055000010219810703105224030106491369499803c02e40c4001e4105120841d5500403801c0c4111540d5901150220003003169030003850f041c40c0c03078a8003d040407a03903c11841a030110300b04013000035003500494020741d4040d41100d051401031000246000072404406034005181803205100b040d8003200440c141c0d0341030705080e94912030101741102142c0c0005102c0c5008074100003401c0f0154420070340140c00c00c2c4600c04503407e0034104580746144c0115100c50214807656400b800c4100281210780c4001000407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 879111834 1250 879110584 879110591
    0xc0a09050f06011b0605130309170a030f0c05010203010915240507060b090f07020705010f09090902060417030309060a091e0203071205031206040e0d05030720010903030c03 76
    0x380c0ca105055a00034210302e051201c000084000c1e07410200d016802d043d00028184242c7c1050402080b03041d061010540004001c0a8086050742d5115060040f185544004080b00200c0703031401c4035801c001c0101d0301d003000050f0303030b0410100c1d04c240041c41c040c220390b00e0002800c20700d80182d00004140369000820b400c40000d80c019000e20401c0080c2101e00040c203119986119500d803134402407140000035070303200e03507014280440c040200403241e100380010b40803904469101c3d401506c040c07030010030a03000910b40c0a020b004090391502300c131140500c090030044c00c180e200c0559008810040d440641e190f4004010444091010026035802c0700010008000490190310303004001d0303d0001a0241c505c0c084045a011506c0070040d05004014400030412820654684140c40c1c0c6d1140710f80200001103980412003503d440d108a121410b0440d0043c0441102143c0a54068000404100510410041d101d5500f112003001d45050456200006201e0200b40340150889107060b20000400d80ba = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 879113084 1250 879111834 879111841
    0x10020f33040203070303081914241011070801020c0f1c1706030c04181b062c0402070809100e03300703020f2a0622080c0a0905 56
    0xf0049031000039650540b0341030903165111010204694190303840a224540346c14400c10350801d04034001c80c018514820112003d80311721101c0200c0003282c80603180e03c4808001903600321400742100e032030f0610818040e83c07080c51fa51103259003241c0004100000d50380260302e8901e240b000c240107500d0096102c110a02000c0d14949000304102c041d0000ca0001114010203e030223590104240c444151006105005040001c05580e014604255048884100c90300d5401c49940000909800b80c402c9e5039110f0041005071010f00500b940510055808025402d003102800e4603540014151070340a025510341d03a4034401e045c04100240d6034158003c0203e001e50f814100d6034085103040b820941d5a0007640d21003034080541034030000009200080107000102e5108040c1c0104000c2410070700b800c151940e0184c040c06c1c0d41d5511690700211661994802c03030480c03151503c0c00180c0024003607030500c19000d200004400324014030680003a030541d440900303034100300e2408010700f42c090603a0300b400740860308 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 879114334 1250 879113084 879113089
    0x40f1502070b0906070209010f05130b1c02010c08030109090b09011518061d0714031603110c100e0f12070204110910030603110603070e10020f330402 66
    0x1001ca00551086240000380c1000c65a100c02c1130301e0306690000c22142040d65900314104081540d0320071540900720040d80f22010b180b2502c204100c0c084090140120411895485d14a841c01d50000700d041c0102c6011034404160400c0246010304604c000000f101a418103140700e919000411a83c1107a042600c182045a2008544021520001210100c2c1421110100302800302900a084c034001040c40c0304440d070404161050007806580c0380e10200c440400203a6045110481c2da00d1481d0303000e501501d00c0d140c4690300c250482c1a107a00864240110203500711705000300e140501880c0c980320201403480e0442801195941144240140099a130340012920180039030103019201d1551051181c1a0740e10703c20071030b494102c00400609400c2c21900010300100050f02081d1207285d40d40c00400b8141c1001c0003240e010b4091038440c080801c0f201750400442007002d180c58000c50080d103004510900d4200b0007000c10160140200b0f03481d8402c40304e0354180b60390b50303d030704002c0c031220106000c09038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 879115584 1250 879114334 879114343
    0x10906120f110301110d06050a0f0b1e0a02060709051f080c09030a0b07030507050906041503090501020c0d020613031e02071206020a12060e06011206050d0503040f1502 74
    0xa0754400c291014440309070801c50004580b07030000da9050b50a20155000e1542031000070030310b100000004000c0a500c58047c0706190740540070300c1012000b070020521200013102d001d0302d107a01c040d21a00c0040c1c0f15001d24040c1c960056403150000d640030700c0078815070b00c0d041200308001c0c0c041038408803070a1400f030340010424406d06d10714205101c2d140c400320390012032031000c4810200000e022170385070700072130314140c64500400c80740c00000038681800b1420480c03059084920026000300b885003080e04120303c03d0441005602607070280341e550307214400020380c280090000844060701400744070081d220082d0802a000b804000480d40c441c40150020350081e0042402d0301583e502e200580c0419081649010090b400428a12882d07840807000c0041c1d5030000c1c81d03912459911015203c0c403507035501c4284c6603e4018904c091100c01b00056065104010006e50f822510b0400715003d507640020540102d44c40c1c4003903071140c000240c01d00001204a44140081c50000b5a04071440148907009440303 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 879116834 1250 879115584 879115619
    0x14010f15210506220b0f1b0405010203120a02120103060506100e0901061b170405130b030d08070504170a0203060c0403030905061b030a020f100e061504060f120605010906 75
    0x318054400d400d0025011303026100942d0150304112182009400b000c00312400311542009071601e5203140000c203110034240d808032a010b03001507081886911412100050003410410341b554284401055640900721140c0218000e05001919040080c1803140c0e0301041c14480c0c0074007051901d10340c565184c04298504507401440c0140f1100c24406d000005410380a101602c40300b850200d1000a105043c020812a40d003121f000a0400310100c00d2410b4404011440e41d258003c03031a4600ca550051002c03e034081110701d4001d240036156080b0306000302d9407007820002d560142d000c00c1c0071820f00700305030307504002e00803141030502c0e1450780c0c002c1412580d0702410740101e00109060602441451810003071042d2182076a0300e074484900001d40d16818078040800d01d2003041100c40510140c5c3c4a407006030201c0340058a01c2d0b40e51241d40b01651405240601d4000c2c1d43c5050005034002c00a00c40b2001e008203842c104c922054a041010590700d040c2c00004082e07140050420140d00740c0f65100e900c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 879118084 1250 879116834 879116851
    0xc0f0d0e01090b041104050631061706160c080403030e0609090115091a180612041506210f03031b0e04060803090a0314010f15210506 59
    0x141000103011060140402e0000141640c0c69030040c0001c100030088118048201514104007135941e15081003440005102d20704401000ca00d0410081680c034030800e050039602e0718021441302d0f40d4000030fa0001d40c0054444032140c21803014084091900780710041040940d2400359084100b9071152240f40c491440001c2c144105290000450b41304c02c1c3c245c0b454844004c000719059a5140c0840340310f2034000c8030600001d030a441c0c000c0340d403c241005034002501c82d030352101d0034600000100041904003546160b4041c0c0188622860b62003200010b520491113145c40707001c40d400d0068800c1c15207501c0d401c1907604900504100e90030030b8090228100e10360704520251844000c500303099008020401020348a00c907110014039100f07810644040820b40241e03400c000c4d0315035030480c90307481c0d0003040c2c501a8094075200e01080032460200003600e031005000e00004030441d080c008034040f10099030313001844d10700205003000412100400001210300110905621607415950b4a4581c00d0040c92881d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 879119334 1250 879118084 879118091
    0x60e06060a0c0c0b031303020c04050426040807030c05100906050a1209062a031a10050d14060a080c0d080f09030708011406030f100504061806060e0c0f0d 68
    0x1002e10000725040f50060445109a030343c1e82c1040c0c0404540d58140d0300040c0d02600c1200c1c1140740b00c0c2003e100d081c3c811900300110480c90104000000040e0410f1440f00e2481d1505000204001109010441c011481400c101c50a20b1a080c00d05c00c00c100d510040da82401481c40e0100481d42d040421510302c80d40070310303000542d00c000340030000c01000d19050140545241280c24041e90501c0c5051f50003843d00010b8803020079200440c00c606860081d00c03000d0302c0e0710b0b4000b00d401203418100020b888610060412600340007110745e95034103c0350745601c50156400390b14140247c0c0d0903c08015000340003040082c12100d21076101142002c81e00c0e8100820310340001074284000640b40307050f07482d400d20040a841d0b0075552240014060a803100039030b48020309a1001c0317034a510b4001003001e140009000a480c1090040700403000625008200381d4400740c881c8808140e0748a000c039003030410340c40380350001107990a105441503c00001440100c81d1942001915841c21400043d120034142889012 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 879120584 1250 879119334 879119357
    0x30e21090a0b0a030902030c04110f03070c0b0f0103170705031617070c0e060f031506031e030a02100b030a0f021906081501080610051b06011503060e06060a 69
    0x584608101d0b80070b159111404a10300742029410303000054140d0080f02210a00b54070300c4100000c480c40070000681c0072100300322240a10035007201450303004a070f904002001e400700e43c861050715401155102080b05084005004102c007000004e180f204884542c0ca08042ca25a0341c0da5603413181c4801804501d04c010701850030090f902c03101002402141d983d142d201d00b0503107409040c85c5e5050192038144280d6400095007410301440c50880b07400010300825100d1080c01840000a401600c0140c260040c1c4045929251100c0040c000c0c542d1745100859a0320442c00c0028181201201e01600c403a040c0400d02078103590004100303420380d42022108200314140d20008284121280c180302340001900d00010309681c001220318883e2590314403600d2a00d64420046440540803104a81e100c0304408401d26020300c01d03406840721400074014038245031000d448891900000b64051400f14006120701ca0000e60f05000d038600400f500940c4e401711b41001000143c40e0b000322410001004a0900075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 879121834 1250 879120584 879120589
    0x110304142506021011030105100c020406170f0c031e070312020c0a0e070207030305071407091a01021906050c120a14070c0b06040b0d05030309070303030e2109 70
    0x40e503914141858192400181c46001808428000d01c2004054010b03a0061004401030b40107a00030140000c541a245070300302030401049034004003007501080a241014401a00e0341e02c146400360401201c3c20041e0b540e0002268641f00141506c091550429184500c940d11b00140e100710701029041c0c5883e201243d80049031401000c1d500207480300401081e00b02849401185c800d1400c41c080d10f03c2c5181640b503e088400b03040d010b275914801644828000c0010901c40e4002d031054503c5460091300790319000703490030728020481d04107110065030344650003503112054070417000410080c0084c0a0038020b071039000aa41c0c02e540b001415043e00c51000521182d0101c048a0501b004100401c0b403d0400007020002400080b02c0d07510040003003c00b2a45090084000d040b01690012990034540c2d98081440080e01803001c456030812402c1c03000c030f00020300a10103540314006240081ca0503e1550900509648005280d40c1c030710b42007000324000020300c841a04524017042c034450b0340e642640700003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 879123084 1250 879121834 879121843
    0x2040e370212101a03090327030a0b061905030c190806041b060509311d1002040302030d2303090d090f050102031605010b040e1606020111030414 64
    0x51000c8092100d81c1007180e01545503403907a064490b41030001d65066200105031003203101c15a000c0486507c107103d8580007184080e0014180380d104420308440c1002140404d00c0d00110242c2240d0743c03e820000c1003013608100d600c1001c00035482c00719050091800c00401e454030301400c2c00900405003001d181c810790100a642000601d1110100ca403545401d05100110418105604031903070382409000414911440658030585001001280b00c0080c04a9111410302c04000081e20011128000d0100344440e1180090040c0d000749031202c14103090104a0a00002e01c140e00c1c9141d105010900241c0c5000440100441c007509040701941540401240301d24060801003420500010030000d0303500010a845648641d2501d41455403501c84d10641e120f860308d8020310740164414000c0340c5044d4084842005a02c0c000c10000a55a901c0e401290554040e0f48003030200b81e108c0c010040e10480c0800300c480c010000c43c07000300820001125440d04501c4064806807100b1007460420945882c20b12 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 879124334 1250 879123084 879123097
    0x3150e030a0e130b030a12022a0603060103060b0406020f160803030402120a150c02010f090b062218020a0603020a120c1709161d0a0c180902040e3702 66
    0x20215451000700386040d80c175801c7d90790b844d040180030b00000395030050203400051840c2e02c03003541104103000c07801c401c5c480650001800c6e41e0406442d030000241803c0600000d001a00d07288c0d01510032066119a100d1805103d401000200c000c2d03880c2c10020f40f0008801c2c2c0b90440c0d41111a03600c084014040b03940703480300f01c0300041c05071806200c0f860f0700d40d052a401003403042c100380c00038400303503947c1d81103d0101d515601e001340080903543c0c0081c1081c54450301c161000813070400c15a000460a00032803003191001e1040c405129403c08c0b140f0103501d864040100100401c0c44c00758544042038000501c8500c506c07442d2503209032a1900c001d08140a69006102e00798441c00b01c01c4186840000386580d500404143c6903a5a062100414020000c1c4e00d50a00005174100b8200140c8620f50214001c00500c0001001c12031100e52900b100640d0710240b00050440002c0036031128100550410005006012460048e803450514051481c18811810b03d213541c241c6ca40c0c001c2000c0140c1c48000c0c0c403491 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 879125584 1250 879124334 879124339
    0x40c090305150a05010e040b07080603071a090102070b0c0a030c0201140a0306030b06041118040902030a15050c091f032003010f060509031005060a090603150e030a0e130b 75
    0x600ca0401e1518a40d483d21400c1003410500c040d0342d8981881c000307081c017520040c0c50b44605d04005481c5c10300070303412290402d5002d400c4903c0240d0302d2155000880e4101083d01120f600060354229940e0304200800c090040100f41c18035045444011a83e15103081e0002800c0c4801c4005000c203680c0a00700e00000c410b0b024440c00d0b620440a41b00034010029800300702c4407050b454002c5541420503118440c0603820b400106440c00c01c985280f01c2124126210403a4000c0c0c843d000c0c06c0058034240a20444544600e0f90a100c0e159061103290035680c0003031174821810800e00441d0701c80e55500725040c80884003038851510354030b1102c0c1c003200903082000000600154040185405803410401141212030355400f283d20180c5411040342c00c0e02c11076018a916a00030311101640301c059a001540100004040d1003810381c2d60740001094407030a0740203861a800c1c01a08064a2126028029105085c48040c520700752203040b010b045080685c81c614040c00d01c5001403280d01c01540e10101450800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 879126834 1250 879125584 879125593
    0x15030d081e1315150608040203030d060b0309070e040b01050919051e0a0212221e0201030b030c220f0216020a09090b0a090303150e101d06040c090305 66
    0x2d5204080d003a00300c0a0103c83c0d803c190b50385480706500c103100d00c50110501e20720041d1000d260010490300410050301c140c0c0d15020401c440c0d500007540c0d1089100508000f6500d949034034040e41114244051584080281030102c0100300009003000aa241034580444200026858000203043c0640111801c4411903242405001c80d50840c034084006850f4284206e1030703d540d800e64140300b030b801850088458001d80e007010441d00c2d0034000351000105d80d0312102d4000f441c2103803652608540034422403503008a0840b004415940c1c140915000550300340c00500702c101d1401c02007614000714a5000301c038410740501000045540c3c0d0801c0d521101854000c0d51126412283c6c0c943c540c001c3e0382d04900c903c1081100007075400150040ca0070341e40e003140d581021651040d807900050290807400300c0401d81d8881e0030b010031500f90458603000c1c2c00b001d0401390003842c1c40c407000310f042e82c01c90700950302d032403d4580103003082c4100040043e0f110038192000708042d21510016911404d0b1600010301707034041c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 879128084 1250 879126834 879126841
    0x20d0f03110703050f1e07090e0316031206090c0e120708030d050108010c08101517040b010801050c160f1122050705160605060112060e01080615030d081e 68
    0x600c0d1078550711010146e9040e0f01402c18410300d002e12100780c81c0032940214500700410600c0398042c048202624064034075050ba406054000b90121031002c60114941181106070440b16203e200040d20350202c0030084030310b034400c0140c83e03000d03c0f0f680d0a00c905580404107440038000c0c00300f00c008090203402c0780d84841101801e03c0107801c09000f440150741c6070000130118944540001d6014440a00c40c3e68105401c1103260000108803443c00070a01070303110940311007109122181c83c4643c7c0508034041035541803c422a0949102a02039040c0080900000400031403484145240a07800040c10154541900e04500a45101c210b0307d540080544000085405a025080600d0140140410403559030010a0f990303401541c4001e5500074816802000048856000680044e0141080c001c09014282520180c5d55682c003d00307107160103880100490307141006015048844903c11204010344000800d0303540c03140a2500381088440d0000c2500c500e83e080c0d0880343d0b03c1c1d40ea01c000c4024034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 879129334 1250 879128084 879128093
    0x302130f06090608030318161a0906030a0e060c030c09090a0902030109050a17040f060809070305070906030314040b160314030a0603030e030609032a0105070f14030103020d0f03110703 81
    0x30022240f4043c201087e003041200c0306000320b0000e240341c1010350f410042500b0400d500c403034020317031107000c440e110402c1240825680c0c80034099841f50310f8121307011907091000ca21803030503c40040d0281d4030f01390003482402001c055803829140c0807081030f2110145940c6001d416405031503588000381d095482c00104900380000417401c8040360740500202c01441d81c101d501a032261066104516403143e41020601c0307400c0c441c4140b940c02c145200200c070a0b1685a40303d6509000d45030303020b82880c56940900b0010190010640d2001212101031241005d1410002c40300c01c0c8510950303543d40c0c596040941003014001d40503041c00c0c038950f40980d81c0781c0c68407401d42001041c03140000d40200c0c0e569107040d0307503500c0c3c0090300b940f1402803a00618100b000399840107800500814499a00012480e015001c441c400d100b0310703208a0311580c41900248060b940542aa041c004290310745000400060003d80c4940d0100e07840c035a40304100030070400481c1000c4400c1c2c003002c00004894080c8003400800c3c031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 879130584 1250 879129334 879129337
    0x180f12040b400806040f020418050609011505010801050a03020111070b040305010f1b0207060f14031e0c07032a05030705010e0d020c180408042714010302130f0609060803 75
    0x1d54400382082c601d640c032034251640c0c5400895004001c905060440001424940c0001850701a0714082d00b0349005255651070404c00d04a03000e0049a556841703181c0d0624888003403200411003824460007550425000c2260059a1301003c1d052211600b01c03a9581c1000b0862000100030019983d501d03191603160040c06401c1c028268480f040c10320714030702010016032441580d01045a00203012143c5000b8050310682031140d608410321000002038402c1c89041d038029481280c4800c114102511500030002d08070740c02401c0402180d4060010741d0010350411950380500c200742c0118141c1c001e042201500322050940c00402c076002c0480e80700c08104054004007850040101a90810605100200ea0714a885004640e00c545c1c100d1104075421605550140c026004400c042c0c070300742d1124506803101c00044e1108100ca50b80d481005442c24082c45031400c0891482c0d0340d211103514607000940d10746150710000320000c0d07845a0044101c015544824010300c110b04050254a5850341c131907849 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 879131834 1250 879130584 879130687
    0x1605040807030c14011d090c0d0c08010302031c140309030702130b03210a230a08010806060105030f0703050613150302040f060308030726180f12040b 66
    0x81d840c2c5104c0004440d800b400d005401c401702e07220a24066416401001403c10740039220140d64842000720300c41054890141c1d030300b50000c40e2a448041d514510515161805c141207007101c05841200703c001e01d81d0301400452052601101460305c83d2541e8101034190322030341728000c8d07001040c8541c5642440c0a9040032840700340881c00e940010007083e002c007082c0308051000c2681d81c030007003000030905801440030780301c64503020a0310b13207a64400c070609500d00d50028803e6000700301a10010807080200b0002ca562016003880e145066040c000d00d0501da0f4140a04802c05141c3c40700c6c00901652200c2105840d0564015414820600301c0c0200c00e5501c1032038003082c1d02450a00f1024910030855005940440ea840503045180d50703540001190150341d10a000c810459024803030503080b25a03802064069959813a501d05000040440f06140028000f1501c60541020780d0043e2b8411604045c0c400305c0d40000d0b40280d550030030034000c0050302a400c1d5410580901d01880e100d030340416803e400301d07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 879133084 1250 879131834 879131849
    0x712030c1a010305030d020d06030b10240203090d02060702281a041401090806101403061018090b0a02130506191b0f030c05071202091605040807030c 66
    0x1040c041c1902804a80380709010107040c0da44200a50711000b80385500030300c4142041d58000440c15201d9032021990f1205030b84100d1111000c401c144202da042e8665010316900102c0102d00380c654010340a5202c0c0181001c491240c007501c407155040d900c91104403168568018480715001e180b00700201d844064210603040b51080b04000440c02e002103040440f05c2003190003c175814075103085d850078035414403141d10b14100512035100042400080000138083c0f9801c1c0440301c2501d060000342030300c0d4110540468802c1c0d00102c00d200400701103001c4102500c400c07480c400111005130b510342c0d0151180b600010203402d200381c10802003c44035400380203080f1000008104003a07590082141c640a031158102c503502d900c2c6003121105008403015a20088013148002e04210302c0c1d2291007407500e1a102c241c0110316040c500a0800c2024045413014000c10102035644501e07075000304070750a00003000441094606a60440c1090207803040c0d50042c1001412070742c0058aa10b00b1885060803442003c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 879134334 1250 879133084 879133103
    0x206011502030406050d0531031b110d02120709051506040617090a020d03050912070b12040f23010606021f020a0e2d0a260712030c 58
    0xa01e20210486003100c0e41da65607641858840f4078418000c004c0071300445001142c0700e501208a0b2000b0044808500000d43e155007561803608010f4043d80e08990704004809024032010b001803004040070042440035075080784503403001e1021805283c0030054804062180480001d10300c03001c1c1e00450b00c03c40507000740140414413001401014011405184d02003060020601c1d8080c0042207160317485408a012141d4500b500d8000c2850340c88504c4080c2e0000300009054240d80c2030440c42c4644448944000b4000c80e071410a150607640074145100e00100480c00100e0240034a280d425240b40383c21540c14000d9802c0800d03500360720142c0005410040d401d000c00060100c1c00422550340600c1035100c00003144854400c00d400a6002840309002c3c41503c544854840c2ca440c410140300d080d20b00c1c000043c060b40041900d086549624005100e150005014046003000107502440d80c09072605c46010b003a9840c00d45800c2c89680d4000d40c140004001406041c941d2080c41e0981d00d0f8000e90044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 879135584 1250 879134334 879134369
    0xa0e0a0c1101090f240203040b0f060a0503030a0e0a0905010b09030d021615122f031005010c2d14010e06070f090504181a011811040b0a020601 63
    0x542030f034042c0d41020306400d500c0440d0034049070920240680710030064080400031070715071007840c0407a001a201680d940030400c0070000f07a8400c041045411040840b81000828a4000000d43da4483d06a40904120601d19000340c41e807141d4007800d01808065000f40119078641e0001c0c541074005100461183c03050000001040b40042180b008082e542111103004605011210a0704695648c03103d0400290704e1110800e04c12622850000075000041e8000051201c0e0800c3d180162100307001801050070001e0080c0d149004641900300c0b0301c28248416540c05a0400000700203030032803d0f54049a01826145600340002040940030f84540c104284010040424074204d580d62001d1440c568484004141080d00800c1c141e500280c2038508008540d4407a0041820f56013201451b69281041050000401503864048044004907a069400301e602d0410780101d2124182e90140c034180e41da410020940e103d46044802034000e1076500f99031000030f120000e54419007413080400d440030f022181c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 879136690 1106 879135584 879135617
    0x4030512032e0303090f27090503030a0204051f08270d022d0d0c0c03120809122b0b0307080f0f06061e0a0e0a0c 50
    0x10500c105246207005001700b02c05400c041d83e009800f0206100490803154150100700c060004500402018502c500007000318a03005401070100104000c06101e09800410464605445580301000707a482c41503a04554203400d140080c2d8001c01089205100c1c0f100000e82e580300180307200350060402c511030704d0801e1000b41100503030031010a13001c0f820561201428104840c1c0c4058000c941e000c0d00d041d0f210440b14151a0600c00f08800b02003d004840c2d410901445d030210024064103041e400c083c0481c5000c03681800507124000ca1a1402c2a81da0241c4405442070040d07010707642e407120300c842d6036404450403010810b075540c0c8c0500d60540c0c0c10442200280044000b514414007000c07409810400c148100e0003460b4004000e0124984a0344407010841a1402c940c4141156040c00500b030f500341a88401110780c480030a1050340e16055010740b4901c00152078012800c01011103 = true := by decide +kernel

theorem cover : BRFrame.Cov 878956834 879136690 := by
  have h0 := BRFrame.cov_init 878956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 878956834 ≤ n) (h2 : n < 879136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
