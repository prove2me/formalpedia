-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:31:54.054005+00:00
-- url     : https://prove2.me/submissions/cec705aa-ee2a-4178-adfb-48369db31453

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 905395683 ≤ n < 905575539 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 905396933 1250 905395683 905395691
    0xd0e0927030a09060507510b0f220902130b03150c0d0b13060f0906051005040306090312050108060718060207061103131206050c0315010c030315090f 66
    0x502d16001e00100c408032507000f01030801001c006081500d00f425102c82c100152011a07e101d9000c805c100c03c40c17403c940c01021403001141a4103c80c0702640c4082e00b4143c0100341e0212101c2c0d1540f0764280c0140e501c0c0201c811000e204020190101c014244241c01a41c00304402c07005d00100101944039107650007080e010340e0f030b1413002c54220500a1406551462001208112110103904542d101c910f20b1140200903d10000b1840e10742d40968980b9080085021409071040010140501c03900b0018981030f5280d2483c28405113018001d80218030019064503110303e2128101413285540c242c800c02c407500300b0005547c50f500c41a503101405c81e45407000c02c01c0c055200315010011076142003100c103250300401005052040407a240058280d90480c2e5120a05c901420741c01c04001681c0a4424584201d0007a00c0c1400c00703006403140a0a441c101103000c10070f114010315140c03d80300c0540020b08060b0301e440c000e481c2c00c6006020380e1006659910804074040b130710180b03d03080390305c01c0e81d00c01e08244 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 905398183 1250 905396933 905396939
    0x615040e0a050a110301030b090703080c0f0609010b180c0c01020403120e030a021c0302030705060c09011e0f32181f030915020f1b0d0e0927030a09 65
    0x4c462401030031555010040c03004100080d0103140a0303601c03100080540d003002d0b1f03a990340c007105078000350b44210058101140d10b00a00e101000a142d001c0f101d4402232100b03061200c0454008401400340001c5c4403404400034144100f01422100404078020085548643d83e0802c11815603250705c0300320009600401e0f0040c1490002010a183d07500103141e21000d880407a400e4424402000c021000d50000b4812040819414805c1c24490f1070140c504a9a80b441c0a000521500c900c0341c40b075019440f0401002c442991100c140e4130743e45240c3c248140c00b90a2540042c0700c0c035229107091040c40134108540080400342c80080c01402c5044540780d1250105681004403d400e5a03042c45807850080d260b0b048000d2083d003103084054003560300b903003400704409144000e0340d000c5080308aa807100083c414841681004030700e8018001d02000e04401031401c2c00007040c00c1a4280313114803c106032008605002115100070710901e103c100039103180e140310300ca01c1d5141d070006c009410100b409002c1c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 905399433 1250 905398183 905398201
    0x1d190b1c0605041a16211409150108030405011b020d030306061206051302030a060e04030503040308070e0f04110c1506100f1e1b061e1806050615040e0a05 68
    0x80b40c003071008110841d0076030b60100003ca505120718441000881c104060401070006c0701c0c450300444038070b0130401003094a09212802d2802e030307500f050300b0180c3c59002c0c01044803103804420f0320107a4000b444e203e001600f482d4116a401c000102005c0d5000c0508240318003019010f81c443c8081700d0240c0c032a03060b80180b4048003011507403d071141d0b94000d0621594102400b1169000f19444038512000040058492180c1482d4403022102140450300001c240001d041d000b0504e02d52000081c60400240710001740440c1d203505c00c40600c1401035460f0211a5211040e0384103450120b00d0101c00c0b00c0024100384450359089a09807407060182c0b480654009a4038451410071424880d5038a40900004544004448032200c8490800070040b8070940200c00c410720b1080384003154001e4102040c11800c160002c19500c1c0500e21441060303217090405080d0300c42441940c05c003660012400265030355594045050240414a915405540000c011038019020078205028060108042100d6501e100b90 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 905400683 1250 905399433 905399483
    0xd09060201021c0f0608031204051513150905121b1504030c0503070c0303080f090d2316030504030510060506070206030601031e061d190b1c060504 65
    0xa5403103580064445410b2881c55412160381415541303400203c0319903880071541150000659011100c1c00c1406000a01c03e0800040741083c1c0d42090310096818110900384920103c0417006182c00110481d00402d18010b511a0500940200641e20603400000c558074040e80b1806a903001c0582030500e11221944c000f4006241c2c407410562107482e42c0341d9072402e9481044800048a031480108508000a07080e21031690055220b074a50f103015050610011400e14401040c0b005141d0061488401c407581c1b2600e2094030045110740d40704151000000c4540c1e40c03207401d0140e030780d41d5404a940020568040020400c813070059041d01d85c40480c026000c8117070380e4580b0400398070680c1442920054a0210015904400141000a06201000040c02091451300c40b945013040c0e0b5200100724400320505401072041d000259451a4034014030040c11000001c82924026640c80300c40030b041d038680e020260545c500980c0c1c024902e00643c64030300d01030315007291b044801c1c41032440000342081321454 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 905401933 1250 905400683 905400697
    0x1207050606060702030a1a010e0a05042a1d07030e07060206010312030e060403110f030f03190b03031306090f0819020a3201020c010203030112080d05090d0906020102 73
    0xc0c141503280c020402000342c00608050740d150240f4440440020b42e82118256010982c40c2d8840e000d41c0760a0b1040400c8400410301e84410342400300b00000950144152040390080c80210400075800042a24410b00715421520b1300d003042c0400c803029110300c109405c0c41031000d40e07000d10141504541082c0c07030302c0c4188501d10250b0b2028006000003a08050f82102c0c1404c185030024102828810492503c0000d82d025400716840841040492005211a50f10494845d004501e40308a030450309000b07100080122b4445840071759201d480020b981c01c800320b0001c000741180d481d01c10f8001107005c20201d034030690000ca2400600010750b080c020809008032910400030f002c0c0d5140300c1c521044c09100d002c0040303078001010400441d51240d03441002c000c50356a6a01c02d4041c1c03a16140c07968000c144420054155404a8550b4400380e03400003c41e8151540d4003030301ca080340401d107013000c03c1d805010380c051b20680c184000c201c01c0000004d20072000004655451141c4c60381e07144203a0803441400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 905403183 1250 905401933 905401943
    0x2109030b07030f06150215010b1803012d14070906052a0703020114092b021e03010b01090e070e0d120e01170105030703020d030c0219081207 62
    0x10808954000c03080e03035001815082c042050f000c0500c110f0100c940541100000040c1c3d0342c1440c9200344c1c1005595001d0701c1c418000c15055041c40d07625406802202c0c8070318030003800388018404c3e9880a421411911207920702003101181c4200c80c40e010400703030308588261146000300044000200e005042c1c0030b003e242e1070300702c001070508000321000d5002940f0f07a0542155852110b162030000328103081c0807517600c1d000d0804281107200040441140000c400e80d048030174080070403281d444014011020301d200c04151100c442c61014084001e09510010b940303d80000c0c0d44401e042c50241e00000e44100490003040202012801510322800602400340c869841c130000801b5a402034901d000740e01c40c0202010400c402d203070740c1d0300d00342e00b50224080001152480c11141c07658000401440c1280f089030008c5072903050501080d5111607610002e44100844402202810b010b00001490070b600904000340580a4140c1028905c0140c851401644582c81d41160400036001c1038a0312076030f0013 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 905404433 1250 905403183 905403197
    0x1206071b0f020907110d050c060a0c020a0f0614010e040b06090a061707030b01050a1203030207030e1801050906010f02030706091a0f0702120708070f060f110721 71
    0x600d0460000d08a88008a40d0340802140300000350b40c3d03584560b4801c0e005513992800000581404d0f40c1000c90b180408000d001043c0401101d039440071407c40c0d80070090000c002104244903400701c1c038201c0c4001c0040c2021758080c0c08a4103000003a000880056000c1e0840c03030250340e8400340014001000c56014061885010100340c2c6450404620ba4206c4008200440d00356102c0c0141c031042d55098550780389641c407081c820000c100d207030601c050051a00f1640000c80c50b29100001008101c543e00060426a00040d00c10070140101034000301c0c840080c1144125015440340708143e00000c0c0030f40d40c071440841d000a55a50311548000800c0c0005170f01035414a4110f80e15800a00100d0703504480302c5111042c4100aa5981600188108208150107807242041d4402a0408034843c51260800008216641c04100000100c07a40c1c0f0390300041c1c1b501e0f400c2071414590024240c5003c0c3d0440f603410b16590103401855100600056401801403005c50b410030310000b0441203a010040d0081810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 905405683 1250 905404433 905404457
    0xc090109150c03081510020c1807120c031401141e0a0506070f080304030513060206040f08030a0f0204080307051006211b150e15030c0f0702030106030b010302120607 73
    0xc100e64107500f1045e1a094514030700380c0b2000188100039503414960044c4d00512070f0b9186071030100c0481c840ca03810001541c3c06400e03c0ca400504503440300000d2a4010b4552003540d4106100707510401a004120800394070558540100191303901070124006d2003049080c00d800c0c0c21078510014003040a50007410401a03500e480280134190708180d00079202010360403129008103c89100135446a842075494650350248a200e1525001c2d45810010840d4003040070480011455412280c800e40c008003a503460740c0c0d503403410344003501c01c031548601c41c1400440c00041c100030000c05820114429801d0f284000102d446240403200180300b000044e4a072141003164160201801200c26801601c00c0307918994488201c2100481d1540004003a01c2c2d0108008a1580d102e1190340c501c034412140105010007404484295000190070b0303400c0b641c400240104041e400d2411203d04650180003800015a01d0401000d0072100344000e0b4000c1100e00244201d00b0004266141f04440c41d8407082c01d1800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 905406933 1250 905405683 905405687
    0x7032a0b191d1c09050603010603020c0d020a021516020d05010614090c07020f0a090e030307300b0d05161e0803030a020f22140301060602070e09010908030c090109150c03 75
    0x50303c0400c22040c040703003441c04149a102c150045003e44400d450160f51040e0318180c0d9813519044007014011504081a044010394800a103010241d8503074140c6a00d0303402c0c640c503d0f9221030046000a5001041c0507030402001019004001100c4100115032a14201d038410b101c10440100c0d001c8104070380420008005150000d54005510300160030003800c0740c2c03201595011600b805609200716800401008500b5610114000303039000300c10400b004e13030134540740002c8010786480d41c0002c116480c0c2d0101c928503150b003455040040e800c0422600c116650708807184000185000305440e0300c1495201c220644505101e0800315292a0011451650303020f81150094106500c030170100308040080144024031380488030441a14114580344162410000d41d03c541d0b0500f504502036410204200429500407070b01c0412580c88484c1c103009503035507448590050041a000a080c1c0e00c0200601100601c124050035140f082a20f0b075415943e154009100751800d01924080010032806128001034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 905408183 1250 905406933 905406973
    0x106060806041d061504050105010e012c150c0c0604030213050601030b1807080a05010518041704060f090e101e03021e1507032a0b191d 60
    0x100c103d0f11a031080b007a8143c03014148001501c0e07000301002c103809240400c0c542442094010242402c01c01c08183c500d0001900700780181c0f504007000000b8140008000c0070441d0208201c0030024101500340301c0c14400040c950f00a07542103405441600007248050030203070205c2e003d40b50014804920454008015406400001d02c83c0781095280c50001030039031140380c8600c3c10410201c4000d141d40c600340c100100341050092040c9034041c01d101c0104229120540701ea10740e04011080c80c070707995031241000052110f81c2c858140a2036000103001031001c0d8026206407840443d5903c40d100c1959600e08440c810300706a8a110440702841403c00c065006012040d0101e003191741100300c000c3d03803500001d0b589101c0500d100c1034035082000000203440d108074007604601d0428007160402d161502c0c0184902c170440025204108070310b18404031000b480b40302421b4903034041d00720242ea1400e0014030074080710010079194510300304411301090454001100780b0b05526040240390b165402c168800e000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 905409433 1250 905408183 905408201
    0xd080f0c0709111b0123040b0702010c0e0d0305090901080a05070603090506060d02120a0503030601020d1701120c0e04200d21090810060503120307020607140c0d020d080108010606080604 82
    0x60b40d030343c4a0301e10552051a50313207840c01c9482c6c030031401e84d0310b400d040c284050317003004000c0340c2107900d00010343c004181c000c510010414026148880405103900d0300303032040d00c20284402c1e40101104000100e0400014200705018032500607a00d94070f0350b03543c0590035150002d034000c000e81c101400080309814100c09400150b40000c1400c40c0c5c0c21901c503078050501400301401d44090300004200881c6503010001e9501071040340c903143c0d0b42c08025084489901c60180102484c03525810791841c18804103a80300809403100c4540c000041c200703441d040c0b81d0303150020000c0d5607029000541420519001c60981c03500d03a0804180014014410441154400500c1d503480603c08e00c01c40101d49050100a810064500c440700050800e040c481010b00c0c0000400702490580020020410403d074003007000d580040140c181400c040c00342c4000d08249004800000ba624400c0d44c1348065015400180d5000541217a1503020035a622910b1003820383d4458061035001c80c00c184045161810554807000744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 905410683 1250 905409433 905409487
    0x150b031329041b080f0a060c02010e030a02030c010b0d0506070305190905061005192709051605040e0a03110c030a2a0f090b0d080f0c070911 62
    0x1031030301d030366030000d0550805450954032103100000d8080a02e102d5141c04001e00070940c0140000c44481d5141c0f543c952900328020072143c0c46d2403082500700e0003508810400305509059945508030008001d41e640c005100c4c0fa200c07982000e06400240c02c144820b1298550010042c00c15035650302c405502800001e0f100415080d40072080400640280c45a1144076110720090078090901d490a20f00f01580c68100d1441244050150036040c40d1207500c020460302c0c4039020070074048003941040c4180610001420146042495403030800c04046840c2c4c00e4601680d090b800869110400d01080700c804c0c20741c01e51b0035400040d9000109005110022800701120704a4010003050000f1a08002000e0340c221880d40100701041541c0780b5140c00451503c281c5003045c0d545900d80885c0044c1d582407449100c0d2029620240302c000c0380c4803403049202064101c0d00130740e038580d418980741c40160b12906845243e801500d9012901485500801103405100c680c6e10b800c0002e02c4140810100c6040e0907008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 905411933 1250 905410683 905410733
    0x20304030c08031326070f05070308180925050d1506020d121404020d080c250b031608090316111806030d050a021609150b0313 56
    0x1001400c0c41c0001c52140881229101c04a642c6103000c0c80e001a0740c403482c0c004001540011008200d01c4815641c405410901c224000801401c8c0346090400a0300090802c2c00c1c001410041c4420040c184906080d00751810007441d5265190700d20b502071444040030011030000880c04405110720064401748460600000d591300c1c43e04481c900b0b5541643c4a800981c20600c099070150382c10103a50b00045140310000d114503445090540310700722004100078424043e4007508010b008460098686101e1034804540c5194480e0f120050042c100c03400c0400705120004c000704038072003880190f03402468802140c603025943e100090744c0e08903008041a9091200b0301489100040001c040d8410b20300414080c1c170a60594000d0002c2203d039a1a05452210820103010103503c00145d44810030107140b030a40c2d243c1c04240003ca05104a00c0703490182c2c02c1074614049101c003180c0c1e200007600b80c14811511001580c500e241a101d010403a03091140480e41041000403450040702da0a02550201e8151 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 905413183 1250 905411933 905411957
    0x7080a020f070c031b0f05011b0b0907080601080708030f0a1b20060f030402150d0c0203030f070f08180c1c0b0108070b0d09110a03120e060405010e0402030403 70
    0x1501c01d401c10442600e14180075039080050007403011030480c030000341d554030142c0d03c0e0174a0301030f04111490703105560400251181003010701000c0540040b40c1e07603114298030201d0401c0c0200640d00d03101806100c0c00d9010300000050840c000080c044211000c9202a40c02c00030000303206042504a44840014049000c244500c628080c0e0710f0000f40380d101c2d2030681c4009e00c4041401000c070303411000b414080d860410a02c2003076410720095a0703000b54116544800d040c00414007d01c0740c02160103400760507091401c2c0b180300350740200185100710200b0300700c00138541e600182103e041c440c03c15141c005c00e00e0b100102d07022166450603008040f550500719110b0480101c08120303c0032403040800000ca0780f0012490800114440b4940103200e043c0040ca00c642c04d0440b0000c2c1c0d80303d60742144000d80d60703914003030f020481419610740402000400c001c04c595940d007004462030704480540e500164000e00d41c6802407603c0e0040d68203845060351140306440c500b0b007e11000750f1004d8001d07030601804204030f03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 905414433 1250 905413183 905413207
    0xd090314070321081614031f0f03050f070f05060d15060519020c01090605220e040311010501180c11010c21020708030402040902060c1002090f011707080a02 69
    0x459040f40001401024010036203000702260406420008100c81e40c0450f00c14240d4001c2e030804604200e000b800d5920f440700d03001000c600a14070b4404200440c116000940d5000300d4000c0e800302c9020384181c603034442d094814107440e030303141c0d0140c00d482981d00316042c880307400d01c0c80261504400000c40060f1f034110042040e05990281d03484103000410024008000c40b558000d40c40d1152000d0001704045044580081c02080150042408001b0085010551082400101000700e03141444581d4041d888943c00c0d0380d000d100f150f054000c111070804000403880c0501c070300790485211901307034004008a400c00401800d110150712040000081e081d164840080c810781403880c0e0180c44004804021000340c4440c10b0402c104a41114410301012020035154400c40f03078001d5040b1000aa50302c07040c40000c48600841d81a105548101d40c0c4800c0f007001180c2c0105151030084548114038440003004540790b210404007410805c03030590114480e00c1c00b9502c026040b0308103400c098203104049400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 905415683 1250 905414433 905414453
    0x6080a0f0b360a06060f02151801020405040e0703060e2b0306050315060a080304080c1002070815041707030f0c0302010b060705070906080c030703031103040306050a0e0c01020d0903140703 83
    0x28a00f259185403c000c8a6088500000d040d283c0b030020340030b560300d100031a40100700d004040b80d500350242a145840c0b075400b941250040d0400074400c019080c03c020401c1d59031850383c001210007034940654500410f0002901d041100d8460303081c030040321264040100c1c9a03003003206203014103440310000b05a560702800901c010740400e01043e03100d440d00e5000c005070440c00750b00642040d0010001406a0703080810f0301c0c40d0740d141c252080d401403503100b0400c07890049660700c542e5042c0203003415480944428241103006600510751000740d80e0000d10a140284114113000300419050507614800341d000301d50b0f40103034034003c0c0000214500541c020400c242c0c0700070011541038000c0002480703800701078490040a4050540200307600249940072a560740b43e5400040d06205010b01c0c091240d0004004079000b455102c14107020364101041450003620080c5c2c1d0207071640c0103185800000e5440010015800c0115070f441a036074a2858640000280d5501b0404041e401142c0300400403d80b8525 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 905416933 1250 905415683 905415691
    0x14010b21040501020c0c01180b070804030c08060907060315061b121110050705091203221815090c1209050d1805150d1506080a0f0b36 59
    0x96031721959901d9480c00c04011142c81814001c01c411007000000200c00614159401c2c00790b0180e85041e242002c3e20a401654002440b800602d0b9000c0303007039080031514a001e0b8508004403030210744c80354400c4d000e64081e080705030300d2000320b440c0c20802d8038031620201180c1681c0c80402214402c003515049182c6404e920030802007038011410360150201007003210400c0288400812540c240140020b12911460340494490081041d514103c03001c01d104a83c3e440a103165403040300f1035110030501c0d1640031881008a031041c0c410844d646858a400744100070440844a16481400c10710300000600c2c0d9441c3c010204010700c0320b41e80c0702e17000910850016a000b0f20081080561901c0010891500503000584440062504200c0c13500d40328071801d0000ba10007041903da503e44941c05000f010f5460349152a8440c900d4001006138025035142d01030b0000c0c070014005a0700410b208009d4036004190107420440035401244203900f00241040c81d402d125040c0c2da41642c2d40c00b19010b030300006803 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 905418183 1250 905416933 905416943
    0xb010c0f08130b0c1e160e06010f02060f061302070803010b070203011121041a0a06060206061009090b15030a1a09130201030b0a0902070503040509070314010b2104 72
    0x2801481e2001e415403544000c00207644030300c2c944000c4010054031001c58251507a4014112003184d20711080601c91038406806c090082d0104a96030400308034904801c1c2e4449011841c0300344640b8800e480800e074a48204000c158881c400c2d11403509002c4055031113004480c21960920440c0c0000304400011341c000c00000813215250030b8640101801c43d2074004103400e03504820800d5a42c0509201c400c3d01101c85a4000c5440542c0d507400d141d100c1d0502420003000c4541c40600f0414246100e03886201520555800ca507440e90381c0c003007403200300c0308040304900210b0030034442084415020380001c08aa80d02601615000105051166050700141c6001d00d1141e2200000b055404800c200300e070030100212260415801c0084404902a02c031040281c100f603160044140030751103030b20700d000040035171420840d03032110a801c0050b102e0304107020f4248038801d4000400c000350700c28000c03200c0c020a50910030f40c40ba40b03484000d0110b6846201d10307a8080b01d0102c03011011a59000c07510380301e14094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 905419433 1250 905418183 905418187
    0x3090201083402030c1c09030b192c0c030c2b12030b0a0b0f030a0608370b1f050a0b07050c041e0902130f0905060708190b010c0f08 58
    0x9001c0740746c1001071010180e8120101c0d101e1891645a102d20501c00310382c2c201e043d2012a407549200304041c100c4c1b890038036083d03504000c1800905501d100ca42e900e04c410f042c95109590707441076245502c68202da40344941c10b500030480701c41146040d60681c41510f0240d10100b00d50320312182044000451240291500480c287e1442c07070164050080448a000490f02e02d8527060811000144c02e01400075000700d69100840001d1040c131a541c400070150000b8021184503c42c01250480c0002844400800c005101c0700c952961142c040e00c0c4400701030b80f001c800041aa00d1607006603424280d00d0203007103000581000020303291139400d0340d803002d086209070603940c400795401c00300e00d8040b05079100c5002d00c3c941000450392002d4903000d8603041c0c80440001c600d1102c2c1d400000ca180000002c110031007480c0c0f92044501c03a1070b61b8080e031440c62280040e1071007075441010135140c0802c111060f186008801d40c50400241c2c3c1d590000880344814140154603088544450030000e150752400c444003200 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 905420683 1250 905419433 905419447
    0x100f150216170f0610060509010e04050f0615090906120a0c08070e1f0303030b0301022514160302010318080d1a040603050307060207060b0909010605100309020108340203 75
    0xe1021503c076400a4000702100d080445240b181411a0300c12a03007006001f080e0800103170f200b003134800822540144103100760300b0080c14441c040b40007581c5091250741014149103202c410306d81524244800100b0743d0095544020030300c481c1c200118405001c4c4d000d034034084400036100c00e0725440500498001001001d04159044002c1d00d005810b54614000200175218000c0c00c404c00001642e5142c5004254004140302090181c05400a46a10380e1001020000410882c000200500d4020503890410041780381d04140c072203144e8004080c0c08a020403040c009540250440403402c010380459002c1400e040e151170700f143c0c000c3c52680002688440040c883c95000202010149404441c00c0006515681c2d0365950384c82000c000828040e00800e484003070141b141c1c070501c0c40540260800340e191820f03501c0540280101d0003482c0c030405980c40c003d031815101c3e2041e242e94a80c1a19041e101d0b490703010000c40f00110139030311109412004c1e080340644402061000c5400c2c0256001103856402d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 905421933 1250 905420683 905420729
    0x1112030c010218120604020d1403070305091005030613020a020c130504030228060e0c06040605030118051003061a040204170601082116020414010e100f150216 70
    0x18003014028881d003104130311242182d0020412940040e0704541002c041d0416141600410000c54460030060001103481c0b800d02d90804000c00000b201261020803c0c2301c090400d8a1034001070310074507004020744507490b030b40c81580d03402082050858011203028114003030004400b010018800303242152034505020030140c0400001c2e2000400e4244081005000c03c9041d182001e452005890f00341c880c211080c0380c100c140301442403d000a0300c181d0341c8980b90700010307181d540280701d25030518080e00800304960441d03105103401440c11a50000241785036880742c40190180112044480c42640710858003a1344920050000300021802c07020082604c0ea155420004142d004412940060b02e0305c00207264800da66500341c041c221039868a0310a0040c8a5801001402e8000e410a152003452040c0310300404e1018100d400c0e2000803801d5548800d00c0742c2c4180294460b1a501c0300340b00c0e005110040c0700440162a44600d881110b42d0702c41c0095007021449103580c4161020b2000104035082c1ca1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 905423183 1250 905421933 905421967
    0x6070c0e09070303020c13110d140901050c1801050d0501030506100501020606310507080604110901080a180506040c0911070506010510050c011b030b0a06020a1112030c0102 76
    0x1c0100036002e0b291454a001e0b440d8480c024941c0d20a101d03010031541a580164804030800180c034081d2a141d007420342d9101d008002d500c028000b40c201c1d1100065202d8014004d1038030411081c0308050030a03c0f40790f400c0d084240c00d40701c3c01d410302c942480100030002040c45042e0007140101d00524850500c0d102c0e03c211b040079600201d045402510070007189071201c5600342074078048048038241c01162415003d05007001d00300c490440c14108800d000d1500e90040ea900c1c003419044401b02b2805003014141500707803080c43ca00d540850152800600452002e82c0150300d00c62104801c0390707032640141e40307081c00d080c0d044030200c2c2d2160545105001e140024800c03c3c0100200c645c00c01d152149580b41e071a41d44c00140309662041e0051800142d00303d114034190b4101490a40081c05848203054000c3c01c0c5c207d2003025480043e00e411180d0f140f9140408005c02201d00680140c001480c190312103189280c0303040181504400003c610501510040000b030031208a0362000585980071040045514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 905424433 1250 905423183 905423191
    0x406090c08030f040b09030309030321060a03051c02100e06010306050609062407080d0c0e0415060e030109050f03040612061a030601030914150f0c07020d060b06070c0e 74
    0xd90b000340903020b0400c1007082150155518100c0c2640c036061302c1c2d40000e01c0d501c62904981c1d018000031801c5860038580000880861142c0c070b03d18001640c690307050204010349488060040d42c08020300881e64840c06180c1d40807900e20384180c88a0040070a1032106a5502c0452401e241d404030300108107020700c0d4451107400501c2101e910050f800e03d540000d10503c80348500310150444d412440412111460032504034552002d01070344c4807021424400014204012290080307421400c814030640341510030700e004c405e0340081c18100c1c581001002c541d18503951941c142c04d50340e11511350300455030401041c1d617503510320f02c000d554407410054000e01030003401003440d0005062290038040003000d000e000825001010b1700b00d89a40d50140102e024020052001e44000c0383d516000081c42c40104800441050f070040c0c1140549403419041610407040321800300d0203c05002c0d01c0c0051501d031b140380001c90700950000c1071241480340003c10702d5210301c41c03c880d1042c0c003071810004407550b10307140f580c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 905425683 1250 905424433 905424449
    0x50405090d08070504091508010b12100e0c040204090608121e03060d020d030801080d180605030910020301090b040b04020702150f1b0a110a031203051b030406090c 72
    0x21038202803004980d110700040c6103800b4001c102c00010380c02d5225400752801010400070a000c6011201c6246a5070502400b03000700d507508003500051107080c85010014030b4401741c00104444885040864014540461402100d014080c90004903584a0016201030104108001022454002a10b241c034003500020b4000300ba050211031000340045a000503d00e075414030180c0c0e29583c40340002d450703402c8400c0080d413040c55806070105242d403000130b850586030034004aa03c030920081040d601d0b440d2002c0540d10582400b070040c40a10b00c00d001441d0001d051208855002030302e0450311040e80c109801c5442d40507914100c034902e81c42d02d8010524907250548045140c14420b401040944100c81e0070fa01380211300103211100e07050f002d411101c1c131030344241300e9009020103504070540760400710400340c5c0e01c240740142400700d40c6001481d801c21241e00046030703000800d5081c41500a40b40c0180a8001c1580d4004001c150004c0da00086103c0c0740301d0b14000841040516285d0740540307564004500c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 905426933 1250 905425683 905425691
    0x50a150b0307050307090816080105180303011809020a090504020f12601009090c0e041a01080303010506071e020a03200306160c0201030e0303011e0504 67
    0x841040e00480350003620524210741d91342d84051083d200d0b200d180e40502d060b4450841801000d0418810300702c01c2d035031620300a006a40701d2100810150b6000401014030360810001000002401840c03c4294030503414045424416a000104030860544c001100c2c161100204411880c2400105044d0201211284540002481000c1e035592031804a0044540844124600250a101410070000702c10060410200001003210b003c84040604050064100c44e00c1140704042d11510034850019101040326a524282600001d04204542611100ba20b4003012503034001c40ca81751445580110303504501344c507980d15008042c0700164416190790304144010b1103c0d595040c22120355582048c44191172400b012000c0c110302d00c01501c004d5001441c810700000700001e00201c1c0200c4000042020000900641810b444540c126014000d07541ea250f02450014042d40c00c1e1031401340180b40c000f07441500101c16500d96030081c0c205540c8a00340841c1c1100207040071808402030441135400b48 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 905428183 1250 905426933 905426939
    0xc0804031e020c06040b0a0e040c05160c0506040b120f0f0c0a090906080604020118120f11120610080f1e10060605070c2106051018050a15 61
    0x4004600003610380200400a08407096800d10030041c000140c440105095a900d5031035000d211160300c04040d11012943c0c00c40001054601031150001d1801143c0728149000d07400c4110541d03000002008440328090100c000c00d40340c031414013501c0904a80c0c150b80390344805000344d80d10b110300014101e601118010307041107500c02c0741160f0340b41c104c07000601c050707140c0401180031365025469030810400140ba005001540c0c80002a200d405103000303887c0c132840540d0315114045139501c80d014a200c0c10360b1080c008000104594240d210041c0510005a0050155800030f00b100402041c00100350340200240180b50022545120042c25000b00818120305c02c1040e07903840f010f40c10035010780403022500e0502e914806001800000c25107035000c010484e2209c202801540000a00b62842840200302107580c1c21940074604400794011f00407140e04010fa541c0901400c030081034101c1081d01c080c0c00140060310003815a51800030320b507010419160090200d021140c0c07040d0498010f8075214010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 905429433 1250 905428183 905428187
    0x2a040f02030402030a3207060912030801140409210305090c0306060d0305040f0b130f05011b060b030d080910050402130b0a050d03080403080a0b030d1101060e010305030d0c080403 79
    0x1c9142d640840b2006c40c088100690800305040d1110802c1c0c2e20015803405c41d62140082100400d81d000c0e84c44a0f1041d40d00c9044a40108440c50780007800324003140700502400ca4050220201031b20002d1021038840c43c140e4408109103a981c840500211a40f1258200103070540a115800803d41c001802c0792000c01c0d000a40c0d50f07902600c40c60003111540e0300c020905109030111009018031080e032410703495894030503500300d500c2070004c482003104c002000b20781c108508200108441d8141d45004402c20030301460703801c040000707104840040d50f4411100441d2014454807206510640310808e061900005150805800204986a1900d1b000420005039108501c241d41c4000d85400002c0048415010031144411504460b42c0034005503403c1e000c1591041e0001e101c1c511030b1340d44a2a680f15002c8020a46181d42a480d600d500042e0030740d2180b030711aa200f5015804000d001003080d56940301c83c4030003201d00f0382007039034241c10010303800d406c0c0c0440b4051205040c41e03901d00301c1a185025200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 905430683 1250 905429433 905429443
    0xf0c0d0207080c0c1e01140d051018020901080c0903100507230a020a0f0606030506010b2107050316050412030e10322a0c0901180b01022a040f0203040203 68
    0x2041d0b050240400c1f160910303011100566006404c8103208001c10b060540045580c000e2900c1480003188505c1b21005401406000351003c4a106865081c0c01fa140c8004c4591035030400703044583c044c4034000604541c0c00c500e00580c0e008118940b190704c43c402010258088220301005060131352101080900c011a90000c3c00c1300c0004d80059814118481600d02031020300241e038009091031203800c0011614080c240001e240b000034850250708810700c0c40d5554690720008850032404200709000050819041402078003040748145001440c00b138482da410359205d85590001c0c2c0c001910401c5210f00e0b410000948841c1d89078034213105460031805c4071001c20145092450700e14840d442c800e5483e050b441402907540711b100b030b10050b41204a4803120404142c000300c1102841b40308417001c0300400c2c01c242210300e068518aa61001000089044c0040a4045080700324114424049c0303080c00d000780304e1111054109598031407844075a1030000c00060301c3e0200400b01001d8030410038000140c2d00091 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 905431933 1250 905430683 905430739
    0x60f0503070b0a031508070803310302130209041104080708070b030a0c1202070b09060a0e060c09031903020102190908030a210f1b030e060f0c0d0207080c0c 69
    0x207004034a0040e420101c1070000840e46c81a5210702c280b0002041542002c0094030b00ba0042c02c030344100c0010304907041c00b10781e00c0c0f0542c5a5000144c004081c005803c0c070b01030090203129600c2000d49403d040d4000b28044505490b66015100c00c042000c0c801000c0501022000700781d01c0000704441e5052031580282440302814000c00c6030359903120074000c24010485036000c0303803100350119107a41c50b40c00d00c2c400400d0f0840d4200c02c40d025080015500704168403500009000100040c48203035903141440c0d07a40d51003400764541c140709240071500c820108036024038180c6e10a90025898080402e510f5200b80f00380307203c850174018205018011840e00105860102000c0e00d01139925142045103010300d00d0001d4900d1071482d04203070307510060111580114403c2c42030300000b0341541c0c25000d0100c00b21080da907680d220681110b008500030103441c3da85250041d04510a903481c0c4845e809a02c0100e03400224202c8242c800860086c8114505008291460b201994454003009407102c0313811003104540303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 905433183 1250 905431933 905431937
    0x2010f0e01090b030a0906150b09040b0f0307240207150c0c0503010f021b0309150705120a0905120607090612021303030306030c0b07050318010c06090303060f0503070b0a 75
    0x3200c5240580c881c0d210380c0001c0480000a5903203040c500100c0001c1c06c81c0700d070155544d500700404a241d00040303070344507021030700348650070390400d003031101000040c14401400c1c640c00307d520140c40c40305a9090211100411a401c0800303400a101e81c0c1484880352440310b00c3e02550066003040000b08541119081c4c0c2c070816281440058040e86044540304406070841a0150720302440202006501c0e0300a110050071050808a51001034403e1907491151000054221402826107921541e40e10003505d03c03248140240c80d07650598088051030303a00458500d01c0000c1242e10108070505200440200049080700602004d241c0501e0140c03d4080c14440e038020448903e4481425000382c0c0d05446001d40c0e202440903009980c2e040c000e01401b03880c00182d44603207102c5000541056644125400c05600034042c506007400c0f0445a1070320401103072080e0500404180b8000052828800e1075055032007901c0000308241020100031440070180c0100340207078010309060000c54401020f0329100c2d0618 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 905434433 1250 905433183 905433197
    0x1b06080a0506120a110a21020d080c03030c070c06030b0d0b070903050a060213060801030c05010815090f0906013c0b13091503030813080c0a150c0c02010f 68
    0x607004900a45807291541072540500b000700400c0003800c102d03014030590106c42d89403105840d80c00c094016580c8412880074541602d44200041c2080031007072008a0055101c541040c3c507240d21141140d01c00c58202019610020740403080000d08031030000509118602007144104d01c502144410400e5000034110800342000250900c0c441c0f03036800d0203154010251114030b8103515000c00a0340050107110070412200d000070510380d1103100c034103040740d070032400f403100091401c401035030401c00141c603050480c03408144030001a25448540c90080e2508003030110381d0701d0044025410204183c004412001800c01c202446201500303848040a0b06090030003910201200301001c00350455128844150010800122001c0721200c0c840446040c08000e21429031b0140aa882c10312007400003d02090000303010411052445034035082c414410651285081c00c440c89192801b51018411200d94140080d6161900440e00592003821401c0c14160450301d2580e0000e400c1a68449404041000c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 905435683 1250 905434433 905434441
    0x519050307060f0b1509040f05091906060f080c0a0b0a200307120c1e080414010201061e03021801030f03050a0c061b0e01170109090c0906121b06080a05 67
    0x80d030000750480c1004100a200d94100404817000f90491103583e88694640106005401801c2c01050702c01d0902102602d034078161a8442d0a811040103000d8a00d603580300800315400010707820032000780c03041c60020540c14980000b001035031540c0b5007110310050400d002601d481504860651041c0305c440a03460341c1140414542032a502442c000603061065903018040b440e604100024072840c0982c1038000b401b11091869201d0901c0c00070004e10b83c020401042100d44103480108642c603005200200d441592108180b5581d10a0b0b50350011804e034201c010800c6240101c1c40784203c0c501407140500d1589940c81380c00682d600300c04041c040c0030340041c410742c0080c070036140aa01c1e150300c0103041006600c08031406c800f010440d44620041011540030083d00c1d030084c0c44011400b50701b058140c107140c0c00d040e1080080e0450040032076240c07c2d0f00c03401144000440c06180040c044002010b1402515800c04060042100c0c103840c16042c0c05034410b001403a404816241d10000b40c2801007000d480d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 905436933 1250 905435683 905435711
    0xf040c050c010603110a06020307020f060a0215011e0f050f01050a23030f090c030a020f060d09120206010b2706070b0405010b0f0307080703120512090109051905030706 74
    0x4076003880c50080d54070f01500442003007a5000d407220008000d94050b042184c986101380d90f01c1c03042610180d440020111460f419180aa005090b8170b8458410342d4012a080a00341410000c2070b00300707101040a030004115502040c1e4104002804440f0100707500c0d910b0a8081681c0940380021107040003800904003a50a002d00002849100c0c600c41a1003903c0d2005401081d90301b0030340c0d0244102c0c40140108120840010719000c12490050140404843e940d08010080804400043e0058403c0c845c0e0100d0b0940d9201d40c1154a0050340741c0d0340f0301601c9280c02401d089058000d600e40460500ca0344d07245409400f061402c540a00c010b412000c90510f00156860050404c0200002103000410040002c1034120304100c034000e61b0001c840784184020035881e2422401070317601a0748401410404503120034a03000540405040c8035141c10800c7c0700c401c0c9e051100b20303034000c1d107a915518001c0400c0341c01c1002104c603c0c1080c402840c080d00e00c0d51402e4503072140c40c2c4007a140c2500d41c0503425800c0b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 905438183 1250 905436933 905436937
    0x40b10080627011502060109110d05100801020d02090307150f0e04060b0706090c0f0812250b1902040b031906091a0114031515071b03120e0f040c05 65
    0x1001c00d40410410f69442401e070015401043c9070b24010b0184000024500720b4038064119a03c503045809401c00011051070070040000401181410801c074400058140703081c402801d12407a42c40c00540d0f200d03035400500d0702d030001c40c0c0d010f007041102d1503401c0f9400641c4490005d00d03083c808d10340042881d0540d0300150180c2400e030030040074900d000034000104062540310070185881108103c004907600c0103000c050704030a200b00c0032150044507000c81d0b00c041410080c50710700030901d142d156a21441c04103030000007010000310344142c107400a01131445c96004080c0c04200f080f0105503d46400c0483c1100da0340030260101c07684940d00c081c05480c4603082d07001072020b0913081104001c80141d0034518100030028241c3c00340826405000b940c2040d410f00308680c4101e8a402e420f0f880d0b04945024400000d10650140030072150600c848000111740701003c0c1001c0042c011000c0d1030604504205e646082c00c070b00d000003480034002e04010a41c03550a9418000e450484002845660110082e00d080c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 905439433 1250 905438183 905438239
    0x603160212040902093f121306030e01050405070b070201030908040e01080601140f04050c120f16110604030c080d02030901021803191401110412110a080a0609151406040b100806 78
    0x40d100410203010788c87c10040800d08840855409000d140c2142c0f0b0b02034200e8001b564007800350703080200184403298180d00200441c52043c0f40024050503940c5a01c915600142c01400700340440c000104450042001030901429a460804c0c006001c040f002807400703070141c0c101c2c0340242d480740001003220241c3c2c002c0d20303054103501400074101e2500311012003644d0805c07a441690f604500c80210140e9126000312500943c1442c0100700580b581e84042c0d802c0c03552481c1c2121201010000c59400d160240080d50080030600000350301c60000100644601025040e83e900a42c8501e450100210010303606000040c4c101071600d43c0c1103c1c0000701405000120102085a000020001903200010281c0c00036240070301c4100c800030820408001524019100e1040c0c03551000404001003180740e80802c0341c2c06e04c241e5034036810010220a0781b0942d41100c24083d202c400040c02c22120341031901814405100490342c001c86450189000303000c030a4060030302400340385511b48121582c5110b841880c10703 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 905440683 1250 905439433 905439463
    0x5100f1e1d0a0e0d080109240308030106021005090c040e0309030123060303191209120333030311030c06090604060e0106050603160212040902093f 65
    0x554404003105008600c01560401d00b030500d0614545680800030594440d40000c96940355000e919041d1098042c2a50002c814000c06904e2401c99580320802d044000075445002d89548941c50200c0290606002c48003402455041104004002001040c10008510202e40000b0014044d40e191407a5000780302e20b590b003544c607040c0104a004c061403601c075203000f8480088001a9603030001c0c545c0b02e001d080c402d607100d02040064214994010440c00b001000c000400080d803003200d4903400d01544820080002081d916054407402c07110f14084525801c043c2d035555000000b10201112514942d480080c00304500d441d405262101c0900880e010418010b0480311072b810903c06060311040260781c11680c3d01d00c1d060355440e1400d41070180a0403254010416030655546080d4800d08030034290f41001103000c1d00455420107000b06000e040034280e0090016150314110040c4035402c0c00307640032100884014011035295094400041440110314031078504500461000586020640e288480c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 905441933 1250 905440683 905440709
    0xc082208031c0b030c12120316030b01020a150b13060305010b13050f0105131b0806180c040302011808011a01030f0504030905090718140405100f1e 65
    0x21500800000b0b031034040d904841076200c42d800031401004598804110700d030075400400e04005286090582c1150100107401500d0070320201803041007580c3c1c0201e515810800103401d80309d003026032600c140052071000380010b000007195a15110529401d03005800041c03a112404a010b40d00d842040784024038400704140000c50300c2e8504a4007806c40020580d0041c005403842504506d024041c02d805518665140803c0381d0030b203400d00c400081c7c3e4411058a041d00c2d040055404000008100d00040035983c6210700da0401070100024143c00c0c420707144600c20520b041c04076502850007105c00b1a942400c054016082c5c3c0010b032109000240d0103150b16500e44030842d580b016880da1001c1c00100c00b40d0b402c0090501908001003291000e42c1d0260004200707160500c8142045403540b0303089005400c00e4010340020088030700d9205d44540005442d23405203040d4980c9414240640c6030420202c14001c0107144c1007502d4000f1400740c5204604061001d911400b402e00d80400030171000d0030303940c89894 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 905443183 1250 905441933 905441939
    0x4080703080d050f2511031b0f2103101d071404060c060509030903070605040f08030a122007061521140f0d0903030f0c030c0822 57
    0x511500505030b040205801e01000402034001690154403954500e13502d00030b040c0c40340c1d4220700b500b40d00040103c10b01500383c001844011007000a823107014a044d60a125a04061243c5400e00140c450411820b602581c0c06d01d22609003020314000f034810403001e050300c9581e00300401070900201d034040e450050b02c008400150030f20080b0010311608043e2078040b009408110944458400c620a1000041d103061800c0d00203459608459007080c60b01d001c5900380814100080d080000c44d0388a0004140001030130000450340100c01030042400201950074240903060141c452003100300108038050741e5100000000310343c1000042040c034100c2100e6152502885c01c8801007842501411040c0846180000d122007215545171046040818880c14200b040d038500030803040041107016a40554440d1001c1d00f60300300400c003041c803182d5a441f007140746903050151904a40b20044030820802c0303108100403e4010710035500b41e2398480310040c0da50311004201d01092004140080ea001c0182c01c0c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 905444433 1250 905443183 905443193
    0x10050a05160f0b0906090606060a0905061e030c04081c200f12091f050f16080c03070c0906050306041202030c0601080d030f06210206160507030b071701030b0c04080703 74
    0x20506c201400c100b161004e0311002e08110460203103813003000001c0c5600c0418856030418901412183c8100e6002c558511186040e088998008403140b030710004c00801d0030032000700200007508800d20300c0b00980e0f61003134010100500d5488002c9481041e040161500080340380100061140500340e0030a444440e58840d080c0036095110001030b6100d004440d00469440c40d00e150f4080300044ac0381c58003854031042c10740140f01600401490035000321164250f60114901d44020406206290040c41e0b4800d4189004000f40d10280c02243d000c9140200510250318001003541d001030b00011140749240245008070b185100720386021006018200000845d44c7e000030306d0b070207100d40750b48046c0041c195441e0344c0c4040781d2a520a0710703484083c0448408041e101004041040c40c00034103907518001c0c401d00c20540091460000325600d40c00007034100103104880038915002841c0e8500001401c003020b8a00188120602001e41f441c0c80c000c000ca0780380c001c85030031a0010300666013603c80c1c503940c85c140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 905445683 1250 905444433 905444443
    0x6141e19030b18010212150609030a050304030218040837020a050d052704020403120c05060a0c02150702011508100501270203091501080c10050a05160f0b09 69
    0x110594002d40e102a0303c03280c060003034039051800314102c00800c0e95070040525031071000180d1150440707020000306006e0384081c40807210441c050402075036100d185105020b2021400940e806c41c180e02601440009400301d0100e0b405503450018070400c1d40d40b2554011080c0c506419504010b0b104010503141841d00820701c1c2142c503000302d00fa520310149060003a5414407a418100012040c20520003c051511904000070f120000d400141860785a684030135024040c0920180802c50132403104040000410800380e0021040d00184811462031002030b5607040303000740100d205410b84c40051000380c400d509c01c4a46940c0110600d5009079142c400c107448a03082ca100341030440c10000041420708010702c9501401c025100c2c02c40c4c0fa06480c1c0826030003500041c00180190045a05540e29114042282d0740645800c4016200558000c0e081190380ca9001e280d007000d01c20184100300c0c005030007400f5500c011034a8204440000844d1a0100912802d004010040c3d010401808031050000031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 905446933 1250 905445683 905445691
    0xf1206060d241401141806040f02191223040804030605072313060e0f06030106200f030909070912080409050a0b1f03020408010e0a020a0605030f0103060f09061e06141e19030b 77
    0xd633090340c200c0d5203800006a034a40e180c000e40c600400b41c1e4202c00c01d940b14413156402030050103000d0415481e95245016550191048400030700146076500104100d403801100803044100d10920b482c90244488000316424400c0e0018008020602030240e01d58a40544c010100144800c1e035940c0c45440152090341f90301107501e07840d400103000d4402805c0009181400c0074a90380110306100b1082c04201c64034000400b41070401000040005181041840c150740487c0f01d1a151926541850b940c2401c8403002021024002d040501c0c180c1e1035100c844005042002820105858080c601003d0b8040d01c203d0344468a00e601e05540c02505000104600349454400c0320b42080790790b5100b2040b9418002900d1045a040d41100100b000620581c071440254103140404206130b25507440300300c2150200752042c05081d251150803180c1400ca0b03c20040541402d104e041410001c200101e00c403009050000c15940c1e82018040c030155949010038144003020800d0210740d19100d15043d410000203417 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 905448183 1250 905446933 905446937
    0x6030e010212010303031d0318100210090803070f020d1e0c17040f0503030c060f0a0603020613090c03091106090f0603090304050f1206060d241401141806040f0219 72
    0xc7c0711040589030103c111182c01d02080c00600c0f51042c66020810f1410741901da55013135105000c0d000510760001c3c02840d00440c01641c8080d00d070b28221030050502035041240f402150088040c8404058000d00c20030f2420900c00008411220309101c2680e40609100300500080740030550602c6840074940100240c95a8403880121642d44030705050741ca00504d80f00041d903800c5039002402141d10201d58a0f4090b1042001040080e941d80100e00c0640c4102c00e4a00c4100c110001446140418010f1424009003482c04129035007007621228140444000345900ca80000100c50700d40b42d4071040c0300f9007070840080182d90380307040590340b0655980c828826107001d80b082c1001910349242040761040c03884811000380c041c9a81d40d01c200204040800b204803916146d10139280c040803000042c072901c504d00704e1800142d20301e82a011030340c8008160b2001040b0140d002c2c140c80f4645459400848010800c01c0c034120940726040060082c04440c84501c810520100f458400200d40d081204541070140e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 905449433 1250 905448183 905448221
    0x30d0f02042d41010801080f150414121905040b0702240f0702010e0f030d050f040306180b0a060311060d02070f050a0b0f07080106030e01021201030303 67
    0x3041800005024912148a041e40380b4410810b81d80843c16010801c10342042e5901c030015682208541e4440c2003051290b5140000c049640c00d58100400902400c04200104581c0480c0380070300d40d0351000e400403031100f0a0344002044c00c000240e103017070140d08030750340c00c1c0d641160075078500718000d0b04105d003008058cc5840e1a04070304240900f0849098400362402c451815109400340725035449020b51003401c3d01c0c1c11318000b251203498440504160810007003013692382c40702800010030416011106922070070942d030302e4051036175000851100c0d201c40c60920300e0301c6107104180007038240078a6002801050604080e507a000010f03960590752248100c599154a40381c244e4002c08550072400010220400d09400c500701d031a0400140c40702401c1c6030005882d10401d540c1e8a80a00c40c0341c1000c4460f40e118441070000c0260319203e135a400b00203c10350081514203110010901e4406214401c00e040d500c0408810328182901280d43e4207908003040350855030740b072030000c00030071f00f07030552246001c02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 905450683 1250 905449433 905449469
    0x507020f060c09100c0515070320040e06040510121b14030a1121060702010e06040f020f0604050607140d0c02180a14010303030906050f0402030a1103030d0f0204 71
    0x402d000756129010b01030a60201207904441c1500c5035450300701c007656136200b03058500680c01419035000c3e00c41c01c0203035170125003140881604041c40c004c10209102c0c1407810b02050115a004202055011800311404107458580c3e00f07a503000201c05810001540d090700d1080418424944426091080f241241d50801d80e600c00c3da040c68224079180740d640c543c00c041e1620001c5459030064264015006242d80345144022091403140d1820201e070700341c1604010200000c00f0f0b0288107428090384040040c12aa103059030f01d5020180540c0c0000788915600c40490700181c84640544003d040043e02d80c560300c01203401e014050001c0425029094807540300c403407803206d1085003c000300540c050a904c3c00c3c4109094000510100203003441500daa81c4c0c085141d6405500043d540218041d440c00190300c01e0f60700f00141a00e03401080d0040003010301040c000180c500056a2020603005401d003110a40004002415071146155001a0500b0500c00d0510101158020002c58079682640f9001c450 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 905451933 1250 905450683 905450701
    0x3111e0105090427140111121303020a060216050105010510170a090204060b0c0c0604030b0c031902030709180903020c091503011811090105090105061c0507020f06 72
    0x821204a140025020b20495032a4181134000c0c00320658680741d141c810b0205103003403080f1410100400d6460f03210308002030590704002e1244101d0b00400d01c011a20f0091800c030840140304016021107580c0c007943e1107400505100b800b05c4421140d11003c15551510313450300c85c00c00d184014600b900e083d4603181c0000350700e182a5486440341242520303055903400c241078140307075140700003030403442c5054846000a00581e214440c12002e03215981246440302d60b0f07107031010300d40303406401d10038080c1034204024030210b1059000280e00401083d40d240d0341e9603c10243d0b18503400e0b00d0300c0e0a0f200ca030003c800d0000b8243c10158920540b44000f21440e2102a00a148010b41d0113003007001e405030308085440300050400308140d961010080105810036400200400d0868a501d5000d040c4072024001500030848420301a0440050858083e941541004001425100c042c461644600300c0000c0c00446800510460003240d0320082c0104450b15003002c001c0d413902d40d44000e49000d406004001000c041e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 905453183 1250 905451933 905451979
    0x911030117060f0a0f0e030a08010f0b0901050d0b01020c0d05030319112a0a05030d0b040b010e280e0601080601050712140f0d06030c0801182303040311 67
    0x40f00c40d03442c210a84ca949580100810300800515940c0d901d44409110307400041006100c00d19450f0fa0f0311800e1b61405800c0011400709410100041200300180302c0681e80c003200303944200c050321200064448075400103038034010005031070340e80190040c0140c00900c0030100c095403158180c0c3c00510940c003c07a048410444d211800a4002860309000e107401450548092030000c25030b0f107411881100a0284962070b00d071240004a503141e1000412030300000417809994206041920f0900c609448100003905030385014502c1c0b4024a0708200d5440011408441c200852400303034100b52641e921044004c0105904076175007404951080d01044241d4401c0044400c0c094001203101d1440c14517031822140c0624070301d0302c006100c034107101203040030029200030300704080300c3c2800091407032844c540290a04001e5201040fa645072588856104000351013021659038005038960041c01c0140b01c6030b407070803948100e405d00381c4000b05011040140e40f0015820300e1000300c44090204841194940e102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 905454433 1250 905453183 905453191
    0xa1d0109030f09050904110d0206280903020d0605070302040924142209020a06020d0f031b080c0c060f0403120c090e1305060c07031202030c09010c050106091103011706 74
    0x4941e441001601060b03242d070310815480c4009102c8e00141034180c000032601d030171580c640f01950555120660002919465018000446040c00098030b0314640018841c12490540500180c2c3c82c2c3c1c0000d8400d034840d034110f802400c03501c40d08004035010310b800750300c2004216100518110740040e001c02c0c00c1c0110810300e8041003000f000d9207202c03070211400d8040b600341c103510f4018440d142e072042d1005948144a01c8040e161942c010701d5012031005006180c15140324a15007818a8808900c40044440c0500860303281a41081c0380700d81c40390301540141e0f10603080341e03903402d014a00034030110a01160b0003c0c0154025901c0300c204803c024135410450301940010000f00320007a10400ca403000c0c00500d5079206120071140316142440c0c0c2c646504105045468a40c0740d003000411a0405030414140410004440411421440c090130100d43c81d104400c40341d4140000882030504000003500b00c038000e40005c0809011400100c00c020510b50002e003d100035a42001003482040c1c28000362003441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 905455683 1250 905454433 905454439
    0x402030a03120603150e1504110103111903050106020610060c20030703051c03090203070b0f0705070806040201030e06040b0609090a05061608060919050a1d0109030f0905 75
    0x18580c050341c1c09035040000d4000744001c49880d141c0000114411080b800300011040c00041541084c11042c68148040f004510307140940300011300c00482c051502c1d070500441c003820005500700341408032490901503511030122840010800c00b1a523681a0449812100a5021640d540e2503641481c40a18010b0003100d002660004190010510341c4a41c00c20f04210b500d00c1c019026081400b20341000099001559241e1000710b1003031200076042d84020041d806c501d0200610714890b80001d888002512404a420742c0108509842c02e07260b10450312300c1355000d000c49640355542c40704140c4640d000c8a043e80401e2030440c4241e2400004a8024419680030406e00c0d036a541e0541000b5030303044040d018845a100b4181001c000402c00c0103c40e0183c1c1200c0c8801c280c8000c1c8500c000d00129004084600898603482030151011401c0c0c905da0b01c40000d05004070740756032824045001414079080b0603a01407515140c0500e40d090640c030400565020356101411582c00e614140c503000202d10039a50 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 905456933 1250 905455683 905455693
    0x28080405120912030711010e01170c1b0601060e09011a0d0f020423091308030f130b0c1b011a010c050a06152103120c11060709080c0306040203 63
    0x55004104801851141c100a10026003448610400703495500481402c841d00052051b8803056580c00110008004c00c00f46001346102e201342c42d021210301d80140110540b0030001c100d04042c05d884480c686c6440c00780e070048400560351900f000307205211080b60640100403210007c44c02d2020800030050b0001c03c101440d10f01155000103070000c00402200811440e2f0034403022404c1004140400810500c1054040004440c1010085032400107803041d400380c0420311842001400c40425664441215a0f640f6281d69411005249400b20214000d000d200d8171010070224041c80e030f001e0410900320703c000300000b00554124a08a80d20b007140301003804503940c1903121540c42486c4107002c0368130500c2964aa5501981e580082da060b001441c908900086c10070300a9500001a01c1c800b044013200500000215403801b8000e140300420b005002516040c05070006030250b100c0380f14500da01022589645055040100400034074013800c1340e24050040c207800c00e482c0004130b043c02180c004010f80 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 905458183 1250 905456933 905456953
    0x6080c0909041401060b120c18130e031902010e0705210102190e1c0c210209090c0f030705061911030d060e0a05070c06050604060b28080405 62
    0xa96824002c0003100c0d001c00c0c42c0d06041c0d20b280203004180c000e2030402030300394440c4441c030700304d6440c503000070000740e00c0c034609001500305100743e40d5842c07042c807409440e400400203012101038054000d041000c6e256100005a0150090300c4207107400c13808403140d0003009982030428a00740c8a5501e0310450364080ca00414001c1201d0b842d0b2408030f214800003000514000c20000710241c2002d000c8045d038007040040403814203e050404096a078050040d040031000c0800c1e0340c420040d80d1640c081c40e040d15100812051301c540c400125540304da0340003880900d141c80c01c042c00c0c0e959850072b0001ea6014002036011942c42d400c2c0014900c1c25100002c00b101e0501c001160b03010401c40306c4041d00d0042200e60b03807070340e1a481d13004d200600b01d0201203034011417940d0600c0368400c0381c0040500f12000403031034030040001550303011034604280ca9102078085442d49502d00042d01800850301300081101e00001c4e5800d401140010807441541caa6290213402550004183d4200f07804a601409a80010300b41c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 905459433 1250 905458183 905458189
    0x1d010906140d17070f0b100e0106021b180f041506030c05040b0604030c08071505030601020604031d180906010b030c030a0203070c151a0f060406080415020c0d0906080c09 75
    0x54411000c55003500340c00d004103030319103c0d140c80040100b0b5440311003000900241f40010203640d000b0341580c10340c039816035142800095544240650340c10b4140d045494a030450794800e03010303910031600b0007202101c030b04002c404003081d40e41c256800c890001e03404c228507007100600c1c000c090407607170412803410300b0f68500f4052202500c891070340182e01440400001c400aa007190005010b00441030044c03402d50f080c00d02101d10745011012120910a06004009850fa4000780c85a4080d9040c600281c420050101070000c0c03890110411b50300022224000d408040000300b62442601e05100b00c1e2031690703a50716021250b110942e250300300d1080800002d4000b04941c0c0003513030000e1240c90322031181503051712030940a01c00019040103454848814031540700040b507844880d5003007200c81e0480c00550000060583c401c0344108000e01c07000710005401c1c0148143c0c85004924022030a540d101c1364101902d440304003a4801d071002c186c00382d00100708284a203c0491103050401c032201d182000c11810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 905460683 1250 905459433 905459453
    0x1050d02030c070b250206011a09011e0e0f120d39020112060e07030911280b03040803010e13140304090b010806060a030b0303041d010906140d 63
    0x1180c0b03641c000c1042020001014190028403a0f101c1140f10602c0100f210300c2c01e07040c1180055a04d08540c0800014040301440c940850740f140c0d1002c5411382d603118024010380e5040c010410600ba0003d08100d4000d0040d0000e011810385ca00072030303080d00c0c0c4800b91020000c242c080240c48d2091940804a4a00340750b004041c40d4080d20071b0aa0001c01c4140c460800c600c1008219000340f80e040707a040e00d6030045580150f422426601c064005220150800c00d02c50310f901030052802041544942e044400d00c40c0300c2ca00101d8041d0060420031090111303800321083d2030441e000282250391900c40010380e207099201900d00031584551424a10303444d00a40c4818003401074206010303a2070300b10360900022551b00030b20980040030b2001c2c5458500d4007000c9c07000c403201044150b041c00501c0040100590307802003103074015041403c0000f00e0140c0d003400301e45075028641000688240b820300b05070058600340c5405049600003d130038401584c41d0007010740180380241505070008003a03020400019a413540c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 905461933 1250 905460683 905460691
    0x1508091203190c021b04021204121803080712050c060a1a0301020307170108070e180f0f01050405100b030a0f0204110d09170c030a03090201090e01171b01050d0203 72
    0x2d4a88010701e00800490203e5412845032405640107145c4003005600031180030103410422101182050034142c03d0a142d503100402c000c0c498000a0428803c0502510585c0e050307001c0c415032600704585034582600c2540c8903010903224a804c5003038402500740310340112003a07803a1a8014040342c1d143c0c131944201400d1181001030b19411300b00140050350701d091001d1407003802156201d0780d00f0082c201340708600300c1c41a0802c51064108010900c041c00003455840c0e040100044d4401c0380c074107a402c2450804c200031170220654040e00c0d01c0340380c40701c805400082c09540142c0c1039031b021018000c1010b0803989011135564068004003088004a804201100c1c2c0c42c500181000c1007442502506110650021070040c00503980c03856250180560078413500d041001d007016041c42d01c10307444c030701c01e58334042c0b68240b000701500c0384000021a442801d144004100d650301c000355a503100d900e081c07080132001481440b2841508a1004980c0e640d00074401a2036041e110b0615094076911080082c2d80014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 905463183 1250 905461933 905461951
    0xa051903090b071a090a0c0506040501140d0f02160312050411100e0306070203070501060f0b03040213060803072f01050a0e010e0d05060f010905061305061f091508091203 75
    0x18244581c13024144c4d145070310645061010308240086482c00c6012100c0d640c0103e40601414041031106980282c1c0055030103005c51005130700c4054801843c00903040c2100a81c40c0c00b030021912003d80a404889003208070300c2515500d4408203015000d0701150011640540342020b610644032260a100401c1ca00f07902440c40d1000b0128613841c0803c0c9040c00540310b480040c0d1000600c00240720003031080358040c00920754042030a9140c440700c03c04601001c5c00291003141001800400c4013115071000000300181410349460780c205007001090000d00701c02c00b4440038040240c0c07448032107201d04401600f0030305071500d034109081041c0443e2200003102c2c04e5410701c800c0b104210300c1036546509100c0b00c1d510032001025180f900a0002c0600c200681c801c4680504141c2800b0345503441202c00c1054010b003000010391940e5520000301380c4021618401c4080368030b414040c8070150301c5030280c000d4a4100305002c00c1307122502c0045500b00030844c0c85824540040980e107000004500003036810503082 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 905464433 1250 905463183 905463203
    0x4120e03060f092404032a0f140a050a0605091501030b07030b0102031c2016140c0f0904111504050301050649050a051903090b07 57
    0x160010a180c074105440202c1c050800008011982e07904000040c410318810950040408048a44040000e4054801420300c0004020003040e507900d11000401d801004081041b02c4091342403110540f500c04005887c0c0e0881014401186400024140c920340d500c00c005189011743c40e141d0348010324000c1c02c0c1440a02079908064110081c001c942c40c00b950013003807041124100040d004e0200c035901c40c003050642d0000d01c880c42c00348800690301e0010003c0124041510880c407500c2e4040c000c00302d2017245250002150390b4103900150489a8041481241007a01c042020180c40c1d5a03032070b40e54002031380700b00142c500090342c0c108602d41700d130400e12640c200c1125504100005101106c0000d20080f5100c011400300051320b400d0084980089041d01d6484078500c0482c825081100540380300b170742c0e0401c0d41968105106402c01ca942448201c03483c11200c402c00c0d86001900d9081c904000da68510800c600141001e000d54001c0e02c1c41541174407651101440d001c00007c8580014009481d00001c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 905465683 1250 905464433 905464457
    0x111506040f0c030e0d0c05030412050c06040605090307080309150906160f030e18011401110106080d080a0605181504050a05090d09140409020a030c030303150b030f0412 74
    0x2240241070400b030003038a01080290440c14460b190004210046040104c0100324401062000c42290161803034001161142241c50034414070f00740a0000c0150031001c00540040d180354040084c0040150032000e483d519070703680080d50760b41d007e449151036004113102d0301400c091110704001c00c0070344030107000d080c18640e086202d400c0156032070200303850200c4040c454078101940451007810340c0e0341c126006004070444031030781c0021010500940003810310742c00c0b10030403582c018059254001d08000013402500e849080c2e0603218000580c801e404183c01000ac0344c0b09071018001d4100360b440180c00727480410000c541407030342082d001d06100d540090015422585481e07501605100300f0b030081005c20742d814440c50013480c2c0308010a0160402400c40c006111400152849a4107107400700d4011981c9c030020300004480c0100ca0f03200414585d00741c0000420540c164005550444e0100700810903c1c1d40da002e100324520007160310706022000400003c001409003600c154410440d481c0220f01c07609 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 905466933 1250 905465683 905465711
    0xf21030c09051002150a05091002070f06270804140f03032212080720030714030c0d060501150903120516050a0b01051f020a02060702032a040c11150604 67
    0x8421b07034000c140c103030702c035410800c2140302000743c40004404400c1c11454278402c0d455800d841044041e0007802c203070325081c20125804d01800c807481c0f018030324814007198201074544540607602a01c14000702103400e20082000e880c10480c41d414000025000d1460f00c00c0032070500c00910b450940c45081e6400c5280d010034410303a0300959000d00c600c030300d100680d24015820000c0c0304103000c15050880c00400b106002c40d80d01c0114000c003c41c0c0c1d4a15007490301001c4680000e04150500c0314541c0c0240c9179820080600c001900401d04a5810f140014100041158100d80707101c40b0b0302002c0d0400760b0540c180da0320700b48210b00400742c000c003821408414800e42d5480900b40015480151041c100b078000501c0640303041c0d250300b880380042286084609607070040113521007a0a0001901c10307030f40030468400395201030081c24001ca00551040314144800c40d0a50100300c8080006802145480c42c10300340760b4004d61004024001520081c840c10b14401c8140004800050505800a45174004d41046803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 905468183 1250 905466933 905466973
    0x30b180607020109210c060e01020c0d030906140403090317070c12050d18060804140304081e06070e060705010b090702030901030f060f0b0a0c0f21030c09051002 71
    0x118903030300200701c81c04c26080c40000c01c8859054480301080050405c1c0b41590008064003103141d003c070000c10b60300100f40341030740240242025078602e40500e17540744855a80c0b55002c0700313036039200e50710410a08613508940790454504803401000306030f1003082030010610441c01301d000310171a8014542f0b06810742d030b07030780e50001825402600003e00410400c002c0202c140441801b0401c0d41c0380026241c0086526402031030814031400b028001084080383c00d2004240b07000c440e1800d11011240d032a5981c04c002ca03502e01200c00c846040080e080d0b0314401107500032944900488460b90340014216a40d0b0801c10103038403460088840d59a54200d02c4260b488400c0700c58400c0f4000e80186445002c0c040024050341c015000094240307103090006d001d1900300d40c11440c20382d06a1400e940d11340d80d00b040180e80250180101404c03040d1000b50b40700410010506040002000101e41c1000541c1040242d05540c80083d00b0804515036100900045c03d05081403101c1c0c0701140b048880554200c680e685d445 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 905469433 1250 905468183 905468191
    0x306130c0b040b070519080d09060209040204080616020c01050901080712062601110706050606070501090503030610020d1d060706050901053c0402040209030114070f18030b1806 78
    0x1040124062080c071200780710580c0425604040b4a507000c503a5911201f8034031451041000f49961421080c0a221240d8103480b260400a0701c115076441e242c1107040d5655104843c6090410108005c0c00c0b4080d20102c0c3d8800035082c180c503041e082c00780c200e0066850034002041201040100c4500c0e1280000358000d4800400841d820200401101c03503410180e02c582c5406261242c1c1030981e011030f02036010b012103180715049100000e2544035a000102a4422020302504944c00d0140407418803402000850003080200c4048014007030301c0800340e84540e600c4000e580482c007494000d480c54018140c203420b04400013040c0c00c0c90311251783c1da44011202e040e54070601e640c0d507440821041d1b50113101c450304d070744442286030040001c180c040c60604007150515010042141404542152a0342c0c0568061710b40040080c0811450702544603110300b002c4400034002402c0581c140e5206d4010565036181425100e1002001c41c21600c1c0c426600e28080c041e10810140c00803440740d40c14051180e1400307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 905470683 1250 905469433 905469449
    0x607060212100501050a0c0605070207080f010219030b1c05010b0d0c0e07050c030f0918072d0212091f080906100e010302010e030f030a030e0f0c0306130c0b04 70
    0x4241022148070a415a45403ca5410b000d41000007609881d004229801e4666200e40d010540741e8916504a00f4003616612942c501c0c030454082c001d1140c4190064940107800c020000741c8410203110881c26148820041c40e0002002c00b080000d200d5155180c2462600aa00220f0480d18420100d00c0743c43c000c0100752000c0305003072070a110b03001480940340e800010900d0000e081c610f8840380503480f031007440e1640d15803c0c0d00180b15482078848081500c1c9240b07a210005e0130030b24002d9009400d1907040080c04400c5000e003075182007007802c281010482e83c5c21603401441603410440813031100d0b9000050b65507002c030783c45103800e2500507007200c0d1450301c09640c4c0c0c501c68141000c036152843c0c04009004e84510f40b030711220500130140c0301100b0904403602480d00b409801c0c158408282848948030030001c460000060400189030581c12940030182c4403c104c03141d01452080d01e43c0c0300c0b0524241c03640d040d00140045070b040b4420700c001513030140c062340c08138170400c2d5a44450032140d840765004240c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 905471933 1250 905470683 905470717
    0xf0b09120f1206032409071503020913140a11040509090a12020105090606010e012619110f0325170123040f0b1908012304080906070602 60
    0x2056207100b041260704940154000c0a40c0e002ca8001945000940003d40141c0f5045100251000108001e580300512005080900da071a038420003c0c041c0d4001c900d41030042125803020f180c0c0c03508a20442031101d004504101603a00c640b00303510007401c4081d40400d620b1101741301c081059502c03030002d40e0040d605c6000030680301d07501e441e1051180b03078082112000c0da4500b070100710a013200416000d6100c4002d01c1c1c0106140192801a81c24807201a01040016090700d0806131781c1c0d403000f401c1da001e9141c1e452610315a110f0a41e48006598049004d00201c0c18188000208076845e0005940c110b400c9110050788551080c2000025101c0d01d03c040c03000450100041040c240314203411030142c11020b02c0c1c0c0242180c00c16044800c0a0b442500034001c583d142e000102e101c9076a0320004651000600c05080c1c400000310f5500015140d00488202d5403814407141da07000b4003c2c200e07000a9919031503603040c0381d8850b101c1c5155a0070030b1a4050b04640d0402070074000903031074402065160b100d141010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 905473183 1250 905471933 905471947
    0x1090902040e160c05070b0a1b0f0311070807050402070305040e040b01180b06090d080d060e040209070e10110709050f040c060f020a02130908041d06040203040f0b09120f 75
    0x1c0b046000690041c014000b6038128040881c20114140c5c0035104000d5000790ba0b1b010354941201c1078484010600c0c2c5861271900c0407405c0101c2c040c60151814041d03076801c2d042000000525840d20151b00c6002e8507980100f600b00040e081035000f0300707145402820305508242e9102481d41650000701e800311141038112005211480d1ba019484240c04140241004035a101c0e0001c590148910780d00c03188101c0042141c0e00800490b00d00715041d907800b6540501c1015910304152101e2081a2012445000103200107a0802c0c4a0f40305161490780081c888001c01c800d40100f9244030002941701b240354041c80201003844025801100e0103406d4a000300880c1d45040c0c10002c1d00c508182c0c00902c104016040f6400c80300e40d00081420390300d0f8046900c00c101ca1100103a201c0140081c071801016507601107400201c0020380c0031540a140d86400e000c5039190384281c00c000491008072801001104070204000109029800c400d602403414000c0303450045040900d05a1a00310220030031a90b4400a500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 905474433 1250 905473183 905473201
    0x327062a090d12180509040807060603050d1119050a0803070c0501060e06030c010804080414060d0f0c08010906030b18150c040501270e042105130b0703020706030b01090902040e 78
    0xc2c6004c00b07461540d005415082078001034800d0006007000d00181804540306d000d0003100d83c0154002c56002080341c90f000302984c80a00b070208d121180359864000d624510700d43e104c6c2c1a05003103038964000094806403030107a452891303640029015604000c03030305401d0b0f00002c10074400e02020f452442d0f6150701c0c6260500c101850a100018030b0350410000d202030200003180401500c4c16a40e02103400028001080040b0b01e05010b071011402d0310909004001100c003440c0d501c50200c00801d0b68a241d41c0c0da0b2a049400181e503601e01c40104403c480341c00240c16000360311100503d100c006010340f51003001c0022000c41d5980b090740d805040c0c07076000804000c60768000582e00e400303c190061907840f41d001810705c1180c80a003440b50914414240300010200205201040f0451006805140c82001d0041b4018001e80020041d04014444c071600402c10025007410350700c043d40e060780140211800d00034210080d00000b0086410300030f4034003010800203c00d00142018007071031281c0219901d055016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 905475683 1250 905474433 905474447
    0x3020126010906032f0f0d06050c0306040e06010b030408070201030b0915010315121205070b07030f0f09080a0e0f030703060e0610031a100b0327062a090d12 69
    0x1380081c117165103d039800d180d100304109400d28402118200140d4034102d002c51801c5a1140c4018000c4e8601010440b80e005200301940c05038000351380400c008520041481d54607507003030103000d40542c0c040c40014009a0004000c000c1e091062501241d00d103818008240442c006942026005400d0b0003450b440d560325100340c2046c1c2c070080c0032202215180058034010040c0c3c80c400a0401c0c098007681440d0386001d03600321a0303405d40c0b16405444e54078000c00300078010320401801003511400d00707000d0705d0315403030502405282c03d0708140c41c5468028540c0c42682c03441150594540c00c42040408000180d6003072040314001c502801c0e001c10200d69042c4100d0a2440003803c0c91300c02e206d800c809002007698049010068110495900807a454442180c02d0100c1c555000c4140714100004100c403503800d4825203100c5480c00c4d0141008074680d40d4490f615100b04036651401c2000c9074064032070950494030106111080009a9403400310014042002a440280e00352185000354450064450740192 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 905476933 1250 905475683 905475713
    0x20a080105040219050d02010e1809030c0708070b0405120c03070b0a0801051819110313030f031a061315051201080a030507030f030e1006060e09060a0302012601090603 74
    0x2040d804c3c090610700050303841d0a902001034100300b50700e00c089140741c036a10910140d90030700c0380d0404058078040c40340940e280e224020310300d990701a01d00e0000d031400c00000c66034150341e0008030403400c0078108010301000c030f0301c115107280c00c0340b01d58011250503842c1405000050207491440c140e85401c03041e0b01a1561906a000c40c4c010084000d10611940e900c2c000c05401a00034080111451212180301c8080c0402300c04082d0f2000c000001c1c010401d601c000e01e200b0311407185c0c941801d01d0b10408801d9080381c102c1c0003049100884202180040d250400c014600c0500707082400880343d4403000ba0441c0403032420703050000305500040103599030380415001c42c01401c28000400545056640080c010b0081d0140203061050380410f4294480c0a6002075003045400c030704884500c0d03c0e800300c000c050304140c40350358041440c00f40e0848607406e041030b100740301d50400741020101038a0b43e4011107035a5000180c94800070360a500015800021100710f038020040e9650100d059400c1d0b0800398988c05a2003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 905478183 1250 905476933 905476969
    0x5060403020a09020c21030a050f190b03102f0a1b020a030b0f0411010f1b0c031b0317160611160b0f090f1c0309020a0801050402 57
    0x8442000140ea4405540c4143c030b03c600030150700c2d40c1ca031000b03071403034411100d21408000041100051103820b800024500c14440701c4000d00c031035120301d000c8820307800c003d4881c40107605000c2d0b4244a01d42a940005000d840090201c407100308448005d1421103000d0061103603409000c2c2c482165005040d00240118206848080c2ca8054a050094200202c4c1c549140702c40e11a0101e039019541c0d980b040f4070045030080d02c50003881c41c0103400641c01001c200e80403204507480e00a10780e0316500c19201c082801206803243c00c02d616017500803001d902500401214140c101c0c12021000550074101d031041048101e100c003000344d0442c42e100880c2c1560084a0040610074092412480c00390b00103a649070f03401c50400984441010342501107441151028204040b4103071a50b02002803014001e0b101704001411041c1c6a1100c685060b04c5641d4080d1000312580441841440c5011a800382142a4514200019a244180c2c04a13003c03200c5c981c88401d40746d540b84100819424802010741145641c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 905479433 1250 905478183 905478187
    0xc060a15060503070c0203030f0424020f0a032d110601080c0a0312031407020703050f15010605030a181217090706030c0509130902120f150a140c03100506 68
    0x80740008125000080000c001c10941d11858415510b080c4222101c03e03040482c61980e41740c5901e043c440c54080c89900e40c449050400e11100c5051000ca02d11000c2c0442e01c0182c00706412a4404407549003000c5c01002c0c05021401150303503504d544918503051804242c6030942002c58158001d0b041480581c0a1586500008070f80c001e169240850001540d51002d80408400d8020001310000c000c403283d00707010280c140e410720500790380020701d20307041f244503c044a40301d0108400342903c821228815182130303500301b0018001c090041001d5a03104880140000c1e03161a01d0703030202001000700720300303540200004688441080d44207240c6c1c5443d031030030241e083c014104544003a42d0341140b44500e4040668070310607403918602c500200e40e46d4450040ca01404c95050780300f13440c018104000c040b4411641c40f144107581c2040071601c0c002c42e04240300984241c040440d80854100300c003c00107540160798400c148000c2205040041c020100300201c0c58880c9424160141d0045d010341010f88a00c1c03003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 905480683 1250 905479433 905479439
    0x12090d081806070309080705070e090c04020702130221040b01060908060601140310090504061506080f0f0601051603021605040b1f03110c0c03010f0b0f0d05030409020c060a15 77
    0x50b000350014103c1c03800103800c00607410405580d0099000003000e5002d00200003c6036600e51190030301440068041ea2031800d000030801003244541c000c000e4200c3e45102d00c00d552101c695002c1e000c0520805862490314442280316180301404450032140c03054110010700100758042c04843c090080c450082685091a40019101001d5519801504400000015010355009005800820201205002a00b03092510780c02404210342c0c4684022001c4c040020703081e2080300c0c1039014072070029080c2d42d01d44072090f1500150500600042c18454104500204443d141d0313066181c00f03000c0d5000d0549103101c80030444c520111544103c2c4100d0800d40d000003243d0307a4002058807410b4068582c20200c001c0c44050380900f48144000f1468003000c2500d0211090105200320f0300001100208030710b400308014001141c018884041d002655060746100d40c0c207004a80c0301c0528022811281041c1d550b5043e42d007a07a0240550804d1a00403c080c0503490340c4501580f01582d9600209004180c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 905481933 1250 905480683 905480731
    0xb04120b100302181b071a070203090a09050703140408090307050316270e0a170f0405010f020f060106032a14030a023a0902030303070e0612090d08 65
    0x3130340c1c4100341500c029850104080901c10125100041003ca094503102c04050030440b15500c602c6110040c0c1180e40ba0000f01d1551010040740e05070722001304940c1d110b6003042211801001c008106100b80350742d030403181080501c4a01c845206e2441500b00507610b110301c41c1498140b42c12030707014038002e0b071003903203070502500441a1003003c1c0c070002c3c034103076060040026105d0602d40c0c0d8030041c010b61500e41120399202c00f6012680411540c06050054502a0562021134540c8105920024004000d10042c003940d13100d191002d00412407441240c1505140712025030504401380d00c1080482da5595203c08400c04040e10701070310301070300c0c0106d24040074107001c050b2500c0c14100100001880000000b02240440d40c10740d40891005500c01c15170300e480520400020184008a0610020903070b01e044110561b4040c50560a9000e03010f141191107241094481c41141c40c1081e90220003400540d81d02c40710103035250701c1056120000c04641c40c1c2c7d690082c12410010b03000c251101c814002d084e40d046 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 905483183 1250 905481933 905481949
    0x50f06010e010215010b030f1006020a060e0109230c01030510060c1410060609051f14070203030d061511120304210207030c0902120105060706060b04120b100302 71
    0x490a0800d0360700c1403410750040f4144010503204000c0134182000118022500c5070185214600540341f2880c280c80d040d45075110319440b8865040160b000f0645d0100089035a080101502e101c0d40c00443c40036419a6044403035013601e0343c0d071810442100040030f501c00c0b08000ca40c24007034007801e0400c0903040070000e40c44c1801031402410103111004007074000b00300410f110445030030300360000c0d204610a1286400080c0c0100d00c9040002442100042000d240846c6148081d072910310b0881140c039040b54058542d52486004c0018204060003a0405620244010070000e04682e0300002c89905001c1494458000b10710010100002c601210111140002d1200c549000c60007000d500c82d41d071452300d610f00441c03000f070f03807084901c009940301070b11500020300d00c0660303100d00820840385890300300623401c03401401d170300110a1010703600411490030000e00805d0310900400000c030b0102d4603506980510f50050b81320004101d545078802082c0081c803003040e80c2000c55121150a80e900e16000202c40f0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 905484433 1250 905483183 905483191
    0x20306100e010312090e0a0504030f080f0f060406050a080703021009051c020d06230901022a01060b0c03071b050f0402031005030607020309180c0a11070e28050f 71
    0x1030065410000c1c0c0710b40c045c3c8021802080c2c0701d840605507140208000000c2e110a072030482c0401c0f4141c004400881c0103e0b4154420081c95486005955411300386161280005c2d220540180d038800000c212515030b0b240d4100900301000041c00c18516500c1805040600107000508000740030382c3c24041c40c4d4a003285006000307030080c000345048100c1d000250100e0000d500007012549403182140c4201c1e50b114010f00c042c0c10300410820249d0300c80c1c01a0b401c0c0d00c12045103036103280c400010405500514540207819401100000070b0150301c50007030b44d5143d07000c0340380540c076540301044110801c9101d020445000c1c190b13001c03812031a80785c10b000c110541c404182044c451900800010760980380401c0303200c02010010212030f03ca04005902139104e5000d50542d03405940810f54980c07140a0000105000c2e46400300d68502d0891002c004031000350500080003014010340c1c80000e490480140281c4c094a0902d80c0c6a040e400819241048000040c0c010242e041c20a420003004004069000c0e0f44 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 905485683 1250 905484433 905484443
    0x615070501110706090209160f210f021b0703020306070f1b06020a030b0402131a27100f080106030b19080c121204091112070309020306100e0103 64
    0x8415492800c2405000e018007032044000011806034180891900f1101d00e550090740c0c82c84030741d121404a1104048200e4001000c41c000e680015046481003c0340a280e42002582d03004e0654020001d1090350034001315188102e8011542c1516050070300c000746215003004c001403240b2841d65007c2a2100e03801005103081c0b15260084070200c0303010300c4594905620103038900035042994500807009410510040d00041d2078142441460300b868402c848800000051081c1c2d1186041289200c003a000e40000c1b5004505000703003010704603030740d1440c200012400d10810141071000e0601a041c08801c2c80102040030360b1280c070682c0b582107820305041d10214580801c43d01402004503950400c1c0c614082e05600030749400054240021440d50b4510900b22001e0700c0c0d882c41c0810f43c540e9000615140c0d0900c0c001000104400e0410b507020107108081064001d062104122850645890882d80180403e03200d01c2200d045142c01d0010581c414400810b10308410f080480344403094805001c0141 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 905486933 1250 905485683 905485687
    0x150901150315051519090b0607020306040f030309050709050708070c11100e180406060815160c0f151104080703031103040e19050a062709050706090812030615 70
    0x2410303c2192207142a00c0740203082d018403202002c9042c0f01c03445c000c1c42810000742c0740060040c401c1c80c4c007904850295400800034425503d9a490b12140c1911700c01041b814183c0e2644041c2c001001071000300700801d03d0b078200113000c0c40c00c20070140101a00400c141c1c07c200c52008040000380c20808500180380c5d080da14003845c2140140143d40304020710790310607130081581c92080c0300f80b030711600310b14412403250005002d465a13958209a503200042c094116103802c0c04005142d01c0500c018005660601d80760088424040362103401c40466000c01c103940012040004402c083e500303000d03000f42d10901071042d520302490240308035200d013124000241000303541071081d8080002003041e5000f424201a0701507148c10003001c0d140d454480b010000502d00c1c02c2c43d00190200c101d61003150100c903e22034001405040f00b9104100d000b400c1c90b18500342d943d0304d9508002040b000c00180014042c5500c40e440d040d070a000c4100c3c0340c902101d5140300d540504108102c00358681c41189464404041c2030701e5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 905488183 1250 905486933 905486941
    0x10311090a031406132f0a140f040207020a0e070c060501120210080403080601050a02011113180504150e01090b010e243109030f0e010203070308161115090115031505 73
    0x1640c00c83c111b0701c10340e07200c2c41c2c20902080036004900c00035401c440403186401c0f407003d07280a1000b617020f1b0110180d80401401403c000c007603034010346c1c0c5030b0012444c64aa00c00281c1c5694130700c01c5400a810100040e004c4c103c00e2800c5050400c3d0f103003650140780c100602c00e45055a00103103041401080b00f410007038081050ba0016000350414400000b615407103c0e1a00c1c800c1c1818451151180700300d00c42052100320039410440244203c0d03028980044030320003100c4425490f40060480c844004105643e24001c00022405090449010305000c51080049090045d170003011814810088e04020000d160300e001d00d80c0d80c0c0412174a00013504400d0b040b1030051111001c4240444001c1c03c4441703800c20082e0001c055102526032104407403074440459585001004903030f02d0003a08002008210110b01142803141522100580d900b61490260400d00c2400c1c5031904200d00d051449100314200400d1125a103001c2c0100d170460b144c0c0c0c0b8841402c003442e6841c1c1050040084e08030381d020982d1030001c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 905489433 1250 905488183 905488253
    0xb0309210f03041407050d0c060513051905010806040b061c0209030f0c030601060e030d030f020c07030605040507080c0915301002040b040302010311090a03140613 72
    0x1441c00c4040082080340c40b46441d040500d020440c0940181d00c0d802000750100d894a02613800c44d0420750880020030701c1ea814544103940c2580940308440e049039071242c000400d40d850116040051322072545400c8494a800009000201e010707240520450400109000e551104c02c1070300d41e04101014241c40342408083c00070024070840b0103158040c0190240174190540000b40e0084040b0300b40e08803000345c0ea8411003101d0801244c8851641600602c0c03010340744178407a810079a1203070309800300146450258400c85251940d90b0f03008517121030f116400c120520200b4050701e0028504900600f00c064120000101c824038001c10302042c00ba210b00103114640c84039101c210302c01c100c08000340c2c41c01500c03000c2d00000104084401080d4414840442044011070094404135240c59500034101030a40d4015400341c1030500702968070308000d02001440c1e075070325062003009600500f0b02c42c21240c02c0d0b80b5035030306000000b07118003400c10401144400080e0721400c5007100d0440403000402100401e100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 905490683 1250 905489433 905489437
    0x1020106080c0d020d12022a01080f090114010f09110909041b09050a021213081c0f1805060f06011e05070f050f070f0305060106080603030d0204060c06060b030921 72
    0x2006c1c1c01c030040805a040f003260000703221550f60510f005510704c001980c5070b412000d10036080b49240004d1500c004145036150204210740c01481c60400400d41d0dd00c071081d81c5003428026071188040303561126042103134804500c02c11100405032132091b440e140c01200481c00010015200401c0b01030f8400d08440f1241c1e240e140d4501900400c0018070042c01c010500e040690080d01c401c089507921200800c0f4480c1c0b034446100d4180b640400d40130f0414a41d0710b420b000180c491200c4800c2c0c0d903144c2c001c11000910380d221340091540003941c001d0f162103050414914000008250580c1d28400d00280310fa00d82e003001d6800011520030450170b11036061200c0c201c9047c0541c0d44002c0203180c10000d02c004101c80030548810441e211021104001da81d0b0544410340000e92001428540103a0018002c4622405010750701500c082c04503484c0100140c2c0041c01c070380c1705a100000142a0304044000c102080c003a1500a0692010301421401c0c003540860303c039101055448840c1300c9170320450380f1032281141 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 905491933 1250 905490683 905490709
    0x120e0d050c1c05010507200309030a0b0901090209010b030a050106020f0319050403151e0908070b280207380415060b090a06020d0507141005070f030b01020106080c0d02 74
    0x1c1c051400e001c1c002405d40051400051b401400347c084664a00d100003003a90008040140103004000160310352080d00e420141500c115035490f034a0b40f00250b201e03120442d000301403c200080d41d03460918200f104580040e0031100854002d00541d4040a00010545003000800c0c3c0c1440e81c0c0b25065281030303071148640d070b10040034550410040104c54106910035411240303280d1401e101c6040d100e01c802c0c1106c5100c44000c1c030503d41800f00c2404200c4500c106940101003269001441c4000d40b401c003009103941d100c2c030014075000640101044103003490450083e01c1070000144482c40040300b80501d20040f000d00001010318000202880b0114118480307890240400700300350307500c405250b0810360001103003034051700a2001c005401413001400786680340841c2d50b000d04040b8184d81d00d0170b43c0811040390700344510405401d5250305d02148540d03800366200f9210301200110790400501558101c41541c0c2c15a4500101045414008103400d6400481207071044031031062803001640891500d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 905493183 1250 905491933 905491943
    0x1b0705090412050d0e010b010f0201180618021206040303060e1006050a1205150102060c040f050904030306051f11061b0c2401030c0e130b090109020d120e0d050c1c 72
    0x500d1715031a0b540194807240700e4210a80c0d92130003802a51000340c1c203031460351840132071088a040302000454000d600c0700340d051f8900f0b00d1120500c10180c00080b181c0c5a80015101c030b50304250b0601040541500c1004002c1000b0301d070200803480c22007404445440107204080c1880400038221030098491862044141704c0120100030f00e0403e0154403407001c4c10008014098400c100c081425461403105a400711607480c5030012074241040305104c00d602000d00300301c2c1803545500002c60310395030381300c4c0308224500b01120f9440b903001504001401c20b41d101183d1406604068140a04240107142070a82003442e60b04c000d648240c00b030001440d101d90022080207141280144004107800d02c0b032124100c03409110300114180c1c440310fa03000780c0c100a5542041d9100810089000140c410450329804010000001206102600414681c041120b42160f4814010b030300d07000903070341107202c030b941040003a42c01484400340c1741c0c0e174a640c0b03c00301021107110f1010440f120640c400d542100728040303503001c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 905494433 1250 905493183 905493191
    0x12020f180723040311120a030305271002210108070303080f090a0f0309031505010504060b07031d030a021815180a0c110109081b0705090412050d 64
    0xc04100080401500c0180004000c6001516601180340705201031281d44503903586400e295545020841da0303282032036a0060280e94000e61072500a0042900c1c0c1806034074086094a4603c24008250030354901c0c0310200050030348a0505d1030800600907100648007600141d550110700b07080c0d070b0802810f004008910300a100007090a04020030440202e038465194044180c4503480c60640e449001ca031000c0059002c0144d080c0400c100004201d94035019080c984ad80365100d40f28001d030355001300340c910002600c50004120a082512448005040b0100113500f8000146c0d80249034043c1ca29002580c500c4030f03503084946a0341030003080c09241e03004009010000442108040c44407048900903042c6030022182c1c00c0c0c90a003e01c03407241208003141c00003030320340d1103050480c01002010b0184c41003101061591030010000d10980082c41d0083d9101d5480e04120850708520889586907000c05400500013004140c64501905030000e910288448008406940446560041d450920200e03424 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 905495683 1250 905494433 905494459
    0xd05070f080c031005090d260106021c030c0507080310050d0b0a110703140c2802030c04060b070b0c0f041d0a061401030c09090906022106010912020f 66
    0x1030348888030790041d001d641070b54a113035180e00c04490f0b003210030501d1a00702c0548501114404d170340c0081c002e000c0e8124101308640c0b5024486d40004242c01000160703208801e541191049140e10000e550504e1506008025a2690040c03180c01341000003010f014020010400c182d01495040d000760074050030a0160604c1c9040502000e80c05444004c0ca03d45072130340c9c418010481504a44040d60503856080c100d003e03084a0520986c808d01e07503100c46008906851861110b41c01c02e080381e48a8010750612020540c0c010541030064080003079100340d28202080114031110001c2c5c1700002d400c4040c0f11023560314008208c9141c03150668104040b80d00080110b980041304030030003000c426188a5948595412481d80100e0381580a0314040c0c0301d05010003e5a5031180e040a44085060b01e80254075940d5012140196191006c040301c0d10381e004113000345c0201242c24000a40d01c0301c0303461f4854134100030b000600231400a001c0d541600d0424240b14041d5202e411683c50080e5025207038004c2e00c10b0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 905496933 1250 905495683 905495699
    0xb0f040c031e09230a02060723030415021c0e0a030c030b040b06041a0f0f03100b01080702030f090108042d0b240f120d0201050a0b06070b060d05070f 66
    0x1450a003181c00c1c054413844100300980495150703000c00501402421a404641c003003220503040860102c4040409440054a5043c00c5500c1c200c010300090065440d01c0c145000143c088c06d00040d0300c003c5500203000e402601940954070b4240110381d08000941c00c0d015000705001884603040a881050421800010040d52a034404e115a0140302038081e541c54001c100416900f041c040d210b600c2c240390409110310f190004000b010900004c0541030304501e044007003801e1105040000401c2c0e0394031114064507580060300c5590122040c40a0340c90044074190861701800341c40202410030898900080400000a050200c2e810017044a80c2c40c0c0b145803828400b20314280ba9048076200b0030349000c601414841c080d031031140015920343c417690140e044144018507510031301580c1d10100c03040701d902100c20103002c160010041d44d4000324040c900010701400b5500d001e0f484c54000c144c01c20550f03010449505e542c54121804403818194a0502e040c160324201a0b6000003400c40001c000000c2c0e0f1030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 905498183 1250 905496933 905496941
    0x1b010b12030901091406030f0a0608150901060501020c030601091a15180613060305132901080703032c0307140a1505190909110d0f0b0f040c031e 64
    0x1440998411030300c40d49030240c800508030070000e117030303084902070000c1403d9620007000640d00270800c0038001100d60752600315500e4034031b10765020705807009000c052204090703017801181c010700428001095100f5424003c02e03902d0405202d80000c643d502c10300c5105001c00e0110315412500010030343d10041070101228000c55000e210815580b1503001c07080d1429040c05002e9422050340310803201481d40c5001016009484010003c0c0c0410f0030000d83d9200040c801e80140840f91221001400b440c0381130004c0211949060f0030195442d8450142000002e40c4002d44d28050044610452a000001607407080b940151005855242c007a010010513031140c1c40c8200c90800d142100c0c0f160b001540c0d0010030324654030904d081d40004404001a054600203a00389800100f0b0714034180c100d00307603280045400c894a10661304100c4500003043c09400c1c3c594080d101c0004407a0800f00300e015800380004902c041581c3c1810b004a480c0d01100c09400d010341d01c00500b02c000100501e80300065688404010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 905499433 1250 905498183 905498197
    0x210109020916110a1101030e03041802030609070201090c031101110a03021b12030d240303020d03050c1201060e03101103011502060c07030810050d110a1502031b010b1203 75
    0x9010928480c001d5100084c90000b0b1603003040c581c441c62101c050044000d000d00340429449440200300c00659088400c1a0080541221000684904111040006d880340181c001c00442e03040c00403840125215004034021242d201d01a90000718082c0c005a58130212420110014060160ba05041c0b60700421450344802040b400c486104e07031903404200d8081c003002c0c03103080d0075442480646146803e039402404069605100520748400718002440319003c540c00c02c50068104440807084076815005080c0c009410080c0281040c62248103003180120501c079190401010089080036514140722149115040c4c1409002d40704800c910410309038020702c42c003191507008980c0c0451781440840c2e040e0250007014101031410100d42c600701c0b90b441001d0110009295a0007001500c1c3d503a201141455074400c1d004420342440325400c0043c400070542c0701d0b144251044a2980040380d020041343c0072a1408480da11041160841d00ca004118054415411080d42c62091903120000009000a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 905500683 1250 905499433 905499437
    0x20d06030218010e090f15070201021917010e0609070f0e030a030908070b030702030a03053301080903090102031b010213061e020106060509130e2d03030402210109020916 75
    0x300d0348804400554840030140d0110490300f00422a0112142031f407001900b01c02d0f82e200242c00c101c1c00844020f800b203103031822100851008409007107a649001c0d00b20f401001400701110b010b14180e0301165000400921103002c101183d1180e00c0401c0c0100a16903096078003404441c40c0411500c0d002d0044055400f4815662245150001c0e80a49010450f40f0450303040d4044c608040d400d11054019060107031018022420104160410380e920803004521400501800441304000000140040001602911150f0002c001c2c007100c0d40d80000c11252421221071081e900e200011b0481b034024051010a86401c080000e0002600350b4404000c0b00c1c80d0360b0261100681d502d521400340d0132140d0344d10403400403170010b000425035427420914900c01c0c103151002c045080c20030b502045046c01c0040c0d43c10480c0034408004050324881e102c0c14070784011b2180c2c004500d0b6003130580025042001e2140704c0d0b88122400408890360090a4000050b010340c040c0c04d050140c1050041d119101d01e64a0888d40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 905501933 1250 905500683 905500709
    0xe0a061e0f0e2a06120105210c13090c03060e060a0e1209180f0106090b0708030a1113030305071406060f040c0509120114070215010504020d0603021801 67
    0x8601d400502c112014140000014400841c90200c15000340d4070000100e02c40159000341410941c85060090414075070003404024598181800c100040700c0b02c0e01256800d403844229030701c140c0782c00075500b10450b504460100145100d498401c0140c03070441e00003041c6940e552400000c01070540c01c080c0b10001a00c0075681265070301c400d0b610407a06545070450096000031101c1c0c501c0c000341401084112006043d105000b550440751608006041e85c144080081903801000043d43c0a0400030161807a45081807900c9002c0c2c40e13507200c500020300100300c025914503081821410032401c481d0110907040f142c3c0e00503580c0b4103014059410200d81903801103003c0031010046c10001c034200384904002416192140c07112000c0c84002c240d81c81c244000d00c80c0c204160326040d43c4040c03810507040009800420601034000c065403101c0c6000c1c00f030805540c047d403e500703503e5905010041c1500c00940780140c50b8101e204e2414080d20300d40d4400380d045002e80090304140c1e054050750314141c4e444009162 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 905503183 1250 905501933 905501951
    0x403020601050909060c180d0507051513140d050f0607030506100f0e0a0f030507033c0602040f0b0304020a1a09060d0908031311010f0c03030e0a061e 66
    0x3640201201c4c540c005801010014182074003d901034070350070001c1024488134a41c2800412412a00b10401303961a40c014101045280340850580d50ba078140c0183c00d41c2020400804030054900c40d01614100031840d50040b0740c1a11071b041d400c482c0c0f642210407154944110019151110700c15650180000e0801e000a440c5050200c0e540c09040941c1c3e5803408140f040c0c0001f190f030002804042c81d4410005180040c0034481c1d0303800711000d54024070280900519602d00307696820321950307803182011710b20080a4017503071200b13041c150710341d21808901c41e5400251915070028869a00b150b090030581c4200404ea1030607070001740d0300c55803003502c9401c0c400340c58a551840340000c1202c480c83c00c24080002c404241450300c0900094134071658013045490070f075070321044030340c00c2150b021610995068000301131122203103034500348034002e08101c050380782842c4009214035050702c0e0150070701d07403615815503a40b24204056000d03640c20100c100b01641c0d00c0d100b03529440700c0101d00c100d605810440320f1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 905504433 1250 905503183 905503189
    0x1c09050a05061920180a0312091701090f03081e0c0903010c0810050d14030c030712090e0a05040809130606110102090f150408060c0901031b200106090f0203040302060105 75
    0x1e131941c20808400d031802e05e9640c20940c0340925201a0f10341d08103009060000c000740052040d4110101a034603403100d10b90912400d0305200b19107a074007404d80d03030410380001c0109002c414a041e0a40c1c051030503c0e0a0b5031111109001040000d8a00302111007001c10007001c0309218000c2d0001c1d1201724000d01007014085c00403108840c007a2603507002d102c81203208021510301404181441c51089411322f0301e6030f0071074910307a00303541260070626056007001410008121003e180d0b18140390341410001c8400c0e080610002c8040c0d0018050742c8402d03641c0e8085024003145d1000e4a1601c1c00c01482000780c0600e0280c1200a001c00d0300c21600411b12040300c2c0d000015060081c0c1f4041c2d04090100760802a00800300401105804c0b45454100340400020581c0d5000b408864441d0030b6102c0c02550300e00041000404964007070382c2c1600c0c1075038031061902400f0ba004850858030160b415560b0940704440c0d881078014900340e84801c1490380b41c1045400c01c0629500610f04c0342d40039800345d0704580e90310001c4c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 905505683 1250 905504433 905504471
    0xf070e070c030807030f0902151e0a020706080403050403240e0102090607080a0e06120631150f260715080406020702040e0c0f03031c09050a050619 65
    0xc1c042000324000a040900c41d9000d100000d00e07541001c601c111541d00410b0340c04d50312826000b410351000400c4060660440c00d500d041c2da5400010ac0c1c5070001121009440707c105010710010010440003140503d8800c000391405035420400c41001c40c018841400113104c0c401100b020403505110321901e1104042c401e81c2c40409015117110702d46040c1c0e0780c0d4070100f0380c4600a100240018880515800c0d110308015002503034042c46844141e041c0301c800c106c100c3c20800000c6144001003071404e14081c1c2c1c0342c6154009180350300e00c0401c1881c0752440c5800081043c2e0000e01c43c01c0030141d80000c00d642d51400040e41c885e034805494071580c948565168940c6014020ba18034809443d444074004c80c851200d00d98030900a00b001030921046074001030580d4a0320307000320b889600013038001c41903207845d102060802402310021854810b88864031580060590b842140c01f0341d07114042c0e41444001d101015005502c18107907007040c40c0640c0f0340c10019000c1540341d0002481c129203000e4000103200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 905506933 1250 905505683 905505707
    0x18060c020f01080601090b0c160e010914041101051e0f12060a0609050603040615090b0f01030618090507030b0406140f0c0d02030606160503090432180f070e07 70
    0x146c0d12101506000a60002c1c1d8020408040d40344585480746081111800303504000e0103100c01e00d00b42c15454800440c082d540d6a480300c004811020080c0b0000801060481040e9402070034030fa62503500d000c85a002ca02c59030020100804000207003400034261400061168415545c2071010700c0d2581418008503001900404010400554041c015031411102542e40988030307075404110380d80c00007400000c00c040340d032011038143e40760320800c1740c64a02031052035858078003032804210851a04c5419041040c040301e4040070b0703d5442d2040e0040c08020301800d0051500300b01000d030182040d16001000348400000d109006803c04081008052030340500c83c00354280303180c881c0c140301010300c001000758006407103035501000c20010034060081c0c482040c0001d034003a401454036110254144802d03070b00c4c014140c480141a041c502d0110449800c80d21018040c08071140394503640d000f0340e51010041044040740b85116210945103050130000c0e070700c03059502107000c0d802c0644846009540500c0d0b002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 905508183 1250 905506933 905506937
    0x5130c030c23280305011503020405090118020f010c05030f0706060b030103050a0b15030604030206010f0f0305280b09010905010b0103050601051b0c0a06080108070605070305041518060c020f01080601 88
    0x8405049000380c26202208903500060f004072071956a40d46650171101801025008074501c001c0810541c50309220784c80e40003801000a0010015102c0010039000610740024401c0e80a990f20f400305034815054036a03881e45c04002c8a5a40302c008041e46c946411070b807000c5500b5420708601150b01d0072103005076412070350f0100042c071101c0c240d84e548442c07401005003031491408415651164998007003002601550103500600302a50520300a0300159100d0741041c100011414403c2000401c00618802c1c880005421a040750074100340f1100010440340010703101e044060180400380c00c040d880b009440b449140200800d00140006500391881101c03200c0c00f081d03051245030751400c0300504800304080c6a000b81c5e108900f20000180e51960650401000154188018404007000f00a084060b10440c01c1450070301c201541c6c010070921950281603800031403a110385414034010003084c0c0042c660b610b0900c0f501c0d52103000c020809110f008050384601740c0030300c40d0f08003035000311042030140a0607 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 905509433 1250 905508183 905508199
    0x30b04060e03160303020c07081c12060b030420040903050f03101a0a170606070822140f040905190206090a06230a0504050405130c030c23 61
    0x1646840c40100200080e410050004015581d410420644004043c81c840d0710016103440c442c0d0f4296207004001e03000601c1c0c95014541186102c52403003408042082760749003242580502d0000b41020345450781c00203803900301c04400d21081140417045200e95405000d040600100d1007030801017550300101c0050f0200b901003103100c216001650045900400034000e20b07174501da80d60350182d240030312520354415000005c107078916040d50041841f920000c0000c8000c0360360901000040203403080c076000a244007800500e0f00d101400780c0340062091101900c0102c00c017070f07940c600d081045601007446845011100d1629656103441d100721000a6001001004000c01d00c2da02c50140c0c902d10502640e00417804d10000b00d5540e50304130024050240d03036030b480c900c40150a4155040c400b140a00103d11041032203080b0086500c603003035400300c40080b200400d9503165042c1d2032407440250380c0080c040380609000070060000d00276480c0200c071110300f07600101c2454032500e1868a80003206640c0c2c807800e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 905510683 1250 905509433 905509441
    0xa0e010c020f030a030305010f0f0311060a021507050304060606051602120c04050903090a0b12070e0105070819022415061b010c080a020903063d05030f07030b 70
    0x30452903460280d2019000b03072480c20104000901d07054010ba02240040e07183d000600104220480b444010200b08041413140e60440e40d8182d02d1120310000f403030003440702081641b0114800c12070402800c442e5104041a070034840001002a0300071102a6903903810700f0790000d101486901106e00d280c10500703881c00703003802030f03820044610100b4041841500c00c1c88161403c0303940342e2242501030360b000c0004503602c02c0b070107080c44000f000c168800c410040090022104011030f038a901c42d880003203442d09101260586005a82e1809840009040c0c650045800e442500b0740400405440b04103400b00e4001508200041d0300025043c80b890041c07004e4000410005e050b080e00c1c40030001713401002f060030305202070340c498140703111001200170310ba44804101c1a007075006807000760090740040c0254900007040b030100e0760b10b4071702800c1c2c0200349084408803044940c081d528110b015503460350032007615441c00300c04240030500b400b50318401d0292000818010600051b001c04036980b0a52810540d95 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 905511933 1250 905510683 905510687
    0x32108070f11010e0d0c1104060b031303020312040609060b060408100213080d050d0c14030601081306180b010905101511010204270507140f07050618120a0e01 70
    0x800b15007894150b40703c1440c00c902c0b00040c0040d14882c2201d507680c11018956050503102443e441d0f030084e00413450100140b00c00401e14088a51010503440b01e01640c0300c3ea4a4102d107580301e0200e8544041c144413007071104001d0241c01280d125409401c00b400015440000c1200d280710317511036614990f1082e815509010002d4001d403c84041d048e8089505582d16401c04e81090301d03656500001074800100560b50302118030940c141404c9602d0021f9199044e096003000c00d00c005071500d81400381a40000303100703024040d041d5103500d80c464403e22800c2031125104081182141d000c880921a800010030080006d104070340c46400c2110914410a113014121800c030b400554207032007004003038002c1c0150000240000c0000300b0541c0c240350420010700c1001011140340600c5801c0542c103103014025229409050000e60002082500750783e0300000440c0c650038815054020080d0142204110f1211842807040d0081407212054619409450040f00e03202d210b08080030740480d02100361400d00794 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 905513183 1250 905511933 905511947
    0x2030105420d0b04120f090506030621071701090b0703110409050108060a0501050402070302151005120309030d05120f0403090b030a090201091a07060b0a0b0301032108070f 76
    0x2084401e080821401c0410208907546840507041d60b1240b5150140f00401c540110249150b1209182c0710008441c85a0001c0c4280300a02c200c6200c0e1a020010501d140d880c00c1e40211900c0400c4c0c1c42540210310b4240c041e8586086104007914042c00884c540c2c6402da043c09048109503014001049a94070711170180d00608040300b00300480042130101207181ba0f581e04ca0315000e07100d020010041c92914140d0038003600d02c140c00c194022030061140d040001c0d00011030711080c0c1d9000500441c5a40c3c0c2e08400c4a1814060f44100d40c0403a0140d0111500600840107200b5003000b6401d9030b81503030010f101030b1383c01d00c00c0300c1020340814401c1d00041c1d00343c0d0203504d41c1600940720303140c070781c281550724171468401d904240c440a45d00e40c0da07503020804568105104c0801080902815080d80e42d003072081e58818040c0207800b400d481e48440c40612160ba40b10500f1000c0d2034007810f030345c0c4c40b5616410712800080300004048207041384140010300e4036029031015841000720340c1d1042c00101d24080304032607003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 905514433 1250 905513183 905513281
    0xb06120a11092206150c030e010e1504180501030c03060507021207050d0e30010b03150703050112201306060f08010e010b0304080a0504091802030105 66
    0x910301c14820034489075100c6200c08000700210500541c0303030300041180000c951460388074000e6528000c0d811520250040311040f030140c0c150411060500602c1d0042e182020034580c641d07800600d40a402200b1002c4001600c261001c110741420342000d004011400c030b40c402e000151803500520010400141103801141e80311b02c5c02d10698200620021071803019400c00720044074160041460405566480039401d807a21000b19824203443e400c1c010400c2d54041100a111110f5440e14000e100d00071094100241600c00542122030012040c080304201e4803054a4110000f42044000074081c00102c19169003682c20200d009407441405c0d010101507240741c80800d03001030850f03411010003441c3d4820040108040d17243d410150706030040c001c144540580100031800d280100600c41e03080b034078003540d41c0250b000ca0031780d6403941003400a80d0240584c0e40301425850402003103440c1400315054405480d0b01c284e00034002c90f240e143c0d000c0c0800003486120119050540000010310550700c0d404051 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 905515683 1250 905514433 905514461
    0xf0b07080f12040c0305190b18030c0304080706091409130614040b06040b010c0c0b09060c0f0115080c010c030e060702031005040311061504020d1407120b06120a 71
    0x2800b40c8400d41039a00120844003a1140c03038103403204000340b0005001c48601c52501071046012183c4942d00c40d40e50710340250036161940d4000301c8054602c5010400c071100300b46031108480e1150317a591003e0307a032400c4a014004c0001d2150000282004a0304000c000c02c2800038000706007a91341da0165454292303809415103130315031114101a0310066514040e070040c0d005684450181c5440d800344001e8030103000441d410400240707183c8001c00e0041001c00141c9410581659566580d0000200c890180030b05c1c13130126004516441a1800c0150701026042502c58031120300301d95170740b840a0f1248009900640404c4500c828000000d110340ca41c071006d030030000c000c40c2c100300054001c05c2c500f50300d0420880501d59508140000d2542200e903924641600038005d00071450401a680c4501c031003800d41a01458011440030701d041e40a401c110641ca441c020000624070744848002c20003508030f103513402c3c0c0310325081c01384115040c01c500310ba07920074803220042616212181c400340105060b18404036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 905516933 1250 905515683 905515687
    0xf03070e040c030c021209060f070218130c0527072303040b090606060a0309030c140c09010e0702030906070c12031809180f020f100c0c0f0b07080f 65
    0x510780da0701c0c03289185002882d035000884104c4410083d00c2e15a2a00c44038609a03801e0080e41903a035507100880b00c130100d01460040d00c522051002c03881c0d540d01c0d9056400d103415580300f040100c1c0c078200f800d502c00c3c17401000000105035803031081c420081c0031815406c0c6d82842128240304510700b0420440d402a503640342240103e4222211301c0c4000c11200000b01040c1000012f010a210340d947c0c00d1508440c01a02500283c100440014900d204290002d801d05440303c291100341401209121141d5801140c032440300c0e0f003220080e030340703274041c84010901c5060380c1d900100d480300040b42d2542c429a80781d0001e61130304110004001c02904601021504082c4120b004241111045842c2e424144070752070b4064881030072120322607029411707009105030707500d80210104600c4066200b42c49880d00002010560703541c60010400c20250b0703c40c1a50454102e16090781079a500241540387c0d1030040d1591840e143c0c8680b40180b541380588181c3c910890140b2020b0041a000c00081100081213a1418 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 905518183 1250 905516933 905516957
    0x108130206030a140117060103123f0527030c030d020a09080a0c171507050307030b0a03051222080109030305130b16021009080405040e0d02030f0307 66
    0x5041c0e0303407048451007070041d255080000d422103184419800b60001080b056169101d2840e00c90f17640805100280c00e221480401c415aa03001d20301203400300e60302d100e82c201c065402c000b0000303074882145020300e20401ca2401c181c0d400201c0b48640c078000c020741d200c95040141c8400c4840d2079480c904500b03038210300080224241b04841080100b07500610382700050303260303490040701808900d42c90344030b509140c210a2881c5c4c0080e00c0d04030f9000541e5828042d15002d88a03842080e031070410310322040100c00c404032040c0241c40340c0003000f4520404880da41401184111001c0c0f00e80c8001d039100081041e8800c170590f20402c91280082c01401d90500b043c1f108082d00480651103000a5600a0030665074038550942410b03854001e95510a85800a80705081c110383e40700c0407180c20040036181c006006420084101d482030221450004018006001d40c40c1e1130f041072f020560203486070912552402074902070034200821034a03600007040e009141842c003c000c0c0018558002030600342004525100c0c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 905519433 1250 905518183 905518189
    0x903010e060109150e041e03030906050901090c081b0d03170c030405060a05060f15090303070605011404110f070f0212030c0705060f04060c060b0d053003010501081302 74
    0x600070440b00340c000c20b00d60510482880100300c0768000d42c98005c04401044049000100c240e82c031030780700c1c51b03191042480c1d90600320000c0106400c010b109034101000e01c8044041508030070070306400b0b030f940c83c1c0e86142d41d54041c07a52003010348102c04090b050036562076071503c2c0042c10a041603010741026211141d683c2c0324500c4890341281c45e40d000410210500c81482010020181c1c4400010010800d07401c0550001d0b03110390b80c0350605071141c0080c1c0b1000e04110050320558440c0b020140c204c80e22052140b42c80000b0301424061804101240440c010080c0380c03034003c0c118034413403402185280c5918052443c1490b48170b0301c401d82e030001018624000586070248060b4941c44804081d43d183d5a441c1c00050600d9526400b0f00c0c40340308180b24540710b4010240071136045820605107070001c051a0f00d0a0006000c048a055a0001c0254420f0042c410046200b541d0032225102c43c202c44200c0b89850072580e000075110b60507a420a01c0140019409130289942040400c0107407141030502d6400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 905520683 1250 905519433 905519443
    0x10909180303050c0d181106042615070f030b0f0d031206030b15010210060501020709020c120a050429070f140607091505073c03030c140705120903010e 67
    0xc00b100c00a1030315010047c0142607030111054a003c0303c546240a151910311014814801c0c4102264010000c0d40642c10301c08000000340c04102d180c602d201441c8c01a406880c540304040c002020900b03111000c2c40707502e40303400600c0c01400c2c01481000c001d201c2c3d8804903140c00e54103105a040940da000003001050a080c00644100f80c04103d220180210f007000908020004400030340260030020240400e80c1c000c6100016540c800c0d00050700c44400c1e0840c81d18014590112504a0000050703d401d2940e00c11300070426110360300c0c03400d00c4c0b5600341c1c05002402111b513595041c0d001e41c1448198001800210080c3d01140036040d2040901c4603034050303d08154007035910b43c0c003003004c0b80e0040201c0385000c3c03c203001401680c10424140703000c0791510390f50003045964040007030310f0181d00d030381c1c801521260781c01c55a114000407050002a614000d8028018a24450040351076200090806010302003180c503001c0d4040080c2407142c4819100702200c0e004040d00b1549075482d007120710030350f0004100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 905521933 1250 905520683 905520701
    0x11a16050718050603070506161b050117101806031b0509070e0303070b04020d081314040204120f03090b162d11011418010909180303050c0d 62
    0x800303090002e181211000035402c6607882209000d00f4a01001050f0340c01080b11403c0314002e46603135985101d00d56101c0d450410803071000709054507038074a000a6030507089040b000d81d0360a0300c40030b1840070407960600d00c0810860316510006481c8209101403090f0019581c8040c04840000c190107031650358020806c20945901514040354500401051600c03034901600840d03281088180c040d000008203460344600800a42011200f10124046442c0e81c0078410a0380d0f046441c07251039208a01d0458514545442298403442c2c1101c20281603282a208a80482d082c1c3d001d104c142160070360b01c0d580d4007540d0007429000c0c050030240000d408030309140100b5440d0641c0309281041c198601c0c080c001c50240075618030302410340c9103c1c001c03c030002001b16200c4079081741c1c079050081c0080b0012515840c081c0361006a800c40891500c2494a042d603101c1c540328403d89642230700c141c84202d00c0088a034800c8030503c00540405600700480d0080c2c0c000da41010b4501003403450820b80308c00240980306904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 905523183 1250 905521933 905521943
    0x204110c060717011202060304020a1205030705102a090506040807031406040c0e13061407031d1c050405180613061202040b0334091103011a16 63
    0x100300424141d1000d0343c41c01c0d1500303401c0070880c0d550502c42d08590300307185090028041d54001004c9010343da21407105034011702001d0444841b4136414600075450f0b4111220480d00e500c03410544105402d150f0007104030360345803003401c0c2503540350300c0344507485000c0d1442c40c90f002d021a1000c0803c81d0b441d04c0e03006001804c00b4000415110b880c5240c052045450010703280c9064009105000000b9141d1035034004031a0358000103055512010707240109210651001081c45151003881e05a500740c101c100c47c400d69664904002c0545003440c040720900301c0900c0d4943c070390451010000d00000102a041d01c004071807400500302074640c00071403101c50b1060b43c2c1562607854103003049901d1800e07240c8200c3d17042d030704034087c080d00340b0700782001408460800c4000d00c141e49500c00d0445c02d880030000507025000310280d10441c20310a040040c0c42c040740340151004007840050100d2031441500559a006400492191450f80307881046940d900850201c68070070041000b1000c02794034150000ca1b1558090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 905524433 1250 905523183 905523193
    0x302060601091e0b0903032511011d011805191a040f03060f09060f0c080702030708030f07090e04030201050f01170a0b04080c07140414160c0204110c 66
    0x4005070070b2602c95405016100021400421424660100d10341140d5481c00125110701c00000041c4c250b010390240c6688403616800490384070400441908403e40c0100c121448210058004580d50100b049a9a880400390b5020403003651250300801d504036460550404019207400002c4c20912226550340940036840c41c0601030718a10424915a459841204a04d01440c10340b48220000c154400540508e560705140091a10700d07070441c90b04154040f6082080c3c60000c1c01010050429015801c0003c61400006814074000401c848140c0d070011021406c1d0340d1020406040b610780144030808000c2c059000140c207e60308120310380183d00c80d4001040601e04001256407850050f03002c0c02c06951140d401180791a400b2501c044060740244800340c4981d62400c3c82c003503900ca01c4c5c02800962040000c0094021101118800440412902030108807041940410392030410340b540340c42400003040c84c0c1c040e28026545024040e1024001142c0044202040350054100d0140c18145403c1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 905525683 1250 905524433 905524441
    0xf020c010b0a1d070318060f06050a21050705040e03120c04050901030311011d0a020a0b0903030f0304150507030c0f08011520120406080c040302100c020d06050103030206 75
    0x3802803071038807102601d28144052a1030b4048207803214480840400041c000089003e161007a00680703100d22001d140c11441001a00d40300b0300512482c01c410000c0340c6080710201c0e080c541840400e040f1200d003602181050344020411031000c01e40f040c110b0740c0748100c400001d0242c50358014a02c1c1120040003454544403041c1c100c00615200914606480604200611050f6a04081e050559405140143c0c0c1c480a04030f04070b0041c4000d021078103444c1040380c0500c005640c00100552418401e944511055913540081070b041c1c040c815001c0d506810900206002c0b00d19000950361050240b20b18243c3c2080100d20301003100c00c1516600000381e00c851601e40516008080a0702400700c03407510341b02d158580780800d10001003030f07100d9000300a59026803801016a40b030000300c81c00c4000046d50b522041c1c10043c2c0003960b11a104500c049004a800030b0024080346c4150740c1100d070007034190032001e0320020341100da03a4820038080385d2160f03454a4035408100244031ba54080c606c81d400030812810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 905526933 1250 905525683 905525707
    0xc0d09030b0a1125020916030c0309020a120203070b04081c0e0102070312050d291e040f090602070f020f0406030512030402010309080310060e180402130e010f02 71
    0x40010300100125040440d544002c54549044944c00c0600280e503a80c2e110180c080c0c0300c00c1c0340c40384601960141c103410510180c1a22855003041c19901030300c080120102d40b074015001d0741d115581c0a903004507098070402150300d07041050300c9860710041c160340da03050b11240c0c81030150b0080d400a05035079006e50130044e07454141c1462802803c455007801d40701605c5c4e41c40000d50b00c42c40d0380001030015220140303500445005000342c882200080c41d0034085440000032460740c064281840e4054400c14102080e4a824402c003c500303035030001c0c45251090000002488090881601001156030b42d81d011400070800364809404500d104200c410300380710b002d004100c1c0c541d08219000c1e2140d494100200000390002030125480642003008613103036555400143c0003411500400b0b07001c4140003040000c0c1105c2c03c1d040c001a160315490340b200c025405420300c0b89810301c0c1323030780314041d54001404100546403528668600c0c8607042c2010a04100c050191070075603202c6600120225004103c50201c03007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 905528183 1250 905526933 905526953
    0x51c030e0d090e0a0b130c030902030c06070f110607080412060606090b0904112101080f0105150d020d0c0f0501030f33030c0e042a14060c0d0903 64
    0x211071880c1c00000706051400010811030040c10960f89a5921440c04199488181460b04038844035030b0b04100302000080301a0283c40880c0c4124482d01403081c1c1c02c01c5600d8500181d48000350003007a41e01c42c12082d80c0c0e650341801800c3c0d501560146041c8050310018001c84010000b520750810040d07038554840c0740007019210190080014130020741428810900d150085d540c03900b01c00c49001c2000f41845e049900032388100501c4202d041220144c5051008131525998102d50b000d00c200c13030403035003201000741c201c55080c3d480b510060141c0554004600c0c0c0910308601617800188400000002c543d643c08203416582d010742800740401c0800c1240e5a01032051611a03014543c017070000b00c1c1e1603044002d9062500300307005402402c6070508200c904c81031050002850f40700051405003034071040d440e5990790048070116080810064a00051811900141000c000000c1c24990207400c20b0308140358074016014041e008001445500c0042d24101b10b880004001c80e242e41103442e0071810142d00306 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 905529433 1250 905528183 905528203
    0xd020a0314040201050a0c1b1517060102060105010c02010215090c03010c020c0a090c1403100504230c0a03020f030f060102010b150421050d080907050109030f020d051c030e 76
    0x880c0440040101503601700d000ca51012075185490816240070340740c0307a6000101c0300310300d4446116012001c10648141d0b281100910340644a03403040c2d0b09014840741c1c1d9614201d81d0305005030050700040090303501450304002c0191050042c1c8404541481391114034140c1282c15080356481050016107e060a218075802c81492348042c1212091005c00718140008501c2620030003560f900d00c07005450b00c900da640d02000801844144d82c0e0078a209024282039444c094240b08605e44403a882e126281a5402081e580260645050070b030394840c20003151f600224505405c0c50b03001c0040242d0b000c0d0740c2c0c00451107800000290002802c01171700090840300c0d02c5264600402c5d821511846003000101a903040701c10150752001103101440080564045200d0000c01500c50f5004845c503030b507040f1040c1071090741a2004c0b10110b40d40e440045800720300383e100150180b0001d85440d0054100040c3d054045030140044031001049060310300d10102000700e440e80001c1d958a2a1f00417410280003840d99 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 905530683 1250 905529433 905529461
    0x9090c0806010e032e0902100804050d0e031b1f020618340b0c060406150b040902070822081002030613090f0c18050901051b030414030d020a03 63
    0x19031003c41c2410140c2e1410320180c1045801c00e80c82c01380175180c1c607004540450350141c244015200350100180c082c0c88151001c40303242c002c64104524180c45041c00300d0f01408010000c001000701c0c80807010342c1010040320700750404010f4008901d60144540c0d1482608210f9000704001e281c419003010b100074540801e8500754009054641c0e448105510508a1418040e00c1c40440c000b6894a10802017050340180707580d56001c03410005540b4080303000d40c40303140031701020700008185148900f0f0480c00d50051300640e040074402803114558075801380007101d01c10301c0074510301207070459130f000382a510040140d48118060401d001800c8244000d014618000c602541107040c501c1c0080c051004c0da680b0b94480c2583e880303011083c4001500c40c0ba18560700200310220894a0b481c1c856281002c010102c0015414074000c9800c40405205103032003109407001603098000c40ba00c09a0340c4e5400604207070b0700400d40d03090080e004401480142115030031943d00582d81c04190b0000341c1940c4240300d88080f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 905531933 1250 905530683 905530693
    0x602010e0a03020a03140903151f051003020708090d050105190203040b1506130603061d011206020304020a2301080717010605250804050a0b0a050904020a09090c0806010e03 76
    0x1c00260009100c94215516040042a980e03266508041a004800300780340c3c5441034440b4241249400c142c214020302203032030142c2d490280c00804e00344454444c807650343c020304144040c129042c4243d0140c010540b042e407c03546480035a5001401d10842401c090712142d40d1001070141b031000905541c60150114038013941149000c0c1c072000360401000b80a4002800e50038240140c42d030394601121100d070540200c185034075440d0540140100308078040c0e0341a0301c20540915800b00303010040d041c100d8184000a076100b008a58030360000c6e402c0604120307000305103800045a120b060300410390800001c1c081040c2c0744802040010100701d0042c080400713104512f0141d0b600c2c000307c811303002d05548884c1001941c40301c2110003034004404001b510100024000c03061000c00645070014011640b088406414447c3c403084198024800c01200c075011501c00c2100d4105406c00d0b4020740148912804d140312a295030b45072642c103454000541c04002800c06080200a680003203100d8085003081c0c0081c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 905533183 1250 905531933 905531953
    0x11707050903070b0a260a0c20060402091b160c03050609060a050c040b030f0403021e07090c050c0d0e030c040908130608061003051305071e09020913020903010908130602010e 77
    0x40b031b4200140400c0255130301c425110010601a0700c00e9009136084210107121040d01c110030b01d4881d01c0c141c41c1240724a0418005c103d8107022512503988032000d0300f281d580740c8010408a180340440e098401ca58520303892000202091003408498481c03081000034107075a160081001e0202c400081142c20101c0d0140024048011841c060381d07880a04d0b203003866641d4803141416440c1842e503424134000f00740401d203080358040000c00d48404591941d03030248802c2000d03007416a0720b40141c05e03044c002c55000340800a01e9901c0b0702051200d204000e8151241211000003060644400c40000c1d81c040000285000b8810000c070803000050109240010f00c0717041030000150240028847c0704c08268507000810301d0b80c4c0d02c4c15a221501c507805412503001e40c1e40c5140000c0f05421200391420720141050001400c5c4090307008071514a04003c1454a5110b155011400250003910240d13070035650b541c90350000540100000e00507104d210300b91201c0585003080007821341d0040804100f03070343c11000d002c0e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 905534433 1250 905533183 905533247
    0x30612080403031809020f070201020c3a080a05280f0c140102121006020a0803011502010e010c050c010b03031c091502070c06030b0f011707050903070b0a 68
    0x501c080d40c1d818078101005091040320400c402e0000d41200600d0362000451303000541d0320900505500b4400c2c1c0a0b079034400801010840c01d60003000d0f40d981803004080400151454805a503c0c0031080300742501d4603401280c640042c941c010034500800314400027000c41c0004214805a050f0300003068182511a001150081a00140c07511520074010031030301c41c1d0100124190703905070b0086208002c54030342900000b220340940c01601d0518001d5101030740440c60714800f1441c08405908000c020b85940d02c0e2000801d0100400200d100441d503030740e4481c0d6681c5c1c000307000e01030f03100e0710580d1030540702c00c900071141d030840340445007840c0302c0e074020818071845100d0003118602103622401d000400e01c000c1e08100c0303c11b5201c8405003040b1440003a02904000d58500068161602540c0030024a40c450043c000045104203005000c102c0d600c0e5444808551520001d9000b801441e0040c10302400d1008a89801141d4100196071400420030900d0694008081c940c40411040896068000d04c801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 905535683 1250 905534433 905534437
    0x6031e0c05090a060e0408030a0506060705030a0c02060409050f0a1b0806040905010b100918050c07140f0d020604060b060304200303070f0501090506060603060612090a060509030a03061208 83
    0x3079036000c1c0c80700300e0004000050540c0280010020f46117010100d1401d80741191055004541415280f440c000200d840b50501c007069920140c1d20100440c600b81d81d800098a80021000080b0b030300000030400820211403034002c080c00f03086074420390792240c00c1079142402500e062200d000d0046245a03800380d00d1700e51084009410000580740015030303201904000c1e0252500604040c0c101041e4400130502950007048482100d000054a0b0700301c0000310304c408155041030b80c40e064025003e112600118024040c00e403d0a0300e1102100d5807242812445800c0c18401002080941c00c02070401c418032038036010f403200303552003120580c1c40e500c0c1c01da445074264002144240102000e450020aa61f01c2c1001161619038000420005030326071031a010f40030b4401610b0844481c0980300100e0038604001041e42d0003108000c08a5060044071110a04c0c2c03401c0c0107090885a110390f40e59840407410700c3c42681c0c041c500380700246607100306202014054410980c0301c40c03a81c603541e84800001c40c07942c0d02 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 905536933 1250 905535683 905535689
    0xc0303031627060504080709020304120815030f0d08090a030801060c0606050a0902071a01062001020405060f04031703060604090203060420180f180606070b0a06031e0c 74
    0x30940c01d040c44007401c040602c4048110b0801d02d02c0c0711880440c0075600b00d8080c10485a40720101e070180c0362600569000c1e804140c0f801442d5402c00511460014010001d4990101c95a02c0092044101d50000ba1810602400305086a003000d4540d181059201c50400c0d44810501d004001d81030140d80c000b030110b4014403c0c1420072011900c03100c101300301500100700a100c0280794025142d04c50300e400c00298800d00c012525149140d10500c051106012004c0c129112074441410000c0720390b50600d21603048201c0c8000d40d5500b000086150b6807078002400e0404400032800b91290b00b10700d40300c07030502d2200210045084c8144200030085d528141114295004014096200d8890f240840c0c00b411490b01740440381c04483c00c111100e030501c4400f0300115503201402c039071200c080e0014031007888030590075203070844100c045440d1f11044400d82207401120241ca030502d000810b88500104c00030981e05460501e032200810014030042c0c0a034001440c65440003401c142501ba03952041c8612644 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 905538183 1250 905536933 905536937
    0x18081506180c040e01150801061101090b250207080613020a120303050f0114011d010509150903070e0c12070909092402040614091306060507050c03030316 68
    0x1900003140c40c1c5510958120440d10381000103041d080c800d80140030354025000c0c003104440b240000140060388065000c3c41d0656070b4031fa92a19900b800c400b02c0d032185500003030070305030741d203275050440029001e107040c922524030a1440801c61309502008400d00f0084101e00c030443d401110148940c2e8004500240c205866031603120160100b072000c43c2c80d808060f8080481c4071000e6141005068054100902c16070484181d20301c00d03a01c419603e1041c4001c0395110b03001500680c64408090b44841600600c0c0c0c40c141007840c14210810000ba0842e040d90040340715992003c585c800c2c00d0308082241d18040c0103400014032082c03401016010040c05841696844111228046041e103805212090301502d0401c2d001e00080d03686003852160030500c94600030401c00d41082d6000701000b90303c296029503046550b21a8009004111403c0940203040c91a5100a5880390f80003114068803d4000911441e1205510b0300c400d1304119080c86900100f00e800b9820030003c0102403280c4084c0d40c0350340306081c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 905539433 1250 905538183 905538223
    0x3d1814040b0402040f1814070c0203070503010c0f1413060f0e150f091311041e0510080c090d062304080306150f0c010501032f04020a050c0a030503071808 68
    0x2040505014100c41f0b00c41360130302002c1100388030032503600403d40b011f800d0083d021280d101360b4800a0500300c0b40119071071000500b0780c0c40103404580c8241000040f804d10002c080c0e08105c0d2541e03c40401404075070044021030321044c4455201500164103940c10300049544c20756055010000890703c0c0300303070031440c1b100400000b02e4814956900400c45190300141c40b04100402c92a040104240e206005421005070303990312151450302c00e0103580d419108050002c402101d0319050a03079a01001400c6c0382600c03202444080c0d40d0351103c0703140707800080c090100800c01d0040642404130034500940031520742030400303040102141c245021250880340548074000d0703420b0702c0b00240b412402000030400744014006546c1041460540040741624001ca00352402e60341e1443c1074029134400701c21812640005011111a1440c095029001d081d11504040d854000c0308040e090401030b502d482240440c90200520071250780c4500c0c000c600e121107035003040302c150816003107a41daa080342d000c18a601080c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 905540683 1250 905539433 905539469
    0x50906030126070b0405030106090902030c040507200a0308070c02011d0f0901030b100e130201031e050a140a09020a050f150304050304053d1814040b0402040f 70
    0x8104141c0002c0e84508040d51041c9440b005801869032203440380340e10941c281040802c02c642144600700540e60b0050040c4075080c200342c207110241130024540d2050084484604128184580c071400c1d0b01d0a200300902100260751501071302c0700c80d003d04400304000366003d5242c0181d82003244040c002910a981c001010180350004007061046013000c1e80000150000008002d101b461040c0a16062000448826124030880328040702c00c0341c1120f03841101d01c14910155000303900443c1c01054280c0540c40282c8090000c906a620540d0151056a40d0701180c1c2651020f4080440e00030410b03c030184910704035038001484d0400e050113541c0c4100c0c0800541a010399480da5810428140c0050040c3c9034500b42c240389449400031b125190081d07440c1841010850350362002d02200040302c1074140d10b5081185450a214140d114440c400c0c06058040002d8820095101c2c0c2d0048c444006030041c0401c010040c031040e038090b96039280c0140e00500040c031055481d00941c0060b102420030740070f28510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 905541933 1250 905540683 905540729
    0x8011412030c1911010f1b06060b0c03030f09030406020a0305031003060c0801060e0109030b0f0403120203090a0c0b04060906110102040e1509150a1e1d0403020d0509060301 76
    0xc2000d980c000603115a0350700d50440c5001d040d080c240303d4040c0004014001a000064420300c3c0c45c41290030020700030900440302d11101c034400f42c0c41d150090100140c99a12001d0f0f810460344662036150181d8400700800a0345020f52440950001140001c0d50901d803030302802954908040d0002020b1010201c005444103a5107a40500150b42055081c4280459242c0140c0400300a00401c0300094201c100002d095018854843c2281d270300c10030030415660b51501115141501038400c404000614000e0034001201e030000c0d6010f12014400342270240040d01d03200c592105a5801170741c80c4102403108000e01034010a50b1001c499542c00c10b80030481000801c1402445150006610101d2190a0021841154000244c00c0b4000d03154041c0a0700c40700e040c0c48041c400300083c9a801420218184500c1482550713559903c05156540004661258101055041d0062440d41400002000c210034158100701d2019442006d04089250426500200f5402c5c80140111820342c1d03210404030b21820 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 905543183 1250 905541933 905541937
    0x1050c0405101d0123130e0106030c0203190c0213060503070e1303030507111606030507020319030b1203030108010207050c1807050906120f1f350d020a030f0801141203 74
    0x34441e0301907590b02c80c070309505020003518500408040007c2d400c00882c48500910407010800f40e50380040d0b0400b105500b00c4003003812451f80d0441000701c800030100058603030050704226850080e0003c500305082000341031030000d1503440f07040c50400b1641403200855002010303440c0d440c3c040c03034041480e035140541034030710b481c0d00d03501c0741d04a00c103150411500d01322036241039007900e032540d9007030000e81c40e0b0134000c17a56800307510038010303401942c080c01d100c00c140030358402185044003030101c6c85c140548076244e60640d0026804400aa5000124a010045c040c40182d1394107000315000d50f034810f406160714100f1800202800300703009000034070f409555184400da401e00c1060b44000845850000030103280500e00307407032000725440c02070321141070864020309034801e60303418000e0125903c50012155515202501c61588501d1b840b07000300c21001e006000718500e40c0c00e903800504c072136a200c0c90f0081240b10600c0c401810090240014408009009122024060100c0310800700714076102d40c1500b14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 905544433 1250 905543183 905543237
    0x7020703201f02061b2b060506040915050a0e0703020c01020909090c03060a05090d0c0807060608031e03010b1909081c020f0606100c030309020301050c0405101d01 72
    0x1445044080324501c0d03600003000c0c2d00c103880301100311188a0081c5002c0596004001d240f100a21a6800e24410f8900d02d2601c6d803401d000038100411041d568a0108800740c0c41074100c0c5511607120051400d5681001d0303800ca000700000c0c0e40c07010541e46080ca21000038503010b002d0104154002520320f0f40700000f50191214144014000901d0741080280583c1d2680c00000d058000d00803440000e003d6a11880340320710506048003d059503800040e1304591020302e04501710b0750500103000e0740011030542e1081d41c020301410030082d541c6400084032030141000304d41e0000c81214007000140a10414503081c0c6051107a401c000c4000300c001c0d040c0941c2c082e8921740205400d4410030800d4448041c001048111403840e076004d42c0c1e07041c84244c0e2550380b50070f011188680c00088158100d2045071042e01a81e00b03450103031800160098480d4006425110103858486041d200801e05000e6464a103010711203101181c20450700801102d1901000705080c2018181806205c000318524280850580464 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 905545683 1250 905544433 905544469
    0x506040e0903070c0b0c010b100f0f0c060f0b031006030c061b02130209041a0a1a0c031210050301200d020d09060e0d1803020409030e0303031008060702070320 70
    0x7089459804405d0710750481c0000450741d60800d02170750218208144c5078045140e065540c02d1040080413030641310340702140303455400c000d0380c1d50b264030204036684101d8180c26091400804e0040d42130041500d0030040c41c82d40201d0f00c2c45c0440420004000118003c11035102d42403074000711082481001e2040c0b54030130040cbd0045407260311032412420a500608003214115001c103e09110305a2624420000810070354001402e09000e00c002920301501d07100c8200c2008a55142a1000c9800742c21a000b038003800040d1756006060090b0707510606450780140100360b000708418031810122011340d21b4240019105090001881a485c1c94903404643c085110200d0502c00d4507400d1400b40e0040030000d00d030300b00da40200600070041c40e02c40e0343ca10701450010211181c6642c110703002c000c014405440c0803001d221184000c2c03050f5480034030107103204184050280c12041d1410205c80c0c1044001010704045400a40003400000c0000407030300c6030384150410702580c00c02142e010454082040b407580c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 905546933 1250 905545683 905545703
    0xc050f030f07052203200604170307020607050c010e150d0b060f040e1b09100e0303070f14010c03110d092d061b0c06050a090b100905100506040e090307 67
    0x810110140407008480c0328803040c00281c54802c3c20300e101b02e9886541daaa101404110030008003820400c00b990041d11542a64689640ea0380007421940c0411400c50300398001540101c8a580c000f0100c207031f065400ea030800140c040c1c41007240300324803450030701411a81d552000720300d45895910550741240c0120070b01179a01d1740c4900416044180886d80b5025400da0808034055444c44481035031190100584541c110100e00d160035103008041c0d485040d0948424003840380850540f180403040ca07070140048e03100c643c081806480c25513800c15549414103080400f003c26050810048409600e0760081c0010f0340f03035103882d00d225400300030642001c60140500803a00314030202440e07485060301c6800e007008000c0e8000c0248650340414000300c0c0c003040c4804c06035400301d413030740d0041a4412946100010f502000d03582c0c5484201064403c02c078100716001090101413018410550024514100c0c1c89900d49801e001030580e102d240a29010b544041c0c0205c0c0d41c0d9201013086e16501c2d903101740859 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 905548183 1250 905546933 905546977
    0x61d0604080c03060a090f02221a040515030c0d0611030c04210503040e0a090b0103030509100201050c031803041a07021e0d021207170106090c050f030f0705 69
    0x2503a2158010b48242c400e0065802050102c121407050540709907000111811010b241e1b000c200c1c44040c060a94154000052041070450109108803a42190703c04001c0e00581d410760140001ca1304020719024166480c0e060141065400242360715030414200c49503400c14480780b521002401809890000c2d00c003011040c007982c030840c0409003041c2c1e040c10810b0190243d008031400864514000080c1c0303682c10070801403100048410702c20354421130f00080824000b0300c954a500801c03400740d0040d80040c0021034600c0040c80c0c041001070441c40359100030701903400c00100880c0d8070300c006010806400c8810254041e24013040c0305030f034000c0030300d0910f202c4040b03050551903455501840d422480340107006c50002803c048400703200443c04015102500114995081c801d00e2810440d00c0803e03403003a9140016040078481c0c0255552540d50000700d01c040c40c000c030120644101810110600a041c03064503031281038001540c0e07011034001031070030381030315290001d82c0c080c81080c000540b80300380e0408170 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 905549433 1250 905548183 905548199
    0x209010905090f060705120411030d08040c0506120105040b2407060f1109040902040b0a14090106020312220b0405010e06010f210218090f010c0503040804061d0604 72
    0x510310a0740c01d074040d1820f1054107001952241c40c00c461a030040356040c040c03030803d221180e80a030f03805841140b00c164081c10800020b40341112b55130351440000d90350030400041244a002c110018601030310014100020312507001c00c100c82c1401034034041c65688100d42040d070b5070001c100c40d14024410070a40c038244030603c0c40c0380562041c442520901e05000395803403800303031500c211403041c900d1140d01828284000b00708030140c0a48202641d0060321802500300070743d00c0c1c1c0035100081000383e0542211412501c280250700744140c2c4140150f42041c041900c0f440c0702c6220b110f50050014803812180d50003800c04064546018501601c510516400c010801005500002e03000e4541c000b200c010baaa68010f42c0c1540c4c000b805456003100c18030a203210520301421103620107034070061915400d441c00710b0400211810894895050f540604180680e0f100c00b03120302c840070441c80c90101c3c590b2406480300313001c031312841c880d01042100c540700d205542d200c0481c0041001000421281e030b40c0e5529021 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 905550683 1250 905549433 905549441
    0xf100216080301060f14120402011b1b0f0b120402060309031204081b01050601120e07053312040807081908060f0105041d0603100204030c2c0f0a0902090109 69
    0x10004207846515a018111b00c04003981c44d02d0f14848440140703a51941c1c01120f8040c40e50804521010002840308005a18141080b507502454520b0442d241d00c0c100c1c0d15602d00c0300356440008146400c10a00304007448050f0040c1d0710030340580e87e50740d03030b9103907000303201e1841c400c962000090325200000c2c00b04100b03550b070041c600401e038030281110403014060040c0c221041035a9032800300d00c028004840003c419041850f5070300b42d14090b0383c1000da603480032a0551501484d0000d4196000304440745180f02011005445c0c0c0103084500c0c100002450300c41010000540080c200d4003021410360200043e00048840e0741e642801c002d41ca0b00e60051014119a1301590300361b10401c100c3c14141e2895220303006031000c0b6030815250b41380c20124218149050940900341c0da4160003891300b010313030080b086d00060000b18490946515003504e00141e00c4e047c02d108007950302a06a206c1030707851907180d401000c1a0400c1505582100c02e03100d61510303000910005400941201c0c0c040c00000d82c0e213100307502c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 905551933 1250 905550683 905550707
    0x9080c0a15060b030702060105040c03090c08030301240509060d090812150f131d0f0a030f0905030c01181a0d0501061e08091501032001020f10021608030106 69
    0x501400b0003a180c00790000580821192400140d1050004100070314058000d0720b40c103074042c240080c1c003012a0300e56010110361074102c040554000801042000c440f040c0f1404824540c6403c0c030020680c2c564001c0c824451540214030550010650313004c03009099110380381c1e8951002c2019a9044c3c040e4007100c07411000c55054400c102d46034600c404a050401040360b6040c40244804103071b14118104c00001d14a1203403108240101c48001181441d0030011b40905040d20401050381e1b40103464006c003510005201203040084d00c5e034041055480018403c070401d5801d00300700f5080660714034191217111a962050006143c2031945140c2d6840030703001043c2d4065100340c10b02003682c1f04c41e815110703500d020302c20005184042a1068200f482003c410303810803403075002e90f982c40c407800040c03118054082c4c10948503995030a01600c40040740d582c001018a10a00160000c003000c407002d20340340c1c0a005c940c4c42e841900000e000701b00c5858801c412145075031040c3d800c3d44a503151100145618444a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 905553183 1250 905551933 905551973
    0x1a061906020a0201090e100506070813030b09191703190609140c03130803090f011406120a080d0e0109020a14010206010b1305010509060c0703141011030a09080c0a 72
    0x28002082400c10742c06c443c0d1160640c1081107035024580300a01c84103501c6a5025908440305010004c00b406405020310021402081031030389904042c811182014416000c000402c0c1d21489804000b5425401d111021480010460b8070303a0b540c10f000001c07090030704c5100f007803887c901703074010450381701641c0940840c1c04242d66048541d5903848038038070035110035692580d1504a400c41440000c203c2e13001550b11a11a500740d4000807090103d207800d58503100240c0e80036162110802c086410503a1030340740e09041c01001040784a0494840d0001440781141c0500d1040d2200c2c06055182c2003500481085540940f520b4841a90755000d4100b011441544a0050041100000c0c2400e01e107400e0300d00c8405d0951501d0302d842c0c9498010b4a03e2384c0040c50080c0c0001090101184c120300c24000000214055218416204590100310f401d00c00500c001a84c658076006400c0d00c0401d1545c01e0740c0d806588104001003418450030100d1050045c070001810074410603240c6000c2100d0000c074104400001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 905554433 1250 905553183 905553197
    0xe0607090b03010b070206160605101d0f06040c0905090903040311061309020a030f1805120a08010905090703052a010c0b06040b01050d0c0c1704031a061906020a0201 73
    0x141200d4807141c40207102d003540400080c07004001620b400801070a0705240e5804081400d4200c1d520081510702c210303100c4052805206080081c0111103660400303440c005109082e041c9068600b0401280018200d640920340daa89594a03040c014075204014040050000c02d080c6004044941d40c1d23800381c00211001c98410203600018185503050300d03400c008400090301c205c1e04010710480250002d520358010182c0b20f1040e045044054800e040b044401440ca5113406840e50910038500032510301a5001e13030310200715207416668050502815241d07551000301d03181e01d90100e194588a4240c0010701a0b02414180e010301218180701c4500a2040341c800307214980c450f90042d184000c01060103041210b17154005640d610385548040c3e89400c050600b0360a02d489410002c040740c080c2d6401d0004100202d02010a100002004001403c019a0028a0300f030440c6c3d290b121901c4d80780c4880012611310004200c0603542c42004042844940c0540b00b030007a85c50100030356682480314140c0c04500cc0e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 905555683 1250 905554433 905554439
    0x140f0109061508010c0804080708040b071a10140405100504020a1106070c0b07110106090608010b1302131203030b0d03080612070b040b0a020c04020301030302061b0a020604020402070203100e060709 87
    0x2041c01401003122007620740c0d410071f036100e8461000581c4010400c0320706070810440821301c841000090250107000c6c085c0300319150801802482c81030300203096498401c070b40341c0040001900140c00d03920078940549001c940358841c030407103099040e010340080d50300900110380016160b600000a9119a4100d01207078660780701d50500396040c844a200141c040740c42440042e0b401c500030002d4a6021098200000b800d580d1810b03240c00300c0c3c0fa55000908140d442e003418042c146400c0c0c0805441c9540c0250031443c2000c0160343c0342c0406100d1003216408a00e008000c420b1502070303800b143c010b20010f04000c200c03c410340780c02000c61038210f400c9803041200c14003541c441200042c40806440004609501e46030402c8180d0105400c4403184000b10301c1107551500443e1070300d0001d5030095200c0e400034106424848291481038050090f41c80d4040020b00441491b5540020117681045e01031341d0042e912415400840c5c00e0011510040b200385080c91841048035100142c01445003265507107800150351 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 905556933 1250 905555683 905555699
    0x32406051803060703020c0601060f0c060c0e090415060b0c0a02010c0f140d080a02070201081f050d050607020106120308010b090a0509040f02030d0e1810150e01020115060c140f01090615 82
    0x30b0b0740159200020101b8cc9048001078940c2d1003282044110f007010041d0140040c0080c2c07100404660455101d04d0120199405a8441c010070001e00002c60310b80342800740e000e00c01a5105600000a41040385000503002417040000c0301035029a00540359070440302c61301c92426661000c1d0304408001402d036a0000340c018013907100b50f0310070302d505030340b00e140a0710b41d004000c00c2340d00d0450000c041e10701c0c1588000f0390f41d515072150b03520306441800981224501580b0281c2110361907801030320180e513240d05050010b0750111603e03054440400800c0e4495038014086100004940c100d503030054070541c1800148400c0d06d8200492a1085080354944a589103080700c64003000c240581d0007185003214415148201c1c000e055001002503181d010455460207c10035109034000e003080810040001800e072542d0a0195070108260400c890b0361061074100000c25588aa01000c2c041080321214031450750824401610f402e08090000e105142203030400c400148030010020454045240300000d180b2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 905558183 1250 905556933 905556947
    0x1a0d0213240308071104062d08160e0c0405030d0f091710050c130e040204020c0313140406030b070e0d02190e060a260c0d12032406051803060703020c060106 69
    0x10f250181036400b920010408c500794150600741c0a00800101100440c01e6441000340d110f00295250021200380c1c82c204040041003000f50601418450800003413285440000b001e038054802460700c14100801c801c003c82d188011604091003001d0540d0314010300c81d44c0041d40901a0b14115420813507a00e40020ae10b0340361295980362000701201d80c4041241d107159071560341e8480e001500c09842c1c400c0d9051590304552054241c082c290f08112018404005184241c01d08518151010800c3c2810760300c031003d518100400c200d0400035481c105070020f44441a41840c05a4003030040050440000440010b1203498028519452280e0000a8551a06a000100300d401260107551801460344015071080b40490010280d0701c02c4020302462500c80d0b092070010740307001e075148034290201200d0080a481e116100450718621410b1042040c4c00e0110f0688219091400c080d5514030070f07640c83e141585800030325140e01d40221000c2004e1281c15130020116031881d04262803560381c032200301727940c4a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 905559433 1250 905558183 905558189
    0x10b0307080706030e010204260706020d1b03020a020a060504140402071703100e0f0a180c270612032606040209060d0207061a0d021324030807110406 66
    0x25030702c00b68040010302c1c029070040400b03418880015141c917840d1460020305050000d8400c031003030595081114500010302402e4007518003407014010001c804000100904030900704105448016101d84040600030011400c085601030419041c0036a2100044d001d40c000c3e00c100040c1c84041c400410f01072400340308481d4420761110040c0411340000081800c10b810062815012600321304000c2000103070410964400e01c040d0110140c245016041c00d000d40e0244034840c5440c803408842040080c0060038468195020300480422401e01e22001501070762225044030070701c03031806201040134a882402d5a4505010f0380380d01d00b074243d46000c0c030000b80c0310a8600d9000c054240c40131900b00d2400b0340003810b4071340d001071043d420009110440300032a44140070844900343e03100c0400103c0020b100640312800e00c02c031002805d014098000c10f0704906480554240140e442c400700c031001740640e001d00301c2d81c2c2402c0081181c668503407070040c080f58420354055420a00000602c90707a460140105015 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 905560683 1250 905559433 905559449
    0x30619110a14091207140f04232701090c0501050304030f11010906051e060901050d030806060c0109050706170c0a1d040c031a0a1a030405121b010b0307 67
    0x28020401c040d14210f4000c601ca02d680314008450101c1042c1c020004e400c0606240905403810040f140108101a925404420300550500442402040c0400040b980040d44444801d410390340b000044101204050105000b00851036900310f0b9a040550010400b41d2003600a0317000c6075290b0005460302c1c00111002400940040902d0443c01d02c21040b407610600c03510008128820f480c0da0740c0c01504c3c0c0c2101c2d0000714042c0c59020f58250340c1e21030384564201000751003201c40365041c407011a07000c6542c1003018080c8043e04000c61030f80e031034036000c0b103480703101003002003024285030321780562030700c40d28171a00002070341224142a8440100d1001c80c02907560031540d030714150104806851509807040c8101d40851703015101c800d16203442c0a4501e60407641e560001d40341049212420510640406440c0280a4844140590001d5040b40021043c620b0718203500c0350f13110f1501900e490410703031780f00606200202c0c80b90034101d45402403841e10100c420081c06100680c100b81640c0702041e20032200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 905561933 1250 905560683 905560697
    0xf09020f011404030b01060807020c04060e0c070c032009090316030c060e10051816031b0b0c030304060509011505060c070803071223070b0c0702030619110a 69
    0x100941c06920b003542006815140281802d69a45602800001c240d00140100b42c90000b04490b0b070741e05000301240000101d0701007100398100255000200402451000012000600403051216101c40c8100441d40300d0071200501d04138034134483c04d113091889079034021081400070410824001c0169070048009088000860700706032422034a40c4110081078540c15511001c1407104841404000f01d0625201c2d40810981001c008044100007103416180d8035410036010442c0602172082c1e035400f242e401c012040b00601070000400a43d201c582d1003c0240c040014201c00c100f400440598402d034003800d410001036940e40004c07800e03039584ec002a01c1c1e1941404050203149072000c00341c50400036000449220b5625000a0f91440e84103190584a0042e1000118819070340400d880c020b841c9081075080540b404205204070034001e0707400c000d04070003060000860f58018001682c01c4107400404075411420b0070106000c1d004081c01c40080c441e03061880c48101d004c907007001c6404c4903045503600e00c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 905563183 1250 905561933 905561959
    0x60406061803030e0d17121b250b07090302010807020f06010b090102190b040c050916030e0f070f050301051501050708070312020307030f11090d0209060f03030307110f06070c110103061809060f0902 87
    0x100c031040d2700280c0700308501c210286078804508a119020710640950302d8040f03010341140005003400d02c0080116045502c4089440401c0402080807811588021105512043d900340140e050030511051500d41d8139681c0d24034018071204001c003a0180c0d01618506c1c40d8580c0342d809028a07400c00315424040a440146144900c5129500c004660003421050f100041c00c0d0f4886281001c9950f4094840c4900d050f0f014401c0707203070038840c00f0341140000c400d1807401c00000c0300281c0903005000014000b80404103048017814051203103200640c40d034100031550303854030380800740003081c1503203802c0720b21850034a00400c1c095002085803080b00004001c0303090700f241c40c0d003080b80741c060003000590440d030401c4007803800361002c0001d90300951540e121240c80c008080c0240d403401c500c9042801c1154403013007e10580c550030801c880744e155009550649031400d003a0051300a4410b030351049003601c40c510003903a90003595600907205e4502c034201c140b0542d402c1114200035a0014140a540f21314141222 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 905564433 1250 905563183 905563207
    0x102190503040c03120c03020105090102090a030209070207180204170d14070206040506030c0a0f0207030f020409031107141206060913230105060406061803030e0d17121b 75
    0x41c0d603010348280e4000300b1042d2070b07580d91083c08101040b404045500400041c0030190203008144c1d00181c21802103091000050005480f42010300c0080e014003410004161a03030320034841040a44203510b0766040c0010300c0846203001354090b00c540e00b0720904040b0740c28244040443c580c90a9403141e40d5040d901000740070003803601d5020f280205c0e80081d081200040c96140c44000c0e52140e2000101c480d00c410805002030014165007c0500454125800600c00111902048100141c060344d000825991501d000c5c2d50001e42d014486000e48a001000a01031082c18184905118240ca9a041a40424000c0f6644980654a0a51001222001444241040141400d0b06d40608040207036590441401c040c010320710f0706418026516441044030509060081000a248038035002050120049001c0310310074442c00010100b2560700d0380074481707a03940020f900103682c0041101801a292410b60050741d80f00001003103503042882e00080010315103001c0c444480842400080c9016a89194 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 905565683 1250 905564433 905564437
    0xc0c18190507090815011a032e03051902010306290a02071a0304230d0c05071502030d0b0405040f0b10030602030f0420030c09040519210201021905 65
    0x8100440710000380c8003e08100b8060004800c2c49450348950510100009203401182421001d110400134840c094a800b007c0c1c0110f44102c0340c03030003c851000760024a034907101c4cad84040d10610030580350241c0700748003040c011540c034801d072800c08c07640d80d6440120102c3d504030a10310000c01c640c050992601d60b030315001407894821510650f40c070700380c640a1210340910001c600301c03808000801080b04022144591250054220202c1003804101e20012036403110031054880030031400510043c20071000704100c0700900300c0120130b48292550080000c0d502d4008440020003682032060803407240c201403080c103008d036400160320030106465848a0f02d4205024019400c10b072907440000000c52100d10155004e03003015101c6040c14101420f1000c46c60051900c12046000c0f05080f03003a03556800079540c0302c101021b0b10100482d0340c2c1d505066082102c1e01c01320110711481c04502c0d404014040317a000604565801d003c402160602d00224201d006d1891204029003c000402c0400750107400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 905566933 1250 905565683 905565691
    0xe0c121e0304030b1003050c04020313020f130c2a030504260726060c090d031b050c0a060905030307060f0b130f060e09071710020c0c181905 62
    0x1107a242680e20390b01c403034601908440c03180406880daa8240100030082c80492501901283c00358118203010140d82c10114000300002c0c441d030440300103a0003903154140006a08820070104119003a8017500290580110480d21600d152004610703014200e0b540c04483c5080307030140e450a00f0b2500b0300e40c0490700c169901c0c03210318960344450b40200b81c0b418101302d80000381254007002c0c05598000e040c100f40c004007010324007a4940204082050500b80001a903103400011030303e2185000e03490900f035450302070150b075a158003c031000b64070042c03020004140d01500130a68a0054059591204403000d60450280d654150400c10041e00401d0300c6402c60081e01b200e203100054501d0500c0c0c000303111075403004000d0310f03c40c0c4c071900040c0a070103191141200604d074040c104895442e158060544950740c6000f800d056242c500d00c0680d5080d03003045882c0700c1c1c43c50b942045688006c4c4500e002c1c0d40e094081500c52140c51506040031850b02e4807000103004070002c1c0a4514200101c1d2081e1001d854010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 905568183 1250 905566933 905566993
    0xf03190305070203101823101a0303180f09040308060423040f06180f0602031f0914060609030a240f0f0506030703030c03030207030306180e0c12 64
    0x10a5121100603a20904484c1c450f4844100d0f802c030898034010454103a40c1c02001d030047c4030f42c281c03401014404245400c94400030400010325004402440200249081c9015018480451030a464480c03854420205074001c9885c041500b11040c10402c2d01d29084a004000403402c0c0045402c5080a400c000c03100000c9004855680207186160303c000d500072070f01074806841d05008102404458800c2500c26140c0114007250321035140c44880070f40489040c0181340681c00400214041c1208503001f030107104601d01c94030011b03550300003400982000366035400707400000008688a0300e0f000c1d04a5030b02100180150103d2145a105c0d0381c034484038510f8106200c086455840440754241c89405000244140001450347c010182c18080717075801003a0b14002e40c40450241b02003a0000a00300b2420350528003d6600e0450b0f1078110058561540b10090044d00c2c1031429816004036080401315545103000c8030558078002003000203078032071140003c2e41600f0403208114141d03455040400c04685e12 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 905569433 1250 905568183 905568193
    0x4020114090406031a04020a0e011a03220804090b10120e01110a0903050f060618220c030605071706040b180109090510020403030e0108060f1e0f03190305070203 71
    0x207441720210f5030b500910500d0240c1c0c4100c200402c52a04004540280580341d0850b0aa98100500c5118101c2011103003aa444c82c0400001c8039818420140c5030041c0582806904c4490b0603d03210307900e0780282c0218100e441c10510103141604084140d00c0b010341041c0d503040b01040c6450142d10080c100c002c044804c5548801d080608120224020040807030f44d0358a411440c1c0c0f5504201e4203080c0304d448001401c0c1c2041092001d03607900d0340040c18114800d9032054a05407100b4502e00d080800c0069154101103502c44114140042041450110303070043c001401076640d032040444011035001012045004100045212130038580d100d07112136040584121076986031000c02580d41d4800b44d02002c1c00644520304030301001b105000e45402040945400d50a140c10350790080c1540484103100750400401e4000948240e4841340e0304e07103c1100140c0843c203003504020002d010f00c05030716501030003440e1005400040e4103002401400c8100303901ca0326481c81c9482d5030200c806900c2005c041e40d140c0b1a0f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 905570683 1250 905569433 905569439
    0x210a12020901020c0d24110d0b0109120c0e07050c120309030f0409150b1204030f120905011b0c0f060207060204030503030c25020f0904030203040b2a0604020114090406 74
    0xc018109503407030b0042a0300310601024a039240903408910702c144800c20309000c440398041e00c0d46000c0d520070044008c404902801c148004031407220700c603401184140c002c04003100920113a407203070100b034410403507010625a50301076041da014401c101c040d4405500c88841464a00c0c00304015580101c03428081d01c0c03801c1a180842c3c2015007098000e120710a03079035441e40310050825402c0134010401100c03a14180305a107510700552a00040010301131040110300307091080c0c803501c05880d5080c0202c04c1001014140d0a02900030000102300c3c58119000040001030180030f01c640082e8254003002c40008180d0995614000c2e4029500c00c60300300703809004c0800041c3c0144051441a41042491907c500303130107010915048511840c41545043c9a107440056283c0e56201c680c000c509503041c00140e03c2d280f40c224514480e0f90304c2070300030900c04681d08481000721070114000c00c03e00800000344801880400b41c1340e910946000740030a03812102d51021700701002c042c0076a041b0007440000c1a6039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 905571933 1250 905570683 905570689
    0x151002060f090309060a09080606040b060301030f02030c0d0809010f08010f060315120b0702070b18011b02060415020618031c0209060406030506090f070801060c0204090212210a12020901020c 84
    0x66038000000c15511f45050080a03400c0151903803000049906201583c1d1450100d122480180006419543d81100c4102552010030012903000ca000e00411402d000c035041282c00b6170800c101c12800640494081e1400c40c1c42409110f0603119014802081146404025401030000c100040011086d0fa000044c041d40e25981c0036407054083c2403845a03130b00c6c10b40c9009007800d440f6003081485a0052040024013a01c5111890084100b270030400b0000c2c006c0e5406000c100c00090f4001d50010000901140364001d000042c00d40d4882c03602121560384503080c0b81c065025442d60300054550040c00b2110314261003c0703501c3d40004030400d00502d0400e1903030103c0d0140d8400e0f0092004261140e09202c80d07070400700003c036840000802c21030014181840010103000062240b0000c1261490781d0324203560b15540468040359008000b602000e40e1840312030b0f124219286c01c80d11000f0402d000130100303941402100d08031980355403551150301036105017000941246500904510802c111080d15807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 905573183 1250 905571933 905571937
    0x40b150d0804032a120f0204181410140406090f080c3d1d01020415020c010f1e030f0e0105040618020a0306110702030312151002060f09030906 63
    0x14081c000d9500c0f0f111304090b04505010f0402290614203203480c8041010b0384000800303c480641c85407250900e02c00ea40001800342001040c82003501a010b1403120070003103042004d40c1103203180010741c2c841078000124201203400d8014503000003514040083c0014900c0d6220610b180d100c0c48060305424030319150901786401100081900d42c0c0280620b00040d80360024140071200182c0e00c0c00614405240c102c19109104c0c1c3d006800e040d05c0784160b020212014140342420529030001b1034031540c1d5000600021403a00d0004400342c0603a5a5410555200b203800c0030101e8150f8441034401200d02d03c3d080012078800303145a040541d41d01c0c0750071030120b0901411100050001c0046034030b040a0030014101c41d548040c07a80044080c01407200107803a41c01c0c03017004407030700f004c40000c4003442070980c0515031080d408000d604d400002504110003500102403805070a0044940301000c0c01040cc1c0102c1c000900c1c0d500c00980e21400016080d40120300c000741d8895074120699040140d080301080140d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 905574433 1250 905573183 905573189
    0xe240c010c0305100302210c030d120c0305090307110d060e0a0201022506230309100608070e040b09072301260c0a0201060f090501031a040b150d0804 66
    0x25946030210551600c0e45405000d0b001000d94001040c02031540d40050407808198031354807400050007401107003900d0f06008540e2610000360540750061000c0500402e280d02012144010034074107690012050f100348100b030720810b400402149800015101e00340c01e45100703c510365001000484003400145940074400c1100404c6000f42010250303071001900f03001c00d01540c101c01075a44ca00c8201c0110007001c442c001c480c400e0400211141468110f00701030010b4080010300808008180a0b400c000024191859855001c0c20000d6540f6658402c2d1905864070031748000701d482d000846d021807200702c0d225400203001f000701c90b8210760f6000f070108140f4118811100986600710828125600b003840d011000c100540d204034500100e80710402164806000702e0303c41500400c64880d514003d50100014103003024107180351a50707504444001d00000d01048851443c010040406401e44401c8540100c0c3d00540d481042c1d40c803a10340100e05c09001105503070051710121000c0208000d00014005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 905575539 1106 905574433 905574457
    0x16032006060114070206030c0301210818010e030106090e0d030b100f0203120a1508030a08060603100b041706061203070813150c0b0c0a0e24 62
    0x1040c004e620000f0340042c0000b0a00600040e16009141256011030b220340b000c54045040458581644000405402d4180110700244080c0d0a0542140340b0600d07040881108890000c0d00b928401d910000e4580d554007003810201405005000382402036050604c181060000851101c00d2200c00040801c0060309103140018402d10481e00703614a0000c017400d003414240d40c0200100300c59852100800e0000e400082c607140d0100503280c0c08082520b403000f42e6034915060002a42c0005c024090110103d4000b058a120752805880075040c48420042075003001650786260542c040c200500c52002d0400d0907420f03000000c121406c0ca9404071625444500c0051407007995001c030340160340151074500c10341100591140207a01214000c4031f840380e080c0c8404902201324801c07010424001784204170200d045003072202040c990ae40300845920000507a0551391409600160340a540c = true := by decide +kernel

theorem cover : BRFrame.Cov 905395683 905575539 := by
  have h0 := BRFrame.cov_init 905395683
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 905395683 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 905395683 ≤ n) (h2 : n < 905575539) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
