-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:30:45.538518+00:00
-- url     : https://prove2.me/submissions/4bddf59b-2609-4b49-acc1-afde5d507125

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 904316546 ≤ n < 904496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 904317796 1250 904316546 904316549
    0xa060c110f070915060806010c14070303030501090b1f0503070207030c0303021b0402040b0a0c02030703021903111c022403280e060103080f0f04031109060406030b01150c06020301 79
    0xd05801415040111940900034980c13255034207640b48090a05140010380721902c041c2c10541040f0300101b00e102081840c40d0b68903081c40000080303581d8690340b4640140942002d00480349940d0403c0510042c81c00c0c26030f0a001d8283c40c190280d2070900140c00220340b1600020641400c61003004000400300794541009805180030341d024004030800c0d000318400200c10a20064056441003100308400c18101e025200754400e50301d0403548000d11400040d250155a400207540300c0781c02209107194101c07064001046074400d401a59140d4200d400700110101b81c14603144004d458607224400510300908128542e905012051000100b00c0085010b16081122804901e4107580c813840000419040c4802149812580500c40d007158112010340b14401884010034910380030070b00440c5c0c4105042940c0c5200006050b9a0b203c564a00b4116102000105140d02a551140114159080c00c4c040c80ac10b40b500014400c22591a0403091740300c0741c14405007031f010480c4140d00f8100003002400210b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 904319046 1250 904317796 904317823
    0x109050d080f030a020a020d0206010303050307030c11010f0902090708010b0706091a040503040603060807080304030803090703080d05041509050c011b020402120105030c03070f140111010c09090b10020a060c11 92
    0x180c1b940d85c482e00203840c00710490454820341d40068010000644e102d002c0b01d50100700382c6408502d145c8014410341e6200080744090301c40c3e5081001c00d43d40d08401382c0c48507481600850710290aa11420426150100d0a006000030400e04000000100718103400140c00c03588907940303400d200b07044080000c90040e0107a80440751a0000101040002e0303040c018140a40382d12030140071410b00d800880d41d600c0c4602d1000600d60700c000b00000e048450280704600c0110340140303e0301c0d500c0d441d400c450f4000300811541120b1403082c02c002004510103d01c20001da55901000800c1c0403200400192030410f501a07520790030352298180070005031204d00203840d43d9002055520210750402041500300055820414007070780c0020030070050b02030311200185c200c41000b40d0000384c00c40f600004850521071341c40110655820b0513100904554046078040c100c444585080101060300c00030881481d56036038410300164068100a0081102c4d0352001071500c01034104150400b10342041c00341042e02e10001c2e007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 904320296 1250 904319046 904319051
    0x40b06090105060a081302010e10050406080a020a051c060f0e220506040609030504050612060307080d09061b020a0b03180d0804080309251d060109050d080f030a 71
    0x40080c0c1450003029000d0441218101d04000a90100400020008000c80000329014580744103590240071458030510010f4070064400c5c0030208040e08942c054030521001582580008010140c40c1c400c0d59100c4040d41e4510307181c5842d940c80d41a481c41140700080b40b09030b07184400100c004805000300003e00c4241e141d4045071030b00c84809000b1a90030701e5031002c0d00d61a005100006500429480d504c80e60090340024190303102c0c1000c40c3c40d0f00403a00480c2d04900000b40c90030124081100703103489124100d04440304140c0b6540c2c0e0903155507040480001245444109101e010300034142c810745800203a0a0300640c1a0940001d00603101e03590011401c110004140300c804000c1d46241441421150001c10b04050680c0c03005050680c020700103400c044c008004680150403c1c46403c054040040e001202e01c0202030b0070312071110080c801d105000c00130300440c5050f00d9041d48501c1c40340c241611103410f118a00002e00424125180d01203501c81e40401c40c2442c825a03201c05180220310700d4000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 904321546 1250 904320296 904320301
    0x6090606110703032001020903030d0b04153f110109090219081e070206060f030a050303060d05120d140112020f01030c0c0b0f0709170d1d03010203040b 67
    0x6442040a0501980607402c01e640520109421800d007400c2000c640681d846801164401c441c02070084c0b0b288150706000000f01910001e07a1a003102d81d108408a400b08062010b41c0b1154449400740d10034074031400131441c1d040d056841405070347c018486824180c3c0b440506181d400f20303000211002d00702d90840c3d0010320a00139581c4800070001402184204504d001f1924140240220070300c81c0b0389007002020390004d0f40c01d0030542075189002c600c240381d603883c0c6e052a04020b0344a9604640841c01101074440306003c0c0d00c0c00048110041e60010301640c40c0d515400240041d003510031105407003520865911001c01a040e82c020039114003a400c00250013070101f10300b5039010406a101d0001e02004822640250382c54044c201e004038002d00f40010b440003040d0341915003003a08540a080d50327208600304039206e03210900340c43c0300702141ea550340e03841520f03196010100c89a07078070840c102d5440403409051941c010000301c16456441d04241004606000c0007900f03a038021074007200c11007072000a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 904322796 1250 904321546 904321559
    0x9010c0905060315040c0e2e050909060405090a141f060537080703020f191208040b0a030905100b030318040e01181103070f0b0703030f060906 63
    0x11500a05400c80700e0300d00d0f504007500c00c00c00011440385000d128913620b403507000070f203800b030001080c510b00040d143e000c03e2500b10010000c10060741040c0081036129a44440902d88540110703901d440004010075659120368082c4002000c00030981800c6118103c0301002040301c0a10000701154441e008201800e1050f0040441c01d16480521207200e0a20005100c00c0d40c40450302c25030503502d80b4444441015804481000240107000015038080d1807601140490f0046036150a8078002e0b1800314020b900742041c4448080140190440404070210a00c0365201c00c5284118a40c01182660b08180d1034251280980e130106458802283da0b6904000070071405128010401c0703043c1404002c0180b11801290304d92041c1d447c40d821211645a8100203980c840c0e21000b84906800001c002060042c500340c00d2900c50180181d64400348010741107c1c5c2e1800266500070389000c03d0344032980d03a24100d640342c142d8006d0b407011070601d41c0311056401211518454071006082030300000c15100d14005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 904324046 1250 904322796 904322807
    0x1409130908040f061b0b190606020106031a040804030b0a0902130c02060928020a0f06081f030804090903031b18230105070c030606180b0f0d0311011409010c 69
    0x38410818410a02c601d81000700c88038600800f006c0d00300b2100030315682c0c3d4142c19401c034442d003580c00542a19003280402c81c40e074158000001c0d42c1c4901d44140d129001c000c20740c106034004079030041120700f08000500000d05050013107600a85012008039040078a40d00240c03e01c002801a40c0c20555100001400c3c154100225500818644040c0c00c1d0b1207980310080110750302040810840403810f1410608640341c50650500a004d602c40f222200c03500e404000303100c0318054030340404c480c500d020850761b410110350400c000c99501103541741c03411f4502246000644092042941810b554031647c0c58100303640c5801c0815111a56110032003404103400001120303010350884e0540310044101c0c2c110f01740a140050316580b00c00d03b00340384c0f00c0556142002d0030b034035039410003000c0e141400000203e0401402c3e10b0b41c80d0401140b4140034001000052040303104031110301c1c544c032405416000e00841c0c019480360709043c01c0740001154a10700c09078020b114010565a076060f680d516804d40e40195800b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 904325296 1250 904324046 904324049
    0x160611090a090b0a0e100905090706091d0103060504030309120e1f0e0f040e030f0c0c010809060703091e14060f010b070803151e031204061409130908040f 68
    0x460307041000031820400300ba40d41081d4011241c840782a100400c412201414003400188140c2c1824015440e00c042c00c56210106031150a0229a1443c804500107608592503041f16000030290140eda285d9227440e8040c10000c0c10a6040c144d507000300e100800c04882c2001030100340c2d40c0794058003011003024000e8190102002000c0c1c0301803141040b428682c02641040142c2040b140c0d50b07101810000013034001d00310040149030710f1200042040300820603601405c2103904d013200b80d074650070210740150342010088541da46250002c0c00090010f5001c0e0b4048240c481c000e084e241500900c4880c645106da01007070041c5d9424200ca0411030b5001c408000b0240d0000e0380f4504e001c419450007000d65001d0068880c02069010040001512122202401003815500070450194102c0b42103200c41d1181c40c5404450203401041001c051604c0008102c070b007142c120b035484441030385480c40000010f070043c440c03039544219000020200240710740a12458203010710655a034980c0380180800009189 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 904326546 1250 904325296 904325309
    0x30807090f0510030b1201180c05010305010303050f0a02100c230708030f070e0d0c090c020105060609040b060f0304031e0206010b07141905160803030417160611090a 73
    0x107a4006100b2912540754043c0000450b04020580d00c03c400000703120300303d903501e14019644c60809100041e019940841000c1801000124511034842c0011000e030f0724240806000300340700f00103440c0303091041001002100a07510542c0c40c02c0c0207405034030054415682e046e0001800e10180c081c0a40c6450038814000344010044920b01107055990f50f5903070000030b0030358000c201180f0003c0c100034010b880d650039000700104158003c0c50701c0c1c5001c44c0d0680140c00303859200c911f481480340143d801481540e000d014010459030a003003015042002a1603042c0640d40c12000900642d0074107100800654046d40c07090311a40f6024030160410341c54000007807407240844d40900010002100b969089508458002d98620005170350003581c640780a60088411080d00110b0a0030001c1c098040307581c10900b0205c080720031086aa40e0002c0c2d90b68003041e500901070401c0451545440003050303008224582c0b00100b4503425540079207520088904441c0794030244200014440c0d01480c0c4420f026000c2e069 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 904327796 1250 904326546 904326569
    0x13080705011d0a1e0b0301030605180109050c0f060d06090b040b180705030a021204061515140c0106051f080a0228031e0204331d0d03080709 62
    0x19041d0003d0792400a0340710b200f00844202c03200c034650b14990716012010300340003011550740b5650b81c40c2890050034116422003034003030304215007000c900e010b000320b0740895040303401040181e0204040080845050300c015a00100810400350f0304c440b2401440c001b407803030070400190820f000e0300f801b0644103480c45aa10442c01c202444880040e99400b5a070844030030b142542d100d07925580c24100a1085180d242d8036003a8140c1040108411034002c2106024400110340d8129031b600b0740ba55408220321811004a00012110b901d000c44000203490407035084000450543ea44802050304001ea040141103203800808680c7c41141c2c2190400c4c1e00615284c200310715101e000103180c20b0604600307000c01540303292040144482c511903044441051080e0840080c0c1030b0000824000a5000d44580708290030b850010700e8100d008070442154481e09800d204099030203040f804c0324031082c105c441b8244c84250341042c1400f80c440e11080a40d0031b12a4940010b2400d0005000d090007159501c614468074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 904329046 1250 904327796 904327847
    0x21905060610031b14040b04030f021e06160809181f060c06090f080318010b0409030f0810081002030a1d0705010302070515040c0e070513030b04081308070501 70
    0x210b14070740604010405141007010752080840d174004a2041d07511182c5a00d0700840c004c03052103190501001228800c55520510480e5020072840442c0d0341c0d490700d80d014030180403078220140c22040c0c5046e2580b03c1c0311180c0c40c280c050000035442e0000003034043c0b000d1110204000c4012000410440d404179003da001c160180b42144c000d001d503000f454020030903078079001c8203002c1110140c10000380951058145031070703142103502031070040340e2181605c0c01e56091004601250138a8400c1030b040640598510122050f8040141c600b180058000a0090045000054060410300c2880701800c040e420250b0783341840c5a44005950300110810ba41e0003501032814036061000400c1c2003150428200561101e02504016040956444946980d120303047c00300020003808070390380d0064485101d8201a0394960103811a014010f900d401074103e0200042030011800b03c1850a6000f4410502c551800462003c842005001c0b0340c0854000c0e809018140070070368000e1340602e402c0c0c940f85160b00800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 904330296 1250 904329046 904329071
    0x1605070b01090603140f0c0d060212010b0d06090207051506060d090503070218060d0314040b03010f080105090d050d050c0903012c0f07030b180d0f0e120a0308060102190506061003 79
    0x13001301c407c106100340c4030082440104501e603019110100e500036400c42d400d6a4031154103d040d4001c44603030b1102d40c9400300102d02c0480c0f902c2543c03660f54004004010306034180141c0581000007611442c0d01c0001440f03c0781d0405018080d41d4007081c86400a541c07180310301c0c4180020f005209074070784422500c1c103041101544440e21011800c0c7d4051500c15186035174481442801e02c100c1c1c00000304100c00000104a641c100d0603418125100d00000f08941d550b070640c601c2c1c42d2140101007030300168003041072070740c3c4110f580c002d02c0c5c0202015003814030380340300c0c1d50021782121550102d082603040040341650b1141000004042d02ea0700d40b1002d40030101c4105c1c00241c441ca10b40c04010710100800002c5440f00200c00100912403400500b1110b81d000440c070050800c0000c1d03000701000800e08a0507861302d0801008070001e48002070010701020150b942c042c0e5284000824460461041c84140c0441e4420404221611070150010300381c203080c848207010704050204072150501d0b0820700260402c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 904331546 1250 904330296 904330303
    0xf0e150906010c0c0f080a02091006141309140f060f030a020103021303050d1e031a0d03020c090a14011a0304030810050d06050a0c171605070b01090603140f 69
    0x1c1092900c40c420f07400a207840500c4980720b802009401e01c124001044c0610009401600c4031b000b116040700395034460b041051408018083c180001d8042003a101442c0103850240c56111482b4190a030b4442d112080c0e10100c503809007035060154003840602c40010340303e8400c00e401c1001907401c054008103000c0401d03038501c5420002810907074001000c401d480c0c3e00786a144003a65115040d207400303044c0000c000782100429100358801005c0702c9100c01105000f0712134800107101204c81e07868061000410801420b8001074140c0c250301540c00810010f0383c800700e40620900700c1c0c020004071483c80511203414010160800c800308603e4005540c81038030302c88107490348035605282c06907480d0b581c00c051401c12912644215000204103189100b0082241c0005105000102e400c0140103094101200c1008511080c0105100241e0108950f0030441030b405010054908015242c00359039620a0420031007640724591640d5128414410048007180105c20120018020840e02c10029090782c1c0707 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 904332796 1250 904331546 904331551
    0x50a1709061b070206041d0a0510120305090405012301050403021e06120f070e0f0901140f12010c0224060d061b0c05120408030d050c130f0e1509 64
    0x14a240041004882d500a000c881400d0360244c071840d213035980c50041e03654101103c504404034102600008003405494403895200b44610b10b4003403580c070318028021140f030f440007005408001080014102540300d9001707041c000c02100c1c0004803d0240302000407445602200801c1c10041c08210400242e540c030300b81146102c2c0103900107070a0030700c84000200d20f4801d000380450b945002e00e08004000e00c034000124403074291602e03107245c175200c142c080107500c0e881e6a840c0340c0e110448000520410720181305a01012070064a2604400c1e04400043c40c507140350001e25821340c0d1a0544c00c40b4542d4180400e002c000740b0f0600140d10385410801c0b1040d840b4000b0841401402811607880078005940c10565042c1d0118007110303c070085100c402894172140319815100b07803080c0182018412004070884045032032020280d410442d546160101908003d4104030b040380c018014800c0041d9410b00042c000d29039064421202860070409a820300303001009000e5000369a416581e0617103c2c48001d66 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 904334046 1250 904332796 904332811
    0x180d1121070308130e010b0409060f082a0d23013804020705060709050916320315030d12090f06150e0f060a060c0302011b050a170906 59
    0x4d895405403000d05404c15001c2d800851032117100c1d00001080540c210080050f90000882030149545030030324541540c000c1d11580301a5841491480070340800e000401c0c061007413480030a20708c140c60b6000505146800001581c240c2620030360071009401410750514146001c40080c41905090082000e581c402d213803400200e15004246075014161440e010f07007030b10b00c0c000d004640710841da04119070b440c0d208072001004201003020100381841c2c014000d0380301d9010f20352002041120307024200c2c0d449805900d4102d03c90358441035806212f010f6214019070040089401c0c4e03c900c0c11031121003610a80b0143e1070300035003002e030400b40e00315800311495071041c0c100e03a00880c038124103290600007044041c3c005440b080c80c005147c1da0a0500702d40c00710856006100c1030180e51103941c182c1c0e203642402d03122598001d00003141080f540b07005400c0d01100038002d00001031a1a01e1080300c02282c0306d000400000510001041005290004092008506282d06044a510f410040940e50b44401b510342c6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 904335296 1250 904334046 904334063
    0x1f06030305041703040816030311010b06030606070218090c100903150c020a050f01050718050f15070506041b060c0c05150717030a051303080408180d11210703 70
    0x8002403902007041703600401006040f1100307039020000d40502c482c1140000c0b00010303806118000c45050500515000000040001c0e1850f294075080010640c01120304a0f0030001e020680390b41501021807440c402c0102c0c0010b040c401c1403a104000003260514000018003910940034800300c7c5450701400e00520b060300000803404c4c4030394807e03446e20118400081c62441120f01c81e641540b030640201c1e01a40141d1607000308842c4c94030b0b851001104c54055130350414101c80e400c40d013505d8003020560002c2222a0a82d2034800551142803d20f0000c0b5400c1d940c11569070310101e107101c0b003140700303100411881c0342403600b034a0159180b18080c8614464580304040101c0462039801030501143c025640c001c81c0d81c2ea4005807a005c2d19440d420844103030307204515000019650441050b2240c20f101e034540d458200642d00c1d541d540d1400d82203082c086041c0704401803a080652611100010f07080e00404180074001210420000b03980c0281c55000c0000324800100440711030001901c200303a9a208001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 904336546 1250 904335296 904335329
    0xd11040507110d0906030501050301020412110612010909050625030903110706170105041529040902031b04050a0303050c03130f0f0902041d0a060510021f0603030504 73
    0xc4500c0c000b075862070100c0e0b02a103500c61401d81e421070500070480c0c403261000c0c00647c1c0da030400c01d403c0340181d2140312404040800c0ca0000540d40c124032104009000308128186002c0e80c5021125800982103c02e0481d078a14031030040c480100700c007550021040b5074114004001e840705280703020803a00701200f03154448550104050103a50800b908191003421100400c0d51504000d05240304000c0883d0700b8010300300041614180b41c094103d0442854140b03900f03041c90158005221f807900715980b000300b070000c1c5182407401d40d030000400040003890000340e100d04052140e00c910203034085234200341c11820001008943c8bd646021000c4907010300342162610b0809100908600c074483d1400c804241d01d28002c5550002034108505540c16005c20748052a141c01014003280700c0c0e03016090310411003a40070b428601001c89640d52140c1c0201000c641c00341c0e075802261039000c0410501c00543c0014908212081004060401141e1013810504c5041d00e1510b010b031440c03044c0d000e0111809040b40d00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 904337796 1250 904336546 904336561
    0x112120201110a020a02150a050f0f0c120406021b030607051c050403020607110d08131115030601030f021608090307150804060c08070e0f010903080f090f0d110405 72
    0x44035848651101d48070340e9034910440d00035200e02c1c1c40324081f8400d800720400517401900143c00d0b91502411034680c2894000301d020100304a0304000f2800e21410810020700b024503a040c07000180d2226030319030041e00c403804c0c858081d040a5518001401d064610214041690342c00214103800c041e090034481e681d0b200720300f042c6a00c40d07c4240060002400c00c400e0004169000a40b0b40c4240c2031555900880426030702d0840e1078104907042180003900d030001003005124080c08a800301842407184404440c40da9010070b4070025000140004110f010040110f0303960903000c3d4840c5513809174001c40c40c085010900414448150740040d160400104000700191070070484100a000c84545100500850080c0182084412202140c0050805c4a400b00141c06842c0550140700c1544070b040c0c000303101c4000d008028000348401030400c5990138002010428401c010090f26200c01200c954414115061110b05440050f100d801900040c0401c0c0100300340030001c202c03130002200d01280c103440c1c0d01c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 904339046 1250 904337796 904337801
    0x15021e090a0605130b0c0c04060e0403050403200301050a0b01030b01180b0f090904080c1006051f0207151e02070602030a080a02130801020d0f0c0f0c0519080c060f0112120201 77
    0xf0040155528001b40c03031402c2c0310380040e00c0c040c2c6000c111028400f440d05d401e907003045480e06450040100b40c00340310600004e14001120540d94008201000580175004c00290a40f40140c80c4809200c0e034941403a4202d59040c011885040001e09000b00310840c890b01e81c8110303270f1413072040001150b40401c4001c103e840203011a89101300091001c3c50780d081904001241c3c1e440010002414850390400c1814503580740a079100320b0300010f004121400500f0601ca0044404202c203030210301038024082a0110342004040501000ba40c654070044082d90451910b50401000d560955011075801c1020540c00001c8610343c01592030407130259201c90306024043d008a007603101a040500b000070074101015405801d0b103985e0705205005041081c203c40003202d072110481400200d0140c01400c0310750050f00d054100318401c0080300c1800301c80c20441c0c6803c3c0b030b1282088030801c200042914421008020840c0c010115566000541d45410700c510500c09619000800322401064921250360003036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 904340296 1250 904339046 904339049
    0x15020d03200f0301090f090b01050f040e070807030b0604050c030c070f0b04032a0c0b070f0c0b070c0618060e2d04060f181815021e090a060513 63
    0x110761294a0359a41c40381140e0b0394000340540452140b8151030450420300078004e2400c3c007600801c5020b0680d00b01001c0c4a81d10146c00c1c901c0307800540301c02c20003d43d40c40400c086001001c41002400c441070540c580602404005460640718500741700c02c0c00031801080048941107000d64110365926519403916103550f441c2c841c005844190800c04000030302da0015501498101c002468107407400c096100020210759144019041d81c0720301c0310910014000200421110303001b00385002d000f1070b4503a2240c0c3d114000e90000c400145003c59010200500c500c50745025101500744600307102500703040b4080034102442040101725900040f0840750701c0c0c81c0d02010034070f2036540960607880c0100310300e2550300561030f040c40d025500e002800241d141660310380005507003072581400d07412407903110014042d04000c88a2484c80d035505610000151000c5242d07c00c02c030241e4170140e01d4249400311559000d001c000b44180c2d06030b041082d16039640d20341000c1c000380c414904241d510f501049c0740002104445 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 904341546 1250 904340296 904340351
    0xb0a05040c141207260f100302030f0a12230310150206091605060319020f0720100e090408300105040b0901030816060f020307020715020d03 62
    0x70b1141c0010030f800f20080c410782142d2a0001d806554400404640b145406150004002c4501052034180c0d05c9641c01e40102450103c12401c0703403241c00280c01c16004008400c1240d1141c44000100301402542034045c1b00b007401c0c41c0264005101c4203601a804429813020a080000700044102101901c00c40141010b030042e4100c04001c02c501a6490809484c074811138031600c9441c28004420941903410740b60043c04260943d2181020f0204224582c62048007440c0c09201c100c0c5695151310180c40750078050031100e940744024113544e88252010804c100d0280325103411220100d600007540c4206000c09840c1c80c0015134660902d19100e00039a203080d000203c9409251120803c9100c60741406400071500440c0c2d641c0e96401c01044400b0403150b540c0105a840040000c1020703480905540241e05400100940c0d15648072011148404551043c0d0340d03000c03082c84070055040108901030442c3d15071100140303988460181d9140f02d0301104000f090344aa00c002000d860011401d010102c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 904342796 1250 904341546 904341587
    0x50c070c0303170c0f091c1407030605090111120402030a0501060611060f090a3009180606020c06090406030f0503030930090402070f150f0b0a05040c 66
    0xc59240050501050301c241c10003022599001c20503a01002007241c0181721021202454035080d0024020303009a40362041e0341c41f00c0c61040f240d002c96000040e0700c0940039044003802c403c60271440c0c803000f01c075030140800056038944105c0b82002500042150040180042205032550f91072000030300c0c0084640c0000c0c065400c003540080c4481d0008140d1043c0c0c40d20b4410307506903585030540b5418582085a03140c00750381c080002c14010030104002000d0410f41000c0242190100a80d10742c0100d4455680f14005010504108029003041ca2440b100b500882e4040c0000d6141400c002d540d01002e020040c0714400026100040303549643c400e070004d6078071503450031000059003045a141c4d0002ca5146405004043c0c3c8450101307000c40003659040500c1c1c0000c04842420703400d2842c1604803d001982003542046084041341403088003007400b511a024a000c15980c0c810020f054440780e074110f0b04618200518031001d981c03840d0507802540c105803030014008415105c1281c00c0f905480c41700d04d040310f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 904344046 1250 904342796 904342799
    0x20a06020f1e04140414040335010f0806042d061d070609082104081b010e0409080304060b01140d1b05030603030a0e0a05041a040b1207030303050c070c 67
    0x90b8000c002d0403c6901002c0821000c1e0740002c20b11042d1160f11000080300b0054800160000b03010b2100301003240d070040044031803004a000c3e50244e40e444088441d95285948004221101c0c004c602301c03024101d00d40142400f03007041e070740b5031030f00142b070000c0300780440045419892168200c0140701c40700c0741c21038024401000c3d0b070002142d2040c0c45e18651450790155410100c1c080d03005455a03000c507101c0d00010517809038070040c07200107041c82c141728100603541080005024201000516102c201b0592401c101d8620319002400100b2036419040c00741d4101850324010407542c105407036000d030300410080307a07082000c5c1c01243d442c01a9400030842c54004915101e00724115031020030792001c40b500340c0542c544151000d07100c500048902a505500030803108032402e01c10320400c2140a80a07001da42c42503141c5000405840040d16481304450f002184e10304540360900451040b4802560b40250754542c81c03181a8031740c120340c08058149921400802c0c403030410308040302d00030780c0c12001215015 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 904345296 1250 904344046 904344097
    0x21110d050c04023c0a120f0504050d17090d051315110d020613080a140c0d03140610080c0f07141506010f0e030a0501090605060916020a06020f 63
    0x7031800e00c0084c01e401c02d05024800c3c80c1090b48007909001d08103e404500380042c010301190b00342c200510080089441d00c1c00354251425500910f8003991043d0040c0400303841d0184000c0400101000200268807040c00b803000300e0401240c01c209100031454100d507a050006809240c0c00880d030311440301c3e441803c040e0040ca44d44400c25052a41446c0107a810396000194120781d00c130340540d0041042c6448030440c1c0001400d84000f8900c160503800e1030b00c924a000010074023507420000d4911540d401c006055410698907204802e03003280100600e800500344940803400c503008071101c0c07100b40000000840c030888002000d440f03000e010900382c1307942c5803143e14160000307088606540d409442400745031070220904901e00f91180206070341d05c01c0340e4042d0b14800c8501820100016806000c0e000c500c0020407000c0c00340001c1540580320119086c1027100500000603402000340072219481a25080318550119a20301041d402c2040541c803140004011603040c81890301011121514003a8010715 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 904346546 1250 904345296 904345327
    0x15060e060d11030709060f2105191a01020106080604080702040903020304181a01030c140a050c060903070b090a0c06120b10020601140a080a080c010213030c21110d050c0402 76
    0x2e41b00b0551b03c0f04007080e001e40c0c050316603402d80e5400f003580580345840d0ba40c0c450070700da11155001121084807070026440e904240201c68002980c2210601005000600c550b0240100c20050603c8402802c062400c0d8450074098002d00fa40248a00d464034030f0201410300c00c205a8003c0c100113486d0001c2000c0c81000080100030040310350450600201c2c1212942d8000d00c600c500c0c641490711852202e8080501451380795020640d440140078082c0310503031081c00c00700915445440320340d0045607105454103086480000040070074075554440c03c80940080c0700603048100b100e0841c203005c0f01d40f061036050f4001408190310304c030340c0044001c60b034603843e55400510300b0b040758841c05401040407804010b12210007410f02419100d603004068801c00655250000c2000c40038500006040c890116001d0220092a0740141c541c0704c0d902c04203008c04910b0b818400e035140f0f10301180c4403102c04541d07122108055200f080c0c5100c0c58000c01100c1c02e20205201242880c0740c000c10840d80c819400d03e54041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 904347796 1250 904346546 904346549
    0x507170415050313030c080d0f0f0f0c170703090f0501090b0106081e040812040812010e0f010306090c08070f0807080f03070b0c1e03040615060e060d11030709 70
    0x1288940c40d01c1d110707100b4014412039004030110103145103d216291001d8030350038088079080301c922900700f024054850151240814034580002c01040380840000c115040c0d403084816149810301d030401c40308030749070407a085800134203001c031201c1d00ea540c881100354000c003980c0740301608070800d4840c8882040fa040d40a810f0b005c0c410100010302d643c944034101d504100071540f1141a454031140c02c40c80075180340c1110f901c184600c122070f00c0c0956035082117030104410f8404545e090800b15084c00900058040380c6d0143c05406d1060490b4901207044108100040c80041c1440b035846100d02c05102e5180141e90203070100314106c80301960356500301c03800c40c0124451101c0900401c2404200c01c40045000d1941c60203000c000d6082c46002d403104404104040c0130040c040320200248415580d1803020700c3c000d1490700040300d440740740c40d0a00f0005d590150034141ea040b42c0242c0c081c00521740281000600004c203560550b01c40d045021224020007003201114803540e800f02c00c00c400103510415060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 904349046 1250 904347796 904347809
    0xe030307050c0d09050105040501140c0a1415042409060e032104020a0b2b0c0318170a2a03140a050d0f0605091e06030307020303070602070305071704 66
    0x140f07442c00300c0300e045036082654082c2c140001d0b403c010400132980308446c20000f44000c40f80ca9890302c80e00001d554507001c8000c908545034041410000b100600074010803160106100850409103002e0340d481034248112070340c00444a02144510548e8070107a07226113882c940c05002003050508440c501035907a08498005c2c50181c962032064408018092110b50080b41e01034110384815040c0307a003006060b002483e407540d062111001901c4603c07203101c03c100e418800d10100090054030038070010305403071104200e102005001c43d51240003a0701283c0b5002c603401001d152a4481c24180c500f11155a40b00c0140320254000481d424a1580301540c80c8030940d20a848503c1d64072188505441180510a585004030300188030350041c8506c950040380c06a035411900040c000d0b1280700055480c4400d075003545001810924000545540174440340c0c01080860046080585a60009a491040140c0200140e402090240401d03010b43c0541e226564130540b048544120599101c0b0b01e50410710551 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 904350296 1250 904349046 904349053
    0xa3e0406080106080c090a0b0d060e0610080c010c080d060f0e06040c120b01020309130e10020f042606250503070806010503040539100509090a0e030307050c 69
    0x51000051041104543c1d400c8081c00b03144c421701007005900e0308000d00401065441c0c01410000b80e03203d03441480a14400e0394000751200d50034060b945490030003481e03908042c1e00034100b4403040c40b0006078407028150910384010000d01601d440c0d040e03402002418203015040000204840700ca00c0b01c100141c40002040e00f00c04c2d981c01d0704000036910071401900115002e1020441511001e03000708464080600450307161802c568080707072050301072005a44d4400e076640192004500c0901c41343d409841540f400390306004803010043c580b882035219451050960380b03501120340480c10340b0f11014001030030590300e141ca40089814140e0700014608600444008828102d01d801181070364000c15942c4c0d680201642d4080054170643c0c409001a1410b2013040c499604110341020b02c005811110f24015415462848401c1d41e00504540750511500c0c40342d540300b200b10761040603500c0703922007200d00b0803d5440b078050150040c0141c50802e02c01d0700000081050282e0494010281141100b048 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 904351546 1250 904350296 904350299
    0xc040501120603020603060d060e0a08031602070621091401051b19030b0609040c0e010e030303041e03110f0703020109051008011707170a0317090a3e0406 68
    0x40a080b42d2450000943c0300406002240940c10040c03040e10441d48074000004182031400001d62170b0070303140c4200b120a5100003013000001d851114010701400e0f110700080141508241000d042d03d68540d0400100d803000300807040c0d12070455000400700540101e66400860000b4100714040c2004079031074060300c0343d00381c191a80700081c04111540402000801592640099001c402404a40c40183c8c0c0c080418011030f10b580c3d8541c41440040c06240c0c40304528942c51030005000b01550300201d5110390000c0c01080049108503010314020021851082903141f100c0c0340c242c41a40d040ba040900a203c0e0510410b141c14001a56800b0b4078000d032560740b41241d4900420000030b1816a106001440480041111081e502382c0c0e105032029620640c0c14075500d82c0414600042e07040000c4400d075200044207402d05400c284030300c829a50044e000c0055141080d8110768540c1007000080401400410340040b0f01110502c508002e10030020000d50325007820400612000004401d0b0300c100d103010340 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 904352796 1250 904351546 904351577
    0x4150e010504061d0d1a0601080702010c1b020111150609161d0105041806170705031c02150a051e06010c080f04050402030c07050f010c0504050d0512030c040501 71
    0x665040f02c41d10340d603101c8854680d000d03112105003c0580c2a412108903001d8000003009000900021100e4000d10412031070a13000041410001400c80740959140c1a4000046503006400c19036060f0114200100c4800520049601d103601e000406068019140e120204804201c2d03028000e000855103c2e4107078a50212000e945140c0040303440116800b550428881d00848090241c50300d8141402d82c00d00b5940c07405411068112000c080301d8a59815090001680001d480100d41c06542d000300503084c02c1c1800300c0c0d0340f40b90b10840c01c961041412032040c4118400c110b41c004955504200c041c8906007012001c014043c140e80e00903844080300111505e40301241d000c1841400141d444840f204080d480c3e8000581c00b042d080b5540a0040202040d40c1d00d4a000460240074550415a6594164101f0714207155a10180724520323414030300920103141d404400d035410349508640c2d4000000c8245850380c54400c0c01c54142e1a2540048200005401c403a00504102ca6003030301c9030312700b5160032076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 904354046 1250 904352796 904352807
    0x21005010815041509050304090e0105010b04030530120601021921020102091017091b0f01020a02120715170a1e0f0204090c05070210121104150e01 65
    0xb00c015008080000040c0c00300d200500400004a0764050014850180d03403610750071030303200317400568010751250302c5c1d0314920100344110bc0c01440f82003541402c0608651b1174079103c00109052464030419009806146290001c2611140094800f00740d0340e2455081c0d0b9985100086603c1405030041003a0165188203071005841050707030040000c1491000742c450442582c1c034204051085640c24042d96482d91a404001e0303000681640f609400c1e03845030704810841210050024030175030403605440510548941184052034400c56281720b113910b0800040f1318050510b84043c1d40324840041a04032100c01242c1a0182c0b0b05100c4820308031090490140d07240900000110084007480303001130720f00c2249a000e811178050102c0d1400d03990f40303608445400c0d9401546e640c42e0456000808120300145803041420803c0c550504a0403c40681c001031401500a540d1005229194000c83c404000c994410907901c054500c040c2d48032078580c00481c1c0c050054002e0341000c2400708011030740c103600a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 904355296 1250 904354046 904354063
    0x30b0601120c1e0e04020705031216080403050906122503090506010314150a06060e0a14090a110d0e07050a0503030f0d061503090b1605070816080a0210050108 70
    0xf500d4503074410325010201c500300b400c20001e1908120080c01c01041940c0c0e00e000800c0014007540c01903407035501441d81071011150280501d64400740c084160725440d03070403540c50345d4880d4060400c55201e2100d0b4001c00c1d840d00c1616414020b910001040002d0001442521360070704032000072031a00303407140060a6080b50261a8080c1190b03100100410009620511803841d2503001c20a40301500381d500710306994401c0549066410301d803907000900c10039900c2005954070729812a004260f540c42c0005800d400750640c4022405003d01900285031100715030040c4c2900e8000f007402c0fa035a0b02130343d4be262004201d111544071381e80c020248001080e10308402d5240903070b0340040245141c1240260a800032350b01a0301901602500e4020000d25005070103808070780240c05403000311307001e545403400440c46200201f40c1c0500884107554509003903486029101daaa80c001e49941e80d07006440d0b0b21140081000c0360080c4064000905a01160b0b0b000c203900780540dd4094080c80b0b0303030740c960f0300301a19510784 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 904356546 1250 904355296 904355321
    0xd29070516080d091a070809030703051911030c0a020f0409050d0c0510142e0504090201030938010803030601050306010e0d080a020709020906120402060d06030b060112 74
    0x14140701c9004100c6410041c2440100c000c0002103006640e036031011140803018a020300500300c10104062203410000703882d0300046010195240c203006a0b00502280292403694040040394608070300018043c80401c01c1010301d64048075110314030a100b80d80e95140b40d100c100e004480c0350b00210074a050a0181207250f55208000c1c004080c90040215005e081c080c00c199818818034055200b1000e03184203c0c449180d802c0180003092402101500341074001144076450000c6412403c40f581c200a11190142c2c0c004503404210600b403070004a014015000010705800c0402c0d0700140c21f2044461100c001c200100c1210031591910941d01c000702c00240700c0c02c41e2036001000040d00f2907115000540c2d20035414100400420b810601150f404130001001710b681c600005100034906404000e502c001749000f08042d85400062000702d0014040c42e407040c11050780090200d004c642e901d409484120b03a00040800419940b4144015503c00c00e030781d030601117154010f400445c0d01d09401102c1e0b03403910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 904357796 1250 904356546 904356577
    0xf0f0609081513080a080601080c09010f050c1005010e0106020c010f09121401020c0a031d0d02240a05090901050901051f020f010e0708060105100c060b0d290705 71
    0x140315030042035030b210003002e21039004040c5050702c0c00108108042c202440b0303540c0d1541a5464954005484148054542e0300c0584083c0a60382d41680e1042c1c110030079942e9450a96101e1a5012240303152141030032482a01608100c00810b810340f1080015040700d0300d80d07085a080d13800c02c400540309400e1080300325001030182d8100740198800d400d00030070501c1c480c3c241090114038603880f07542242c01040e001d03025504000546020305034001d0300c4a1810034202d0380f601c0e1100d080c0c00055500c1201000003030003207104440d03041144a0b081040c18542c1000700019698940e61000144168083c3d0780d41072080384410300200b49800c00304840c5040e502e001c3c00080486144402c200540002d01a81c2001c5104100140410305420b00482c07900e09840d5004110300d0342420300c41c1c1d06006050300014000c1000014403461030b40e00c0f991080c3e016400c22000500d2085d0680450b8019495210103072000c4842c0705c20781c01142e07845250b5410403300d2070440105454000c01200e8521a0807a140310703030325 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 904359046 1250 904357796 904357813
    0x90c030109091115073c05031b0717010b0d03052d1e031326031006110f0d03110702090a0b03280b06030f01060f0f060908 54
    0x100c0c65481166843c2c050f146400e4454000d00020307070b4080b011410502c811501141c4101000a6101c1e91010b030b103d207002c41d5865031a1a9003521010b070941128550390142d401d40e04040c0031041c0101d8006070104402c0203120600107103513580c2c1c1c1c0914850003a01d0743c4581c3e5160035451061244c1c250300d01000341508140800340e00c04603050b81050f01102c0c01c0c1505e41c86414102c1840b13002150111074140f22040d1268004061075000c0d510001504000100800800c5000b0300c61146101c0e420358041d402642c0710100e00903a03410302d01d0708440b094401d0b10000c00d0048115078100444d088810315689e008a030140c0718505a10360541d143c0034401544010a80e030004c5000c7d400c1004041402e01400d41890f00a400255a928090f182c88840e5a520340102d80315007014000284032100105d241000e0b0015002100030300c041e01800a0b00c603440349004954540d90501c61404400400002405410740362a0307440c8914105200306085c0c1c0c480f1a0000518601074290501160003903c041c00006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 904360296 1250 904359046 904359059
    0x804030f052a01060501031d060106030e15010b0333040f111b0d090614070c170114060d2307050a060807030c080c03181920090c0301 59
    0x280c1254003804890500e80c4461000c084140c20050124102c850000c10f43d40d01e01000507045802400c403c0141c202ea00501030100e1400096690448100b4540010003100765100542020043c42170b04016940303420001034071100d080b000c1e501904803c00f100100c5240c88070700d000900c01307a42100f91402c1c1c4030380c1031031140e20306548484411143d0280225060100362201c0b401544007003031030407150f2841c02e01c0b501d0008082181d5020854241800e900950401102401409941c800289003110018800b030401170304442d100000c042548511080d44c030329250580c00781c070f118030142a2601000001030b00d64036007005084031158000c0c8051201060b075140740341c2c00d10b0b85558001140d20941c580000c0e80e80707684464000400f1266170b40425030801a10003410350300c00a036031008201d1280140704806c1c01c400b04903500300f100c170880781d82c0045001581c41c0c108501c0480207540d1141e4050700000b44086884001c011040d450000942003c0740b00c200044414240e030359605c80003081c070050100 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 904361546 1250 904360296 904360307
    0x209040209100915030c0e06090a0902030c0d032d2a0209070914040204060e040203041b080c0102011d1e1906020901030b0d03210b040f06050306070804030f 69
    0x7080380202441c088035101c3c0001d40580342d03080c44480d02040d18400c1007007400b9032070507414081c00a240c1034500340e0600c0303c002414154042c0240c0d008982d0741c40500115a800c00604c1c2054001a008007502c81e11410301921004d210840c403011003000d090b140d420043c3c0c001c4021881102c0d034540c035040d4900f00381c0084c0003018403460392401450482840e1b0140e50b880c800984901001d43e2511002c90608071190603044180600780d0045005100074010707150405070788060003d042d0303401a120b5441d4107042036100e181182c041c0d6003050750740011503608404039800700540003e0b002801000d00b12290018010000b001c503214035081b007040000b00706040d0000c3c0e0009190a0212000000c501c0320043ca81184c1704411101c15500207500142540c1501402d03c401004440d441e0000136981c4010304400d8a4085039040c0801e021399001200301140d20020808001a004129000243c0641d0000b411140034440c4207100345000500d4540c480c0207901d2195038195a4506c140020100030b4a1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 904362796 1250 904361546 904361551
    0x1806102607060c06181b14011e05190e01260c1b120702120c03100c12060b030403080609041101120905030c15010909051c1403090d0e0405040209040209 67
    0x34020307118105c81644080c500010310301d581c0210f1000306015910807030f414243c4d03125403120308a030f00c80c01945001d80e038020102d18621a00f048400c99120700910017224240b0a00c0c54650b40315480c064003201c0e241d823003c09140148001e80716aa5140042500f80c20302d43c0100c0604400d15080a00041448003604054081400350f00004a060301506100505061002c0d480c07011003140481d040c1c017545005c640b11105c2c45d240501030301a2480700c01c0841e8652110021140c00940c13a0102e0300090351280301d0010f0030b031210314410041a921419020300690003034805a002900040209500d40b42504016004550042a00d9141c41151005599202e034070f410030005590303102c1010012401c14070007010701e40c0554000d00441c0f1101c4010100014043c0c102c2e60b5110700c0c2858000c0000d1002400d00c500507441006502101c14107041208d525007a41d552150400b40841071045a0200050f20031000c500380e102c00c0c48100240f070900044590848000c1d503c880e41a010a003d820000721454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 904364046 1250 904362796 904362803
    0xc060c0207051207120609020411121005090403020d0c0c1802030117030306010f03150b030c090405011a0d241d0601023706020a0e03062a031806102607060c 69
    0x640f8010000380041203401080710a284c0760bc03408204141c844240d100c0c00f000d00000c40c0e00e5015401c06450003562103913401544020b21200d034404409000d0500001e01c01410000d1003404103a014401ca03202070b41081c0f003000305c041071414514400c950044252885408113a40317a1980c401150b008501528501c03000b01c50b1101456004520039103000d000718031035002c0c005860b6550b90028140000c80700164420504041e090145048000a0790b04862107420840b00100c6d450307e5400e1001e2094440f50400c1110101c11030001540d81c89501045a150340c03420581c2003140e480703500581c0c940f203442d01510754090a0b405c810441c14516068603070003c0f90b0001204240030541d507600201d9101c00e0000010654100049106240812016900c0b981d021104490303d15241d0b0000c00c41842080c142000c41c00200001c0c0503162403204580203405444201d443c0c90528900e6241c00c805d881c0070f486034049035152000c1d82d40c4014500041015003447c0209460b51400400322002030080c1002c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 904365296 1250 904364046 904364051
    0xc0305090301020f1b0115090c0905030109060c09351c181a040314030c0703030306180e1507110307080d05160804030f0c060c02070512071206090204 66
    0x50415803402d1000e8100042e5241d9815a03405240b4170b04101c84080041025407070381010044c2e000700100301c1c003030401c89019601c00b142d22541c141c1c050711511120381003203070503604e0000403e09021075078204840300501e6440e41c405d40f50715410090456044640110500c401c255103d1a021340311600d280c590074200b20540711030300700d50102ea01802110304110b100003441007030161030540301003000000502d1810707001141c08190014a181e01e02440c4400b91101c06040341c45011a1418030445071118001c80c19540701302d459180107030042141e4020000c0c4842e99030000f0300480c9451180c24407816000d002003007070302e000d800183e840a0b8014680402c0288a04040c00464404c00c0070348240d81c0b0901c840c43d1601e45107070040e412220020705158000650f03c03c80202d058200c1862604241c2501e4200416070804805039980c40d413510008002a2420252001e05613010030f010342510b07070407207800c0303007000b105102d0540d54140c42c0a01510b845416088030700141255000c61441440a00003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 904366546 1250 904365296 904365307
    0x140108070c0f12030f2304022b050c0909031603051b060a0c0c0b010e250e10080702150a0603061404060b010203040e04020609030c04020307030212011d070c0305 71
    0x2031040c040c50b02c01044812008400070216040d030580a0035441149040781042251880b0a145950b8840158007000101120000c102591030b070369020344042c00c02e02c4011407d0098207001c1c80c540902c0c01025541d60180038100c203010300d8000ca10900881d0b24070021418204a1400640070402c0c824045060142c1001540c00f00d028041881c80300c1d40c080c001504e110301d060f82d01c0000f80c401020601f01003154240c142000030310b5001c1075a040d10403030740d150152641c5201030051010512441186d01050007841c0861003540201c1902ea076480c19600342e0704000780900260703219403090390128050703000f160106e4030711220892420b038000748200c1f001c60401d55035210314040750012440007141180310410042408020700520652400a200642c0b0740b82c90a61030720700412018000034415100000d14405a0342c00f00644144550024811035803802d025038090000d611003003118841032840070000560b0000715100002000508c0a00d104035614501c081745e5580031044100e041c00001d002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 904367796 1250 904366546 904366553
    0x7020a020f0402033d080a0201050403140102040302030102070c150c050715020a020a08011d030a0e0d0503090405100519030b0406021b01050924070c0201030b0303091302040302150301140108070c 86
    0xd1640f0301030100042c1c100b80b00d580517a0240420500e405c01076840d401074500b00e0060b64804c04440c00c0b41c0e0801c2e01c0d9150720350441c951501a1050f0361001c2c2d41507002180700024040d641441c03100b143d84000c452248000c0c0c08506458040c0700f404041c02d00d41100004010085441100f52440103161042e100c14100c1c60f1700143c146d903001d03080000d140e9550410611020012030000144080d00340045041020b1407000400c101c040c40240d40c01a1940d241950030404104141c0d8618030001308240400d00c2d01204486584a062003803a11403c0f164201150000303080c0d4800080d41c0d0000741003115540c82d900e581003e50300004002151240d1241a5800030300288242409201e06501410b141890507417815030044034851060708103030405060200841d00420b20507009542800c000c1030910034107000a0441c02000400303900030b141e00c3d04610550b6550340c000d0041d6442201c951200140386903903060680001d0240c0c104680344004002550f40c080c0c19030a5001e4218a04583c0080d200d98 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 904369046 1250 904367796 904367851
    0x12090d080c0304080106050114041203090e0915070e0603060405060a0b0403030509030c040216030c0c1815240e0f10033305061b07030c03050607020a020f040203 71
    0x1051040e079500045402d110b0ba590030f001d408000d14003480e1440d050108070341d4a498034441e500c04d0081c0e40f45800090810140260007240041a03039458540e0b44d85069480651200c0514841d41e0183c0f000030000b8a003d030151050500c2100c01030100c0e419580d8079030030b100050801600c0240d001540d40b0f40003601d0002000144003030b40c800d5807243e84582203902890300c3c0c105070b034105a20841c01846104403c641c00d031020f980894051a140103541114188200040d1054112441018040f044030170314800ca9049003500d03802d0050f650f410f031aa180b00c960a0814500310030014501032919501f01e0a21a00503941200e40040c421684181d100c0001454620b1120340703613010130345510004004107000942c16200341c4007801902c0017a2a008111010b20140f8003e0318490440031500d51b103810709a0200e000f40013582e0f411690566201c0c144001c0340f150501c0b0480d2a8800c0c00d000600e41031000c1441015598007604074900e1050301c02c20007010750001491f40b40080b00d21b1000e03004242048 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 904370296 1250 904369046 904369057
    0x908061308030916170d0c080d0c0311030a0608061308041206060e010909151e020f0d0e071a0f040510030b0405101403061303030c0215010b0a030b030f12090d08 71
    0x809881d0b0303100103911317070303da04014641e4049028411010703200d0300803070b141c0390490b8904600702c80e0020794a03204e640194000e02003810340c860322500110801c8601c0100e544100141c0b0004c1045071055910442c40000d003941800340101050010f1008101c1a81c91000311b8120a20070807020030001d450711a5034542c400240d02c429200d87d03c501204c0705001048901d81c1d00c1c000c0800c428010054640c85140038030582d01101c400350b50380014500c85140303900c81510452100c0007003d111040124200595480240c00740604400c5c8002c0c1072000741400e2012500c00203411100141000e04e40741c1000100041c10b19090b00b4076884140a40a540e564842d4610408450011440383d43c2001500d100044c44070180e40c0c0a6803064081c004110b0f01c545040702c0ca00d90520340486d1071610303008224100903500b402c019092231a000041034010514020306a03040e00c550b010041c3c00000030405030b80301300440305d07901c454000c540410084048040180a00000581120101b03c0243e640750360381d5005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 904371546 1250 904370296 904370309
    0x1605070b0c010212060303121605120a0b09090a030e060901360506040308090402031e09030711100e0405041e0305040f09060302180a18120908061308030916 69
    0x990000b00c00c55040c0115017005003035004604103440a041c0040c071000280185031614004c805c0054801c0c400d03030403609130544030f0101d0034041c00c005444402401030080313003610a9000c540000e940038800100c0400755900f541d40c050200d050300091010f40c1e80801800c50405c070a0500014a15590211006c80408181c43c242c90441c5003c12603d5025969040a0300c034010401082002c00c41403000c0d0307280100201c500598a8945071141e00e4080d907058401d0007400c030700c0f208110142e980032002d449182c0c0a00d042d031140130514030400061075140103c16011a4100500011504040e07202c0c81d8410b100d0707030307012090300d0416030390b41e40030b01500300b04900080c0001020701c0305040041e0058000c10481c034040c0700c05400c550000d1144a160880c000e0299031900008080050540000011161491a503881620641012100b0b00300444c070f90303400306511003000110a40006185841400862505141e0700c5040d5a1040f282d030019101000d10311601c0b40d5156000054480c142c024101d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 904372796 1250 904371546 904371551
    0x9061208160203010906240803030106141c0c0909060e01030b0f0a060503120d060f05030604080a0219030504140f090a1a09070315060c0309030b1f150207120203031605070b0c01 78
    0x1c0b804801e87e000540e0350031400c00e94101344010401e0907045852003204850100031383e0b494201003458a5202000703500254170940c1410482c9090320381000e08036044d40e0000b0760038843c1c50b85400c00d00030001000c0c0b100a0034a822030740090040c203c540d40c82c81d004040300302d01096081d03071440000e151a012008a4811400000d00c02c2c031021594890b0708014401c141c07002e80024545800a074840030010320280c5180d00020304444894824071032800e880b9080010014545824100207155030030034020443c88401900d0301d18074900c1c1090951045400084c000100380e61001e01d214040c0c61111481901c0c201354550071801503a031000150300c00c00c1180c0e00003072a41c034500100762058016602074001c1c0035902e00c20101083d8231401c4841980d41003952210f45448a501034008c201c800490442c111080130000308071181031412503903802c1456800c941c00140c4403003083d01e076000c0702513000794503500821a0031988240ea032488203030030340030b0010358040035030710031103940141c0c011003404000c0d95 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 904374046 1250 904372796 904372841
    0x90605090f07030f030c02130c020307061103060d150209030307060e0114090606061b060915010f0b09100507170712090602060a050a060911030109061208160203010906 74
    0x2010440721841c0d040c00c0e0300900b00c642c0303107459079520a02c0012000d4208034107a5042025510381c2510341c208083d40590400580c082240025200c1d00844000c0b2a06400d05460b03900301d00703101d41528041c00b80108030618401c555510706c00403403080c0440001c410340070f0200d608165424030142050901403e004030303145410f007000c542110403040e01041480134078818000071010000f0700c030b503000d842500c100d69211255130802c0e1041125895003c080e10481081080640c3e0110380081c0c1204029403002c026600c5401483c15603000d4092075201900900c4000700c1e926282d04190030080003400d05504d045520b07141d001d10078100400055001c807000032000100204112100b01c1e10600d881c1c40c2c00c0031810301c50002e4842c10040c1c0795184980d100c10120b50075444941c0b05800a02090000700b09002a00e51720800940003481000c818924190b000036141042e1440303990800e500c10019442c0080c844403031a1101c00041c0243d81540d41c1d0f42811000504500c0b032000021005015204580d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 904375296 1250 904374046 904374061
    0x302210306040b040c091e0f0308090a0f211a01031407090507050a031d0f010c081003080f030c04030b13020319082d0a050306011e0806041e090605 65
    0x121840084613000d0f0b8a48007400b407600764060b92000030b0b182190708403014100b0940705040c0f00710264104140402c10b0382d0001041102140c014483d419054407030092560742c0d00d030540034146482c482c154119142030f8a2600c0e08080f00e502c2c40906200721002c0034a600d101224000c1c000c8241c20807982005088940d0751202810004140109091142440540ba1450006160303008003a07000060503210100d104034140791402e848120218601191000041201040e001e00007080501011a6a42021444039454102c1c2036007601d41090700c0501d00012029000e50991009150401410303051201000042003d0000c41c040c0c1a0241031101c00c508500400d802c02d0303141030b1000354195044550030006064542522400c41e8030f050b80200d00c1c140942c1100011003401e2406007416400907003843c00a4014010314024402079a07140d45010f04000341b5078004220605100102d048400041c40e680350680048541040380190f280c1d03580c1c40407038188107544181d0411a102ca4036101006841c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 904376546 1250 904375296 904375301
    0x120603120307140304060b030109081801110d140d0f1e140103110111030304060606030c05030f190605031c0206070e0604090b04110c060609072a030221030604 70
    0x965411140c00c52460801c8000640804810804243c1e0f00c01c000c0002400c0c0700580e800501e40070000f40007030101c5800d915101001d58820380c2d0149000f0704004c44100c3d1544181c10b0000962000001081c484034440401e490080b05d00883c90350243d07041207600700964080c0038a03140d8070b90600011503002071540b03100c45040c00d80b1450540603458622a181d03542d42c001e01060441c0e170010250b102401820f8012128406000301a40181c4400400d100801147da030061084034126a01040302c1c000020003181c0340d2006488948941e44107501203032204090300c5107405a501c0840d80040c8075652080803908041d49408500f00d110848015440400e8050100c0c581c80005803400304406a1701100085443c0501d00500d080d0940c1c44601c55079948490b071003100766540c81c0081c0390b10380c0b02041d40903980c1d15048521a000302a00c03004504143d014001003510a105505440c02c0d005240c035060840c8607a450040d0f04603c51800c00711907524072a0b9140446002c4a07901076980e180006c00d000a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 904377796 1250 904376546 904376563
    0x1a04050d0e010e150f13170c18070306030c030503190503160c0501090b2712070b0403020a0b090102180d0503040b070f050105010b071101030e061306060902120603 72
    0x522040162050542c0c0e80008031200189040b100c80c41c05001850f8801030304e0061010a044030b450015031460381180200da40c4e8115100b040099030440d83c424899038854065030107050304100c6031485079003241405110745500280e0752a00164581d92515440e468150310b520654542c0c1000031603d80c6000d0801c400001c0500b81d003491032a50402c2004010980c01c96101c1d102081010642c90007046429004a299642c010b01e0070246800c00d008411201035961108000c0ca141031039020510034404102071480a45205070103082860f02d031030307060092130f00034000c82c11400380303010358030000d0499003a0301e005041050005860305e01c0b4020483c0140d03100302c0c4040c416055200080002503001007260705030f0f6402ca9805407200580c1c5800040d41d618100000d01359424400086155182040034103100c2d0700800c01c17581001c40400054046801030307041030b0f030243c11600010303082200c014401c6180e01e00c0362000281041d9200c40c0c000407608590001401ca0508000b07110051408004e1641c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 904379046 1250 904377796 904377823
    0x31305150405030406050706022809060e010c0f14060903030a0b01021603030f110706030504020a0b1c020a052703160608070e1f080a0e01020a08060d0f1a0405 70
    0x81581c20036440c0d140d500c2c0101e2040d0350030810001424010030843d90182c030341070140f9605260310103168a0304a030700134410492090001d0b450072000034006224020000500e50b041c1c41d103015075422074807001d441050b18007060310450300b500016052500100306081c802ca41001c0619100e041444507881032f14106402e8070b045600c4a0030409800302d030045080216a81030400280e1483e0850064900f003c41c100c2c910310078010402c000035482d416070402e03446144200c0d104581d19071148034115550182c032000c0f00c2c4040e00078501c0a0124456030042107229440e0401d542041c410001e401410341c500003620885005074140780d4035a0130108100300c80380703500e10001409982000802007000000030046000c1009002412075641c452070350411800240b03150041441c0100c1c40003a0180c2002e942c0e802100d072400300c40908118043c800e8074201c1540360f8800641e9290070b402c2080c1e020312202d0030381d565034070a840c080000303502c403030140400e1600d20041e0a191416051081c01c1c21185403166 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 904380296 1250 904379046 904379083
    0x2702040f0209030327030a1703100503031b060c0406020a0609081c0902090604091509020d08040803120907080726010203040b04060c090f060807030914010b040b031618020708031305 80
    0x70f00712349000101e042030f0391800f54890b07452400c100c49a107031540c0040c1c1c15000c00190f11000300f6544000c42d00c8804040201c55440e140d103041d0b201d0f10300c940d20507000107030031102164000480035000704901030302900e80c0e00c1c202207255000a0f007400c01c1800121001e031f500e160f0701e4114105410002c0e0711000841e81004020b030341c4d80f140c00a02d45000103100400366104401c0e021955102c0904d068682c102e0308140d04c8584031200e0540d20303401603100515009125001450342100014800e056581420142c030105103000c015019460b4402912040c400e54110800c03160300007403001d14404c40c0104085545810582030801c1207503d0f0f1890ba01c00c01c0b008450921881040c182c4e0001162101d20304859242e540300310131802003208403030040c04215403c40c000190f400541102d1402d0404071420000400d9000406a440d503c0d01c4000750013900051080112034044000c000c03000d180d05502500d810016a50450031390b10403200341c12440c1d89907101000780282046051020846003900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 904381546 1250 904380296 904380313
    0x3103020108061819091b06180501020d0e030102070f03090302012007030b0601110d032319020a17040813120f02060d06091a01032702040f020903032703 67
    0x2c43c0c194000200169000c02d40f903513500070007007200d80c841281e070340e004004801c05004111590f41c0150213882131000090f440c0105150607081c958004080b10b40580041101c3c035204002278030204000d900c40d0360325550034403440c0c010820400b1001d850300e02c41c1d502d45910074154400904600490386910100e012400301d40304459100168001c00d41e900180700c1c0100e0707a54140125001117001c540c0150074051100e46014903609500700407009001d45106050001c4488100d8800700c104540189260390038401e41c2400c000e26600501c201c06a80c548030041c0b092804000000d12815038044541c0440091600d85041c0740d000b5080240c030b0004010182c070004c81c4c45840c0c07902c100142c00b904c030b40000111b4000c0c800450f405003006003107464090200c3c1d240303030f5401c500f48600852854046030401c0444242c0008212140c0401e0b42d02c00c4096804810a80900004204011564444540c2000005550fa800704090aa0800c6008c0c4004400c0c003402038800020000081403402913000402 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 904382796 1250 904381546 904381579
    0x60806090a0b0c07080d0501030b06060a05090d050c15030105010f03110d050c1c02040311011b0f17030a050402040b0a0b090112020d0207050a0b060a06050a05310302010806 76
    0x1408040240c2003001c080c2d0580b1102203c164a10038104010200c444c0007840400c055010307040207048a00410440c055681c900382803100354440c0c9081300c00050030400035405c203403a01c0c0c489070711003900820071540c103003c100d408140c1502c2c00441c0c402110102100420640d0b81c400341715443c44980789001c0c0905d1445d0403640940707004003032082046e291034900040203200440251412601403190348503208254a00c890000e501c2130000b512101c4a10610200b60350190404084448078052141c040c1011921000b8030031400d404119803040800c8240c1e814112100080c5000b49440c804c001600c0c20a0301c100030407200b01c03100d50350040b0564002008003c41041c10b2724841c08087c20a0340000340402e0b050b0009102d400c09118010388013082c0c0340300703202000400740c40141c401d210341e0701940c80391020403149046500c070700c4000a00c10005220a2807040020746176600c5072103481090701808032102d40da5003190500d80d00000e90400804c00556038006401900f29000340c4d0046c0744559101d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 904384046 1250 904382796 904382803
    0x2a0a1e0201080a1a031603151401060c030c0602030709080609070323031b060106091d0109020c1c081f050f01030c02120304110f0103020c100b030c060403060f06080609 74
    0x405403010b07030380d44a006001030a80c0040c4010941300017810f550702450006540714401c403a0b800142d4901ca05d80c1160400f00074507209140140d500c401507070705541c0c41e02c00e04451031010004220200002c1c0c2410038000751b20f0340051400b0300078640301d00c06080d0402011901c1d100e0000c1040905600c40c21040002c00e103101d0700c0401c1c140451410340300180e21660402e10714454400c11104e20b6406a8903100c1c88803010a026041e40d071160740d50500070b590740c802136105440c80d010180d10111404010005030342194010455140382806490458042010001c071054103400c5400118840008020702440003240d00c4d8402400800311240c13803801c2c00003287e044059042d04a040c03503a50350300749580328003c1280705244007050022590307901e0640741c07003035a01000d20f40030750044200c0c500d03038515503019009071180e602c8a04000c00403520700300c071a507000c0c00b0051307012a094055144210400d458a400501c09580510710200740448a0190310044449c20307485414990040710900c90581c0010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 904385296 1250 904384046 904384051
    0x9050618010608100509011424090603040f0609030c17040305070e0c0712091805010506180a2309010906030201090317120403111b06040b2a0a1e020108 67
    0x180703030940f080c1d80c54201180b0307200e00c1600626403044601c400000c0d2800c6011064540c0784e01030b07980308040c2018a91800341c0c01c0c134034040101e020300103000d0001c0d03a08014018507803190154190340c1000040351915411155450010360010700340381a01c50611101c0f9082030000f5100903202841d162840c0c607440c0c1c5039406402800c00303821405003c5100425540f0640c2c06140d0421070703844d440e101441d00609110828807400241450100541c1522421761241c903040b5040a0700c140d1415403040d80c0140f920010000f0a680807400101c04103600315032054080500743c22950100b200c601010804c40d404078164010000c0c1f50401d101400185d80c804101401c0301d611900040c2d00030000e0400460314010541501000c0a004040206060348607118210340b0545901381c600250321000c01003d41d603142c400c1d0b9074008000304002c00149030044000e003140071000101405441c071442d0940340c803081040002c3c905511000e034203010700500801303082d0504181c5d043c02c1200343d425800603200c100300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 904386546 1250 904385296 904385309
    0x6060a0b04150c0f0c15090504060b040e0601020106030b0a14010e06030d0c210801031209060f0c03020c03070303080906010b0c0c09091603030f02010e03070804091e02040b040905061801 82
    0x7183c1c0c1000400c2821401c241c1c401c0c0d4081c0d0300c03a010940b80d504c00502041c22070101400201500400952803d1602c07450381952860440c062a040c200490340891184c060200f43c110b40d6113120000104400e035018500859105601080b40c101e81040d0100604040c2c000c3d28840544000b0301079181e0700010b40b03070001c5009003820b8500c1d0145040c40f030040f96421207005410070030b107130410071074903444000a81a0307446000300d0480c0801008045658120f02e02900d008111900000c2400c113000e04641c411240c030904c1250040307440f050200341040c1c265030040b40800c0c02c100900803598001d00c02d4502401101c440e06090150040030181d07100c11403035840b4064502400410515074050081c9101c54880007001c0008942c0c03460000d03ca5403041cac4040740154a80185100280000700071152045c4d04080400d0901e0f042c40044070007064030615400001042807070b400d0000711640042c10003060303040041910b5503d01003030708081e075000901152190342440349001200490b24502c5041d1f812 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 904387796 1250 904386546 904386557
    0x50c0d0f121a270129040806010303110f07050415030506040510060501170f07030b030601030f0c090504240b03030d09120207033309030206060a0b0415 67
    0xd100c1069603000c81001d07001c1c41c4103081035584409448010030aa600341c0080e10719000d01d00000d0050100880d9444010245841c204010801409140b150854010501c44221402d00c00c000903007449138083e40c00500c06410900c0100305240d0024030825035217084c40040d0101c8003200c0300c0d5580720049401098480c46d9501a8690030740f190410600266a02030101c9074141844d052203603948071440100d000c0207080a10101d01d07540300300766030003001c400024640700716140c98901070f01158004041e1010503a80700c6045029031b034200324086c02540180c400c03150300c19141c100701d500c002280e00442141404c0c02e0520001922058800214070728080c1114044002e05019101604e203814081d0ba0600c004a00503080d410698030004005124030b4080c03400c4008241c05070b846114520001d40700710407407294031344401411700c8012500c174000740780c03007000200484400d0b044440e100700507001a80180108229420071405e20006020140c0c407141c2460300c2d241d1040701e50102032404808212 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 904389046 1250 904387796 904387817
    0x3010609122d060f020f041202120706090306051605030402040207061e0f0b122518061706010513020703051b03070213090809011d04060314010c050c0d 67
    0x1080000ca00426000e14031021050100601824441c2c400c18009a40c0789141c90403501a07800540300715440c040b000401142403528240780386c030a8140540013a40c002d50180c1400300080300910401001c0c0c10719440390f050745411130078a00216507000700b08480d40b4003403100904116070450192030b0300990489002d44e940c0080d01d03050020705150a4803200103281c40040040040b100e812030072990405c4c41c410031080c12070324104a800c0401c1e20511b11650044d21107900c001c2d80d01c404250b44020b00e915004101980c462804070340038543e4010501655403113109101c00158649001d58500402c40180000e5042070b0001c0d45203640c940400400c1640040c10800300350003401520700380f0b818482070700e1075100003400940d16548030803000c070301c52003031a070b010300d544c400394130801428a4101400604080490b801036030b590100042259082d2080044e14102c1e82d52401004041e6204440115241446800840c02e5421420f9100140b2408ac0280c04540c1e500050b01c01c01c581c00c0c3d00e40031b0403c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 904390296 1250 904389046 904389053
    0x315170a0611040519050d0201180f0303020c090f07170a0b060c010b030606030307171c0c031a0307030f1704080307060c200c0d060f02041403070b0301060912 70
    0x1403a40c0400624250800d0a242c80d80400d82d40508104c03038043d074410301c1118911160003250101405500c0d4040718540d00403016501c14804088090a0f000002030803544581420001d81c82c1540101c006070321541005419040451040743c000a5603030b40c0d04501c0c140401e02034030321909404130380d40d00360700d0340300160307141041d50485029428083d003010f50728620700780f14501030001d02004901a200704404505542030010845241503000b6844003428600500021982c2e400700c0d15462001d102010700c600c0c609818802e40c0314483c044c1d00c0025080800384078100280341c0b400d00c0207101e5041900100003042145403c10071450340005050150303002200184a540981d4204800d180705c0460035800300070140d0300044450700b241e128041680105d8402e5480001c2d001040c401e1500900c940c068141001da02403890113104a10114138058965509030072030300640d01809118a206a064046050034021131006d802c0c054005d5140d581040405000c016039441010000840401c42d0001d1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 904391546 1250 904390296 904390303
    0xb060d0203210c06091501140f0a0909050631020d0b090304080c061309020c2b081e1605070506041212091203020703050903030a05030115031517 64
    0x2c22440700c0852030504554080001181c120070783c10042c40c0314800115181c0f080014955001c401240c0030611642e08114079081c502c01d22550543c0c12040d4148482800e07900d107010100603001d000c0c4000742030310315401e141c0d180c08405050070740c0d034803610003c06580d540c20400a0451500052194110110500c041090f1200c454405008103100c6001c0c414103c01c040000c00484d0319060844605510550401506103e850304204c01e07101c0c4038904109071051a001707420901c003150280c800b00c007654440ac100d414155080d0507001b00d101c1e4140c2c0c000e60b030003000e1709800c195a2140c190784035000e0890305920580203041c521a0074044051003035514401c204440480d48e1100c181e80c403509140ca0030301d02c00700da01d82c3c2a0f80481c1c1c0711400c1c10807001852090b10003c6401c1942d041c22070084074004d0300258440e0509804025080002504549040009011070b035030941e0b550784e4962504416585400780c1031a14030406082103c2909016080641402a02d9088860480c0b00f1000a040c514 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 904392796 1250 904391546 904391563
    0x1b090a0e0a08120708091917090d0c080d0203041d10081204030b0708040c0b09061b03040305070f1206270c0e0117030f0318060f04020a0b03040b060d0203 68
    0x7106001802142c1800f2502605005641310b840b100c5081d240c4501e481c1d01c4550004c040005945585a5000480c088483c030800030500300e6002d502c0c010b541c030080380d48501482e03015104155402c1040082d00010094000000601c1c07020f10304180c10005504190b288110b82021104815000b150b80c1c000840c10f41c000420a5404a80010140f4011820242c1043c481a00c800300110001000c00d401744001e28461548010900d0b80da9091914940040d00080d80c40e50300001c0c01e001c4820030611014901c002d08012400441d1103034a1442c11520b004c12641041c0400e200c990010450100e500285409042d84840c000c20202c0c114a5600c6080d01d01c0d82910902d03440b407000300c000b48922201200283c40d8103803131920325a0b0302c039013007501e03426200c125503038403544100851075a080340940a0f6800442003d003002020655030080d62801400ba240f0b442810600d06c184011880c2c00805500108400714000307042d072600791501044400018403143c015800d4a100c60110340c0c0c20322402c81c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 904394046 1250 904392796 904392803
    0x4060e15010f080607052104050f150f01090b1003020a03151212030507090314070506040f080c0f0607060504031707111002090307030231020c1b090a0e0a 68
    0x4456a41e400e50055201d0b980c440c03001d660080a0104025510410880b80000246004c0d09a00008110102d442410050069544e0301400b145800e100000348601e07e1400c001c2d1180c82c1c0701c0e003441080c2154850381a8840c04100f0b1412942024545a105d020414221a03040c01619a00d4030346056014280c00c4070640c0f5081203200300440c4400c5000d486503807045c01103000740b100000c041415412254240c90400214a0b42e09081000908002c80e02d884c008400301690801503403507020402d2030701700e90801031950301c0380402488032510810101d4401842122002d0140901e0303004104c2c54400d401010b0406030315000081c06060103804400a000350880c110314440c40c0c0b002000305440a4501111500c0c0112281084903000c280252241d0500060150808924550070004003080c40e0720300040381c014659031100d1b078045a105250700160035100c00f50352156803020a07810079040d0104e072071240d0940c0d0038512581e2a5541c409510110300c500014040c00b111000703a1501d940007600a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 904395296 1250 904394046 904394083
    0x2d0705030d080105131b030e010c1d0d020a050d06061a040e220c090b0301060603060b2a1b011407030f0f05040e01080307020405090604050c0114070b09060f0a0b0904060e 75
    0x401d242075150340300310b90f4234419100800002c04100001c491181440880d210b030030a800c80103208511340b0b4441582840d20003050818420307524804a14800c10400082e604c2c95a43c0d4001c02c03001805241802d102c040c0e55079014a0203080203040c000d07600d405440c0b402600d9120402d40c40c100888038004000c5a00141e594954a588100242c003070040016664040d5080502c00504a8000e01840e026194840c41c4281414052800300c102000d4003603d414003196015460381c45800203000c408044910124102c0d815000a400500060300101e40518100c2c0204005400310380c0c000748200c280300c09454112a4038094001c1200c0b2806a82c100c885c210440100005614900200030f020f00c91003568103000070f0791580f240311b03200e0074215405005c51b005500f0080e0799612440f800f05006081c0101e05007410515165035034101012a140d8042d6400741d03050010552002a00e03503807003c0d4205083c0425a801000b0504210001d04020042ea85508820130622001c2c03002c881c0080c66400716 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 904396546 1250 904395296 904395341
    0x20406170106150507030c0818130f0b0f131505030f0705040e010606050301031106040e040501021b211e0a0207031704030804060e032d0705030d08010513 68
    0x24240248400d2240080b40441d40c800c03000c1860285040d45c03100c9401d0f07126103000030002d40711000f140d031080070389001121900494480f02d0b55020005141100c0310180000c1c40c2c81d080303034444106c0300741409907445000d110070b940000355204c002600c001e41d01d0700780100d403048075880b00f00c500200300c3e00310b1949801013814010003c44006074000803039008640902c007406040304028200d441e54007030316002540800043c80071038454800f804400b0000f0302158036241e5500d902c044952015181100c0607500004e5101c100c0f09603842c1541001e64020181c003042501ea80d1031010828625002c5040c050041000207060120120300445c044509003071664601e0a80300003501c0b8452400103c54080c3d51035903840005500b60251004d40f40d2185220745005c1c01e005081d00d101140d5540c450b4036101d80d507020010300e91121500f0908601d18600480004c1c8080402c60400e16580c1206011707601c80ca91a4020541c0118a0b0b1b045500c2958011201d515840148000e411281c40340f02d180700b0078411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 904397796 1250 904396546 904396589
    0xf030610090905151c02060a1110020a0804050129040b010e121e070308040603090f020d0302071404021c180506040b0105090f07020d03020a03021e031b0301030f0f020406 75
    0x20a14030740c1c4d008940c66a0000d40130f01215180c0d540c0705030041c1d0030000a2200c0c2140074022105858152002c0048401c0824080b00000c1668440415000051540024841004000d01a420602d0a110344101c3b0040c21003696602e1032510405a83c82070792588105281c0d6402440c43c0020b040c0003074001403208110200030355031283d0a8041e00a0f0302810124405052004200001582c0c0c0c8101c08a2a003031414a003140509174a18090754204400058000142c0d030340081e403c42c19200345c001d08015072034011002002150040118002e500411602d89900445c0c0c200e4038505150745400208a00c0d981c00a42400040c0f8000511074401d940500040c001300903101c1d4100e41080f66074440c150b440d41251048054207a0b880030140c0e008091050317015029401a1000f42d180d482c0c01414800600070700540100c412814808e440b1000040c80303070744c5100461602806040903003051440d4916920350100c0030540c54054250403400e547c600c110b40c3d40e81c11a2000b00111034076915000390144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 904399046 1250 904397796 904397821
    0x207210e0f04060b0c0c010f1b0b15030d020708010b04061d0a021b012403111212041e0807120609060209121c03060b09010302030919050d03050106050f030610090905 73
    0x200c01e280810308400c82d0b403118034859244480d003131100300b8908400c4071503662882b01d5080064402e8040c000c0514a030036064170100444c0107e200300c1e40c02050310b2490401c80d1400c4604222006002d641441002d008038005220048400f0b050700b01c4500c0c83d90b6520741c5400003400b80060080051309980c04c011170740041500318070f4014a605e001080c104403000b244610810740fa00c4002c00c070082c2003001c0304507403916032105000c0300c8488040d1059503500703040c864410751268004010307001640001030308516032030b00c5100117007000d20000e0000307500f8480d180801c0249d50400500789a104c001c150b04010003901a6640010080c01080c2d101d515100807540714000114554640004450b012422921034083c03241201d0242041c1840c0c40c10010045020358401848104540701d0303c10300040b94103138003440241d610300441c05030148000d92503000382552011b900c800c0800c08240029114481c24804036600513404558907409401074040569203040340b40e204c004501c1ca44400c028640512a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 904400296 1250 904399046 904399063
    0x160c0608060103061a031e07020d0207080703170705010f020409050105090a050705040b09040b0d0804050a0f260a05010501180b1206150d0c0305010207210e0f04060b0c 74
    0x20345500945560781c400440407280c0c0d510421214034000400c41502880300f000842c6c0041005a02d1503c3c00161009031119560507506240180c0c014000300d20000d90511500c1301621114014041e064a1501ea2400240c90710303000d41c1d2074600000308401040390940c42702e0021b07900301c00195140c40e551481140108400d100b0680100801d0700040d25040c00341c8100d910414180d00c940e41880e0500400007100c1c0c10506280d90000d40e134120704075969075200460203034548510b2240390758030701306000d1241120240c0d0101304680740c0148184070048251509107842d85e20344400d203100c0c0c15030901807490300c00301f400040c001d54a48800480c40e00410000510000c01d16403040c400f030981d44080c0100c240200c0421101600500041440b80182040c4681401c0004142548100f250f88074101071200d81da000b281c41ea940042d90008001c00c10102494014242d0100c1d91314030040b044c0680000b954200c02c0c0e2185141c0032945c981541c803a4000d5000d0904018041e40b12400d13480182c1e46c80340c06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 904401546 1250 904400296 904400309
    0xa080102031510050c010524030102070f1b0f0902031807061b030504030614011502160e04020a0e0c2d1209011107080408011103061e032b08070e0312090303160c 71
    0x9001d000c08c0941070500848504e1a0300c1030f1700100058950310303a001512207000914080d120003100002d048402e004080015040380c000059036818000f1000380384c2d42071100c1d0703000c141c0c108d01410050345800c03070b40c01441d6030006241c030002181c0600d412140b91040e5040200140e00d0b00500700720707030b00c0e0800a0034180c4400c04140b8000c03c010040c2680e0781d0407200300f420701800d000c460521482903c0402942c01c9880070b8002c1290301d407142c820000000003101c00781e6110b070001c9100c0a40000304881408009030717041d00e02daa9502c000c90041c4851052051200d15204040c011545083c82517200e0800e90046148c0c00e5100d5006240c20f000c1d41e03000f48030700700c0700b58200002c010741140c1c85421240100d20051410090040318120070031610a041c5017071382c3c103010300351010807101c4a10030000c03040d03030300d00c0341883c50382c18111800341c40c0380000b500d40c904110744140c002002d901e0014541640f507034503d031001d48030005540024a03500c9100c0382039803c04501c1c10620304101e0710030a5541034868 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 904402796 1250 904401546 904401601
    0x21e0102061b180d061b090e0402060a110c150d14101e0b0a120f0501031106071b0b070309170a1205120c04050a080102031510050c0105 60
    0x48441d1048119205600310380c104610800083d844410140502030f00e40202401c000300f290116151401111007400311050784c02d241c4440108030070761000032440078101c40d01041085080035004035402d400741880240a01c40031858041c4548001c00040340074002c010070816840c28a048918401e401c002c500c0d41190f41000c103007030410740030030b0f072501d00c500c54401e00c034a051841c0080c0401c044a0401c0c41401d861816038000c2a0f04501c80001e2904000c2c80d00c0c3e210042e14122404001c541744049030000d094a48001400000c074610024841c50804071001030301d400341405c041c0020010784564060110003100000b41c9203c6243c050310316107001e600c40340d5849982d00c85008510420519564440d0044041e00b400030346c042804080090326850800d00380800f00003641c0741e061301642c8032000b0030b0300490704104c0c901d000c40f1420f0242103a01c00a504608110f2038100c1d041100103000d920400801440c00e1000d0310407000d5034810031030840248114140308101a02022014480450b50718 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 904404046 1250 904402796 904402801
    0xf0708010e0a02090c1b10050121030f0810090501080c0423042009180715050405060703020f1c0206060907050a0e010509040903111009080d18021e010206 68
    0x21070210701034250907005006054166910045402183e00000c008074204c580c9000711450600d080145080403407a1210000c0c05e035040030442d010200700004c040b4061502c41407040c2c000381d480034246209081908010350300341c48032404c4e01035044103034200d0340085141100000d01c080d800600d446094405440401c1440b60500c040030202c2d5400400100604a200c04900050030350750701100300c00d00f00b0010f00a4050450000b940341c440035560540c40249401c1c1c200004041801048018080e00041c0d00f100c0e001814083e0490103148225031040d8400708003581414000d022030310449071420b01380c50288214005000d603081c0003041050040c410700c4000354060030080d51071030041c1c250340c035903030300703106143d04111190180d0112550401805012250007500d450013040c030054801d0300c414445140384401d003441c0c070a101010900c500c1c00e08103000d01080c80c2c0b00c01c503000304229980c040341d0204030015451503c110108029084240e00c04901c40a006840c4a117860190903030a40300c0c5034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 904405296 1250 904404046 904404071
    0x210d1107111807050c1009050d181406090307030822140105030619080706020a1505060a050d03020c1806030d0c02030d0e130c0f090b0f070b040f02030f070801 70
    0x2c0c09261807140c078075624000c54507142c083d001402428042004550b504031480e0314101c20303105182c4044429611a480c62801150410014444c400d042c80e541e01413a46011100c02c82e03a4242c040c19030040c08001200340c1523032414002c3c800a95045a061656000d8036208000521580c004c03c081c1c0d0f00301c01d00c0126110803001e442001620050b5035480c1592a2401080070501c00d010044101640c0301320300180c91041482800c000308a550080c03c01d50036141808004c031000040044007080c03421080080351f90703034000f884e4191303501502c1c0304400ea03040d0314069160110000c15240e00003143d0254a040340c8880a0241c41010185c041c1c92081016a00a459102031040029459005008030102480c8a03407000001d00500812081b1031944400c2030708200d650100f41c500024401240351070040c5d8000d101c6100426021944034503010a00750324a005005882c401080c06004901003030074042c00032060242660000c003a42d12805400c100c480c5e880c80c151190780310719401e140ba03401c5d42 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 904406546 1250 904405296 904405309
    0x1120501030f0b09031c020d0b0103090b040321020f041d070e04020f040302041d0d1103031906031505060910050d08090d0507030b07020c06040305210d110711 70
    0x40701d502190401c201080b40e500c0c940410b4004042070083c2c401070182005c0c0e010181c40b0000050240d9070300694420344100080c05030f400981a1606250801035050000340500030b102e98443e40510f0000307541100b4901072035030414004c0e038482d02c0600110350b03130110f821124000c008582e900d130045030100d101017105e041045800c940910215070031590024641c113242c0c005120503010078014900c0c090716580081c0031601c4807001c8002c104084070703020040e444108080007441034682004204542c0c6060696941e1000034040c09012001c66201c544203d038681048000c0d5a1200d24200100c2c0300001d80c400425080301c070140b00f415580040740307010007050408003d44202800088404030152a1914603070301040d04260440e016900c10310100703006200c0a80030b1032242c500a006c904040c1c000901d00315445030040d12031081000300f0400280e0001d1041c0f4490300b44c00d11051481491405503a03a030088146050043d800e0001c040c80c2e03c4850703801024481e100f440104155200c030340c05d1200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 904407796 1250 904406546 904406549
    0x1b15060927020109050607030804061a1f0207030209190c0e01050f0c1914010e030313060c200c0312041d040c0504150302010f0c050c0f030f150601120501 68
    0x101c400142418039580c25004a41e5541401814520202545c03500860b065501940081e000181c0c15001c4c001000010302840081031010040c03640c40c0794004000807404001d0061420b4910100e01c071840000d802030026900840d001070000300a0f00c0c1c4680c88900c1004030b41c0800b090740340b410f141440306501036807007040d040304183c0d50385017040c456403059622a401201004024807500040e083c2c10740350380e00b1660360320b4400c100c0c2101d1a03500324105825104c01c900c4038a1507402c1402000300030540b541040e20300035005031000c10140c07000b042c1a1791100c0400c3ea240c01d0b0500c6414411000d4000090200c10700b07500360111250500f0000c071381100341c000c1f0b0203803448804071241103902c03038a155450250450b000b8060310601c25925000901261148480c4403402c2d644c20004109642c2c12140c01c420040b540d0a0000d01520742e60b642a132034200f8407082e180310340030491000c400d80c0c4041040540c850307103a0302211010781128030210b80e074903c00c0752000c0c00140c1c0740700d60400c0300e080c5005160 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 904409046 1250 904407796 904407821
    0xf030a020d39061401140607260c070b0406080a0f140705301807080a12030b010e0d12030e010501120b07020a05190f1e0b090109051c1b150609 63
    0x71b807641000204400c1d580b00c0c0d5001d6403d40c0b009000c2d411000c00c4240f110a07031380310600d07046075542001d91030350b41450000d40c0003501021003404108a2203410a1481d5403040b0307161400180240c04100b070000400085082c540d000100004100c41640c00100401d40c0c40b4180a41040d0480b1400d00040e172205205980c6024190f1000860045207082d000702d0306852403502591101621294058585135070b0b500c003500c002c1e100e41c00620145400d8814044085c00c2841c1218680369500c02107101e1040d44640180759004541507144030360f01c2030b8050482c01d40800c0090190b565a030780c8000b50550b40720420f685443c03601c004034070160300000d444c48016920030007034804141d065140603030f4401110020b0b28040340e0f018100c00007030f91f40003102c16000c0c5103000d42190054541850580030400801c1c40e00d040c2c0c540740440002c42c0c0c00182e8122000002e0140003482c000c03009088070182c05a80500c0500c2580c600c006041210305000c140700600d80c04020040c0310f41e1040880d090350020030124 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 904410296 1250 904409046 904409069
    0x60302040f0e0a020f030c130f1503020d15060b070f0b06060a02060412140403031d10050702090a0603020405070801080c01030536030301060201020a020f030a020d39061401 76
    0xe100509051403805c4010400034242d94145803800045540c8600c034107589843c1720f503a01c8031602c03502054420032094861500c400c0004600710790106000e49042000504805034080b200c4070f0b02c50300b540042e4003030302100d41d240c2e032030b00b41910f01050003141d05181100c060200400080781801c04200352403400103030346c0c014000703a22981c8421506c0315000c0348800c20006881030400c3c4034a42c1d6402080150f200350707912070015158040c03140051161400491140140403a0707203a50135800401d803543c0b80e03011507501240352a0074054000034100c80e48001e4000c1d050408100c03039950007841c01d504961620040d5208820540b00440445e0f0048500c55a80c01150468210800c24102c1d10072610082c4030109a04500030020540f464009921090050390000b644d080700e190b0610505404403107407001942080c0300024040c0d25140c0c0407030a8000c200d0403006d40b20400030030741c01c241d00c180035503610f07034034407108602c00b40ca2501600384094615030308010790380949000718103025040701c9423441d06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 904411546 1250 904410296 904410313
    0xe04080f0a0e04050c0d0506030c030601060f0504050d03030504150506090a09020d061d0c01080c1206031f060e0c210a02070c12170a080109020714030d060302040f0e 73
    0x266840c0c0c00c0034910784100944424102c2c0b00740c940c2d00c9024012101141c040e03844a40940c0348205545008100034084d0304100307601141501c0000d02e090540e180c5040003540c400400404546900035503000305d80c0010a2900b0405054241e40f1250140d40281c00016128401001c0b040c240c52080d203640c0e4004a40d500007a0050341240e01c000c0700c06100402c034001d1742d24a0b840d03040540c0c0e8080b8014900c000e17070706800207041c403040102581c091000c1c2020b03100f41c40e20380060250740c001d160500000c0007202001a001e0b640910000d2041c2d0b4008041a03c11000782c00e00070000c001a0150b189010f8180e404168001078410984801c8002801e00041491804030300c5d44081c60050140c00d8090340034044900000c2907040c0200240507160100c03c2c0700155400c01c1041924007000361a802c10742000a921940e80c004442815901e141d0700141e522150340c0ba01f04004040316040381034078000801c04889102c810f4200c40c048a000700c40a000c0d007019440284201d0304000510300d00c55201192 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 904412796 1250 904411546 904411567
    0x121803100c140f0f36032e0911030709051605091c0602130b0d050c0301060807050901020a1509031416020103110c06010e180a02010806040f0f020a180e0408 69
    0x300003080100100303a117800040e0000b218010303009105d020242c0420f0900100c0360404114001141c00b0241121050074410350207201c0050a094003108442d4545511009000f40b420001d0140000036040b602401d40d40c142c5e80c40100415203c01e881c201403600c01c3c0781601d1040080d10141c0100402020f00300310000c200c0281c0b40c0d1301c02401c40710150284009564280700f550300c1d100410035080425661000c0f810781d0300c01c48000801045050361b0a00040c80040d601035500c80d40305500d4100f0603a0349081c8030040c0d2610141c0903004080503089007407440c01c43e00942002c10350b14030a840354180310740c1c810280c4126000d070422070000c0c28001084c0301c01540c4070350401d0b03000c1c41200c54172900e40745699108a041240c242c001050114080b41840606d840d01701084034001d092201a16040569a00003010b81b6000303400301d8440c81e1a150802440011030384098000680911b00710741d5921800800703411034003001c1c080b4030a407544180001c5c0d500318a5010710b109941c400d4003e80382405000c0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 904414046 1250 904412796 904412827
    0x120f041a061003240f03051515060a17070c0b060103060b090415090c2021210708010f0f050f060703090b040306050126121803100c140f 60
    0xc403074100b40542c4c0580c48540e000c2c4501800d014108172001d519485065080040c0340900798841c030700700199143c1c1040300c003042c20340042c00403160445640c4c1c0d480d201d05100b1211413000700880c101e820102c1c41405022070b00070b80c92442031449007400301d505984240056088412900c038616152104104898031071409900c00b1144804a4504220f03007070b1103034020021501c0c0036000b200031540c01050303005410351034000041c0d20031503100141140303180d0b101e100d00d50303511142000d85060030110303c11696003100803420742c02103260600a200e03440c0c1000010030305d1300280b04550200411410100b55013607419058003d4a1018011141510a400500540da4003d80040d0104841449c01184481d00040240025401880c01207010b5040c0b500d42e00035004010030103540e0001c1000310400101010403180c0d0700d440600d010b1380d1544445000d602c480f1440b00f0890b60301d40601c03828003e40e800603030b000da60310b04100c1c1d0350059008200500d0703000034401d5402d100380c0c0d81d500340f10303400603002e40742d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 904415296 1250 904414046 904414061
    0x180902040311041e051003060504060b01080606040b040e06040b06030717091504151b030605010306090c0c0605061f03090c0501030921170103050c040b060301050a0b03040602120f041a061003 84
    0x441b4107500c055541c1d103031581252803d86045a610f500d4980308511580e201c0c0301076401c803c2c00c40c0c8240c60710f03151107190880342c40b0310f05c503140ca600d0b80d41c000070f40180c0d180d80c403000006002400141d501d00d0702d050010b00014040c646d00d4005501c00010940800c070000c0d5010218540005500c043c0d100c07902c0b84600b03803103d01a011029501d07010740c0000d01d03a0888202c00b03120b030951004200d10382040f0000d01070b604950021152149841594001158003028003890541c000070300103229121240401c1c40c1c0010319141c0350171a603400b01201601c582c980d000e80c100e10700500c586000c254031140110281d54411102500440d480428206007541003d00184020080d0030203003031085c81a035075900340300400d030b00070303941c94001004005070b609103030050f01c08020b0210340321031641d030400300040c4001c0428041d01005500100000b0b0800c14240d04950002c0c1084500003643d141a96035003140201c115800c80d45114400e55490050303401d00c81082c01913100600c1301034149030a074022401440079 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 904416546 1250 904415296 904415311
    0x120706020c070609150f0e0603091c05090a05060f0708160b16110c0102030417010e070b0903070608150f010c14160e060a05060a180902040311041e05 66
    0x200706080c10a4420402d0300c0042c00180c44911041e45003400e412484451003055000703210140150012003903010031480d828150880d8070603125200c41c08000d03e04005800c100c6419503490904000c0d1a070400042d124980c41152041051503c1e07505000c5030340a80780b011541d40d20705000d4103000070b481c0300c050486220720200819004613641c55110004400303940300120f2450405000588650045422240c06a810001c03c8020352480001f5540c0c41a48035040200b60506641c030b1020100b03401050100320002c00b01d41c022030301d0b10301c00f8110764090f5041c54441e20582c500045d0450144501e9440307a00c0c1c4103000e64940001005120610300340c1c841d05410810204543d81c00601c40380301290201d02500b004200c151030260f00002601900c0d0017a030210760700407042000560700e0780b001d8070940c1c90964086443d4801c40700e0a9841004c807609583c040c00f0b1810012402880703a034040e00031030303010b010b01c0070080c8265010700044412a0046210b100801554192900c0c0103400c106d400010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 904417796 1250 904416546 904416551
    0x90a02092b020609120a15050c03130201050d020408030d0f0b0a03080306091312020f011a0d080f13030503070629101e0801050f1801090c02031b030306041a03120706 73
    0x400803e42d810b01c09000d07000c640c1500b0940d0081908411f5108540e48100001004d07440d5082840010b40103082180340241040b0300011300d000c1c0d002094044d60010a80700f000c0320b40b10480045100090001d010b60400d00c0c920b40001b9000c05d261424000d01142d422070307441490b6495542c03e000c0c0b0307520000c045042d204085181180083e42200e039a503100e1100c1e80c09002c8442082d44d00c1800e40303a500040160004c1a40c1b0001010b541d140560100d103544030703904a03950b005200ba03905041c094013410304244d0100e0365000091100200080098500c903a00c00c00120303104029844502403215900182c0b103000d04103198540c1090200c4070f104e2001030a101c00d02d071001160350015150306100310400681110010440f07414035070008540b807081200c0001440d40d0b00340c1c1c00b003403103481440340359440340e1a964201081d41c001d1045400040c42140304007200108034007090ba032030388142c8043d40101d18021096040c146002551800200010007405203a8030000445c1c003550408070341031f981c0d01d9 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 904419046 1250 904417796 904417819
    0x1a031519090b0a091502030705163003050106021516020a080406170a110a1b0203030412030e0306190b010201060b0409090b1b16030e090a02092b020609 67
    0x240441c66551043c100500e0104214281c1d14151031080c591203d8501c0085c014414040100e402c00d060310b003590b80301c4145000fa0100c034200008036203c0c0004103505103042c0180b01c100f003441d111422174291200e4030103006690740c5203030880e551240100e4080e204001c00c1d002c03a51080a40c1103204c07413a4241d20442d0300011150b1101141c55020780c1c80140030452101c0c1004600d03c04100351540301d03070f40030030400c010324100b98139078014410354000c0c0c1c0400a850191541c2c41c8035019504c84a5500581180c2d11103480301910021a0b0003840242e000c16203500c3c080f1b50038075000030217620450060650403075903894500c0440c0641b8400782d000741555200c8101180380c4440b90050001840a0600070038171103014144000860406403190702c481c02003088001c1d10b9080c1e1412244030940441002c0d01040c180e04003141c0e40758051081c95801040003003842030340704030b030f0b00502402a021200045072108240303000740c1d0304244004035a0303221074941d5404050714288000d41501ea20152000c0d1512 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 904420296 1250 904419046 904419053
    0x5100e04020d05070809070504060e010b0c0a05010606051b0105091e010608031602150a1b03030605090907061b051509070b1306021b1e030f010603061a03151909 71
    0x8070f104451a000051003801048044501042207a00a00003a00c04001550a01003881803400d0140515040d9041c005403c0080c3e480802040c003189030080000c1001940721240208641c0c44800b0140c0e10341d07110114044101011b1254900030000383c0024808203107480e904e65605c482d038590f4900c507551b88003000034800070280010000c0c18181840300d00c00d000da500c104035042021304c0d0360070f00c601b03824440c448240750031042030b00c0c0313001030054074540f110381c0d03441e0484c0030b00500c1e04115001005081030003c0da4800084200c1074903959101c1060400301103405400400d00048098916442a441c07001c10702c0044181980010001040e904030302c0e2542c000c0000340c5d06c503a610402245844004000c4076a041c01130080b0310f40f000c018a805400b40c2d9000903004144e85034281c2d90030700c1e904007000155404004014103004040000e10906a480c100b1304000d18640c048159030620903509000c482ca0f01141084000c001c503030f2401a40d03254036240d120582890401c0b80b081a56400320140030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 904421546 1250 904420296 904420301
    0x70507171312050d2a05010917120f06010c0605180d110c031903210509070e0a1103010303140721030b040b130f0f0f0b10080105100e04020d 62
    0xe001d00341c2c503003000c07240c26160042c80d010004580108001d0111081c0707204668642001d20480d0181c00b000c4440601800c1107801000d07014401030030742d4018400300e0a48031b2680098201c200d0b04280b80101982c40c1030019100520444400d40000c000134a2000082c85a603c804c1d0841851a14411081021036401d4580000c1400da10003090f5080c95101110b441004002f40f4136400f58060506100002d80702d200280b50403d0060a0200c0050408070b00c1401003251080c010034800203100605104003201d86901e29801050b01c0c104401c03001903220301c041e0045041000c48420100c0c50350b80ba540f01100c2d2042858200c819507441000078001140c1c40381e030141500c1c200416050401c00c0341510103400c607880c142401d40140c0c00c1c0701000d401030ba1800540e020407140004c0128050600b40c41440040c8002c0010f0f07091a03280c0760348640c450505234450410a48295002000d4070221081901da0001c01d1141d0b552003d16046656034652203103005098001e00500098203221014500109 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 904422796 1250 904421546 904421549
    0x260c152401120e0313121b0e060111011416180f030f0c180209180910020a020a0519060c1106150619110709090b13020a0e0a0506040b090705071713 65
    0x280290013142d20004c1c441154040b8602114110000c407400e4688803018541150040a181c14084465552201003a0a421855100e00214de0f288044e1822469a420011a0781200f000040350360010021380503071224844c2c16201d0044003240c00c24616699180e24141900c800ca40c400090000090850104c90302d000d1070b02414600940c2301c1e106030090001045d107520361410f489040800340000c521010400302c4000d0700448000d41e5480c40390b0004e038a44030710b8040050041c1b040386945501c0c00d090080c0010002d00c1580144404800c0d101c084440c0004c0f07106405043c0c1150010a10040300da28041e0f00c1800040c0000c0d0900d1541c0c0d0a004d506458512076002140459654440c054801e105003009420803450411610340f40391211000345a0081180c008206440c0e805003d40d0340340c1c42c0307590042c0b01d45e130b4034a480c1e498031180712006000b09032203040c056804d02c0080b02d0325251032201d0503c40d04665460030700303040302510741010420751500e48e6041e074501004041c4030400440c58800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 904424046 1250 904422796 904422809
    0x403150209090a0501030b04020d020a081f060909051b1302041d0a0c0905012106031a070e010e0603060a030510090201021603260c152401120e0313 65
    0x141c03a00300403001c1c40424200100340e141c0c144d00d044014000580340301401a04a5015285070641ca081403002c07414504e201d4204004510485110b030807001004030030080c0c00d52403c1024000c0e81d036624900c80603201e0096004000303401100c115010b00800503140301410b000201443d0485905290310300481e40540c110b44100059400202c106005541003160010b05d059010403a0721041040140014114011f140c104510f0b841d51130007800350300e50340361b201c01c0420a0400a25030b4030319040300008841400914008032510000380c0a0b400345c00d91404021041c0c480d9807003070482c0d00c100500c40e88020308082e0710140c21342011002c10400c200703450740007081c4400058600101c0c000a0f01d400c00700020746010340d01c203010520000d030302d1003104010032400c40c4060b000b66883e581481094010f05081c8603151244002006030700f070502c508240280c1640c2100001c141048402400d03107985003e05501003003400401c0000034800e03602000402800105484c05c00008044240c04a1041ea12a2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 904425296 1250 904424046 904424051
    0x4031712010612050708061e010e0603070e1207080706030e10090b0106030b0a0521191a0a090506010e06060403061104171f020d091212051501020303011406040315 72
    0x103da82841c240710310f9030400c0040c18000018640000080c04900340001c030210050801409558143d01490308560240e00041034561a4903040744001c0c4110700c0b00d5001c074421190542d04191aa801040c00c0042c1c0d01c81c0801703030106a04000c0250058501715441c0d80b540d04c100d07658007074a03500d184500300d040381c441c840400d13507545002070040585410300d01852040450440070405581e50101e41c0080c02d102000380100c3d152a060005e0402c000c0b0101d646400004407190b10420044420202d00e11031000c0c0001da00d62a0718040e4011524081d20040480d4001d5005215900d080701c0c0091380840001c106500c0c050700d0350b80c4c1400351541f00040106000e80800c060001d842d26101d5288d8560a08008215100061802c45005924248041080d660004840c3c4100c8116001240c000390000c144104d02d40700b10030020014502850480302c0c642c45d11012500065646140c4801014168010f6007140d083c205040400345006a5a81d03000404010010004401043c040c040c5800100b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 904426546 1250 904425296 904425317
    0x1104051b0a082a070209071407050a17091c050c0a0e0a0f09030807080c0409020c030a0f03021305120703050706050d0c0203040b0406030e0f1903120e03040317120106 73
    0x183c02c0d00c41102d02c045541100310412030014403e00d405540701540c04461031002078440325030544407140b400800503009040001c0c90828003000280111900348110805c855410300180c110116001c0c41500541c4503201c40d0000070340100e500141c0b642a030154094401c40d540c850000342c000d42d9598002000c51040c641000300000f401e00c2090300c1030b00e80f06070a000d02100341d58005c0c40d4420081c8840305114446000c100c1c982145410344025002c51081155651005807000d552500400c0c04000042d0000107491852231083c02510b584140400f0403020040c03d21040103090f6268010014a602c107000c000408a1000c100c264000c01160300d07a1035071400c00c0311400701075071203464850b01554820032040200148000850b1f0440c0c000d440c1c00600e4103e480c00c054100350714464280d2a0740304001072101c000003003066800c4058820303240c40381000031000c95402911548070301c940d044c0c0c005210030400314484103482400c0440340034031035250420000c1842491042a0090000188821030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 904427796 1250 904426546 904426561
    0xb031015080601080a050d27030602121003080306100215010f050a060c030504090c030207021f1b0b01060e01170c03070801141e0d08160219031104051b0a08 69
    0x20b80340546007135409056141d5058844564074449980c00034204404029000c44400b10640c0212501c0078505d46984126070321706008000e90400d4441c0307011071f011000410039581c89814030600300e941c04001e0318116a24017007000a003619081092055008100710f051800c0e02140442c1c0c081c01c0c059180e04030b01740c01c000c1400400c01080c1c200c0e205208000742414040ba81110545048490207103000c621900107140c210041e024611000350000003010141c12a6480d4001c1d0719100a43e03680c03a452406014007081d82c50b0b489006003c0e21021000006212041c810340203903500c2c0c00103040c800c500b110b040d0b0b423180c46101c04843e140c03c040e43c007100b800f05066000314114010f0042c5269400c0582040d13000600a60624119140d41c24038040780881341e03100d040100b640c040d00204125143c040001403116520f003042c1d0200d124500d50303010b10070030b0000540000b0680ba0000d0090720300c0070408041c000140005446210032442c0500e1a40c0425402402800104196038a060513800e0126 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 904429046 1250 904427796 904427803
    0xa0c231e220617060f0402090415021306021c21060b030c0909130317060112110306040b0303031006110106030204020409150608070f0503100f081e06010b09040b03101508 75
    0x60030343c0fa041581130051115403800000d420903012280e01c842502c9130f150046150920300c00e8400820b0002c642a0300e808445001101115180e40a440c0b00c00400c0f44944031000260110a0108900b031562200d00a02e00c1c1c6100e4405419180000e202c60b142e112260b6942c0044500403141e550018500ba000e0800d031008541141e0404200940540d640d90090042d006046488020044010006070140e2003101c0c6180381506100c02000455000080c1e0b002c41d600459081d0300490406441c0d500c10304000044a106101c84e00322009010308080d400c81f030b07000c0301410000d40307503403074400c003201513600da2000704000c0c88401d00010740b10002000b000405119940075a041c4945041000072690704148003501e114001c0c9410b554039a240107020f0550300c126009400d1220b801400820000030014071400308c05e9000c004e24451540c17900000b50360307580c0ad000d4000348078420301c088440c90829410002c0b400e5002010f940d4441d0003a00500c00301d450b800203560000b98824420410f804003070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 904430296 1250 904429046 904429079
    0x10050613090b040209150d0b0a06020d1b170a0c0206040b0702040f09121206081509070b03150f030c030615101704230a0c231e2206 58
    0x243da043d400c0c03000c2000041c80d18080405039101036603000900100350102940800c010050040c08102d821351101d03002551070941250001c04606030003016000401e85400365605680c3c001501d84140d8a55141041c4039081a032a482c144100c10860000583d910405040038140c03001089854915900400083d600340d040fa002140b07242584901c0401c1070354068452048160600100881e082241d01d4010f0507142d002d01070341d00800100c00c50b40c800e0a80e10501840c0b1080488811a40b02d403003040462205483c20342c000000036408001504000f68039943c00d5000a05807906003c0d440c0110b41401021101c481100c14561501038180c030b4903c5066103500350780d16100c0d003140c40c10f5010807554100900003030184041c1c40058440d170195045404042e08624040d503000f08018a05060780303403414003a0b4004c14440c1c9450038860404e0051030300388440c0040c05550201080d041c00d51400d403e01c00c0603074200500c1c5002400342504c2c0d48401247c80c000000018049280c40081204010803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 904431546 1250 904430296 904430299
    0x7030b01170406050f0a1401030204020f0d0f1a100e01080705070501050f220224190305090705300c031b1f0503010e0603150a0203100806010609090510050613090b 72
    0xb0a8166441c40224547c2c190640798155001696008003003c290114095412204521402d1841c0420001f000b40c00a0800000d498040c00c0c4001040003001310a4000d2688140003c0c401076500e02c60f5846076000c41d80020050038030300d16041554941c10f003514001c40700c409504a081c0144454060922000111019900c2191495210940c0082c040000300d118031100f414840d9404000401148200e8021040c20780c2c144031050500500a40070703110490340c82d03e45000d00c10000031603040456003070000c5500314885403202c41f0800032040c0702d100b070600c210001d88180951a01180c404028580314480c0c4103040140e2004801c0801554400441e00751741200f180d00400c49060b9042002c0d01c0c113480c3e02e10240001d81d80e030070f03001ca442c09200c03428456505900c5010302c20121401d500031030050b114501c0c40006a07803540c11440d41d038203003071140d040010b0b40d144c0b00300302850700f5601190b00405540d20340105142c0e603070000b500c603400540250190341002d180402c0700000703610815200c4d100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 904432796 1250 904431546 904431551
    0x3121811121203040203070e090d0801080c0906131b051b03190f03020f0a0e0316030506130318030b070207090b010f050901020115080304060210020c0607030b01170406050f0a 77
    0x3000d2400c1030300e0381820b640710300c2108000b10200c0d086590600260016026071201000b40e0b10300b0030201c9558006542018011807502d90020959503c08100300300701d000041e280c9400ca80b201424044000b043c9007a49a2441c0e90740041c410258120507844a131109076602c0036100c0704d20440701500e000a02d07200ea001c0da48100722451614410301c4000c03c030820b00b4200207001c0e41040030300f603000e48110003071604d914500141d14004c1e1394009522a02d0500d064040702d1031113034100da01c01c90708400d50102034a2584020001103900e40042e01103001c0314868640850302010307120b540048081140c0084030000f0207403080004071641040583d0092850b90f90a000c02104da00000e003603e800342c80580100140001e50014690003500700c0b06403c0480d66800e2131a580c2c0d035924984136000740c000d4000502940c07001604840705030003a40c5480b500c21003d0407641c1c9a454040d80280200445541031180b5141c6010340380c0c010b01d1002d07104500491000c17415103072040342114200c1c4018440c030356051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 904434046 1250 904432796 904432819
    0x203091501081504020604150804110402120c0d38221a190303031b0e06070609021c060506090910050c1c020d0c030b03030f0703121811 60
    0x800181e040c3d81450b8000100c070440e00c8600200e031741d5201d103422542c50944801c1202094640c802c10036403040b409114407050b00c1481c001080280c1c81500c5100d4146031081c00850080e00074280103001180b00600c0001d00000740508a1110b10a42d0b02413101e100345100c0b41450780304003034000072000328040303500e060292507198010340d000504c1d60110440595900c000c03c2d010362043e055041d5020000d01c01c505020004949200907030b2035000450000782485041d820a1a48184034400c01210392144280200514180311550b001020180c69088d2105401f20160300c4240c0c1540d14030300800e25940c0501c00300e0a285003510740c09403e05005003507250820181500110700c00c2c55003200004c0c0401c042e1614002c1da1500d0181300010703c03161980000515290701c40342c0c01401142a40903041c0550364080314140c04960905185581581080111000300c0e28941d0041070182c7c4641801c02e41030b000700d1a00421207890100380030b10307900807460200a0189084408804038401c482c42c03e14035 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 904435296 1250 904434046 904434059
    0x30103061128021e0d0210060f0b070c0902041d01081b09090f0f0f100605030d110307080403111804050c040e07030f0602092b0305070f02040f0203091501 68
    0x200855030110000b452000009103140e00c20301044000c1ca2001c00407082801d82c90700685d8555086132090800751050144054040010b402050b0031200c0d2800450561442e09201e240140d000e100212400d0402c1c4a020411070070602c080c102400c024040f010902001038100601a603040e0031141555010301c00d144c139407180007021815085810f1f03a404019899010203d86040c55140500590340115252694a01d10008001000e44002d02c21a4504503c00000c18100c0340d030350041c0d903090340180403107512aa0081c054010350030301a2003140c0c40c001550326201141d4016030070031503058405410092540c500300302d041560f9603000c80741c1042410030795101540e801200361454002e82e00d850034005600010b21070030b002181c010300d091450713160343c2c03071301d90000e60000f01071910402120b002e48c115144901c80e4031142c000220f0780b5078210013203a00c0c140c400360007070701044600c20341031006400180c44030700070f0040f964911480981c41e803c10b000c043d03040802414102d442c080c0c503000100550b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 904436546 1250 904435296 904435327
    0xd2006010f051203070c090209030c12061303050c070915090c08040b06030304080a0c0f0f0b18040b210105240f0103090209070f02060c030f1918080301030611 70
    0x80790002c07501e54902007288101c503804e50203410006070400007507050028a1503015001020005c40440544881420205c05c00400c5010030088074504c2d4040c00000d1705c01c4250001492110303000c0c0c1803281c285984101400e15004958101a02e116110020316400540414000000d001000418401c03184200801400c54100400140514081c403000c500d542d20140112405031480744143d801c0c880c0c85003019003181826105150300449406400504ad0311030142000913108403840d41c5140c103415040b60f00355001400840c81d40560307502c0d013514150386c83c2800c030807900b4005c2020543c482c10312100d260859000910f0300031003102108110710b80d48a200d00010400300c2c111542c644d02600c0703800407001010031940007500222400188101c49030008440c0704545415400c96140742d90308494090a4081903494104414111020403215007402c1074620603a03032a01303800070382c3d080751b0100e600e184c80301554146d0702c0f60b40000041c13089c020140203240c0e0903d408014036142aa811607491103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 904437796 1250 904436546 904436549
    0xe130c0813020a0810150602060c0d050703230702010c0212040603021309090c091802211039141615050114040c0f1b050d2006010f 58
    0x20007070807103203000046548824105014180140480b070340d2600385020b104c01404040d54050410b59549000a01107200066140c0f24003515001a0306103052a0310807030140202805580c14503880b0310b030b080d00d00c04a1032480440364245010f40a16401c0c00031000c0e0840780c1c4052864115003100b07c0301180e1000307501c01c440884205140050303441c141c0c01884c200f84800b68200605e014101032030385007801000e00c00801611000d42e402c118548040038030341014080e10070b0007504031044040300d042c900980c239270a6101070710310000d40b8000003e0050300390449210b4011068a400400042004045039039140d105880d03140b24a99450004508064a01e001c00b0108010200300002c50701035810302d41810440c4141c3c0b2120907841c0d200071ba0702c0307440a40402d0080541d2041c14024500c0e080c40c0a0044a0a00440d500c600d00b000840804c00c4a0340c2041d061581e0b520070007100c00340c00040d81003040400910045d40d0b81e56034401c548a000c4402d080c041d06011032503204000600508584103203d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 904439046 1250 904437796 904437811
    0x31506050a050c010b030102070807020102100203102601090302011b050304080421081305040b010c0c09020f1b01050619030b070804061b18050d1718100e130c08 71
    0xa0f110074900c0006400350540c610400d404d540080782010401000d50068a25030303100340c0960305441c441120b6003040340000c031550071410010f604108010031204c0403040c2ca180c41411410750100d0207624203825158010000c900507035550b0748210341529010f0005800c0401864864a9824992100d0215000b14040c0c1c920440013551200d040d040c800c43c4280e5855804203c05071070780d4032144900c418142d2485014007407410720720b02c0c51484d03200b9003c6482540e4408482d0700c1d65401e01c1b49610082d0488209603e802400b0800030411031030101050400340c031250300101c0d145c9480000d10004c401d5510f5041440050078000340001030504402070343c007841900d00350302c1e41d5981b8180f9a01030440e15101b241e40074042c000c0c0c280a982d00c44079511900001d03400e15041390340e407a42403103064010460043c10000710b803011651401003410003440b130055601000c0c0b06481036003000a418401d0310724607001003500b10740f01ca46642049056008050301c011010000b5503075035007024180c000b0003003054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 904440296 1250 904439046 904439057
    0x1e0c0a0501021c0e0d03050c0114190917041206110901050a030903050906030a0c08011a070204150e10090c020102041a030a060e13060e030c1207080d0c0e01031506050a 74
    0x200c1c86100c4c1c9400005160020004544000d860601500381c0e441000784030b65650801e898014604254486c050103000c2400c4001a4a0280c0b006000200211340080300c000c251000117000701c0c0300320400381010300b054400e44080e007400e40c40c140301100c0340450084810002444041801c0e82c1050617a0074080080c1004190340040f840d080307880d03100d08581e003075000002001384104410643e00c0f5040030501c5403030303203151a601c44142001103024065400354440c01084038000609003508420010b0301400107407651161140003c0611070401c5038a60700005109008100014841c01040440c10b00c82c0021407500d401c04031424140c25410002920074100080480d00402e40c980c0100001c050681e45041c2c1c0e400d01c030040858010030310005440d554140401c5c2a40d00002000725086100307020000c00f06200404119921900400c0c400d90344507005120640c0082c4807809016100345a9582c0c040020301594005002c039425180c4240a801c90f859041c0b02080d000000c075805094281401e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 904441546 1250 904440296 904440343
    0xf04090201051b24010e0f0c1b0c060a03050915010506031302011107030507060f08192a0c03080135011508100e030c0601090c111e0c0a050102 63
    0x3080c1c5000c501002c24507000c40c0900d1300e03004514a00391418142c501c8039000f6901611040c1d003003032001c2c80070345880b48155010060140c0ca1802c120f0402c10103070494043e02c000303440c000c0004615170080f0440101007501d400c1000008203083c052000a9003100955140347d5051501080c240c5c00300074604880410010849030a580c040c0c002d6400f0120b4800445950549910f4840d1301c0761a0b0f40308140202d818004904036503805806090311030a0410410841000320a4201e4042c1c0842d010072944e01850b4607800104c08904c42e01041180c00e1621350a403504c00d20b141c001c00319a0141e10041c0340c0f0700d14162070780455200019000200b4070744414426800040c10302c1c14014003070200c02c0d10710015420000500e06202084404c21402c40c81c4041240c00c01810240741c403031040200032040c9401c60001030000050300c0d80900c1c080000c40c60000ea8586106409500d0101900c40e04003141900f170031030b038803401410000c0c9600c01000f55801d0003010300e440d002070360b0707624a06070160b49030280c04071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 904442796 1250 904441546 904441597
    0xb031e0601142d1c0501060306060b1213080f04061e1407030f0504051003061d04020a120807080408060613060b0f0c190803040c08070f330e0f0409020105 68
    0x10b1840400824905134450340030303149070580c002e210a110455a041c140314001407800910800d032105041c0d24540c44940b540c80c0b2030350101c00380c01e940b0100e40a50b41800911210400740c80a08064006522000c500100041c0100441004a6582e01c2080711704070540d010121010281e4030015491b050412448480d0301080d9090300442d000190011041c0c20000d0425a154000100312051b650918003000c407004100d040c4908100d4000c0d42250091801704482d0404c046005943c60082c041c0c98101981561840c40b1584580d1081c1d05503031124017401890700c0c2071601a11004909030f000c024540c0380030400c01c9a0300890ba80e510114a0104420a04103001d00400c42e000b41e060002501c454180d241604030361b0002d40d011760b038026980e4408070b030b07000307000840c10305030307a034017500d894040e0310b0100d107007802d490201d08100031940510301500d17410001d448a2034080c103860b11078182040d0581e05101034401c54041c051300c20707401c12143c200943d8200085a6103c00e10507a0320500340d0f042e98 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 904444046 1250 904442796 904442809
    0x7060218030d03061d04022d130b0f030f06010506130e13031d06070809010309020a0806090d03020915071a250c02010e040b031e0601142d 61
    0xd41007509030260300741c14202e166040c0c0c4001c064450f803603941410f0203031080c03841035802801c035402908090300c03004007904c84815070f8a43d0402c1041364020110b401c041000b0032003504d4511070141c0d03c19118071070000545444c7c8000c091255043e00144a0f180621201642e10308040c810300d4001c0c800080c020032106840300380390700582100410b2650354208458807840c881108c01080d400101c011544c0399503c0c0040c501d030172182c44020003503801c2047d903865030780c0c003640808851414581d8802d00140183c503a018a5001094100040c020a1800a04060410011400c0f02c0105841000040c51998900380c1c2000040031340c0d00ca060300c2304160b03d0407000301c00044065403c414070f10b10801840101c00c4e829000d200804903080c210b08601a101941c0219110400901045070f88600c05100d040c16400028030060080498004161b001500f0b000e044030b84107800c103103030005401803106241806c08551076035400e031440b600ea84081200c0143e906c442c00d119094149241b01041215030f43d11 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 904445296 1250 904444046 904444087
    0x10050c0403060e0f0d0906020c01051305031c1206050a031e0b130302010c0504030203060f0406060f0602030c07050d0b010b0f040f060e010e0405071209050304030807080d110f070602 80
    0x82e004101c1280003c5425a9071250440300c00518403803501c4080311140f2a101480884046400915441803030a005445982100c40d02000b0007504403800503180c0da01b0060801e0136000c0004030340d4401401040280020107100060100c103040c888100019240c440211084a401420741d500f0410075521682608110120141c10134081c00c05000540c8114112200d40c6803194001b00001096900251030a002c0c0340301c044c1d0305400000003e504000303180b13011a8418030503132000500a403600d26996004000b508040f0040c0e1000c0340703480c290481009000040c100c101d038031070f0250200c4e03568019681014003541101c25004031b00b0740454041d94090394007905000c1c50461079203845446c014682d11100741483c3c005540741b241081c09041a21420380106260f989400d00380c4903403000c1c40068401204c00701d60300d200030070000011a40b80c3c3e01038413003a4030800016907104d040b00e59034030a5800a08800440716420001070002011010441d02c51650140d4090389a507140c040c42510b06215 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 904446546 1250 904445296 904445303
    0x706110d1118450610090b0a020a0203030a021b04090b07110106031205070203060a061a0f12010902071407060e0f21010615030b030304090b0d080d05010302130c0210050c0403 77
    0xc0f600d2440d0349415a0300f900310b10a610f080c0740c2a50f40d4070b039020010042c101740001710103e50740041c1030144a5030340005201001017401200c15800031980400d01e1a841204020010703040081c91078003400320340c1e020f603816441c00c64081c0110310807a22210850310b00500b2450078005101c61049000e1b83c03c2d045a801103411070340c00032650700c0000f0040d06aa100c15001c07440fa0054200003500540309100f5138040d5004100035a038460107602401e500351b4003404040d601c1181c00d104a41b8950140581c40e40a0080001c0240e102e82851a00b400c55808800e0f40b815a500484028000d50380c0c014240601c0341d50407200a078079048132070302007900d00010314010703046621082c0d000800c807101508100100c83c11034035420305455040a08034110b49540c002154107800c200000c101c0b107185034105d4500c160005001c4a088522075540d103c5079400b1504079080143c5a00040082d86400c031040c00c00307500380d581d023848480c0f20304000035210805008002d5171b4503641c40100f07001a80410948014551 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 904447796 1250 904446546 904446619
    0xb043605091b10020c01050d061809030306083405060705010b0307051909020a05040509090d030f02030c0d1116050f06060d031d04020706110d1118 65
    0x2000ca89140c1c507045900b904510414008105590a0034001c28000b5140800c1d0301a099050284e80115100d9105070140c9080c3c0380c07030340310209416550b10002800714400450000c1c0c01c0c046454042c3c141d502503404101c40f500b04441901c030341020115005440740c03204a4642e068401e044100703a410b4143d40013903400c4400841c00d001045015803103441104422002c44002aa44c0c104202e11214101c41d0750f00c0c840a032400030000f4800e1a0080c04c44c2060a040103401c0a4840c1c0100381c6950086030406865032012a400041c1c5415110f031030203240b5000000d500d9441d041e032034400640300306444008010303951440c200f0954111016144a010080f07501c1078528682e06045a4401c10079140700401d010301c0d0f0100710189410750484c89500d6254584480c00d10032405000007511401e11025009502040031000142d0144650000300012402441c0c541d001c2d19101d0045444110204011034002c1192084822048005d10014282181c003042407891055500d07410409080708980c0210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 904449046 1250 904447796 904447801
    0x1503080a050304020f03120406050306030f010c0206040c1d130204150b0909010b09030a02130e0328020a02030c06130b120103120309031205041b0315060b043605 71
    0x41e403080045000c0c074000c840f074000c141441401c1586400a0066170640d03284100000c0240f14020001f941e40024000c00b552000c108004030307142514240e24401c0010b0300100208020403008010b9023018000c00300598950a19000c01d001c1411000f83c000180100040c22441c215a110340040b100810030104e15006107503540d20540d0300341c1040b80c1c5c280c0701d04003000c00030411030707404003d03164010f1001b0014040407040c0d80a2003c1200d00340d452240300d68603000c115051010030001040d205100c0100b10845a1a02540c0111788190091007821904600c01003405a900054080c443e45000c40700300b6a00d160441c48072201342c1441d403080c410f807034010690080a40e000e110f4581202d010707a444039031203400e40c10f0407401c84209420050104612001e02c401c1180990f101c254454800d8410b903044007005c1c00c03541c540c100c1607441101c500e518540b0407040f94429000c0c440003005155442c5003000e00740603c4a4080c0000b10600c19200543c1404404914140024005c1000c012500b00003a0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 904450296 1250 904449046 904449067
    0x120d080105151c0506040b030118080f040f06120b030606010c02011d1e0118062307050114041403041d090a1226041a090c1305180d12150308 62
    0x404d4100c80d00e40c031803440c080700c1c003525003018050410440036460781594814a6650745413100d40122182001c1c002040c0710114080380c0d0280d1480103032501d5250103003800c1004600d2000da502d0041a180242c000200b400348a0340c004114080c0301e40c1c2420480f00480040043c00d008000041c42c00f0b038007110200780c9800000d40c4445d40c01c0d00034001e82e6140c11202c1124002a406030041c85800000380e03180c241c02c00c02c8880581c148006006000c4114607188842d00c4042c2503d0594001082c6290700c0c1052004000780007202000c82060600a1400c091900e000101881903105c6088018008400068100241488003250459002c0059101204a0f40c0028100701291890306080c3c84001c2204203858544811079201e298040341c00c00700020400f103101104500503051014903c44c1c120200780d55900c2000b007003070210380c5080c0001d0390f04d490a00c290089496200340c50158210f100b680510645c40070000c02030428003100480c034140380c84050a1031203040d42c07015100d90000300c0c0c040c171107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 904451546 1250 904450296 904450301
    0xf100f1101061d0a050105030d03090318420521070c06060b090a050f0109170a03120b0f0d0f1209140103111903020c030703080402120d080105151c 65
    0x83e020f0350740511081d41c078490720b241120020b000b03990745980a891181d60041c4a5041841e030b041c0300e881c0c141a244103042a8101c42d1005803c00501c46c000d03101c03078000b40c00c0d003c1c5030810a40000c541c5c40034034030410742c450016089010400400c10900060404000805032100f4295108056185010f490708407002440c0c12018601100e640d410000300044061049007600c43e074082c0205803a804078607080820280b401c02b0140d25052141200c40000c010b12034016034490010044040d101d0400d41d071070024041721509140185041c6032515215060f240c0c20b42006802109450030711002c0190f04041c584103031080300c018800c407200c2c14001d0040b0380c0070011034101c0b4605500948102d11703103c0194191034514004440c52042070008864109a41c0004000150079041c014600081c14400300c1c190707030241a090700441d112406000c00c50030314010380d840810848000d8038040c41d42841c014a024018803801d071094584040c901030a410440131107001d030f40c40c4a25070749070920941030b9001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 904452796 1250 904451546 904451579
    0xc090409020d020d061407030605060a0822050c0a0609030803041202070911090414040b07080c0c070906150810331d04020a080a0f150305060a06050f100f110106 71
    0x891440126070054041c9c05624196900101007a013452406102200c9040004041c031842840348007400202149401c03030110818042c42c06000c40300720841c00c0c0300d0740401a5200c6410000341d030004001040c0310303c003500d4005a00127503c01c90a14031300c00481c54a1440e8106a041031714002c0b8141d010381c40301001300a80c12055905101c4454030060410004030f045901908160f05100081c401034441c0a105520001d107a0b55181851100f440b45841c110391900a00b44503591070340c1c14815160310f00703813042c0303225014079010000e49071480c605103040e0b5403072094284041c1c44442c213464503c0c8014440d0f001201c41c42c0314100c5040d0350f9100504044a01c42c5c421843d0070312442d400b100742814001c540300f03c641038403010055207964008400a15054590001040c0c0d031391360001d2405000400c510045014074002c100c40c0c04e00d03c80150407200035034803540c800d130000052451562180d503250340707000943d800d00040c80703414400203079140c80e800c440b080255440c01002164203820b0121034038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 904454046 1250 904452796 904452821
    0x1008071203020606121914010f0e0a080702211608031602150c0f1513120518060f04210b0112080d0c05041701050c090409020d020d06 59
    0x2004903598445121a1403410000a0010b03004000011020304100c00441c4950641004940130000440b00020300400c005104a68240506150600d039890902500c1207010518404200804141c01d05550ba21805a8005c02c01c400105044e8117541d114900482d00f049025200e0b003281c5145103000b61500d8000e0b038840e5035004516404921000d000042d2504014110042003101d1b89940803c85080410b2000c01c007400c404002640e841d010601c00316001d10783c40c40041c0f40080c288010b20000c84801400741c800015009101c5001c61440b4417556220300050a010b0ba485030b131030312010380e02d004401419812000005580c044c071544000184119070f1540003028103000500039104a10030854005050340307010030014002c0a00b0310300070000c500e1040450614003070f02000038005942a01d88a82c0c042200414100a0000056101d0751088003c10082055241559612040e40215502a4081c69440524800715141d840455450a40091038504c0800340c0e490004003501c000300104 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 904455296 1250 904454046 904454053
    0x2a04080601030f02120c0603180a172106060304080c1e031e09060306060f07060c0c03080108010c120c0509130b0f091006050f0919061d060304080903010905061008 72
    0x20f0001c0002148840040c1e500a10023451502c400603071048842c2c6d90a100c6015014140300c2c00300090409080903000540c0702d445a46a6487c40e0710038102d04043c00007030703001c190b1000800c02140d0300c8108032644142c0c000c4d805a161000000e02c04e1514a0304143c1507560b042400c0d501200b0200003000d0300343c55004040d101d0b03c1d1200310b031540b040c5001744511581c02110900c00b08001e4035048029040740d010035451141014525150340059520f09007100000c5110b0001e06418181d00035052405007100328002d01a440706600020710450800c0f2548021941d1004101c1107640700c0c2007142e800110041c4401400145001000010040000710510807001303a5420f204a0502d4621184203800c080c0b11f00c1c0c412858040d040c2d0340d40d840701841c102070701030400c4a40c7c0c4a0340c071030b10070940301a01c2d005e410102a04000c1c010f0040e101c80c0c500c1e14007031043e41117100500e43d566811254041da02040c541e844140000c0401d014182d001c0d0300502c180035020410100720345106205c004c944000084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 904456546 1250 904455296 904455319
    0x1e13050c0a031502030a021e0c100b010f03110c030f0c100b0604030308060a0306020301030b270a1104020c010c05030712020a05030c070c0f06020a03020f062a04080601030f02 77
    0x801c07400c60628400205400c008441d01030841d20103074080d6034803105200d400341c41c002000d0066501d090f480500b41408602c08908440c8100301003084607001e29112808121110705c0b040003a0809940c59504000c068a030039412405c101c080d42601e002ca504141140d48425444035030138a603070401d2264828034401c1443d01e50410040e400348010020000d07004920340343c29500d0032a00000000d21503900b20080b503900000040d200c1c4000c5009600070f82c5040954140000e0001251001034002d00082c602d40c440c105880401280426070710354000d1100032411150404180a4003400300d010308113500c0c122803081d510b50060b0040d48164200c0d03032102c1d500c1034a80d000fa0106d0013040061300004005000007030b02049503000801d403407402944c03410501c030354840c43c140307900c001a00010010b0300004007a004243e010005501c01c09100000341c03009240c11300d1030300d2001240408007900761b629911032070b0a0342064012500a031913000107403461581c40e070500d21f04400071084d00301c0c0240010030b007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 904457796 1250 904456546 904456549
    0x6210c020a2306160903030503070908031201050405060d0c09020901020a08032806030309060e0f1917070e04030c08070605040c06090b0a080601111f05040506180d081e13050c 77
    0x20800007050860719104000346c19505c04030f0f1207800082080060014143c408105d4800410260040500c240345450241d81010107000075114003416903070050103c030001c600029040c11566003a1480b69400686030030070303000100d00e8000ca254015001c4070300007007441a0001050b20109187c4c0403400300b102c41900c603140000859403a441302400260000350184a2584966020b814407030000700780c0e502c2c2003506800a00c0d03a805803e5901546042090b0400c04004091404000c0a44002c064400149400009140d076000100300504100310f1001140800400c030003500c0100b6007154080040749071074030b4243c12001c6030f4020400070032410b107000a501c4c842c03001290300d110072640d02d6007250f807295401900c00c460414031034400c40c00303040e45044440f0b94a04007a00c41d08500d40010555090504045060480143c60249001d40154284122100015000c4c03c01691460300d003015542e0079001d00013a081402e200705100119a040c407120f0b940d5481e048500381e004200341d0b041c2c0444d090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 904459046 1250 904457796 904457821
    0x14031507021911010201061508040f0c03021305010f0f06020c040f14071d060a17071112040510020a0b1b1902031b0601080712050f031b060106210c020a2306 69
    0xc8c412800200c0340000200082c46402c026414140b01b41400c061098985d4001200043e040b0280e602d01c0e40d0b0740340100260500c2003000001800201107175500c240c217240000b9200c0410081190203a9102e00c1c041c880442250702c0701101405c0806108510b00b40140020300100c800d4002c20003410040203d00304918244007110b020318001e840c1ca00d070042e41141c915040c03103002480c040c20300640318003401034000240300340b03906008281681c03030ba19801c003401c0250748000b40c59038104540c401804140080c0103030f0300c02c0303400003214440303154280c5c1000c8c1c0d641d9091050074032809c0b01086000800800d150000094403100440b00321000c2840790040d1840d640319000d1007402d9017a40140c0c02085611340c48481568194081e905030755140e50100c160724a540d003c5000411032a21808550250b00c005000e0a40505218a400c100301c00c00e4031102c04400c22456030001c5840e90b1525002d0070180200311618806a1200c1e0310178242c6444520303003003c806d958610000600171440014010b02480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 904460296 1250 904459046 904459079
    0x1903050f0a050414070f0e0f040302210d0c03090b0603010b0f0f0a0e01060f120c050702010e01210203100e0c07030521010f0f1403150702191101020106 67
    0x84041091955000c0d81c0e0005001d001d08250f40c1c4104070705802010020034440c0b070002e49995036015401614000050881c90340090500442425030400d2000003030780032a045140c2084020112100c2e2040c0320a20400c2c4600600c0100b950328040c0a006450b4054210100c2c0c1c41c003a620885950381c452040c142a2901013100350340c0240118480c1005140c5881c80b40080720740602044451602d8a81540000c0c20a80140012520200c0401009944050001269614224140030880300710070060a64001e4003402814083c5400e0352241c00e92207118101070211408030102003c03404180103000a41c8195040302e104891603c0116480e8400242c040c0034003160480c02d46440b0058804580d030390400c40d420020407279102c01031081c024030200703103501916030002c0f1003203107519060000e192882c1e69800b16002907068512a2a40d42d4082150700e80c03184028080c00296440420032414030304a0181c8414006410184400b03000b00b41c00300ba000e1460a0300208109070701d5400ca4060820070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 904461546 1250 904460296 904460311
    0x60f1305090c13053007031b0e070f1106070305040c151227141e0d03050919051b09220302031209100b0a2d09090305190305 55
    0x75842004541400b00c0701e8422000c5d24508541885980c100b108114038001c3d10140b059030000100744144616003610442c02c880e0304040710301841c0380c440b102d0700c18031005001c1000d0008124100d07152038080c88681d242c8a1031501078900304d140c100c3d00580101410b641c240d62807a480b030004110b507520840440c2d080d80c2161103202401201110000141c0464024001500c85911200b8030000c0b00060840019201d02299400407007509015858075648403246c2d033000103140040c0441c803101141141c1c0310700d100d142c080341d181d640388141c03031914103402d10010200010409040178043c020605444601c000e030040f404800000301040580320303060714603d00110f8404280b51140350794000c0294014801d0065078201100c506000c601e161040782d41110f0b58002d40f5440801d5201445103c3e14079100b22201101d807424074102403410b01e060078404801c41e101c91404044840c52811001c000c02d840181400403420602d07008080d174101c3c1020750b24619002000304180c40c081c0c001d4505c00c6d1607 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 904462796 1250 904461546 904461577
    0x1d120c03160c0509090d030e060403080f04110307081006080708070b13081204081005160c030e1f080a050c090409021314102c06060f1305090c 63
    0x100c40e06400124108400c1c00c4500c61504880083c0607107038044c03414811450100a419030b0502200c0140542c1c1d4440306098160300300004110001c1d40082080360810f0303680c4281030f5240e446107085c038540301148003000d905204001c0c0010311080005202c20b070000555100784002555140c03584d54546a50103800059041500b081c085c40c01c9160161002041503200c02404c2c41d520b8540c0b50034049904d003150310f04d1100113030511024000b04082414806105410462480d002c0f5080d003007a01510101000c1000c00d40d140d07024144580260b0a0b1181c0c0200034205051401801040e5105d001c024503011031401c0c0c00040500900344115071194802004c00380ca0601c0a4040000801001404a0307000200f049207190180903031180c00d010114441d01302e80e05042c200c11103507002d460355011000c03441043c12240c485003101112051444400881032a103070312040001405c90103503071005d01d480000072855000c08204000a401100c1050303800480076215401d19490f01e02c2017060b884800d10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 904464046 1250 904462796 904462807
    0x9170d0e0c150f0d0c0309020f09040308070e21010c080906040f03031e150618030807080306010903050f03090109051002060f0901020d06090b1005070b07051c1d120c03 74
    0x80c0b46001001100c03401d4001c5890144004400e20444000c02c031030354002070b41c4450000450600c903081c0758600c2000c07102c42d0194a002c1d0b0b40200b001600500e148100b0169050003c100e80700c80751900d48091201048a075603408804d4924000c0c00d04040c0200011044008150b021002040031401b540c1c00c408500d8520342c8945007030b800340c0550f5650800c40000d10054203c0e8400c203100310007c91090011040101b031038500300030b011424442c1258020151100704100043c0004101c5000030382c4410a1341d100d42d90040140c66602040d0310140c003070301410858403550740001c4000d2001860907213500850684403420300100403400840310015a0020000c19040d020b165591a488022000090f140403d00181802941c049601a03802c181d1a64080000d5103400148500602c50a1510030305194640c0c40f8545c14900240c00e00086c840e0000718500c030310000c0c003010781d07848200341d1081c4806100c9810600701d20b030410404003a04e004080c6000c0c0784690f0001101d1288941100650406 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 904465296 1250 904464046 904464079
    0x7081813231f0e070e120f1515040b03010216080418020322020a030203100c1707050a080901020f0f0909090604031e110706021509070e01060f0309170d0e0c 69
    0xa500291000080c17200c003d400540c0d941d0b4200e51aa8910400c2c000350240c1301481030b6040c5080d007010000c0300c10194100400c1840c0c00014505801d0702412500855030034400300104e4024444c014500c101c0341c0c4034005800601064400030720480da1440c504e8480144040c2800b0200d000503950803640b01d10300b0501e84558080c584910000034001417030000300d00d03500e1340083d10b411840703a00c03c2c101c16107078405041065003069100d204e01c00c000d00d5051042ca041e240003007041c495100c00c08140091140441c41e00d1009606854080400c1c2d0340c4203a4a580c080c00054850308200c152038800e1000750005403a4500200c0c0e82c40c001da80c56100c10702600e95200d00c986840142d405028104440ca01c290860800d040100030014819074018000350015075a0528401c40014192110395000f504100421580b0103206411103542d0300c0c200d00d038249030382d03801c5024010324039009e8481344022030404070f4100742100a01c58101e240f8420845d089942481e80c0c1c544180c40e42c1e450b0300210105048050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 904466546 1250 904465296 904465319
    0x3060a090b060c060403021c030905060c133206070f1203020c3a0f03052706061011151b03100e01060507081813231f 52
    0x100710000b010700b810004114a038900d0301d44112420f5005a10a000b98410b20b4408225500d140440e4501400112040e0311403139a560009002d8030221000015454050340e17000400c04013074025000da9542c00346680c005910300d1121188480040c00d405120309109180503011111341942c056600102c0120984600d43c440d880d40400320705154080084040d811030a002065503100c0511701102c01005491016006656188002401e4800e100c944102c90307802510b06141c4081c58540818140d80e141e51807a001c4803040580c10215440c1c2c444034006032001b20366a03100f8101078405803120707403050008440d00104011440e80d2034001c1881014540010a0300680c464001414040b10850003e1131303040550044855252440380100c05000e2044142196401080345103841130601d001034848034010320501000c4a560440013042009130740310b40082d00d0b8540947c0604004214209200240c1ea09001c094030078850111000078504c50a80160800c026010b5010400300b2414020303481c60303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 904467796 1250 904466546 904466561
    0x170a110f10062102150c030f2107050d02071b03030206070f090b0f090a050a0b0d050c070b0f0402180114010206090d080606211006020c040515010507080d021b100203060a09 76
    0x5c1c00b0a017000a1480900c00700020700c0c03800d080003030056444d60b50182c1c80b104100c4007414406900810000e00040d86c0e4091f060b260201c03200b081c01a40c40d407035860040d0000d20b00a94107000d00711284400401c0c1a0049210380c86102940c4404c02c19000142007212222118000c0c1841d00f01305000c01030f0f18051110141c08c6140c40034100c802e8040e04c410001c1c0c4080b80702d80c80310342c0f01030000031140c03910341071030140c10b81040d03035050002d0804a2039510710008010061002b40071001402c005815943e6004280c100f841840c0441e0359a540c4440482c0340c07071522a0a580e01600c603401c0030500c40d44002a40800400450f40c81031981d840d18020050550700801c002202d42000d44610900900030004a0740580316222418a140b8580100a0b040a0006940034829807803e4104804404503c1214031890402d10b050740d5102c019150400c0c0034040c140708403003071910104901c2100c0030407100781045100c1380030072034a116040100c98400d0740300444510f5004803040904020955854001c4032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 904469046 1250 904467796 904467829
    0x3361807111f29180717040506011406070203060403030b13021603030f02120a0209060f0c07170609070b070c0b070c03020f030109170a110f10062102 66
    0x210303220071485140d07070320100d00751440040701d03500c0542e101e141e1048100c4885141c105002d200030380d440200007400790003138003540c040d2000701e810000381814451524808151554950603140f4201410000e03640c217424050700e045c188068114064510b8000b050340c0d51568014010030b02c5580fa640d040300582001414150050580030b01d0030000401c030f0000c1c000b9410708448580b51100c090a00805661140c081307103e48a204100302d0962110021006600c82000c0902507aa48110000701d0290701c11070707100211501c80440c086240d01000700d0000708880006100c0b2180c80b00d13030001280c0f5024240c420056543c03240504020310007940340a000e600340a034880c40e141c69a5101c8070403641d40301000032588485214000d00442c50048030307010300b485007079008102d00140c5a4038550002c205a0400140724000b0415909007403003420079000e840044000e50b1284080038041070355602100004850203810b1401c0818201c95040380300b00ba17034058020084080085800f4000e02103c400c1006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 904470296 1250 904469046 904469053
    0x1603090507080f10020315010c0302101509140c070f0c121a0a02040b070803040f05012901030c27090e0a051e060403050c0336180711 59
    0x2640400d2080c0800e50007411200081c1c0b65400c60210310724181181488185649407040c01400b60505880082c4101c40c4000e09201d1010705050400340d140801c0703801c20400d01424604201c2110301003070400e200316903000d4814042d00c028040c810752030b04400c4a0400c0300d480d0500c000008246e41043da4441140107051200003142c07211502d288068404c4030540382c840b46695100440c07286120141d0348070035030079421410b103814a603555450b071140240141c140e00012004c6000e000d140486000c00951000003001001400050601d190100040d000c0030008843c1e0b044030f00303500a008030760380c072445030780d07000055180720040d4000030015941d603004c045401c56011414605500c9541c24039001d42d0002d141e00c40b41840d002e481d0917821180c0c4044030900070315070844400300240607070b042585424003a494054142c501c07491401200da01191908810200b6920425041e070300780141541c408004041030103000c1030008422900d001c078506243c68500156200c1d02c01c45001000d030487e841a03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 904471546 1250 904470296 904470311
    0x11061b031902150402091602250f0f050a060c0519140f03041401050c0a12092309150301090b010305030d06081203061c080d321603 58
    0x48a00e1900207840c00c034240d010301c0812003441e540400c60743e40c14081010001020745020790100f440b410000d030031110845031482c4a00c00307550007440101109041180d803101c500310815440d08050003203129140d0003010014001c0b415400005910094400c00b0b03015135419490620704681102040354203070344c58014071595511900082921031040390141d00b12074100e142c524400e900301441e20b66000c0944e80b04000420003c0c107800780303242c5001c50908046440b40d0b8111038076030806501d13075401000007090680d01d00c00c468010126005403041e401455814145a1030346d0013200d02140d021950000094000030108510b590113150701c901d000d000070502070003d0741d80a10840c000e0300304403041d40010551191b102c2003486031000800048004040624405c03a18076010711015100034001d07061a000345c107200c164003032916400b66001c003005a483c1003d20402c0002c141940e10903101f000030850601041030303c13008c0c200d60901010102c5002d0b480f0417000041a40b0803103c400103041e210090f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 904472796 1250 904471546 904471597
    0x3120b060715061706130503040305060f010f0f06050d050a110a02030c010c0306030b041101051213020406270513020907081e0c07060c02010b030613050c030303041106 74
    0x280c02407920580c0b201200540382110802501e00396040403015503101c200d040703041d03040050403540000a18500c000b81d517090381015421407065800180039807048500744603a04980d405064125411420307070f0300095031908141c2038040380d94412000010382c18000c510b48040690300480e040784070b02c0000106110007028a9103150480e03282040942c20104110581d507400780280d1401c00c1443c9802c0043d07a0543e0740c2c5000d207000203072004e803030041800300190703859010b170b02103416100c0041c950522a20301030001400058035100c08a008504050001810000040955011500b400290411403541a290100405008102185602072041e000d0050b80364101c201e0f0090380e45944514039450501000c101c012450181480300c40c1d80c481c100700b003c100320000d80ba03180754440c07004100b0b40500c0c4d1080340034100c0c1d580340940c10301441090101c14210120408000c42c40760050b185c0105482c400c15469010441d8060b02c1c070300280e58080590b10f8418020580a4a9001d038545415403004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 904474046 1250 904472796 904472809
    0x50603011b0504030c09201c050f16030c0203090607061103010e27030f090117091c03020f03040f021318560903040312110a03120b 58
    0x850641c0400c2c80000c0900601201d40c0401004d0f00c007051080c020f07425103a405041c41d107120080c0044145010421241c80e5880f400104805401d0f0b510a02c450b003002200c0c0d40d1865416501d803071014544001c0d130640980240034071808414260041c0d0304041502c410700440d0750101000b1070760300b50781c0c4440d0144850103401841c040d003007040410383d09140c4059486e01e0425060080c0c85041c503001c8041254a00001c111031051032410300503074440020100580c4e65501d4014984c044a190504202c10f0800024000402d03402c01d4460041c0195844000e41c124480d00e81100121182000003901240c805004264041d01c0035124035520b102001070b0804030f90380413511f00000d08903038244e002800010140200d804400070050100d0070f44030b03542940602031407800e10500c1c544034500f03c14031446050900119103044001c3c480d86140c640122500c0360700c54041112900603d0400301c60749449404a086002080b000070400000c03d910309454a4480100d10f94040d80c132010104a00e0b16000d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 904475296 1250 904474046 904474091
    0x51504090f0b041d0c060d0b10080402010212130302060a020a050f030a09050f06070219050a030f02190b030106030915060603200a2a02100804030311120a05060301 72
    0x11500011948081e0302000103a0340000020342d00d482ca08482c8110350034000c617008403861070848034199030f500307500e0450f03001d085001c0c0140e80c01140c2161440480e600a07100c070388614400da0070b4540c2c1030101140b002082c020400c07805101d1702c902030706200500300b101c010451090140108d8141610980d5010f1030301e41c40f1140200143c001107200054280c20540e120081d020883d5030b07a4030030302c83d1000702c0c040d4050031601900c20160b40c6154001c0381c040388080c4010b46005000c00c0c845540301e045c090000c090085049010b00034584c04555548110b01c80541a40ca000701560b2469107000e0045010b0181030a080e2402e20400f525001c40042d20322032403004203204d440224426164004420070a425045030005494041100d4019664040d85a046089056080400c15180d21600c0c640c4032005440003074001e260720a940c600c0343d410a1109102e54400d90341405000207803091048140603000300044042c52a00224100d80011b811181d481100600000b940744d040003880541d11001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 904476546 1250 904475296 904475321
    0x280f2106020c07060c030e030d171302031c080612070611070504140a0e010b010f030914060a0501080708011b031a130608010c1e0c08070807060b1305040201080105150409 75
    0xc2e030610745c04141d0840c0f01032034600030885c040c0580b000040e401910701540307582d01d02d555070680c10024040ca031405c7e00660900d03070007030100c441d072240030f60795210603190000d01c40021030304060020705180317002100c024821a04c81c01800d19180b520744181c3d80c007d40400400c009018005010031903407154482c00a400c040c4104115280c00d2500a00040f02c06415104c50240d041c10354410007a40c01c0103020041c2c4010349000504142642058950b4490720010400c01d4040c0700d080c00740400154004034141e0305110300781c41119944030340b05401c036282c0307480c00c0da0182d0314182100080c1d8004e034000740241018010000c00004030741700040c00340d40307541da590089965404090000c07500034424a01041e02904102104000c59000c0b4064501140b150008000c12075140204100140302178411007036008a42540799141c903e0008041c5c11051071440c0546800c40240c01408564000c81e8060758042e110407525900b040240012102c0ea241030030f400305400c000001e501200c3e4403460207203004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 904477796 1250 904476546 904476557
    0xb07020d080610140f0f030a090c0f0f090f0e030c0616031e020c0f0f15132f030307060f0e030306150a0905280f2106020c0706 56
    0x6080054042c112501a504001041c00d60940211440c1e59500880100a0b00c07543c40c40028102ca10400f030308215100d4000c0203001104886170007400b01c1e2845848a20709058446401e0b014030140c520a0707884108032440100000c1c2c45c03aa10925007522490404500f00700d444480a2130f681c40805116240c1d402a41040309520701d00040d81c00560551034203008801010342d000140c0d482d0185c0083c541540007170020b8021000f00850711007510070b0300980711035101c424030303131a26a03010b00c00500500e110000000c03041d40e02d007500d400f0850307401104201072028650080407003460700030021030100400502101141c0c6d0800c0a080c10b03078071640021075103a0191510000340c07610f1040c03403102e940c01441809940d9a8000c00d003510581b1b600c0840e030700d405a5800449403440d8a500068100e103520fa80d0300e52080480402002100445c002c84101c00d84d5048400b0f02075042e4440c0c6a003481902901002c5480f6001444810901555001d824801d0400c6018100900d5070301c00ca000c00c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 904479046 1250 904477796 904477813
    0x302060402010e3f150412020c01090611491e020a0b04031d190902130b0c0706020609060f0708061f09140a03050c01030510030b0702 59
    0x40e408400603c030040c06031880d40460042a1070380c08608407203040048181d00040f909a6403500b90034019490b92038a03000c44401c042e0300e2440d1514401c00f500e09032440200c0c2441c9014280c00001c11101c01030040e511810000d141401c122100d078201c900b803c03e1070140358103c01204080303030302e41958030380e450215506040f00c806e14600800c00d44580c8481c80705100790700005a54200791500d4016240110760f80701200844812801c0440e2194010301340b440a030240824103130b1120404251400c0300c4820800401401d04100704042c129801588201003940d05200300c00c225006403241400b0748410b05d10182d1141507040c41e0781c10512841103c2e40c4031040820026030304002039038002d404880644800c4c1020314015401c2c0300300420f41e1083c4001c1c1c5e008038045071a0603003290040141000300542120207003038000d1040300e803841303030429010b0318604d01851403511a10300c1742101d511800415001c1c0c8040015000740400502044803965039460000101d00c0d9602040e104281c150302422010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 904480296 1250 904479046 904479049
    0x12111f0503070201180b0f0c07050607050901030e010506101d030f211305100e030d0c0c06020c0d17041d0a2d0902060f07210201020a122301030302060402 68
    0x40d0000701180b0b5564090300f0714440440c180106d99900000024800b42450744c1d96950200c09115451009000e48903070010002d01c641c0c0308e8060102c0602c241e905204c003850b462890703400d9403800e0b0389060b84018032030700c40d402c420302446081001c151000d41c10580b00c862040020b0a010050b242d0380c200d60442c4590102541c40b1150080c950035030700101c1420003420001591550048e40a82400354903091008100c0700c0c00355860f681c0402c03000f0100c0d021703450850301c010000f1789101401c80b01d440307040e80040f4110780080342c42e0103000c1024022540ca49450b440d1082e00141c41031131005505420840415400d117941c1040102140014502003242440380540d800c8400c4500c81e0f0401d06c09041c1c3e045a909580c460343c0c0c4c410a044030700400c203040e8900008215110f001d040c00e00303030782001032050204401138603c9040c240b0498150165a01c1ca014141d00b40d108074919000007655100e81160a80004e901c01e801c40700300850741d078002c1c91040c8104040c00600781c0007940581c1c0228100001c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 904481546 1250 904480296 904480301
    0x3080103150509030703030b0a0315090605060f061c1512121e05220f0504140c1b120a0327110f041b0503090f010612111f0503070201 59
    0x40082140c07040085280c41008103450f4000d0450040c1056140d1028009075507468101101954101000b0419200c11110000c024412040d0455140d820704c000551a4135000102a015642c050402403030409480c480009107088000341da40310fa540d5401c007000008105280c44c0103425022424101d80d80d0908100354042c44280011041291001c018400c480b021070804005030058105161a0040c91041c0c030b000b81c3d52a81e0710704940807030183c001440c80011508404885060b40c080000e088c60380c0c581d01054000b101c240121810400c05c440304038076140800305907a88070005591142289040d42c984036441303100c48030300198442101090001c1c100b04869072400341104010400090381e42c071540416182000548124070f0400010240d1b1100d40084000700c0410000035010314919074083e007642c00a55910344a481152100c0c005c5003814410401540c001c92036071040b8051030b41c0c0300c4400800c21f086103908940c1a010490351462034005054011003075855864032440d100100a08 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 904482796 1250 904481546 904481573
    0xf030203090306090111040303030504230c0f0415031205070b0a0903030501140d03050a03060f0b042c0109020901110105090705191d090106050a090506010e0907051206010207050d03080103 83
    0x722179160101444004642508640071a07601d4100814a070707440d81018060081e50581c8206541089031136003460403804640c038130b103d180440f0355179201074100c020b10040300c894490310442144910310520102d110b060b0b4901010388180386c41460001c09640740c020404082e154804400d4590810a08150f0180151070240c00c1106411215001d4003002881000d0400e00190901c500004c518800c28820b411a00160410200b136a4603540e42d407034150b980f030744144110554066440030848070b5a00304403503240c01c881a0000c445507a404e0402000c000d501c41d48019050089500b075480c804a020b0041c248126a45005005000d00c2c5c8010311480d4102c0d0707001075818a5400000f03101601010f0307400b2030795200d02c0032107040c544e0760540c026004001c02e401c06a0301c1624a9800a0315080a0b08072070300c15502030f44c0d41504000a8014402050800ea070001702103801032120202d1910341c410038a0b0300020500c100c038034840d601c80200c0e80c40542c9100660000380ca590040c810300c44200368130785 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 904484046 1250 904482796 904482811
    0x60c0f14031b1504080304200a0b0705070902030403141809090d020f010b130b0a0806100f06020d090b1e210c120f2a071b0b040612090f030203090306 66
    0x2071903d415a101c01c1e042c407000380018902e8828102020000714a4005102883e001818440ca42783d1104006842504114400c0781e0345c0c401c40d040842c034001c090007600d00659158070340070720301c08584000e119241c11692000d41100301c2120510160354540c81c00b40c3c003c04002d0090301995120300340081c1003003010a010445a030422105091644a011090498015445c000500c45810500290503804c055011810901c0f0b8803041c880c864055603101001c030341120684da50f40702c3c1e6591003680c03989424030180b80400c0c2c00310710410104038824000c1c444c1444071300551700c0b420302d03126800b6416042410b040c00381003840c0b101240c00d138107036100e50794102d00700000c640c0c20b0296902241a81c140024000b044411124005c9410b100888004124030810a0030380144c08103e80700d00d00c03150b003150034240c6017694074001411076035414040c007400380c800c40350300180b405040050a90740b00003641c44429140e9502c0d603894022410b406c01c3c501e110352090740690343d1b07019443c1c1058581003002d042c12 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 904485296 1250 904484046 904484083
    0x8152e08040b011406040e040b01060f020f120903010b100305060f041503060221090607080106030510050f0112020705070e060603010b090415080a050c010206010807060c0f14031b 79
    0x1002c109051015030454103404441c081000700c40000c100c00340140d40c8031700c07e13600700501440201b101d05807903d41030340c4180c0c1d50b001d039034503ca1070100c0c1d0b10030111b00d807034245820880880d4a0003140c5401020001006030021400140407004a0110001e0451140010303554005000302c41c6440c582c1503082000444046c021090030183c074103640d21852200804d82640055882550503003a1054031b1418106a613030300907032800c1c400c000e1b1242002c541e04ac3c00501c0603000860340c0d9002c1c1c0304841c0100d8111440440c40d0381418144800003c1d4101901c0c107102c1d4031a071601405000f40001c1c030231984a040075007007003480d040c84000c881070701900d00e034404c074014001400b01900820580f040e1220898003c0790800240c0107200030420290041026805004c40d25028480005146c021110003a4200c1d01d140c0e83e510200c079100c8459019030b50002c0c0c01c200710000403032000582000402d00440d00c8540458220703a817185541e000b0400d099001100317013401e00b502c180900c00c0740100c50303120214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 904486546 1250 904485296 904485301
    0x1e050d021e07050f0d110607080406030c03020c0a120917011401090209130b0d0812250e01050d020d020406020d020106051e1c0c06020c09151008152e08 67
    0x113040e58040e000541d024180a600074414049286120980b244020702010383d2160780c0d041c0001355600c140034400102e81021850400140720f4400c440391070311f4000182040180c240d68416520b000340b0366007800c11000718408039a000c1d25090702603c160004d0000110840088038088190005900840c2050701c1809518410f4030350503540d881d003404034103001400000c0000001c040e460301d004058040e02c4013081240041c0500344485000e51000c191202d203400c907112042d8120352a6aa400c000181450f103501141e5000380f01501026001c40c41c05801c2c685608036010490300182d0200005a10091502c81442e4080c80b030341c00a00820382d40d41c0c4c4649441c10007266850801ca8005000398a0001c80000c0d040d005078000d0201644407001f0340c1500d0765000c00030340d5480d2680d20188185041000314401418000c5220207140c00605040d8000c0401c41080d034078060002d010440003510305210010540e150559018408641c00b80e0b141c103030340041c0e01c82d00304036214501c0300f0601405805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 904487796 1250 904486546 904486549
    0x30d051303080118061a09010225140d05010507020c1011031611041103010519080c010f02190f030f02011401260105010909050c010c0305071e050d021e0705 69
    0x300503040d940081500141c0901c1d40021307000506580c1e0065101c1b101802c3c0e14040e0307000007402805012402d03401c554188404942000c0b001c4440f00320712132491040102004011030029048110310360040c240180d0074802e450750383c2507800c22241c40d401600f01414154251501c07030b1108240b68020320b0710360000601c00201c0383c0d603480fa1801b240404003c140d5000700b00583c044a9094140303002d4418003c5050f15408000d082d0030a0107002d1046242c82000ca0398440071207849011560500300034440c0c1d20f817001c019202403110406080850280c0f495603070700c41d582100803504481c447d8191100c1070003135050043c03002020501d82c800316410400401d05a0380341000ea10705503019008441d604150300c1c42030341ca080d4030000c0492515424040000340112065016900380e900503810780711013500800046810782070340c2c100180481c0c0240302c46004074103824500b01713050700d402c924480c10406544400d40b503d440d01001b00016802400d40700111461001c1d080300c40e0b0441401003910504000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 904489046 1250 904487796 904487807
    0x414240604110409020a110c0102010e06010b09010905090709050906100c0b190e0708010608070303120203060d331b030906060b0301230a050a0e0402030f0f030d051303 74
    0x140320510650700d480c4564400381c451800c0341c0052454501c119910314508030080c080b100b151141060b203001e86603441e0b0281d401030041c00c0380b030007050b8082c115681c00c240b06d1403040d0304001d030302c18104407c07440c011896403180c0070020300820490b00d40701400b6250030304100004c0707001031596014a4940224100b19030300034003949412580011700b4150307503480504540d1440514450491a1820312540307500501c00824031b00e080d148101d0082c4a09911011701d02e030340c1c25441c40000e00003101c002c000201e2070807981c0034580201008003400c021403007944409581400c010030a40710581e401e492a10328400c142c410503000b01204e00c0c02d00904012710090b84140340c44090080c141516907910030204040d82d8402000391403045a042e8a0b540c45001d009282240500c0e9540d80440d0058800014038156070810b088500083c40c0c6504182010ba10b0107080a020b00200c0e0144141450000c0705181400351001d0140403030b00454448141012042c00c1c4d80001d8000040a1402040c040102e544130 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 904490296 1250 904489046 904489051
    0x40b1309020403150507020a0203100603261911070b0418050c0a05250c15030e0309061b060403230306150c16080604030305070e012109020405041424 66
    0xf5400101786d568040d0a0303091030345001d03009502d80620b80000d10070348500d901080980c1d0280115a41907800c1c1c6055840c803501c00849030200c018180a12401d8020140103043c58422a14116140b224180e039000c1c03418905800c008809071000c034091111990050808002d10301c07066041c441814a10003540c064400c002c040410004000380c0900000700c11a1340441e81041c503060300b103030700085007026180c2000d10300179648035412498190540c0c6200b0f005681c8010b608401662800e952481000401e40c8558241500721000c56290b40c40744206002c000d218901036141c0f2102c00c00110000e606148005030721009031038040c0280715081d1184804880c030740d180b40110542e0317100362609540c82c00d1032840410350603c00700da20200343c1010110360300c0d006a100307840502854641c040300340d0f80e0502029030726001800844041d90000f0520b04002041c040040340054412070315004141600c004413001c0d40c000c0e2281007240007038441082a140172281c140c018004a030707440c0a400c1c01c0d50001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 904491546 1250 904490296 904490333
    0xe070518040f09020a14040e0303150d061409010f0b0d0305030606070219030f03020c0a14090403050904060f1818170d24050906130f020906040b1309020403 69
    0x845060020002803640003d000540080c42456400d65903182c1c0783d12800f1204a440c01603040204900841e50300000b5280980042030100c451030820009002000072401c10035600c1c01c0e00c6002c0c00020845941495005681c84130000c10b440081c6009e01043d81d0700c03881c045014280001001000c80c1d8042d0503aa00314000303c0f000e6644d094680000703880c600d8460859894100c04000c00030410170b03840d045903075003031080e02510f107104186010001c402d1a140301e90803000288802c0114030385488050b0a600510030300701203043c580e45002141c11126260040740320004000c0c814045601c04c110443e0310408904424401d1210b01c0aa180380361201c03003001410b0390382084111144000079410748038442404035080000d001c85014020000c6030458000701381000c0c42501003441c1c1003040b01280f240a02501100d00340102900c410000e1500f0000f100c4070036801d0001008036035680006000a00c940d14400342c40c4d180b08004900100c840d9845402854410001000091300401924000340740 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 904492796 1250 904491546 904491551
    0x2109050c190e0910020c0709050a1104050f010c12091a03011a0708210114040b0f1915052502030a170d050f0108070915090b030f0a0c0e07051804 64
    0xa480d11501d04d030800c15860315124500105440e04441400a4500220380101c4c0003803060761074251180085900b0032040720b160031010041402039060200f409050144103240800c0c4400598a03040980804a0700d03c000088014600f0055000801172038181c815468007440c3c51540740c60391010449009001400a10300080f4415043c41f00d840c0030b503000c0c10000c0c04a24012621200c41c0c4003203140c2402980110400c40b02c8001c2c2c14286071040c407003242009403a2811310031610080003140c400e00350504a01d0980c0204c08508160b912840f001d000581e030300c5103a101c1e503401d4400303c28000c03858408844240c580c40683c1c05a40c1c0025080300c3c00780c2011005481001550700414284203201c1030b4404a170400040c0f00307170603140100c0ca0741224001020759a040c1d44404113101611168041140c2c1820200380c00e03c510000c1c1d078400c00003944000e0440b24281e41155642e42403040191040e926140842c008008041d9001c08442d03018050389030140c075190340803803000d0062400c009602e0182d035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 904494046 1250 904492796 904492801
    0xa0b0306011d1c031202040602030406300b0a09020d0c030605090c0f07060204080d0207080d0f05120604090b0a0605011b080715150b0c1905100209012109050c190e 72
    0x10b002d240941c042e04171000c025903840e611107901035901c0d07000d8401e0000003400c02d0100c0210340300c24901c040d182d6901c040d100900d51100c9100300c0251250038042ca40c48000c407980000c016085200511490844030350100e07248090603401307030848849070301441c043c01000742009040d5000108454644101c40085511000030303040941c0203000f55001483c50b44a030b241c145036180c1d00040d0205c215900c1c0c8080368580c0003801001c68002e5018451040418400c0c0241078240c04103104059000001500008401030b440d2154500801305580c00740420380d55a40600842d6800300d00c84580105090306122580100d40d1005072900c04e08602901ea150340c4032a60349600000c0d00b01200648c2c0301451010704540712101c0c403802d46d0010071080c1c11072250240c90300019143c0c44080c0030b03040d000f0014180013503201c5084400b960140143c41e041207a0303239103403414171000800c0102c401c400c842c400113042661860083e15090030040b006205165080440301a44c8201c0500c0050324001c02070882a80c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 904495296 1250 904494046 904494053
    0x1032907050319060b030f16090b0f0d05040b100609031101080711030d020c0c090601020c090408070f08040303030b090610140d0501060f140712050f090a0b0306011d1c 74
    0x1e0075000f01030403080c0c1000400960303242044051406494250445039203600c0c0c0828008981d54605070100215140c80c40030410a2a25805441c90b5100c0280303051a03e0040c0b0005000c0702c608403401c842e040c0b41f00051246551581e065880030301282e0412031111800c689600c03032008039105205040056200025007011b2040000020880040e03040340d8950f1170180102c0c0194001060501c1c152091101240103454039a50701d6014a0042c1c01818800040c40144074160b0802002681d00d60001c226500005041d2544c88140c140100260ae44590a500c0d0090607640c01c8440107204080c2202448910758a039840410300a146003020f812031002d10304007001d64011011220151498400001b40e140d070000c9551a03035036240e03956541d89494603900d100303d50290030780240c80414003141500345240508010a060102c905a46080c016544002501c0340404c1e088240d0584001c420700ca01941c0001e50071074108802c00c9550f01e80043c40001c03803e10304541e011030820044c80001d040c2070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 904496402 1106 904495296 904495321
    0xa050f15041104110f0c0d0e030606130b030f0a06021206010206014b05090a0b0d02041a06031e0703020a050d11041508010329070503 59
    0x24400b0b60050100815180034141150703101001042d29220614016001080d811001003d06844060004000000440409000c1d600c000140503040d0307245080c2c50703644020b0002c0002d0701503107980042d180284409000660340650340c060300c14404190020140c00340307410b1aa0200e81ca07080012039852009101e2030203401c010342c4044510050703115800c0c520070b40008008482560310020700d4540316210f40c8221102c001da00041006091407038241d80e0040c1c00308410807402c0c00740070100c0c980302d060040c001e1195030b480403030350303805512402118042d1001901c1c0b02d840f0300c0c200c0a03000564184450b00400380c10740340001180540310b40219150204603945041c04c04d00c01e00408800344c000201e4495040c070040c8000300e0000306616161013011055030380c8038480e500d5400d210702d03429003854041c0701e01002c0000c51103800c1941d2100b40e401008620b4866030366a20900480c24 = true := by decide +kernel

theorem cover : BRFrame.Cov 904316546 904496402 := by
  have h0 := BRFrame.cov_init 904316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 904316546 ≤ n) (h2 : n < 904496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
