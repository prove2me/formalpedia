-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5421
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:48:58.197914+00:00
-- url     : https://prove2.me/submissions/6c1be2b7-dda2-47cd-9ad1-a0426ae491c9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 974820143 ≤ n < 975000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 974821393 1250 974820143 974820157
    0x50715141303021012050a06180e011b020a050d020a1502090a030b07030509070e0c0a080a0603020406121a010b03040b153604120c030909182303 64
    0x51000068021484110310081c480110f40c00340008030001560b01c8050001c00342e020460343d0383c0d41401b000512a158501c02d1405903284001250240c920b0780d62418002c040c1480220790541d40c0708a48907642010301403108003151581d0040030582c04919000b410301c203a10400e18195480450301000181215040071444c0340b00d4203005841d418408006201d40341154800390a0b280100c060008035903058204034483d40d8031508440340ca5175a50107504a0681c01c550600e000e070814824851494465604a50840130039900410002c2c0c030381e00005c0490b043d55101000d41c1842031002c0040080034660161104680645d503201517240c004209050f00c0000d200900311100d80f00025640040340b680a214024003600c3c4100d082c8503944008031540000924510a001c984181d054410741d03140f490b44141e5200314100e0700240c06040542d60803410343c00840a004081c0e2011507042102d101e02c0b4120041944100c01180b21400c0c070843c40090400020741444100c000403000c0d00b0700000f21905 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 974822643 1250 974821393 974821427
    0x160e01050a06050a170403050903060708160e0a03050304121505190b0607170d0605120307062a0e09061c0206180405100329040305031b0c0109050715 66
    0x11340c0c000d104c1c0483c1c0841c481d1a09445610402d0306200506034130101400c1c400c3d000350100d5071507444810059a80c0101240c00785d5003010400340304000d440c444e6404151501024221b810402d44a40e1498150740003600700400d06030043e4801006d100000001c41da03966005d0b01c01b000345d802d26440140b490801601149561070302d03000098002d403180c4003280d40d819000720021200309440f19004c00c1076406150740f040c003070341083c1d00800c182c1f0b450342900143c00b444000442c600340b0190365070340c0604040301c81c0003d0001a00d046000d04281c1c000c003502041a65961442c0704580d444c100028180050070444c028000c0305070100e010340c00c440c60052801d0701115610741340c0d51806680088103409102c80c50b00030342080107203c00c09074484a4441030702d2103600801141c2450703400490701c6c1e24007810740620070504580403601290003140116009402c10282807403640716804070217031300e5000130340e000804d0b0b644250090601c0b5050114401170000750701040117401c036800000700001654118800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 974823893 1250 974822643 974822647
    0x30f130506011e2d08150a0504140a0308040519020102060a1104090608062a0d0203150402070b0601080106140d02090420121005090f040c0512160e01050a0605 70
    0x34030403801403043e0003e1440d10940550340004060f0b00001d101c0c0c41c0ca00d020746220000300072070040d402081e840d0349014083d100002d150b44080c5601d010b0300020340140c440d8400c000c2c8080c02d510051101402950281d2154445401c1c24a081841e10031030300200300c58440300c5090400142c0c1c0c0031034059000351142001045842e0fa00304403900c94407641c0d2201d501c0a181c81c400040318040826102d100360303200740c01c2c2590301000c003c940b0710701000a0310a045c004002c02100c0305011980d80656002000180c0000c04000cbc80e4020808030f070310516050301c05080710801c1103c0b9680c4200281e01401c1c692030080310042e03448518009030300801070040b10f06500030800884039101c641c00b01006074816440d4005619184481100c60350002c454620782c0e60403100028a551680706400d403c0324000352080718240c0c1c40c05105104000083e104a4129004080c005250f561b0107107c07030a00400315000d0614201d07040403003c4c43e0b44142e446030009944250041040b46c0e0341d0b0170f001c000c685260410503 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 974825143 1250 974823893 974823929
    0x606090c18040e0313060e09090309011103091504140d020f0103110706110901200606010f0309050d0207050f120604030c0804080304060207030606091a040b03070503030708030f13050601 82
    0xa01a009501c3c221040b444082905040001091144070440e00d141d00c503440e00055103401d110503000210f414160a61041014100b25403150140c00e050322051800c1d0703400e1021040000380c0400c8012100d03a141c82d0003040511181040301ca1014141008171580020107460f50b02056004014010484c141036545040101102c500422181c041c0d900c0b034420001481c800d04440040d810105200703001501461400c0700702d0181c90703560001d1110030f800800070766460100445140039072140070420191603401c0d2400144007005510080c0c4265005400041d040c8024070241e01004411070748104a010b04020015502080303175a04035415107070a070b18140942c10034a04e54856a8040010352100180000300c03a40d0100d0b400e410b5074440d11040c0582960380c912030007900c500955000704596424007900c49860310b540304000310580507064070742c82c540d5000080c0c11904060710650302d43c0b40020404c812030000e400c001d03600003408120340311003c12a0301d500d50f0b0780c20140162610b009500f1420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 974826393 1250 974825143 974825149
    0x10090f020d09080a030507140403120e060a120c03021608181806031002030f060f120102043510090606050409031e021903050702300606090c18 63
    0x150140201c48030300384002070581c500b0751825848030b001c0c440003925007804102154816084102c250580e61809402c0c2420f64803030400104100800b04180202451003440945502c1d000d807120b29015200c840c43c5100c4070b44041d05580d100140301003018070400514007142200a80c10b01d0b0260000003043d101c801e81c0014400c16a5100c80d09540124441d86825011200e603610f00d104020907015a4280050503800f002a400203480740744081402d000081c515050031b68141500140003021070002c04020000749003241c2c026080040c1c40742c1d007102020140b00108000040710603038440000d110701140d14205480c0d01180305188601034a422008041c803c854001402030040144100443d50386850007514000450241102100b418144211060300114031245030b00c4428040c1302e080081030390200c600d0ba002c050100c3c3e020401c814401040f9046018480401c074207405216100c0c412100c04a2a202004003500c1c030510444040200c050484410fa44d54040c1d45c4010307241c0c0c03030006000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 974827643 1250 974826393 974826397
    0x2503020319051006031113170c09191a06030606030a020903030a090915030203060711100203180f010207031403040609150b01030c020a170c030d05010b04030b0a020310090f02 77
    0x14141c0024208014029648090000c0104403070054400b0098142440d03691982030091030a8030001a00800e01084103c101d01c5254130001805001c0d00d0f8014206000508811400d0b203500300107102811005201c4007807803040000751500544031808d06034103200001c90521004007060701650001c804611800b51030b80544542800040580c2e444040c1000000c0a6801c07034803603400d8850802081c4062008500c541205482d0080c0140910303a442040a86803040e044040307000d68422005000c0040c11503101860040f8404541001c6401c82050460310302038040c4200e6956034410032040000a811440402d5460503501d0309588a45d11401c000c2c0062000090142586000100e50805c548899201141000098a08012042111000300c0c1d03560304080c1d00070b104060701110264511b00c5403000e01800503102c1700700d03840c003c80c070f42d485c1098600a0703220403000310303000c201030080241e000c070225440040e5610460a51078400c003800820419441180185955030a000340e1100701901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 974828893 1250 974827643 974827681
    0x21e060706020a0206220f060b121603050d0206010b1909090519050c0c030715090c06090e18031815071b0e090d0e0121090b25030203 59
    0x1e0115251088500c02030b4907680110381c2c0c002805001c1000081c04101c0c1401c0307950603a00400c28a1808100350b40d400d00405c0030000b0240d000c2c4805550086119007000701a00300e0f90400e90001a682c6507141c0b0340d10f807941c0c008240003550000001807094900800c1504d60104c4049a40d5a00d510002400c2d1070503900c0342c006450040c1000c00b00468110401c07120705076524255804c0016030341b48000f5205c1809031510b510301c990010015100819092940c6001034a0200c600044001d090b650b50810409154031900109180d048104070324061110255441011034040700c0e101c41d40d40c8e00700d94880c410a010552504c100800f1081c1544600d18a900541c0001d0600c0303a4500c814106032286406071044401c00c55081400407070740c1da401010450064100c44010100b403400d0040a0f55218480018a41080f88524420100d8a8442051201c02100f518009015105030800c2050700318024446424510506801100c105070803481405402003468010303200c2d101c0c001c0c09007410798556 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 974830143 1250 974828893 974828903
    0xc0204020d0c090b090d0605180a050d0e0f0d0b190606120605040c02190515070c05060f16050a03180813140a0320030a140c01080103021e0607 63
    0x46124040301805038009003158159458100d039940e59038040132920300c03603c01c8180c0c229021010f81000501ca982000ea000504d007900b0b02c8084a82d50061480c00024400c1922b89034042503c01880940003104a05082c60544204000416480c042841804c1e020381c02810030b5050302c0041c2da01001d1a5900c1044d000d403280911190342e1303691000344404c9a880c4905a200e1408000051514003842682d803200d101c0d401514107021041c0c900886444049401e682030b00400c076551091a5001415074469042900c0d000750140c52418814604179006100c4105100310105000c4004d880d1309520b03141c0f4015181030344da210807160048001c0c1060301d070451551018050000308000085020b030940541c2e1018254145588005000625440c0d01859409c4880b00106001240145104903140d58074002c072019045800c40120b4a0450740c0b5402352035900489007040c001075000d002401c000d20313007441c1140b07003541990002600a80c1d0180451081032060440f0042a118041541c2d01c464101c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 974831393 1250 974830143 974830147
    0x30f0513090b0310090b0a020a0c0503030f0703050f0906040b090a050708060414070f140a050d03030902030c060a1b0c0e04050601030b06060403030e040b1324090b060d0b010c020402 80
    0x9500070310041c10340c80300024401e0107098101108440c2e98403803101401c1d00030f0010f17403079074540c2c04018000b548094499030402013040c0d0240c0c0441c1c0304000a500030b030315500144e07240346000e00c0c0050460304064502043c1800020602c260b05400140c1c260304640c03c50307003027491070701e80911861402c1500000241680110701001400c10720214400f842540241c83d144400104801034545443c903500614504401150702440348210001110740c0318a400b524118802c1c0d291000144440c90310402200029241d42003d400c60409100d80c1e8281e09080e2030b510704080403114040c2c800340f894039040051351502c10b00764080c070207410300301001860700e0310401c0528241800c1c0300e40c40d4007003408107642403d81440400c0c0344d41001c80c00c85089070b8050ba00e100b20000320104210107407001c0441680d21a42d00c805100d00e00364688185010005111074490380c45000445031081c8030590b6000d44103c1d0314148001c2084e0316120100e404030400d400300001c0c203c503090010327601d4810002c40a50413503c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 974832643 1250 974831393 974831399
    0x521070504120b09120306010c080a02102d0b01090509060409060212090105090d080a053408060405101e0e040f0201030516021c11030c030405011b050a030f0513 71
    0xf524060740201d29030300aa9422030604081200244402c0d1040d030f00290042c2030344008900c045003d4a60050944141c0703840a1a90040c101601c1607101c0c000d00303189220741891040d000305a800d20b000d400d0903c0502c010551440040c0c81c40c1c203688135150290308583c0c00101c281c2c0c4e580c2c0c03050000541c003c2045440d013411a020503e05581201c00b001e00f0743c40d26020034500701c400200e02c1d003400c1407030b07031004040d44e1508900030281c00080d00700900c00e0380e40e00300c6103040c502c410b020380b1109058110810641c011400001e001a001900642c05903103400e00b4001c100c40c0c0109a02c1c2a149c042c511181c0590f86042e4a10205141d64030107442ca841101c00c0c030041010325401120860b000342d034188500c1d2212188011110000300158015a006044040c0c00b803040c210390265200d0b01d400c01c4069640303403c07840c5045074801d05081c3c4480d08002000c1c4020b41c1c008a20442c059500c0c904114003055039903400b65a49060f42000d400d10030003040b50203126200780100c4040200c00b001e19405565 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 974833893 1250 974832643 974832653
    0x602040f092003060a0b0f09150c011d03030a0c050403060f0218120604020108150d050f010c0203270423220302030919030f030801060f052107050412 66
    0x8020004290599080001d0940b208008050b64094803000303001400c1240b92003920000c5600c4100c0c0d42c09014420300c1518040e07559802c54000e0401700c01100e07562108603004481c03c440841814032110b89a02195803520f510001c1901e0384201031000c009070a5204150a0f42c007800380340d0004040d14146201c0c50500e50142d0081d0400b403202d2204103014090000401250f03a054207094100d03035110200040140d0702c50384c140f680280c0781c40201c01c1c0203525003011403640305034000181c440d40e01c1480510b009a00074420118220502e20103941030507002142c072490442c151010101c10794071212054400d40d2141d009800704441c0c0028038000001a00d000250100c0031a018840b41d044161094403070104801c80000195142c1d01652401c54814104040044007540c1240b410018680203c00901440070b1300c2c501e14002d40301e15250b176240440080201120502020030003400348040301c01c0f240031802d1403c0385210311a05198569540b00200c4a90056500016152b54000b080c1420701c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 974835143 1250 974833893 974833901
    0x6061e040f030218010e13020a0f27060b1603030b0904030e030f0c061b070e31151802130903030b060405031e0c03160e06010206010602190602040f09 66
    0x34802c4e68029501080d880f4110b070851001d20490345000110f100292120a251034034004042c801802e40c07800545422101036480d980b504001040c49400c1003000c842141c1d5002c0d5100209035400501800f03040c0900d5204600440a0b0a00c6441d68642c3c5d2a0426010b500803401c8044054a80b2805152505005100d48092007116002c2d000e40708004001030808560059107000180c01c4501d000860154031410400d0090700072024000c018000c54581014a04a4050b00e0407421000b0510352081494190410143c00091a1840c0b4071203800000d290b90101d940c2108841400a034401c1c52041c42d03120580e03843c00c0254080054100d001c002c030200d90256040c680240d504200d0040f0b0b82050205034491401080e905a010000e424100201c55020314070208020050320810b03403c880100e031810903c1c014440c481c00c08450140305860009420a85c0900c007403000701402e52500c20302070340b176120310120546480b03032425480080c01070980440300104581d102407068980d4401ca114003c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 974836393 1250 974835143 974835149
    0x4030c05011b030f0b0121020c070605030f010806070c020405060f0310050123210307062a02031201060813020d080c0f0d080105060702210105161706061e040f 70
    0x3c2403030100c0390100d644aa114800300444181c42d0740c092428848090011807920b242c6008001c0e4007040b000d200c500061050400512142c2c5a0035241c0c24600781c13000440ea0141c02c580780e5580508200822541c0c005280d601d12a010303113001035640c50350000701f84041c1032090603075014800c603000c584064019605c00d0b07040b1070038041440100100c0105040011450720784080e4064030301c140001d0b8085910305034503240302c07452044a191071010366604d0b059449400e4910810110303822015100e11400031403800c0b003c154400785140c52948100d01001c4c00307041c091b0030100070940c400a1404840005898503507174001700721049102d82c9203080c00d0203074441240314030a40945203041110240014401c40007249545644c1840ea08050600042d0b03046864240c0e400554402041d07112102d5840c5844843c14050010516290900071090b5901c9004000820081e40150070f03034141c0307482e0144a030840003c40e2075590b10f05090707002e00d80c1c611901e400c000210200040024540c40001c442e4012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 974837643 1250 974836393 974836397
    0x708040f0b090606040c260a14010807061b0b040f050309220c14120a020d140702160506090126101712040603020a0903080a0c170c0c0904030c05011b 66
    0xa006c0402044a0f01982c182040003025201110b0004040c1117502c0d1691002c64554001400e0511100800706880d00ba40000741a41180d0003d0129a60020b003802180b0401c01c0880c1c40c0012070342d9000700c02040200040c00d5201c5000360841004414402c80f40e007084000c120382c1c0705010490307416084004074000707248141e03d454100910706009100480074101001e142a0030807402035200e01d4510402840400e009900708061900500359100b5001840e005850f071501a01e044403002e071030102c060300101d0091004080800071a42c0d114100e0303543c11828030b0003511030858681d4100d41c0050030002c3d281e0030740d0b4203010403080390b09860341d400c00c855074504a03400c3c04454082c420740300c200401c0d02c8200b2010400c018000540250001e060080321403034180340e51136070394550080c0b5801c031020f1000003411000d240e2041c4142280c010024005d600900e80c80e0200050b10a0740e9030030094040d50041107580002014035008001900314141c00000902110b12007006040c42d5642d28800800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 974838893 1250 974837643 974837651
    0x702300708010603020f0120060a050f0a0b061e12010803270a0306050415091b0602120301053616021b1c050708030910170708040f0b09060604 63
    0x18008014003c2c6001c4940217406d28001110f00380046524607100002080c2c5800004501c96544808100300380c03081e01024800505070030300b0701d040000c00b0006406082400d0401e80f60341d00a90714602140c51050542c10740c446613030410000d6200354058408041426a103103400011038040120050032449030140c40d43d2095906400759130032a2110840340c40e040140804d040c0000b402692001d0b4000c2c2c0900800807050151441580954030400003c940120680d0720442551a040342010041c00c203a00140601f150440070050301800144280c910075001c17146200c4e00001c903041840b8084440f607064905289414188081c0c1d10010f13034031030041d0005240844a25403001c03890500c0e40c1080569610325086c50800c00000102002a22681c2c3d003524024400182c020082d02c401410b040c0043c6403200400000c01c01e1070324207030301050203110203440d05c0d82d00013116040595200389242001091a00e840c1400001e811008100404c1d075100c0c20180700c03006c0400075000c0d11031003044900340 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 974840143 1250 974838893 974838899
    0x9120d0e0319090b0f0702041107060f0b01080702032d1606050f180d08091f0509060609010612020708042d050616021e090103030903030f030b0d0807023007 69
    0x29100e00c17802241d09030080e01030004000505c0c00341c2190450f10400d10026040c81c1d41c40c0c483c0c4c0d08031003584000050840d5200c0c0800d00558111075401e600050782e0002e181045040d4a0220034801d02c0040d030001c01040007051760315800c0000607200d13924400c2d1044070300f0320300505d0484c00620b42503030359403c0e00d0b40040014140c40b60f035000540d5101c000300c000e006401d850703900036600400007a00325065130080b040000318a10f40c02c1d85840d0186884800403401e802c04040150403d034018000038000c1e6015001400030320f4004075070b0302040b074460703d006a4036501424000e81c0d50290303401c058840507266580c00c480d2540140d1420301050031031002c0d00724a9507802040340b1441110f8800b8521507440102c0c80c050f10704603003200c8000301100c0012440060450000e80d0411007600110007050a6280134010f2641c041070142d07070702565040410a6213802d10001d020303d81030300c03802420744100003510800c648070800100d08805150428003425695084c1c0190002d0701817900801d1407107408000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 974841393 1250 974840143 974840159
    0xf060e040c06090f26101815020a020c210115050108060d05101a040509031b0d080f190c03021902031206190312020a0605060909120d0e031909 63
    0xc103046821240440d081107502c0040c80145c01114200381009015030b81301c2c28880103084c0210395105904d5906000c03206020b1409040c00c108044104d8111807040c00040d0b4895000540f10140d48822950003424244607450403901c0c419103100c85141d9400c046104c206642068140d00680d0401d0321007060503619241404885002010064282d92040c1000c40650074558011030f440c003405403020b100380040c03d01003026982c06503004a02ea500004440c9081e41c040c420803a1241c0340440500b20005109800920700b150107460200414040c44c08160340d0340b40b840c4c40000b424101030303082c8410506084007500a412a860298018071020040c110310741c80401110b002003181c01c060b500c10380ba01c40c2480041c44140b0313400550811803c0c1d02102090100308400d0001820b41c0c02002242410710300351095403400b4284d18028800f10052104c0a06e010440700c03001d9000b804038139200c2c12002c0950025107045c40c0c1c0c21280340000201e1140c100c0070203481c416480c042c1c1c0c0391840000d60320000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 974842643 1250 974841393 974841419
    0x515040b06010c0215030a0b061908070c05060a0f18200409031e0203090315010f090606020a171e04080111040b190e0a0e0906060307060507060f060e040c0609 70
    0x5d41c00318646071010501071000d80610b41091070a50000345207081000441c0380b40c0d020000d82c80c4140c42ea060500030b015404000c44e580300f00c85140c05c0b4a881c843c0e95407030b40d58540c0503120700c0600f40c0750110842034088031b90005150b03480841c501d070a42c03000d5007003000d041c0d0380042c9182203141010550444504041c0100440c40b80e1560310032404101c0940c04841e44584410702c90111b001c01c20034155255010008a18051a956800300007940342040c40d54244d0450f620116140d41062010014560007003000c50b145a0082c3c01d00c1c0c0b06001c01c1301c0000140c41132109003c84440143c28112000c848800600b080c0c45074000200508083c0012410340c0f400b6900c5604600c0404019501d00305010401d030100c511468100f031008034240c071000031803070700310358002411500142c4100705d100c2404101054000d6001c1e03003d00642410104000c000d80704080c030160070309888294040d03800b40d0303a6000200408400e500e608040c1013a01c1c002c545840c0c10302c10900040c0240e00301252040034000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 974843893 1250 974842643 974842667
    0x9011103132105160e1302010c0605070e060a0e121c0c0507180f18020a140613060305041a010509010909060e0a061e1104170a0515040b0601 62
    0x30581400ca150a5402da0708480b42c21200074a407000c0303915100020380c1002004400c144010401c00703280d05107514040e08050050802c000d185980c0c9140f000760b60020225040d20f508500d010030241e40d00310094035086403403062241c0094002400721102235020880502500044a5000c500c1070940c036a035540d0301c50038200e082416440100080e4007802110300c145101e1041d819a185241e8940c0d81110800c20700c4030070140076454219032000312085110b130020a050107556066032252a4000c608030301c016009a06c2e02c5c04411640180d19555070041d20303600340d848c4801159080d1034980c010098801910105d03506412810b040d001111124030b840d06030307840640a802c0e10303840c1c2401100901102e01050380c0e1141d5a005040ea1701c01d00740003a14019001d91030110340014120583c0f200c0c0201c11007069a828030306160b0004400403101200c0484174940000c43c209901a81c1c03050900440050083c0b591140009480841d6440350950f4030603409000b0742c2589e582e03082e0040d142c40e10303914 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 974845143 1250 974843893 974843917
    0x1b13020708310f1a12010e0a060305240105060301030f0b22112416020a0e071706060c030316091e030c1e0b070501090f0809011103 58
    0x1120780d92090308960b84129001116100c0940c003004448420458600da5801c0016007012140c41400000c0ca1304d0b045072070b460702ca68540b42c0b50049000d0500301c036031010b024007002d10742c1d0000030652842c0e840d00070402450b0800d00741e50b81020740308040c040420154003107105e440d01c0c0c400006183e1408505803412030381c0188200d40d08000f165550019540001c10407440c0805880360301400d190600c1500040714465117000b410391043d101040300d4480c40b4060704006e007035400c0c21804504c3c11441a2040c450700d55205d42e003c542d03980f000801404050f04071001d411011010010403a5101403a20f078081803800c40c0d4031180d02d45009101040c0b02d0f90400c40f03130b03e610400200c0c1c03440425201401c1c90298034544007000310780710710600c0303c0c5407040441300d27070f0342c210b0403106006100003460f03800014030f00311180840a0a50201c11800d14406210740710510342e0214003401800429008080c1e0b1992100107420039450034541440140c00521020b4001030500d6540c9400d55000011600c1d0f10a07a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 974846393 1250 974845143 974845147
    0xc010b09071803171201060c0302100510171507120f060302090c1b0618100603051f020c0d03020d180819020307080d0209030f03030705030f06121b13020708 69
    0x15104e501c03616107010030f5202400701c10402c1030001c0e84100d0105019000550f644030800301da40c00c00038a0042c2c003425070483c480c0342404bc402d01c6201c20f00d0000407992003c03004c203d00310a0980310360a203d1008041450303030601c441002a5540d20601030b4511141014040180080e140102401c445c0540002500130801401052030715551a0182121034030342c18040680c01c0070b030480107040001c10b4550328080124501000b404000601140c44081402207041010074516102e50750b69642c040018000700c1462202844c404103503404a480400883c412941d4090300148014003e5216503401c0e00051700d030a10f00f604954840d81c103000d4164000188904041d4039002503480390302544c1c0c1000544c1300401214000892000c060002d1845c685c00c01a200c04020381854181106c0344038150b8590000c004124035179800c1016070703800c1014058100995940c01300400e01c10814280307070703605d5441201006100441c0c800440808140203403203600020701d4242494092b030082c15070040c104441 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 974847643 1250 974846393 974846399
    0x40b0610090b2b060306150b0f031308190e1e09040602090418060203041208160e180a0c0f0c050c0d0201020312010b03090120030f0702120c010b090718 67
    0x40d5891203001071030901025100700043e02c19004a40255000321000c0e41c496408500e185016804040108120607103246000640c955200540c8801015940301041c00312a00f410b001d00d15040d601d1021600494641c01140f500000d01094000000720340f14038007002e00c0c0030492102903d840404400a420240f51707445981e9071902a4101c898003541142c0d690182d03201e100f880e41d050600c03031402643c0041c2c4d6410607041000c1c003038800e0104c4205001020050100c0f00c882c6030019400d03002c81e440c1007529000400000744020890404013020304415009020200d042d603484403100c2005529036508810b018403042e81c0c41a1842c0000d881d0360041003451960382446590302d02d84510501c1030340c1c07408540105400304c02c0703802e8010340340031880402045401075003441403045100c3e410000c94100c40c03001d1400400d901c030007800c6010f0445100041038825000700000d204047c40a4038150719240d820b1314a500810702e240c2801c0c8908903010125450700d0141f0320b00d1440d003c000803801e44c2141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 974848893 1250 974847643 974847667
    0x8190b040f031110020c0d0e0a1418010303020633060705070816140108011404180b0c1e0903031902160e0106021005010e15010203070605040b0610090b 67
    0x503500642c01c0c44540c0708040d004400c00d010b400c6003005101c00041e01c0d10015074881b4a001c20910000c0c09110a41c3d05101955a48000420403544010030101c0204e1080c404510f00854030070480c181084820004003c0540200e1400c0c070420a9030100032034020003c802500801250003103188094490811100b182880340082240d01e01850843d201a50340e08041441d12a0700c802e091088081c6039014459080d40e18080380c0301c500c09103005486541001000951800720b05c10b61440307196185c0014880780c5030704404040988e00115001c0d0030346018a1640395a0348003511201c0d4840354414880c41454080c03090b9000b040c0c02070025410310000142100e4040c805a40e90701c00e52181690802d1300e0803003000e414020701600c0451003003a51401101914007000c01c050590280e007080010f0100d03c0c889489540e100105061419546001c4d40050f81184200e20025103428180b00c00c10003880000e00209000c0d14050b15038680798000e5900440d000c620314080c66040000400c07074103420071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 974850143 1250 974848893 974848913
    0x1090b04021605070e0703140610020c0907080108010c020303090d052d04090b030c030a020105090d0b0405010606271e17060a06050f032104081608190b04 68
    0x8400680300500e84103151003034041c881840704048900b80d2065100707115201c01e2801164210945003018000118200c88145020400911403401024904a80c50b01c5a05c01c101d03d509001d4040d140c50427a08190400420401090003030280c0c43d800d1011034214244004112881400000301a01941460110448444d4040068880549101e0089629001700030040c200c0700384602c011940e4480c9031025400c2500c0c18102800e100c2d4016005008a40d240800c0c288000c541c241307000c3d6a608003520000d04a800d50640c0074101c090712000304410400154448130030b86295444020744150b4480d845034081052810172005000c03105810041140500e4402141c400400f4401c030005444e0f2100c1304000c054120803041c50350122040c850444454850100500310030790706d031503401c40802c0110307a41e081103285c91500d100c001e10000c0b51240c24101501c0c0900094029101140c03003621340c09403000c1903405569021b000e00240e003980d2031190400900c0c55988007038002000e03500c584030440c01e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 974851393 1250 974850143 974850161
    0x3030705031e0405060d0c08060d050a0f0c121410021608030a140f1005241303020312030901061211010e04150801060618060e09150406090603060f090b0109 69
    0x10b65414800451242c0c1d0b035002400c203050320a10001480b170350350070340101a074902408142c002c50f0104c44c1280858404500c01404d16000400d0140c40491071a181c0c00c8403040d98030544401e8607048044080100c000c0014001c03011060031501564040365021049120b111160481c10244280c00c40024000b14040d40c2e1100703c072440024409000f0042c1519864126044064440c18000300240c4142c1c842c001c0010300b0041c0c03884059040a5801e00c41e5207500070700c40080c200e10200d02c152408503040c800384080e550140c25602d8401044500d03900c19081901d010040b9400c1000c0800c500e00c5440c008005150801c5001c407208000c400107540d07400c01c984000d40c1198513100342c2c00c04800340303416a80041c03050600004071140f414400801c01c2004040b611100c0d50341c5401004125440b541082c0315040444211180351100840c40c4281c0c901141404c2c0c01a05120000900320903907400502142d004030380a200614002c444d0340c007201c1e03462000810f01082c0500502100e4000ea1080146c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 974852643 1250 974851393 974851447
    0x806071815050903010c02150705180d03020307051b0a0e19060803090a06023705010912121806020306010302090301151a0301030b130201050d1503110303070503 71
    0x186512511004072400c1d40e2940705010070300c000780c401d00ca810f0921600c4201c50b5140701403ca250448044040c03004405443c802c2003010100da0082c800c1c14404030340800e074000400c0c808104885140c043d40781c0d000640140ca4500411604d10305440700d1488190890000a100d178481c1c50410400030744005020301040046203501101002c800e4841c8101800303001910700941c1ca0b80041030400821307080c5034104404540190302410f90304010740040e1080301c011000180b8611701941e001c9040d1f018021030161103513003000e4401d010f00407414840c3c480c0c1301856603042c0b80d658071556000c1c16a05001d100303880f0725142d490180080b0305290b0107140c125505140261030101d0000001e801c0d07420102c403013031a40c009400301700054031840900c0c40003034103c1061241190b1454680c816400e03001480e1070325600c0c0d00400d0f8802c582c4034000702c6002481204007000924000040344030440e1190104643c9503420468004403403038004145c5021607800401180341103503030408552a0982c05401c018 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 974853893 1250 974852643 974852687
    0x6010515091309421e2c100e0309100e0906180103030507020402090a0303110607050c070501030f06210308160503150a09060f030b10080607 62
    0x1495910764215118021840d0400f080d011a00d0a25101e201000243d00c840c0ca50000d0012413680740c00b0500e90000507848004110044105014002078181302200742c038120082d00d008035490019501c114104422814100e550034541090741000038500b441c0c00200780d0142c0107984015400340c00001c8100c071b084040c0d034108800d00c0040340040502c03510003804103002e06d02012103030030b090368540e50010b4201c640b00d003400c0c2c0c0c01110150040040c0006800c00c8400100300040d91600e1301100c07103086015100d034030301d82e41c1e80c1001801030a000c00da600d0b4501032040811061f5100350f003554036119054001c4c01c003040c0b900c4c0064005000080c05654140e45400000030340c140303049802c894a180e05d003018040c0e40d01d60f1a0081c4542002085058080300c94034100d506140e1007810740717611000d2110701100201481d00014807085540d44400c001c50705015011030150700340d40304078045903c2400c00c4482e03501d8142c10b01103481e0710b03800f0754155a80b0180004000740d1088180c0c0305520307501c4403400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 974855143 1250 974853893 974853907
    0x20c0f0607170a03060603050a0c0504061d0d080a1b02030606011b0609111504061b08090907112a011407062a0c03020a030e0f090109090204050105030f06010515 71
    0x50b200f80c01c50100d500100713980e40c8003041800d8141c01200e85c406003600040100034181078000c0d000d07008500488042111010100e040da041c04100030b0049080105090308500c07291600b83c0895000c00407803400605c604030205144041d8060100717840d94010003510389651420011070308881c0841c3c1900550720914000300c04281244a000300460044045100d03000c103050520070130b56086a044070800408220400c01203602020382d102480202001c0000c803120390400c1c1c001400344401907035001405405000c0380d15000413500d4030a111001c02c0c1e07a80c110640c02d0364000c0c5890b15681140c16090984100e50942c4544c05620441c402001c6103411700c1d42c541c88500403142001c1c00101d032520b03c10300c990502e20b0350004009545003907180034911140155002501c45115100040a201442100400da5500c00d0311080800782c000c2e000300b06542e582c0c034240010b040810000c6e07024510f4000082002d0078089000d1880c01c00c01c0e0000e11540e46000280724040074041a200c0b11008207200301 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 974856393 1250 974855143 974855183
    0xf0f100e0f1b040803030f06060c0d090806070e030c09090a1401050f0604020c0c0405190c12140403080106050705031b06040201110309031009020424090507020c0f0607 74
    0x141c000c4003000c051805030701d412100c021510540c1502c5048480083c0003c02440700e0000481e80c0c00428402c1c150096140c8502048150241180d0020240a42060300505560002c3c22034201c0761000100c0b0b440f91103c00d826501018162042c45c0c06400005030840340d41880a1142d8000104500300d41c0510010348905201c18078103da5408165114800c3c00100d1140d86402c58014408481c00c61400380303000d01c020b40e41c0400d514214003894480001a00c503000414500200e001050720920800ca90b50f08010980701d8030a49070001c4030300e0050183e140107482d8201ea0310455140d200c604a80c0d081075020b90b0550011f1008481074130081008952807061110200b101a104100074407142c14603100240880c00e003000d13140520790040c4180302e8540e500141d83e1940f40b8041c5070000e5544c0c1c0500206018049042c030102050290382812820380d07000624100448901e800100b2240d11981c5d400c07030300c8202c009442940f101212a829030300c0d103040002485003510484100c141c0310054100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 974857643 1250 974856393 974856419
    0xa0305060324090c01020d1d011e030b01030510060c080f040b04180b0306040c0611280201020d02070609090b03030d050f150f0603010306050907090504050c0a0503060f0f10 76
    0x40340000400b88180001c41e501084007196500f0700f400039080418440c0780080c216100c0300102603480c200001390071000d074003a00351040c010b280c03020700c0d81186c0000100640500070805482e400a072428002846481c0641d003200c059820b2691803020090503034441da0126009640442c00d15041000001244904d0000502c014410b22403842d00c46440100d658040345c1080401d98000d07044002004000762101500c0420f03620320342031031540718108003403041ca0480c0c10301e08052900d11f180c6602d9000d14038003910f01c842c54800d03800c0f01d90040c41084101c0c1c90302e88612850000c181046001d0005010541041c901104003500701d03030070300404030030000948809940f0301d6102d00340d00c0d0900c410400141115400c151003542c0170381c407046020010402c1c5200510003e0846a502e00200320804c4090059034000c08070a00240000e09003410802e840d295085002d074498145d480f000100e81c14040f548520501429400d035415a03600002c3c1a40c01d80c0051001081120205001c944e101102c20 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 974858893 1250 974857643 974857693
    0xc0a060504180510091e0501060c0b0115020f0601081e03040612090206070819090503010e070513020702090c04090f0b061c0b060a0c141203070513260c060c030a03050603 75
    0x40c80d001542d41d000046c02191b6047c0c0000d42007250708449040401c44880d07140e1b04640d107043c2c0701c81040d260710800300d04292901000049600880c0000280107030001221000d8500c0c130440402400210406255280701381d100d440701003a028a10020040c071140c4c0104031f11400034041a10b0600301d5500c402080c1d124003e00340b0444510991004090703440030501000d03101c281c0003000081c1c40781a1040c0d480c1031a11a03544101400c1c60403202690312501910082507003c3e00001450802c1039140c1d459030428000c202e4003618000308900c4100a90150005001002c3d080610700070f51500f02e0554400b2284070f80f0788098580b416007032903855030402000010143c0d956441000020316208100144083c07001445038041510442c00900a10499400440b28103180c0d84d58000068030100c10708103507001c0c1605a248a00305103440002c40400482000e1000644010f040c0c0f41d4100800c83c001e003400f8403060b900c2805041540b5000b40d0040d034225074000c0844983c2d0402e4416000c000b24a00c2c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 974860143 1250 974858893 974858921
    0xc03180e0408030925030f081e04081b01090e060a1e050118063507030f0e0a0302120a0e041803020f030304080904020a03090b090c0a06050418051009 66
    0x400000e00e01c14405d0001d1000703881856140400c0300c110a914003955800090301420060759020204821b200844400000110005076442d00503075607050030342c01902c1000110700454502c05414400c81204074160780c0142c482d40300c21401c5c0228054003070001441e440d0003c1c00c40e40040f031150090a10f1068003070100d0541c1445600385000103140407075242a80c00900713400c0105010036a0000407601841000c0c05405030728403140048102071508401411500c801d6080920503015032540240c000b61500b00401d01008180a03407682d070343c032051240030300143c201b40001c26912006ca401820212440e2421054200c104400070b02259101100c0b0b0b02504190100d04041540612261343c140b4603c1c0091411031400751a110003038400d441e40c1511441d40000c041ca9014000e902c114011508078031500000d14090b0103140d40c50b0460089544920340d0b00d440003880511400071541550910342030010b10034200d42101024101c0604103001c120f481c4400407031141001c1c401e42860309601 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 974861393 1250 974860143 974860147
    0xa0c020612010323060c12100b03010602010b0922061113080c2803020f0d06230105120307020910031208011a03060d1506050409110a050609010c03180e0408 69
    0x41c00d00c001c0d0050641c0c40c4d10810b900b004040003203655134903090759038480000b80100b582d5540d0041c240c8469a15802030440340d4408000400c4940d170540c0300f480300c07500c243d03813100494503800c100100c2c005200440d014019001440b000c0060445d422900d40100c100c803207681030812000c001213190b03900343c00850f21a07011000c1001149091510040c0501454003580d030203c10404400301c00100c1400064024544c0002c50040c64803007100c11054550028010071103002d004800d148001c6251074141c24000b0388000216141c03400402e59100c4280400040d0f280417665828000541c20080031000c200c0c61402c0c00001044000b01c03000341e0788100c5e80d1619101c0d0f0600010b00ca1291282022781501e42060041020704e4580c1402c4040c1c9640003c0850707000c10704030102c03601501568124682040c10030340d0a108100031030548241c228001c43d41001240d032075006001c414041d04140c03034000b42c0c004040700c0129004464142c1607045049103244c010b038071000001120b01c1c4c00c1d581280d5480c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 974862643 1250 974861393 974861423
    0x30b03031e0d06181b0f050c031e0310090b03071806080d020307050607080118091113020a080f0408040314030c24070e1005130315090201080a0b060a0c0206120103 72
    0x2051242600421017081713400d00007400b4203001445030070004070110a2000005104004a6040003960b00181e0072401c4001858100600900c81c1d8006803000f1010b4031038800c0106050015003c0c4c48070450020340148502e920b04074a840c071681d0038002e0b51350b0050b41e0f603001043c64503003805104104070254004554603412840c0280c035014004100d08200014100180100c2c04001c44481c0c6504456070003145185980c204080c4a60080103a10b41c003c034008507143c40e11100d600030301440c055540340c28a1641e125000381c1100d1104950041c41214204000d0000070480d00008941d94008002c50b402c04482d800c04514020011240c11081c1144002c00b400d03000a140c3d1003513100c001f27440d01c0c24680d8030a201140380b2201c024076003810b1000100700c3c1d180381e00e0354a1060000b941c110b0040e07405408070480d0b02c0002c04211406a0000da0058001901d1a855000d000b0802402500c2a450840940011a40902049030807a4018404c0211626a040c0810110301841c060b9098a4200320 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 974863893 1250 974862643 974862689
    0x2040906050a080705090105121005041211010e120a1b06090b060f2d09010b0d0501061e08040c03020d1202010e0f070509060a0b07050303070e01030b03031e0d06 71
    0x1070b43d114503820741c401d00e0144100d484224081e4110341c005d5030484060204019294140408001c1c0f61551500d004104400d10a190325507d020324000e46075070311910480320340d040c01e0342c604605155150380600c903034488079164440100b2410b072030340c41c1c104040070f290000401000d2034a88260340380e50320341060809204a502e01c4941240d0304640e5401c4804102c00410b121f001c100341804481d02e2103100d010726681141c080e2481c041001441d03000c296850740002c0f401600282da200404528150000c83d410b401001054510081c84003000d00d00440b00e10101d5020f64002e004459603121503000000507202c4075007111030141301d954200f1754400d0380240242120b01c80015066543e0000d08800700384880460131205490003543c0505140e074407503010600d050b03502d5020b00400320340001c1d06828840040040c5000349102e98800c0c0800a00500442c01da6841d4840d80354507400c10410410b10008241e89251105540748980342000040980d403001c5442176030218180d0f090318100562440 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 974865143 1250 974863893 974863909
    0x2010e0d0201060801110711040b0f03073003050f210a090302120306130905010222030614190c0e041803021002070c0506070f051c080610080c09040204090204090605 73
    0x1113400306c1d440c6c20002c40303495100c0c0014507102598040ca50310400b011541c0c444100c0c000c20300d04080c003103a040d40d0303640809404260300505107050040d01d142e0b10000650301400200c000700d81595405003001442010440c80394803107481c01c1040c58135603d402c17169002e0a0003079441030907030030b500255844032418040d00308170650340d8100c4843c1c000c100b0800203940d003a500301c144070501200010850f10b1391030319500a20880640c00924a0705e2400c09040c5014044004103a902c070306024000e80e90342418004c0007920035105900540080302c1c5442e04070700c1d50b48c444040241e43d40351048145598201060071121489140c0354000c0007080c86805042d0100a03040040315800c070304510f04000ca440f02c90620306d0a0003558400e90380054030806100c0d109001d032804070b400c41c05a420b1074220b0000990b00d00d07403908041d004102d42d1000a0b00600d0b02d01003042100180341c03034500e86a9183d581c0b148e00b5074030001a09901c00c1c3d0a0001180091041c409040a408034003c0061308609090400142c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 974866393 1250 974865143 974865161
    0x702150316030c1b0503040306090c05030d020601060806010804021c05070f0608100506070503070b0901150801091a1803450d030c0615030b060a08060f040302010e0d0201060801 78
    0x8142000b03c40782c44154448007410890040a02105001c03c4e40c0c60705506510856001410040c140300781c8100b4007944040c480b00b25030341102182d0804000200a98560704240302d81004601c440d80010b01d654050008942d02c0751005103110400e4000c041e4070545141141d10954650303100c08130074001406010740b1000900b2050401c904280360810410b420b40440e0301826001700d80c04115102040010003d55010561210148440745043c096281c000e24440054188004561000180540040c4100041c5e0358000c0d0101e0760000d8405000601d040002c5d02c80d480b05095420070210240050000e05205a801d04c051240742301020701d041035000801000303411222101407a0580e807000780306100c0f070354002500c484201c1007581c241500c80209060002c1c0286040003900c05880701100924000d40384a000d1444954907140c0500107a0078050040030042e9015002003060900e6507018251b10900c03e10000c1041038184d901c0f642040c0e001052a000341c0c0d11030806022040b0300380251045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 974867643 1250 974866393 974866397
    0x40f08062e21060b0a181a09040303090c0504090b0610090918020a06080f0a0b0d0c03060b04050a05060307030809060d091b090212060f030c040e16050604030b0f0c0702150316 77
    0x40507060042c0d4402a2100c0740400301c1c01c9554070180500340c0301b07d100d50401410010100c010750f00c2e050070050043d00828008a4502c0120040407071180340c6440f40001c220b81041c05504159181000c1c2324940e9004942003041c091100030000d00440c003801003560b501c802c2e0040b03240071040381c414400015825004502030040d002c040000c1403100e1141641c0c0400200e0002c28840c83e00760200c0c000342510040a0001d100b500408406e201058025801c48103068404018642d11051201d04884081c0c0d1450341c160001c2c1001c00c04980d00401500038401e008020030328007026400d22004a400507a001c460840c4110520403902c00700c4425070f801814170786019031805c10100366202d0800002042544220110000c00a90f07407004c100745550280f020307004103c1c4031100c545039135951480c00701c1031803085142540800c240c105170050741c0403a6480f8a004003140c49205889501d500c00400c2c44070403540c140511005640d5070407000d80521041c0c031b80c2c035580f4246501380c20705201040780341d481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 974868893 1250 974867643 974867659
    0x1401141201020405031f0e1507110a0c05010f0207090f060f0602060c0d09150c121a0a0308090d0501090f020f030a02010e13090c0b040f08062e21060b 66
    0x1c0c0b03407000b041c803c1d800005800622070503030000400200a20303018014046234410351040d00c03222a0004c001c2e40c020300c1151205c02828141e4400a82d40f40d450441c018500d0551800c1041194055400404003403007a0044c0c514840d00c44041008503440c030380d42401029242c42080110310342c5165040044c00191020300503615055400c1074151080806544c3d0f11603403000402c050000a142c24000c002e50301f1410b1002055000004081c2850751707025502c024a80481005414170042500103100006020024210314603151040640c1014100b1508910442400d20000c0c0003840740052051140ca042d4180544074010300c4034a407030800382c1502903032141c0c0d070310780160781c0081840c40184412a20940799003200075910b00900810240103204d010111740214010600030b0180090f2510761100001c03840d601c02c13050340d640c041644c48081c080d0100321540e8034118a0520302c100020211074010348156150a85900402c03034103414051207000f00b820f1020001c050182c0c0165000c111507d507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 974870143 1250 974868893 974868899
    0x20d0e15010e040201050c03030a0605150c070e0c0c03160c0f030209041403091905090a05010b03130206130602010207060b06031e0a230901050906100b0a0314011412010204 76
    0x5100c031481802010b01d502050710026003103a1050049038101d070311003001c0c0c0340c5034100200c042001d4401d03802164031411021419041e10801c28060b610310000040041140600c0c0a0700400c1402e80a000781c03003018010810070f6032030307902040100314500444144001c448447c0c00e01135001862900109052500c2000420244e80d0b242c1d00540c00c02d8000c610a050640020744981c51841007008551300150707511a0070720b403c240900307070808031039043d0b4a0188a80d161480c4100b00c60003400b40c8150140e0501c00f05070503010b201c2920050301d1000d0a240e01d001401c820000d90340d255075200100503034001071200100980346c0200002808283c6d1001c0c00c604102d0402c4141429482c030548081d405400007a8524410390840b0745903002c01041c4005032060114544418841142c1c00c00080d0f08043c080b41000c90005003080c0301d08015002004030f075040c20420880e40e489811007008041d190085100700040c811400c03030007018481103041c0700603144c205100012000d00030000481e44140020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 974871393 1250 974870143 974870173
    0xf06070527040e030c12030c04031b0b0d0501240504060e060d06091b020714060313150e010c0801030803070305040203031204030e1e01020a151e020d0e 67
    0x51480307100d1551511081d40d00c0c40650000300340544001650142c101100f00210300008002040f6000c2c465007a01c0280d4030070424949140310948a5000e0704504000420100381841c507141140201c65008005941d176441c061141c035001040f025410395610300c01000384002000110b00c02505c09014564100798104019005006601c01d10b814008074408544240c2e84400445d24a0206071500300840e9840d0003140c4002e000c8e6034803841d4854501240144007e00014203c400c0b40d5141c180c44050328103003010300281e5007000d49800103c5203100c600d840010703031003241c5100e56041508001055240aa1502e00703649a001d00e21042c030020a00500110342c054040300d6001c0103a04004c1150f44803403004c20b1852003504a44200d0b00071501c01e1104040c2d00100703980304040200e900900c007450441d0b81d480104840140e080c0560301c40d071310417000140da0458400700f245425000040400b504004000300388003005402c2d00c1c1a03400900d42400d6610f81c407404200d800303808000c02c1c0038100c1000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 974872643 1250 974871393 974871397
    0xe041209120f12050c2a01050309101a0d050a02090105010f0915090b030f10151e1b08090a0b030f1306110703170105030d050708181005030106020f060705 68
    0x201501c801c0c202000c1d003030030070b005800715035099041c403044401b080c0c2560036142e40000c2198440e80814002c2e100182d072503200310140d901540100c005801121100003402005102d20400c1d03c0003608003071240081c9581e0340c60007052031405400a030100b03004a104019900740140c00c5581400b21055610500a603c40403480960b0540c0e800129034080280054550b150154001c40b0508400010003c4841c1034001c268003812100425103040f5031103642d03030001251441e0b4032400140490027465001e00320414220351850ba5803c00c001818040c4604175182c0d07400d50402e4403a038100003404102802c2c640b003060014514109a2801c5003071410291420700c0000c1c02c0b07030842c0c00e040d0101c0d0043c403800b40c0c0300c000c01c2a032114a003640c0392510303d00502100e0a000d0300b446035070b544900001e0302c1c0c280820046004916965a030f80b03007440340d50343e4040c150402c0400315500012100c143c0c8040e268401c5c5541505616101e46880f50300d032420003454442104402c1100d40c2065050010035500281 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 974873893 1250 974872643 974872673
    0x102092107051207030803010308300c1303020405090d021c08060d05120a080103031101110f0c0f190c1e0b18030d23120105190e04120912 61
    0x902684034650b070304843c0d85801c03c00d0700302500c4040300000000401c03025000410a0001c10440c03a01050394907444804d00c444c0c00074a900602c4020f10000e21004070a000600c00803801101010341e1139240c1c0c010508464003103801010550005031420440c9404000d501180c202c965070031006c0c10b0119074000c00089007c1e10b10781c0a02c000c07920007000c03c00c0500c0342482a01c1c0411440c8c2d1a03800507540241415003c0c801a80850030070001d01c0ca0700301c41809210300c0a480025444c0c40e00301c03411500203480d44560840800ac4c020020700b5030003894103000d0340410600d948965107905d402424407a40800b0079a0010822451001501c8900e80f415007048045988400465869801250b040188028207001c01c44d411f01428446e01d0072540c10440c281200072410501c040c034406100c031045940d10641e900301e054805281c004200d603242c52501c0340c1e01090500c0a0260141d600c0000012040b400e850848852111100c070009155100369940002c08240100c20301268082c2c99462440035060 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 974875143 1250 974873893 974873899
    0x50105071401020a030b10020a0b01060e0303040e0a020307080c0a0801061d0d030c0c230f0102030c0703030c260307080423210309030a0309150509010209210705 71
    0xc2800d0382070000c010150110800c50070000d41d03594188280040051035500701152041a0000c2440c044910000360505c20755400314901107581d0034070341c0c02e41e1044e440010907a03061204100100d100868111007030b0083c0c031420400350b02d900b02140041e0107403038003c100803890303074047c4148001c043e4826480d0381154240e06101b040050034034085140d00d9100144e040c0c020365a02482d030100765120f400c00f80c107030740590230020036141c56540c59030315007503200e82c510700740d0007070000440c494a082003000015980500480c0d1030f040d403e100740350034486a6841a00401d080c03288041c207011440c980048010880c034080300d221080704904070030b41c0c040a00182c0800000030001001c000f107800c40a0044010b0504101820740b51025944c0da030260110700e40141050000203003c4002d6440940313008001c0718001e107003802c0c0030304003c030010900d005042e140054416021102c4d00200c0c07059a006140382d0700096519049401449040414070071002d43c41440543c480c135144e030012400c681612421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 974876393 1250 974875143 974875147
    0xc0207180b120c040b0a0815090307060516090b0306060d3b240c0703031413110306040c0b0708120c03042d080a11070303030e070506070c050105 64
    0x100034008104800d5655048581616004000c1000041c0b01c0240a01241c0038003031400380005000808169102c0c8032003a0344101c0c090181200610a03142d481145801124145480c40d11050191b40e4290b9980ca0600a140c005883c86940082c50304050f008403403070715143d03040060209980b8806e082a001e0541d98480c4012290211051030101c1c950b40800b200d2427110b4450005000c800103910b03001ca083c8121456208010070501100119103400c5280581d20b13030302c3c024600d80c1d66000d520124109565407041078211340700b14060500031060316511f42c10035882c07898580b00c0c11000c1d0010360f201e60700810800c0300040484e204201070343d808989064540c101854050424043c0d0480e0040c0b0460901c2000700210050010b14411030054040842e040031a0001e40c0c581c0309058814000090341803074020200300e140c0700030300c86041b50740345c82401e11300303060007440c100701c015001200020744594807042600380c1000b400d000b40008032100d9150034459941d0346a0014144a118144400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 974877643 1250 974876393 974876429
    0x1050607050f010c02010506190e161b12111516050d021b0c06190807111606080a0204081009061d0102040f170d110717010e010b0102010c0207 63
    0x203128007906100002e00a0112841a907000307070181c8001c5070003a004258241d070355540c1100ba0802c42003102c0c00d18941d281c89440d4085004603c4042c564640e040c0705590207010b102820012004070800e026000b42140d51607048001080440c60264205003540442040042c43e0144840d440d0010070310030300c0c0c94031a00441d00a03503450003580c0000035224030110b40c02500c88040728100c18505540d6003503460181800003040500d0041c0c000c03c181c041c7e014220308032424010b84001e82c00411034104030407464905900c1c20b241a80340d4110440013241c0940030803419400000e41508240305c44015401c0c04e05180400703594482900074010f2058841c40e10300203001c010707802010030001180b8040480e142c141e0803540070354024407441640181180c800a4503004203005030312200c40040141c0b540e401305c65011161200c003e56042c070b00b0b0041c1103002900d84a000c0f1000c5041e10104e0020500c0810210203600312400d190040d8196410460f480c10380c10743c0810020156174039241000d500d102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 974878893 1250 974877643 974877653
    0xf1b0306060d06150e0a0b041506120612050109060506011d01200a050a0b060f0d0212070e070e01080c07022b0f080306100903052113090912030e0601050607 69
    0x1c00d19000d010342c1004000042496117000c010b00b841482c07441014001c0642c00001d210444a5211405c480300c0d0300f83c0d40502180b4407172102403a0031081c0840204a00c0c2e00c402c68091102007000b801c8a0581d91080711104010780c0307024a80c1c0c81103003402e01314281c104501d9040e503a03080b0301019504000c1500210084041c0c0340c141404a641341c4c1c412103881e03803035034684103a4610540c181503c840c03c50358001030883c5020704049078a00f0001d0f0415058403150303401d00031102000d2419140d0382c040c00130301143d4041842c403007601c40c0c180c1d566030003003201703444001402142001d00480c19902d0300b0070000025132182c912802c034030028501400c0000d0800c00791800c800301084001071040300e000703405405008170304018502681c1c1c11100313907600080042c415507070f20307840e48030050481c2c1104240e044900d4a104d0b02001c040d08241001d0301d080b1070319000032114406a0000d0105039603881220041c0301c1911503200c0c800f8454181041074840391000640c0d90101407089a205440001c5c0402c02c000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 974880143 1250 974878893 974878901
    0x50d0606030c0f0611070503030904111c0510050405011203050309070f03080a0306060206100b0f130305070305060c0c330a050906070c021e061306020f1b0306060d06 73
    0x142c00480c1c030a401070b1100c40e48880322441c1c2c03003004002448022042e02c0c0e554089149811100e00a00070361a01c0c401d20144030152016480000140c0005c0c4469500b90890300d01e10040d92031074810000740743c5419100c52100329413a4000038001d900e00001482a003100001000140d909400d1498a81d52074004403490b11178250001c141101074003000004001598001d808400d8040e10148405500c0340c2c01242d0768a01202c8084210b1006001041002d181900900100b104840c4031450000100451182141c840d84101d031150301803041082800030038003003150080402e8170740703900d410f0782d10a160f43c0d03982c00090f0b03120049681c4045c0700c05900c40720540c400b400e500b0300040741507072410401072030040c00111401382e010f0080e0800641c030140702e02405983ca0b80c4c01005100000c5c03804007900f03248001c0e04545034220398104040f06000c01c001d000e4000600480d4003d0100781c8003101003034201700c0315000d8500c0c62211005484196500410390540c000d00a03103c076801c2c0d0310f403424004060 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 974881393 1250 974880143 974880149
    0x71706040818120a0c050d030f110f0a03020c040501120818010912060506150405010215100b0f0a090524030403140a09140a0602120c070914061c020109050d0606 71
    0x210540c0000d103c0c03030002141404020b0b002e80c224185560b03844050010850701c0d04401000100074900025109020780d01c00384d410a09401110420480c48010b181b5000c40080248c0c0542d1050300a44514905400340303a01401d0300603000001941f5541d03500d2064014900e40c001c81003c442d46c1c60844d130340700d41c0d2264002c0150385140840044a428101c000309000c1c6e6025000703164500d0041c201d03800e4101210219001030340100300406a401d0003401c80710016040304070168003850002641d040103006400c6041229a80ca5a25090403030013500007480703944900d00815145a251401601185111862180421440b5500c0d959864121030505041c0201000f540c4042021400d290b072250440c003c5e11605085800034142950400c01c2d1448140300b0312005038440480040380d6022107010300019107240c41101c040d1501c80341d00b84280e1f1000c4d51140d240366215000c0105ca0329050441c80c50b8000f03000c210390b0404d0000d0300020f00c0d04209019140c05001c40414850401415601000003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 974882643 1250 974881393 974881399
    0x605190e03060a0f0b01021f021b030a0504081504022202160c0602010c02030c0d031d010f0c031d07092309010c02010c0912020108070302210702071706040818 70
    0x510f141051591005081094800395080e00e8003c07041c816500015000054085031215004000110000400650300c15170070340d454440300c074001e0405941c040018120b04031040d02c0d942e4540c2e090480d1640b8200c03420080440386a03d050600001da20f0b00b007901100080e55440501c00740880c00c65502c040c0c851030341c0444c140001141000148100c0e1080d01c070503a0816402801b120580c1d8800320707134134003d881c40c0003942e82082603c0d500e454000e9000d80b40c0c0b10034103607a01d140541d4159040742110354600c4522451500c0313050101030079a25111b450b04015411030000e104404d0001a1940c9c1d61702402100c18450307580700c1800c88900019000c106210607807000840314941514040d000c3c041e0307004000d0166003460f032103110f02400351003010161840c802d1488008095900111007140c0060440750030f155003040403200c5510301c1040d407051800c1c83c050b000c2150070010b00081ca0030085505c007081c40e22802083c03200001011030300540040e04841c417079488050540540c0c24903d034002c60554 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 974883893 1250 974882643 974882653
    0xc0a1103070c06031a09060d030c051002070b10030f1419031805060910030903051303050a14030a02030414180106021f09030c02010c11091306050903040605190e03 72
    0x1c00c00c0000780b010029030346607076400c0c000f0702229060b80560769106071100750b201881c1070018540e420038101d0a0b40306402032038182e200303110544a050821940411000f42150000b9600050200c10481550800c0f4003040a41d041e40c607680303c050410300024070081c1402013030281c40c62506400c0045c6d06810b00c802d03c1800b004005807401800320100c0b484144500300d100c0000040038902041a0380a0301700160591800381c00d0108200c000344100c45088040c03002c14808403400c032243c1d10030300024500c00c00082074541c2d650304010007041c9071520f807001168070410547c02c41c150f001c010b81e012208414510b0134141d000da80000d5000c99411824031078900604000602e1070b60004e44800c07004074801040c81c00c1c0c00110125020b48080c0400036000c070350440560001544035501e00b500f4203024042483c0c0f90520040041c1c1801c0341611104107210f48404a241400300300e03c030340794100e02c141e0005c40c0f500c1e1808070060258050603420602c3c164402e40c40d9400c840c0640b00032101100010241d034 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 974885143 1250 974883893 974883907
    0x7080601121a0105030a02090c07081605010f1104061d04020c071502070605070b0a0b0a030305091306120b0615030901020a170411130905030c030d05090607080c0a1103 74
    0x340a840301c030035060310b4941c0205149800c0d6800c0d1652241030300c00c050040d040d1507085070240038001e20003910041410500b0010341020648202c098498210b020700d0b0a4018030071402c00702d003529084010031010f107162000d40703041c6000c0c0c001214111040c6041c0203004001040085c5242e10f01400041c1d04a0300005510b005400301040c220305917901c0340c1d00d01080000110040341e54100c04d00415003c030303000300500c5005c290408010350f8007044045012401c4000034000c15410100ba52003107000c10702c04250a090f034a841c4a8421140c6098403040012900d04001081980d000e841c02402164100003c02c40e2912651750091031201610025680ca00380801024000d40c41b0b1180500092012410a41290116080703907000780d420001250b0b8120300c001c01c000680700b6080d02c40303d9856584141200207070081c40035002d000d08400c055a00c400030489050f0540344003d00208168000710208011075810100f880e0704604400300d42d41d2182020601a01c0c18065110841050701c0045100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 974886393 1250 974885143 974885159
    0x30b040f051b0415030518010e010b012015041e0b040c0e2806120506011e0f090509031308030a02010e011a06130302100c111c03050c07080601 63
    0x400e001d0681034050702c0e125054040c0c0000c180c01a80079114254400c440f85a032001e2090304169000300885900061401140c40300310b00310b4801414611140e512215602400c0d070f001841a074000c0c1c00244452442d107038100304207480304070180203807141071403450100c4c05204001c802d030115003020901c1e101c4220302504200e1804d50080b603040381d210b0503025003c101c007103c94007054041e0707510003401541480412000503100400000f065092a03640c80005107084024101000b55402000501115410104e400440e1868030211020112005400f004440c5108901c02e0407a4042140041d0395195180f81600310b114080c0c117003500d5296a0b02c0031800b41e00110042c03000310b0041e0020468808000102426180011078040d0f00c0303c3c0311340d06880c8904014009100178084103200e03014507500c980c00220100307a000761140000701d0b0700c400c25081101c44642204081c1e4121403040d81c880034100c0c0d43c0c0120b00441c800a04112011624107101c02c8100b011001074420081502e6980d0303111144 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 974887643 1250 974886393 974886401
    0x20d0b0108070801110307081b2a010c020d0507110a17060a0c020c01120603060e0d021203060d0807151a031e060c03041a090c18070804020f01030b040f 67
    0x40003050b0042c080300107803440051042d41501410040d8040c150b50300e1110a81d54210020410403541c00406074400251522000900c0c0242c10b8840c0313402d004500c540880040c100c00705e0441017580c5061f204402032600090084110a041d10308281e5800c00c40c6403569101914182050f045801c07250b002c2050480c108480303180c0d00303c80c000c03608a96103004440c410b443c1500591009604003101c415540d5200c2c2e0440600c400c030075000070908954950300c1c034044600c001400006900226001400203a0602a85031125940f40300281103040ca030700000c10b1103006140c020070354032000580c502007041a02c01400800345e0030800b044540f1954040400e205901c00710705100b0701881080040d1150388282d4624525178001c014980c03a9507403555000103078070242041c0c03058034803044201c1d00b102106121a1061040340040d0515803030107070611250303000c40e4185003900381c414802c001c441d82d80041d4166005404480185da10269040180c0080c084000f01c0f41e000360404071460b078800d0807900 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 974888893 1250 974887643 974887649
    0xb030a1506031e0b070503060103180c0609061e03020918040b010315020f120a0e0d020c090c030705031f2d080a02030303130201090b19020708010615050313020d0b01 73
    0x41d401642000202c0c83c020300c038070f50300246020508000f09030920300c968003555115106040c0050101c0c0881a010194842e001040710002c080003c1441820340c402c51440040641e400d11801e10424801102921404240350a08141d80410b03089080d83d540d03401000f01707030b08072984181281800d04248081d804240025550a9600203030741c100d06946200300c80040341001c0300750341042c0c2e4111045000d00c43c0500b01f08100ca84030b00e40c20490040c2408040001d00c04d9400400c4026091014051a00002006075040480500c00c100c01c10750041d0413294004148604500e50320002c211480e050304440d00300c10201e42d04090740704401800070355070f00e0701c52002ca14551290340d41c075812a0b689484565000307416030400e001266156424400082c04184141003214119490343c000c40e501d0340184c40300c450a2052905c4082005070107010841c007424415009000c86401c003203c001c0b6807080a20400d00304400000020f80851080c03a50503c0b082d03000b44a8200500c1500f401e8030414400c0c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 974890143 1250 974888893 974888903
    0x50f01050c0c1504060b0907091401030917070309081009031107210611030c0901030506090f1303030b120c0a060302070308061e040c08150307180b030a150603 70
    0x50041001c0051040580380c03151449070003010700c0360508940c241100405002150400d85031070304a0720310394400710341ca0320691b0305554003280300785042c444808100c3e450103030b0742c10715240c5685a004900a02015001511300242d025070311681032400f114180b0b05a88405140d000d840b40c0e80c0c0c40070720b10343c024035521070080c2d64007010011a6401b8944502591241c00c1d1502c0a1480e004000002c504038201ca440c020703440054071007200c40041900d5403045072020070404001031038110940e01482015003002c42603070b0315000e501d403a032a881171805001d051054008500d07881f62003018480c0e00b00c9000c6410240000c0e00e12083c1c42302c22aa10170400030358922071a1a80300104106119200b5a02200d4165545d071415031124030034440014034803200120402d51112201140c1c1d00d81c0d00400c040508559500c00f03203407404401001d0041000c808d864072a411046040022807030308902e001c102c09035140002410b04c0078200181c9040020340008012400e03150a1a000c43c1e015441101101d00403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 974891393 1250 974890143 974890151
    0xa0c0f0b180f0c150d021305041a130b19030b010e09120403060b040207020918070603020a0512180d0f080f0402100e01030204050a090e0c1005041403120403050f01 72
    0x18001c06842d50801c0c40d0340c0c030181d0701c1128414003c1c5080c21002009107024440d041c41d1034002d50038070003a41d02c907182801074200100c1d030030403541c207252060103001503030000501101d1024200080b9072204000c8400b24181d180d400032884c65580f503411500c00d040303400c43d50100a50300c0c0380c0144d908900348242c04180c1e010000003130140e580030030181c07400310754100c05514081c119580c040003082c1c25111280c000c0c0d0700740003a0005854000e400740c001d254076401e00200e810140015442c2c4807168124604141c014090383d61003130b030440281c2c0c420040f0082000d6081c1d0b140482c1000200c4001179038000380c4075030300c900440d0130741255044000c1b040903911201240d40c1d100d84000740d0b070300c1034400a40100c1c1580c8284d240c907100382c080214140b070501d00585400c0c4e031500061410215a0042044a0b82c0c0f0413040c2c2d40c40c4400c12000c201036001785c1e00007e001c0c4884202a08500582c801c400e4007412007845036031076036010f10030704c0007003406800d0891700c81d500c904025a40c3d6141082501da20341c60 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 974892643 1250 974891393 974891431
    0x906190303110f2805150f04051c0e1c2102060703050f0c0d0e060c090a1208071403070203030a0503061c0c06050a1103040311030601090203040c03080a0c0f0b 70
    0x840c42e0154443c14941c2004955642c090003001381044c000151480c1c01002c1072a40701c03260301c5c0900ca0045140540100c00c1c1e08060400c58185420f200c41c2a11102c0205082e600c89a00002001c0d0400c2d0101c0f10800c080804503e4041201403080c802047c140c240620412041102c003003804035082281d08942c010b680b01c1805804503201611101c6c111050f031800940d80491040044c203c60b00603040104203201880302462034100b007a40e2454841c600403404405074244440c241009101c9503c00104000940d16101003030310803400b000e06520150140010b40010400840e10910350140840b650b80e82803501c02482c41c1c1003998010311039100708194108112150100e0203110781c014504100e404c0c03408100b036845501c080d0050090005030010913903d90300500c0074200950041c0a4145000c1c030100c100340c01c0c0310703058020b0702400e4410706c11300c004140c0e03002000d01543d40c0304401540e186c58220090760340e4048140c000300302c42400c102144c10000c3c132040c0c1d80e0050245040c00364101031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 974893893 1250 974892643 974892673
    0x91002010923060c03070314011523031f030506010b0711040c020c040e070b0f030405120703140304060902040203040c0302030c1c020f060708120105031c0509090619030311 76
    0xc1440b080700040d481000480c903042c4014009640008050400064003800364104d144079410907070025074800300c80680300031844d4200310002100803000a0a100002070215004400d000c080c01d0364920892413402c0d01601440c2101c20409181c00c1340c04c0b00c07140e6075240e12101c42548109800c442c003403001c000c00c40d0319003094045d4203c09040c41d0050040020140144070040074140b50380305c110b224030080028071a080b20014031110a614404607500c1c5000d06047c0d190141180c4c1c0c0e20810304041240c20f010a0348091404401001248107903500d40342d60400e14082d10040c113020b5441840001030000304032503030300f0f41c400f140e02c281c05403400c10307401030208140c208100e8151203005004158050040c41c04221000e00c4e071900800141c207040564030b8401c001c2e0045c8010147c6001100014041858104001c0e8011110303041428052400e90000508c68068000b0740b5004d025420046000d0b50340b03051034a82075500a12404d00380c0b907660b0030020501c07410204002070b940200ca11440f0b80300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 974895143 1250 974893893 974893943
    0x10e09070605091e0f0406030f0c0f0302010207153c020c06120a0204091b08160f030c0e0301020a020102130e0f04030815040504030306050f09090d140910020109 71
    0x10401003085013914020048410761040d0704034140d6004805101510710756803070341301d030b0b001450040480d0340c0303501042d292852160125401442941920306000c00c0140c0c0c0c0050004190307002c0600325030a1801211080da0030180825568185000700c0c8034400c101c10f85c0b0400c04031500d51119480b071036640d500d030060383c0f58503594000d290440c800300300c0a605c03000854502604a418100010b103810b58804114003280e4211902c00714030481403d02410940e84280e01036001b0b0f50040042c0c80000300b00301c01509120070181500145604c135803080d40031710b000f1070f0b91a4464001030001d650b6603014030402030003075001c00e281820a08003020040b0744001d400c111745108801c68483c400c0561034035101640c0e00c4100a040c00505a01d64244da16103884500500b80145d02c04d45010500d107003480b04011700032420b5403415009040801c10041001000140c40c807250100c0d05105c290304505034403103010385c403415100341c1d0003840c03148003a4001503055001c8001c01e805440340c108031501a00420bd100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 974896393 1250 974895143 974895157
    0x906061e090f05040207110d0807021003020301080309092d0106030e030720030a0f05151302090703231504060506040f09021804090302100e030c061501020114010e09070605 76
    0x1451140b802c3c8404c0c02c040c0d00402c1079034007030301c0c8640c07000c160b100c00240e00b803100d5141140d4100c1c01081e500c085052a2044960083d11420158255070400c2080d559130b0042c441170501c18074001c2c7c00304a10401c0c1501ca032980446603540890f590540406e41a001e40c421303c41c0000203882c024140c02c280d940070064075034043d840791411059100340d00c4001c4c0001d054210981e03041c00781c11881030016585070440b4903c00d100c2e01c080c0c0b520b9201c1c149644611341000b082035a64409400e01440144d0395201b0441c0d0050490030001045400412000e000200041c61004032010840a201c030150340c0382002c3d081c0d04822201840b0b9942c5a50a01c04140907a20031000107450018061200d9482d540140410a0840518101c26851300b80014181c40e9884402d40150700078440e0b411155041e80211039210310140000c601c0c0c200c000d605240d0390340b00103000000041040c001412268400e400c8a00613110704c15440ca4556110071b10389052a10603500560300340705130362000a4280c0540c05444070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 974897643 1250 974896393 974896409
    0x1507030e0703020d032703060f050601080a0509010219020f1228020c0604030305120c0306030d120b060415020f1b0906030a0501060b12221403040906061e09 69
    0x41514590130b200c0203140301903084050001c1c00352182c94a2030b00049010440342c00003074100c840ba1030360038040c084944c1043c801c00100d00b0201004020b0342c010551035000025a03100203102d03519040d07010300a000342840a5810035401e044a400c690b4002162802103400c94151201d241c1303031881e44681c6200b4050042002c10521055820041466085558001d20390042d104524440800591981c0c05900120080750020917030803c00024620b2a6920a0140d4030366480d60030720400082d960041c000c1240d0400559003180000d00c140f60f044509501c5028103002e4403552aa04800740d9441c028450304018450701c840c9505a440006a090380301605040c600400104103081c0310740b0810042c02150980701b4907034540005217003403041030010308058006035269590364102c41101700001c5d0070b5107d05110b243c000591041805e0b0705c180300d20b070700c91203641c0700341d0304901124114041c580c003052080f417a2440000c4e140d03402551281c0e18500c001e02e002c402c02040c44c0c095a2160f000d000b8591 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 974898893 1250 974897643 974897653
    0x11701060b0306150d180b0f07031e0c051b031903020304030906030c0521090c15300a1a180621010203130c0e3c091507030e 55
    0x381084c0e030310010315802c0a00c800100300e501010401c0b0820401e0190100d039008000310810000c4906005003075002036261405004a481180e20840801c3c91003104d02889651480c145440324014800c5910303078904164241e85e016900820309031641c0152210900302c240c0202c00008603403203442140c1c452a85500c0d046019410a5022001403000003c09070900408009040f00300c0e011034494540d100c0300c550190500d1400204190900d44c1c00c10205000d41c0740c03801703001610200041540c2c94851a407030301005006500c1d50410320107686440001c4403208002c1808000b80051b003015100230800803440c00c08620050900c602d81000c8914a0030400c49040454414605000c02040c0c0b0101c100c03003209400c0c0c07582c400608980c01a50980c002d41d16048c54282000350900c0600010400c0140d00b00c4103203480300010806494900302c2c400c1100314203006000d91540400804082c0c3e4060034005003618100c14200c2d5a00c00880140091036098000100114460b000c0e0b04800030790303100604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 974900143 1250 974898893 974898919
    0x602250909020103020d090c091503080304320303060907080105030a0204050a0b1905030f152a210a06050607060b060409050702061905070e061308010203011701060b0306 75
    0x10004104080080f410180c0800c4080d2a01506000c0c010500c0d015203401c64003646005040000c43c2e017106010750880c0c1709080300704085040e40081d6035125801c050550f0024101400040b0410500d0f00701d4a0b24046660241c9030070705000011f1481444282c40f040500c2c0c45241003512511024400c0f41d5141d48801d00c200014102170700800d0f0070501c0c0c50004252010307000c0010710388580e03c00512008259101c002c00c01881c04016000015020340b0142415000c0b50503c84d0000d20300400d070080b0b000d10f11030003071540b038120024400340c0da00071401c00d52144c95a140180c0e58914220021408031810000300e03c000c0383c50300c00c80d07080307900c0100030718580005070307940b0400313021080c010f070780d00040a100000d0441c5c2c0320b00520344aa9060b43c040c00880c41c0c0080c50910441d50f50b149080060314150400030600d8000303501d802c00d007804941d120b40715047c03902010f10095941d00482c0d0705500100000030714a0900c03070781d51420200b8000a005413078a40c98607001da4001110300701c0d8045c100c2c8004d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 974901393 1250 974900143 974900159
    0x6010207140d02040603150f06050613170c040c09051003110414011b1101080a15051c060609020a03060503060c0a0305040218190c0e0d0b090c04050a06060225 70
    0x400d4242c0e01c040c1001c11041d40e00e44600840341c840c43c0007000095100c1701c0d1140e002d640c034401c5501a0000704c4030740e800c000a03901e0001d50544140500309089880002d08500d05000301f01c4402d95030700042050048040c0040014000106449864015090340304480c000e035000f4015526052482c1e5203007410b091500101c86138485000920034180b19450071405c1001100c85034061240340505c0d20041c01440181c001044400f00074218200d09280038400c40c04802800440403c50710125500211180c4405a601c0030601c001802040e8ac0e180181c00500d803000c07500904005072141d02c0401110b5501c10a00d41c03122000c98200b070303540408202c0580d105000c0e50100d900305001500820383c40c0031901d00a085074005498546c10115507504d02e030401036807406040441e05540c588030803003104d000003040402c0c21001000307040300c02180001d100141c040024548089008006110794105049820b0082c5118054031300180140051401c210300d454194210316540712103111505407810100e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 974902643 1250 974901393 974901409
    0xf270102190e130b04020403020d06051b1602010507021c05010c11030a0e131104061805040b010807080c09040921110307030f0c0b0f060901050102120702010309060e070605040e0601020714 83
    0x762545c004e9007480301001585600b403981d240244150000107840c100121858641403042c4030040700c219040040400c003144050341e900045a0a007401e9854a08501c0003601643c030355210702d19508501c151207820321405401c0000300a0141d290f0300a003150b5048015181c0c486c0000c4a00400c14029460115040c96003540100c2c1140041c0002d8010f0084004040f540c810b910a0001802c203001032030406140c640d400c00185070885041002e8000000080c0c00d41c0c1e001002c5c43cac00cbc0041d110004000720702c00b10444d004070100601c1044003d05a23700001032200d425040034a81c196072410100d418000c0003c0078030044440004c6043c4159607900300c54039036a040c20b0f5410010710001e50700000301802e14150242c1443c000302c0c801032510fa010b00184001c16403000d41103502881845680150b644220784100d83c0a00e0302184981ca54240b0801401d01d120300c1190358440d02c0000511603500c40c002d0400d40d8000c144181c2c4e141c4404004a1b568405400350f902c41c181c081061511510380454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 974903893 1250 974902643 974902661
    0x2062a070c0608010806090a030801050402070f0203010f09171e131d09100501050f060d060f0e04051905030a050a170408040501020708150f270102190e13 68
    0xa10140351500941c0d07503400404840d0312800210380c010740188058101400701c50b902243c00c0000704070580c0c00d51001003c0719410b00c6250b0140364005000320501c562240305000c880d801500034844e0745500404d4000404488406803140c96141010b00c0307400d02034004484032010041d441002a410300840c240303d9600c10300b89110b4412143c44000f0b008030003400c94107519240c04200207028500480030320b05042c828003504100034036210050106a9131182202a10001565001c1d1107510201001000301156045969030700e100c0100000c810480c000001d1149214a042d22098054103100c40300f01d140110001301160400c0c80030414403403060010308003120340ca2600c40d101c0f0307583e21902484010700761003e694107030000809111304d580401c1482c0042c0049401000401143c8506010340c03030f4007400c12255041003001007400404060600110307030100b100303100e40303506038807142c54001d511808503003050b020072859150406010303200c0d480252002a003036040d46082c102c050801050b100c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 974905143 1250 974903893 974903971
    0xb0f0c030c010c1e0521070203070609050c01031103010b0904091515090c0906020709110c1e10111c110d24030c060c08120f10060206 59
    0x4031901001d20402d0080018808040c0c507000d6112514102e0202c1d00325803288004184502009050403030b2801040d40c04071140328509005a03601c030600b00300c2c1544a41400540b03281d003040c2e0b1140a02c0004521035510350300980381084600d8031455a0806404244550072809200b444030000301c1c205500006074440c8654078500c240320444c41480116080c0400049010f5203030384050000c1c5840b841401030413003403800c0100d5840d1605c0c9000b5a505410b004200c030040d06e95910745110482c0e00143e4222442e00b0b400d13a400d807952583c0c850008010028030620741d00c902b60f10364500000500c55164290303561310a080c81c1550150186444080c256981c018282d907401c241c44d5440a10f1020f00341110030003101165180340611107000812074a41e0780f4200590740d0f9070410000c1c208074412411102203050403a075440940c180342c505805500c2095900400880811040c01e038680005071082d0002405a41d6454907100100d82e5038100701c41c0000e218100244800308846414444d0001007400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 974906393 1250 974905143 974905147
    0xa050907030b040603140619060807170708010509160e010f120203100c05180301051e100506130302030f011509020c01060302100503040c060c2001021e100c05040b0f0c03 75
    0x1c0c0d946d001d10440d031041d030000d203600268207100d0b448074568800156a8142c8006214542c01c0030b100d5a1118030301d1103003005d07849002882106201d02400844000d0144100030401864407080c8961a005440307410b9000d154480004103141d42d240c42c0290580b99603042080c01036040c402840c1c001c08852034160307494402c800c15107a04080a010f0320841c8061544c3c1e003500d95111070a8404030070302c80d804103807007641481c0410800b5a1048001d407500d032080390b5006099241c0301007070710b58048150411500b14400080c2c1015079002300c1c0c1d031303141124825401c032144100f00b03221481c22148102852000700740c075404200003140894000e0070b0000603081c0001402d9989500180900e480d03070b82c0000104d04007104000c1401408407411009101038201a0b085c046c040da26100c102c1d28a1202d40400d14010514504591003046444a09010715010300c00c1109c0a402455a8900c0c0014500301c2d82c3c24008000c60b02481101034404541603a99002d0412080c050300400c83d40180038408034034401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 974907643 1250 974906393 974906399
    0x9090207080c0723120a170705010507080403080c0310060e0312070f11090405030702011803051509010c020106140f0d02060f120a3c0f1401050a050907030b0406 71
    0x10511603000105122004e0568008410489039800600140d800f84204040740d0340c40031044000c9182248254085640c000005a0a03585015800b8842015006610f084108540107801c00c0301140203500070b0b180d10003076665042e1b2201642c84100d4120444d20304c91442000302a0091020165403980201600c00040329008544580d0300060000d6801149100c02942403052642c1250b10040c000c1d58141c00c189020384800f40c1d01d2041080003410880580c48070740350300e00c08127801c1005c0d551220603520216415001c80021142c284c420b0350300c551038441c00c1d500e40780c014031400003200c025100400c0c3d807000d03000800c80da10111542007038101418a80c9080140d464200801080728000c132481e0321800101c40f60071010700300904002e803a0789424a001e8000039a0107042d6041d1005145280c10011300d5107420300d81c01c840c9101005014104901c1c821050100e401c00070600407500010400c81c2e0341c460030031511500c1840f4035038201a860f800b107880396229030000103060401a1000c1400c0755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 974908893 1250 974907643 974907667
    0x1107020d110a081615052a030f280905130518010504050f010f0b0a03020907110313050328142802040b0405100b0702130228020604030909020708 64
    0x2481c0642c500340c85415007404000c0c0e40c4017081000070014505507040140f2140070208240d00c2c2680f40c1883c03080c15807008401b5504000b200d0800403030300344031600c0d04441810003195a8422284801d401080b040c401100e80c8101c281f401120710060540751504070020058001f04005003041014175001d59882c0d2941d207003401047d01543c0700714010646003440f10a02d908403a0011503c1c8122801c2100303a091941c1e400a243c0c082c0c940454143e820340c2c03581182581e0150740703808003189034007010031564003800c2d01d9400f4008a42d4280c0c00d80f000e904803c1c2103101c0750340071113100320030101c101c042c01d801246c0c000f00300761017540309002110030b08912442e0420f42d0391015000d0100b040901086038086062030302405102d814180c40034842410881460040780c1c866000f81083c884e004552041503549a0140340f001220019085681e4403924020700c1e0881c2243c100d650a91140307018940c1e0340c902c00282580300d41d80640c6e1f00c501d058102400c204c003942c00400c055a01a1003071010060040c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 974910143 1250 974908893 974908903
    0x1701090c0803040e01090c1d040b0901030303150e0f07030216050a150e06150108150a0b0307022a0915090a0f0f0207170a090305031b011107020d110a08 67
    0x7000c1e1100840d181c0d80b9204100410400513084552400d040c01c0c20351040d076400002e0022006820403c00150307001003004a0300512600103a035a1015156000005042d015403046403030740324103800d000030307540c940320612102c02c01030b580002034604040016501c18031a501402e060f07612050b6007034003102203886282c038169a80030140da010080c08501c0c01014a1803240e2a0b05625003000740c02e0510b00131048071034000410941605020a4800151017816008101c280c2000700412050f00f103603c88182d07210a0f0801c45181c005403040e045c0c0c40140c0c0050404484c2d00301c040d006010f08254000043c0800043d014080c0d2015809a0645a202d507490000091145e40300070303030014009080f021000706a8503101c0c214045180f04100c03072408140a07548210810f81010225a40c8500c44002109c21000e1540007601034040400e0700c007d2854010504801c0c040810000d200304082c20040c440c0c1031203450300080d400065094041c00044201c481e6131509040200700f81c01c0c0c0c40c0d944504030300308 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 974911393 1250 974910143 974910149
    0x503160303020d1b0203430c0602030913020d1b080601020714060d05340210111813050115110d0f08101a0a1112041701090c 55
    0x80707030700812260b03e00e00c0703607100d0180c040d41c2c42c521060744415010006501ca22650910350301020b0b882c04600c25900407058420342d2600300c250025140708185901d5a00c83d4805203040300c1c0d0404184002401c0ca2000080d181e102000030200c0c1e945c0414410004025400703d010191703c0c5840e007007403821840300100480007a407099214000303185440300009007031240b5904110401d50f4100e103608a1074441c072058551444d04003500203007503100c101585194511240c240d480d441001400c181452680c189d003920380e00d800d60202e07082500131020f660252002c070440341c24243d00510040c00380c48030f9020b0000300301e80041d00b000881c1180c0710018080c0c0d402600103240003503100103000c0407030307038032a100c07142c09500203018001000070320f44014448000c01a5040401400402040c0842800381918000f001e20040442d03500980e901044140d030440103465001c2021303030745804a035002c04600304284201c4a07003514030b001e0034021810003011711028400b50f60765031900d007072000a640c48103080207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 974912643 1250 974911393 974911397
    0xc03070303120b1005030c090a030206030c07260f18090a1a04020309070302091e040b0105040605010e0d0803070e0a030515060a06020a0809060c06280209090406050405031603 77
    0x2d002d55440003001550200344070703640104400700f0920030440d8010141ca81105852007025030350242c243c00a5542ca01c5508040d5208000005028003502c44a005281080c440c40d01401020b00c110651b00c03000e44641c03080c0c1c2c2c1c1610100805600d19041000078040003e441443c1e554a00845012034441c0008603401001240c2e0390305446146124511040c2c40c0c0d2404881c1980345140c4440c941d40c81c0c410760700c0028003842d09030002c079220031002e8046048818603064000154a0142001050550284a128005d5150120200d020351140c18040d07003040c0058880d07903170503242e072382c40800d0380c4c0c0010503110070001a10003e8510340e907440204401140903a008113000d00300804c00000c0048054041c506c40d20301d81508000c0b030742d00455404c03d61138002d09400d440d00502d01c00702d0b01c580f003120140b5000d40201070410410300c1e100d1000030071407582c0001e070b012030030840304106040303100380ca00896004010500003000a03650703030091a0711074410313810f980c140700543d0040e0180e5280d2002c2140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 974913893 1250 974912643 974912657
    0x5070905042d020f10140c030f2709041a092e150e040f030519030e0f0f0c2803030804140c0a1e1502070302121c0f020c03070303 57
    0x1507107000401d101c400801202d03260500c60300d407a4041c11b8a00168402662540701140c1c2c4810720000303209440140301d0628555603140c98114090058145180081d1388482031240500c16a003001c015051203190321440d8802003401400c001880f4035001054030390540300c1c04180004200c1400020f5000c88410360003400340401c0080079170103031100b500e469030650401e210100130f80b240582ca02078206030401201d494403041800e040f1000d1140c140800c0c11940d18242907410203a1660040c0c89503054a01a101d000407002c400b951110b15000b02018194045c07090100f107440c1441110215080d00001c0c001e5040100700e584c07000510f00c5d40103402054050302004148240400b8003150700308040c018103000c425400000310b01c111640599000740c0c11040c115038a96019220000240550b040c10824190410000941c0c1d00000c1c0403c901400400324544040040001d10651300e03040f021141c0c03600e01c0c503c00100d0342e14008480030800c620801c803201805480c10300c10b800180d402581d40da0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 974915143 1250 974913893 974913983
    0x150409060602010e0a021f12050f0a051b040620100509061005090721110309010e06060a03030f2604020120060103020405180f010e060709030507090504 67
    0x180c03c49841c2c022134074694000040050042c5d58803520a00256100306018014842608044445c42403a61580150500d40406e20074059a0941c019105501c1c050051000d65110401c0c42d921500000c9001e06080043c04280b00c81c034014041c4900503e04810342c110910131510200707103051100c0303102e441050303602c1d0300340007100f401071150561003481403141140d1030f480c00d400301c0c41e81240180917004001c0018110412400952240d00304910502c205002061050b811803400d0ba005030381350302d81c41d840c02d480013901c10b0010031414031500d002007007140c0c524a191030689070031a880003030000700a06105201c20b5400a44241000044d40489090703030341c0f50a10015141c180f03900801d24002c68000d114104000f4000b03402415203a050301c010513162500c504441c943c018204445025000d500071035414441e0542c40100701108240495095490320441139550440307034003003c0c2c050b0300206c2003403015680942205402a20a14205899926090f0006c104450300000f000f81004150040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 974916393 1250 974915143 974915147
    0x501090c080115051e0c070501020120030a020a021603110f3f0106090f1a010f03090203070510080a0f1b0311090405010609030b090102090d030e1504090606 69
    0x455024901801d046510354103088450302d80f1414880c100c4100a400510403848100390903102e80c0e41200e9004c465150354002c41c1ca161112400d003e07041c0150310300352802400020144c0703040000280140075a00c0d649034159402c000c0c1d030211281e1419440760b4000002519050900c5000450185184030b100740304410401c030442e0010041107115044407040b80e403403040402070000d012640700031444410020030302d00100d100c3301100d16911951800d030001030030440c181c01800070180d0701001080f508108410ba2491048a00c501900055141e280100d00600941c0b019400c103000500320343e5010781d200d001805810a200e400300c0015070307110520031049038901400c0211a9500010b1002d550b400e4034915509071400d910400305511090b0401541c0e0800b02242c04401010f0800c1c4510368540c1c80c0603001c5611888202c030300744540c00c00180c030800184207172880c24030010031348084075411752811100c5081c2c1c0d440340c681c88140b507004403141d40c014400910041c004840c0c0424980c0c945840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 974917643 1250 974916393 974916401
    0x10810030c030807120203071203051005120c0a05100c121205070f0e0102011a0f0117010b0712050307200c03060a0507111209060a021204060302070c080a03121a0d06050109 76
    0x40001b55407091044000040550107140c140c04010300e000a09075136800c520001c500100e0b4001c641100070300c60340240401000c104e002038100142d85c240400c59480d000d0080040c6400d509a002070501c961980005a40d44032130000c45240f45082404a4401d000c1601140c000b618044003058201200b4800e0f65004481e01c3c3c0145c0003400208102c40814406180b02c5c142c1a1280d40309600444130028660b0190464085450700301c1603001c455a15005035041e02c4e4442c00303081e202c0c892141b40140703500344640101c902c5040f5070341d0742210011000d11044004001c00c95110024001e50500600546007000f0700d0340306000780c035008140f5050600c0003501400102c800c151540d007010000220f030801503011101c02280c269000b0703075a0201a48101d0802c80d036541001d00c040030019000503050b40c1038020f00122070041000c2c120f070035655180c0c2990360b0540c00d00200480c0110710010030440d090750001b05030790200020b401c4c8003144200060020014004200c81003035844005000507207161003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 974918893 1250 974917643 974917673
    0x20a230406091710020f0f07060e0601080a150515090f15060a090e060319030e030d0e030c010e03010f060303050d050a0b0d1509021203071505070e010810030c030807 73
    0xe0f28803400600080da442d0407107408261201d83d00040c00c540703611403030411a03142e81080c1030010f850351040d24040e006018039808102c0f02c0d1081c03000121b114013010450740240703030f4001c07921240100c40401075030282c800102500708003010003086070066156030106c3c51007100500807040c9945050140038440d0b52285803418042e9906000c000202600811038101f6244d002202201507601c500001e0310b0244103c0e41550000740d4070003250209500701c1946001340b0811001e0f103605519102d03007292803034540c5c801030340d2550150030105020350080c0b4444002d003030041c001042003464801900309860050b403084001441c002005214905a4800c69400900040e01403185a00307031400540c90044000b4060041c94010602e512011190b034840d480841c0d000e031a160901107035255a40d01c13500b0000302903511246401c940e40700c041e61885551300c1111a5164111980711500c011548628020812022624007080c0440824900441c000065205010042d40da01c503610b0311000d0424985 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 974920143 1250 974918893 974918909
    0x1003020a18060c0605100b1c180b13030c1202100b06190809012918010303020d03020c0c13090510050403080a0903031d030309120f03010306020a23040609 68
    0xc00340701d6243d02002444255410100218032a1140c1c46084a00d034003a82c410b900584001440784c016113000004400b03445010402006030810350030303405038034646608009003503024580c001a2000403480320849454041c1c07404403159501a40c4042b642c84291034080096481074805a0340035130180550302c0d0f06c2c0002d80703906051030030844d01a044000741c584c000e4203201e5040001001441e00354007007070800a6151800700c007100a407141051000e440c6090310f000301151041003050b0340c000740710303541241d030700d50b000340181035800c2e800705d0007900049411607103400355100c80f20080d80c40004a40c1e818000ea140000c01c90b40314a0100d15145810b041d0f0ba5080781420b040001081d00403008a900c01160040030455101c180b6084009220f20b400c1a804e0412010203d1720006000014500c2422001c0c11075002110358501c82c492030244003101d2803613480402c01440000c0c81b5030003400080c03402e03003802d411a042c9003003058183d160000c0c001c0c44546021908003c039691211190009060700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 974921393 1250 974920143 974920187
    0x30d18120b070503091005130627020108090309210106060908030405010320030f040b10051e0301060e01090f060e07051210050a090b10050a1d030a021003020a 70
    0x540e40c00d107440000614201c248100400040c50100080c0403010310511501c0d4208603c6c6048010b4500b61901c051003611003a1600030041300c105240c1d00c2c02d030301580d000e004901c050350950b401120001802480452640001d0114040503202c0140125202144100e4600c0219101c03060030308449032a4449010001600c1003040281310100c1150f080c4c490030b00e40466088040080201070304640c800b401c840160000c10411070344000c401c0f0b180914410000314401e5220080070340e0412199004040c0d016040e06141801c1140f1403000d00107119001c1c0002c0340c034503a9005042840d40c000d03170100c060070b51204000000110b040c811600075060310f80c1018058140001c00a145010300c00da003004610021003c6010140030010210007054001d04102d019502c40c00d049001e403074180b009a0203504144c80c80a481400f80b400d460300c2d84a180c1c0c548024a0101038100484840981c00681501130481150056150845041c4680709907480c003517611861480e008003c3c1c060b9101d881204000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 974922643 1250 974921393 974921429
    0x304060f0b150702010302040e0702030a0906020d0f0c0f0206270301050f06090a1136010e0d03110d0525031e05090d0c0f0b040302150703050702030d18 67
    0xa030340c51482c01e040c04080c00645a5000c0d200580c002e1095400241d082c0c0040820800344d11350002c020710b034030a016a5402d00d115910300041e0fa0700c0c00b8001c0b0000101c0d8080082540f1103104210070b070803150007084250441c05468010036010b90001036044041c00e181400c0d040140714103100389020f400c1c141d00801003440d00c000f842012403006400540b081d50345a01082c5e81104540040416a40009145907618480780a140400c0940c5201100c0c0200b00380224608200c1c0d0301000221341010b031902d138071110b2040308000d030903045d0b503030100d05000c014814050a0740b002c02520190940a80307a041d40c4801a014101d1004c42602d0303200c8198a0542c03001c00002d42c0a804840d9140c0e4003410414010b241312001e81e0b03140035101415401001c074060000a202e09a00320034110f03001e40100c040d01544410070b50941388035502001e900564014003445818003c0700c01001d09a00929205042626950000b42441c510080d11400200310003808107290324195101c0b802090310b0f2072480347e9005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 974923893 1250 974922643 974922649
    0x9091b0304020906031c080714091309080c10060f080c1305090a02060f0301061b0533041b0830070203030409050a0f02042304060801110304060f0b 65
    0x11000700000c3c0901038100114203a600c1c1048825580c414010f01841c1c03886c060840100481000c846503400104901600c01e40c82d80d6071760885140034406440b05034191a040040d801800c5446000c84070024104880c503800c2905101c0c0355103c20f83c203200030810070710b0710500c10030a43d10f98200c0d0341e80ea00414071071003140c1d68104a981e180d10018402082d5661240403990604e1103c110103500103400250403140c9034081002035059541d5911641c5017243c0340f028400008820a000400e10b40c008605541c0074100107048203202040b100404a0b0030403d00c840001404059800700c81c9010300001015543d058a00860301030120f28000b400e410110080318010381d00c4001e005001000d0307460032048940629011591050b070060200ca81e180da03131320a010014a41210300c4441e0a28042c14844020014021902120700b001800c01d0f203c2d2078807000c00203004e12039103415401560b42c1000100c0e21710a0085c003440d0b84092001540700d14140c10200199846a400741c58918902072281031541d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 974925143 1250 974923893 974923897
    0xf100806010c080c01020708031e010305030708030907090603060f0c0806151305040504050d09050f01090b090301062303210301060c030329130501080304050103020f07120509091b 79
    0x40901e480e82d07062485007400e88540c41403a1408949500004101c2c1c00c1c4401280150700030442c10b0544040b030600420503403840c980c203002c003c1003500100485004503613140099a040201042a0b41305180d6404650f402c541a540c0100c0b051510b40341444c0700500a4030407210f0340d8026040c203201d00d20300400007507113510b8110a42c4610340be012410105051140f900c500c042c0c08041e00130040341c181824042e40e03941d0060541d00018900040204040c10584021026152f060310f81c104070700c0c02c00440410070303005010100e40541d61100c0000390500800310144540035036080600300d41907983c2c10f00d402c040c2420b04001048510001c1d0000001c282e8013228110748980c0741010505c0214503085025111402d003019070300852004998400ba02a0b04038584070785e0031204003045030070509201d019580c0901c101b5a440e002808200600e5010360024010b040d0603208091600c8116590b4054644854240300002200402c0b110303001d00701504c000b90407510020707002c4c003801c84d0005840b8840c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 974926393 1250 974925143 974925151
    0x5100b100f0207081002030f07020c03060604020d140703020429040611120d05062d010f020c060f04060305091c050a140c010c0216060206060f0612010906050f1008 72
    0x88440c03042501c4a2081c0200c1000c1c040100584d40e0004942d54510040d42040d5101d03801000002c010440150002482820008014011b00001d5484000304030081d04034000101c1525144c03400c2084ad0740d0644403040c882c1540380c41c01a119400c0400c403880001003460701c21044aa544502002011400c003624115403072403030000c040504500c00da600b4542940740b00c0c0300504003c81c9061811419801062041c01c040d180301401d20f0a00c00d00d0143c410b640e14041410083c404c00303c8205510501034100f0b0882d00d0b0046645022080c0003140d000e51000344500103003480400c051018a61500a40780c01260487c010701108040301c020510390080482041e0610000150a09000380210fa0311908070304040a45038441c040050320718082c100075815240140140002121880901106041500d000b60700603d619981c02c2e09200852b4105800c40c1e170b00a805012006a200d80c042040e400b070905140301103003442ca043c1c1804420018a1203c03441050b0b05200e801d80160301001d05640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 974927643 1250 974926393 974926397
    0x30c0b0d0605030a080a080c030132100309020f030a0302030f0a030605060406020c041d1f2a11030403080f090d14031b0a050c13022505100b10 63
    0x515004200d002000348102c0c0d00003505406150085028014802c02400d00a282030b04c480180e40d4480b101d0a40e944000d0003042c1600c3c1d4040c0d00d0060f04040d548150003020102c1d101c04003d061140d0010390010103000e403000000317446488940c1142040305446401000c03e074001c001420459501075140d0140a49006c800c01d404100c00820f98400d0700180300134840900401da030f03240c483e44002e45552200c004140103d080900c0f240b0070180b443c0e41040d042e50190040c28841e84144c02d00d00031700703280c1c50f8250005a01c680311101680245145001421454184200c03024031125026061095022030844150003e01041010034000310880305038104012481d0780e5a441d5800280300d000100001074802c2c1180e82c4c0f6a0a203d6002004207840c254500704c40c02e0307669901c1903240d910500000000c1c002d800502d501065801c00d1810000071008041001d410282c0b41150785a6035440d0050702d1442c1100c503807010042c00f4061158038140c1112120030f000d1042c200010961149521203001c00b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 974928893 1250 974927643 974927647
    0x2042408010e1b1c0c09230403140a20030322330606020102180f030d08060a091b0f0f0801140a08031303032006010302130b21070609030c0b 62
    0x440440a0040801d010ba804410f20030065100c2213070717100a00700e07d0040c099039403140c1c08900d99011025185880ba0781d0603503130281005445402001c3c0c80d04040c4039541400f1030054580505404102d280c80d00c0340e100c02c025a00c81c03804002041d5000361001c4250034040120140002184413007509074001040c800101d00003074181994a1070b0f05e042040e074500414a468004610558190028441c847c1607009110480ca011000c0260700c0411076070030b0360b240c0c1c080c0c1d030942c8015005000701c1e80d11207402001030803890760b100c013000141c0728041c0c8900d44000300f20702005680d03604058030304200695440c004041100507030000c2c102d60380602503a048203950b00030002c40e43e0780700860f0001801d500d1007543d455080a412a2601040034001200490801e645000004485d141c11024244465000300074503440c640034006445c203200124001c00d0f8856031104096101d807006804071487c0d55961400b10a102c1c8941c2c1d050913250380140d400c100a01c031041004c10010b401c0721003913841c26a07100d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 974930143 1250 974928893 974928919
    0x3010b180616080f190903060c020f0703063603140403081b28021216140f0a14011d180901060f030b0a0e060c1602042408010e1b 57
    0x115038081e10482c918015914001070740e40ca54000c846ca030031a841003c051103102d1048a0136615615421004030301d6500c03d071802c0001c03030341e160030164556174403080a0240004049200362100d820314410380d09590403030b100c04200750340849010184980d0b0b04200b801c1070700b10740e115a443e200300180704840e0040f2070085c048460003800001d03814095880d40aa4600c01d541015054428041c0e041e8402d05c0782103c20720728040041030b4030358000e0311202061611402d0100c000403d03100d07518840e4000030348110303000c2c1070340341c4402c4940640345806000006003c1c1200041601048401102c00503a00510031102078940c0803111701500d40c08221f80c1165a2044000750042440d03034803c00d540c10010000009000041ca2407501034803505400303112450070100718947d1510280d54051501e8010400030a03100c0c482c07400b9001c1d852000b4000f1580d10701c0442010340c0c6075641d5175a0304103c4048907040008003000d00c031303c3e00041c0c1e58501901c3c0c03103d0b113428001c03040c2c400012518012407418442c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 974931393 1250 974930143 974930167
    0x909080a050913180506161b1502070c0801050a090c060507060e060103110315040c1203050723070f030203060c0313120215060d0209071202040b03010b18061608 71
    0x203400c60705500e00410110340c0d084c45452021401134801d5a032409140c0c00714409207403000c15031504441d00c1d202c0080394541480000d19140b0074003000d54480714806107040051a0b140010b00015024684204105081c4894503003140c00c080d14441d0a0352805200d0000035001840e817404a84140c02c03c1385e165211400e120014062502d442401070007003034000300400040f459803584c001803e50484074a0110000c01c1032441005540107020121921010800921500180030640d44070340f078800d00b401101d81c0c038800b41000c502c0c0d08500d010780c0300c101c42c04030304000c005c5c12000b06420301550103001d00c0c43d008a900c1c1e0101504000718044000005107028040e645400c040d19485a16240e444680e410001e4940c3c0c080c40c204e122115650010403d507142c60010070403910b4005220a25a440300c500a43d5509542424600d070250244000a420081240654000c05c0701c41e981503940d1000d2a94011255031420040c2d00c252014412103a05202c81c15074150f207154000300007942c408042d500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 974932643 1250 974931393 974931409
    0x22109060903010e0d090f0806060f1f020a02030c030d08133314041509020111240a2c0120090a051e061b0d0c0506010909080a0509 58
    0x4070740c00d5030a00c2c044a201c6800018400880900c0d17940d41d101c190344408a440342d20b400c510849200c1d5000c0c0d8045407061600070b05040c228007006003080d120007000083d0107403801c1800403000142c0c01180e0f64a041d42414000003108000450282c01c0c1c042c401c860160400031f01422060002203135501c58400c10049468070705007520502d8004c00607000c6091080c2100440c01074924001e0304081d02c0304400102c084005000d103500030760400e20b84880d008400002d040d43e80c0300741d04020505c051405150428000070041c112011032a507203181c4c8080c0507480c00c031005840085500c0c45c1c226103030700015071603020640b6000d030380c034850300000d0407035035107501420322901681b2240c856544601c81d440602001006203005c26135103148520340e10310420800010381c4d61803c0715203220b1902c40c01749107403031740050070220380d107045184002540e060a50300d003402400300140400c9030301048400303221007000200e0042c007a034003080c001c5403119034074011140200b2004405215011070509890358903500c1c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 974933893 1250 974932643 974932657
    0x7060201050603210c0609061909021c030c080c030705010e03030906041b080102130810050c0901030207240b19080a030c080903160f0b090d02060a050c060a060303030c02210906 78
    0x8441b440c2c00c0000c0245e8a89109450220314a01c6501498201d42503500980b1440c80e0010480043c4045040c040e9100883d404801c0341001202002100021034045c05411504540340041d038480019180c81401c440c03504c40fa04003594418810407110038000503045a0141d800400c910b00c00c103504100d0b50420709140c100c00b0f415400842c4016180c000480b481080b00e082904550f40800c1103503c150444d12709455040f0450317010000d514607540607800400156100341c0040007281800303004c0720000406a0204001d0544469246299261204004001c00300d40a401c40c030b0185401900ea0b55480c01d20b40082c00e00c00040b0a040902151005980c0d52a00160a584110030a140a000c4410340c170300601580941c60710703001c0f4159000105948800d2130140c0501d403060a29020050560412691071042040800450404a1080c05038901500900401043e0142185401b0b026250000801e1013103500142c008440c0d15581040300204101e010025556021060003243c0d851040517 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 974935143 1250 974933893 974933917
    0xf03030c060a140f0417030606090d06020310170d030c030b090f010e01080d08150d020a030b04061107020f040c090518090705030f030406030f06090504050c030706020105060321 78
    0x5041014210060f041094940c442d103000b803c5036039a099102180b100c081d5005800c0c05485c8044142c0d544c0d80100030340d040780c1c005165504184103180080c441148a40d01102c050341c0200600105032410018200503102d825815014481c0c401c50941e03540c00040000000c00d902c803d1828103c500039440460818406400c1d95154680b00104030540d540038880c1d045c085021000000d0b03013003000714000c0246a013a80d21940a0780342d204011610000090010354413407111112500141d55040c03010004510510900c1120b00d028103000084401c40040c40820070420400c400040c0d4070362184135105042220009420400003c048882064903000705400074160f40010813422209820740b4403828100007203d181c9511203040c90344403406940c840c03a0590050000b40041ca009400000350f03070a10380c500181c0d407680c0701c00c80810b403441034a0a662a4100400c0d103106030070140729500150485000900140c2001130104c1c0d82d0707a04120154060360301d0b0b1940c020000100804581404501d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 974936393 1250 974935143 974935153
    0x103020708030109051e15060d0e160f0b0712081b030112020306161707030e010204090204060f0315051e03060c09100908060a111b010507030b060909060f03030c 71
    0x10f900d030040184003d81b08440c8020064903c400c45083c0800e003030380314011380345035040301080d407200b445856004611a9117140f500e4000039403414000308040300104061007000c060142c5001c03002500800f254003c0041c04100704200d201140808408450340089032401c0540b594850b01d2514140344912041e50302001c0000c000102c8019064100c00f210303008034195003150701d8059081c0c2e80d5440140f4107038082014800541e10a440b25404107078030000c00c0c1004642c81c060040d01600f2a0f10903003190202c103901107414007400d035001d511100103220508080201c215005000400780c0114402c481c0301d41d032003040d031002820b40304000385001203014007203c405007899440303401903410140f980340c02641c101915a000520035400d04003101d82040180c4240d8840706000006030070fa14071a40c1c00d480e02040555010466a00d40514078580040002060b081c1641c008081d58040840c02c0d2044030248000f206603a91903400b690451400c07500103603076400349000310342540980303490101c0a000e2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 974937643 1250 974936393 974936399
    0x807050a050d0e070f051203031b0309030409051314010b03060c090109031a18032506060b0a08161103390106030210080c07170c0304060908011b020607050901030207080301 76
    0x10070f5400009a1b40f0407120103414072032413400c030307683da0000702c0710b8003415141c038000e044500d80e95900840c0c104581170182c038940364a031902d6405a078026103200c4c0c003c208045023101808442c2e1948078404110f04021f22501d840d4100080d40c0b80e0300604110194680018600b4a03a8040c040d880700460344402464901110b10443c80f01695085030130300e0803166240840c00355640040210f40e14440f07400b17201c1b03820f4601041e8120007111104030403030342c05903a544040799402c004000341c90140210340e20045646400504c906a013007504812005021032200c0c411503d01c00803090347c80b42d983ea0f14000e18118005d09840ca008064020381500c202c113000a5150654030640100003968001e95552001c0c1c44451400c481e640310844d8441030189003031241c40c0c00140c1c803505448801c071812150303d040810f4041400d041d907200750301c030102150f18440d040101040a00660f941c0208036030180382c0305003000310080c1d1140d03c014111000c001d000101e10400d03a010f81d06950101d41c04c403418640b40e40e1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 974938893 1250 974937643 974937659
    0x71b020d03211109031c0906050c100608012a0909090507260c0108010302010806090702010609020c0706090b040e041b080a0f064d0c010b100807050a050d0e07 70
    0x20203407424078080c2c00b690b4000b03c0c50480c2c1d010040b0521b041a55450b800b1454404121200d41180b2042c020500842e0030280c07000c0d4a502440010304004000091001350212005038040c404905501c9a02d102c1840d1104407a044051030781198124000411505811f140050502c03c854100c039441980301c812440e00080d45a28501c02c40340407404981940000e040150ba18841c2444000d000402e10f00006501341404420700780c1160450001296031038480d5810016030700904a5030352140e00c45481045a568080303002d00c01072002003200c5150908000043c01c14440c003e0014207014400742510100c03100c044510f2000700000000c0d2001c4201918054032460146481664003504080c6403692190000404800038410030741404109140515030920315034041030703600782c442c402d010484460036003a0001c0400e000c0350800016080306c202c08200030030340c030f42040c03070b080105800802c080c1c96044401c4600b001ca0b0303801d0035034880130148001c0c3d0241030302e095043c1e0240a0807000280f002 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 974940143 1250 974938893 974938897
    0x30b12030d0b0f120604170c0a1106070507060522030f0210140c010219180302041e18020a0e04030f1d040c02010b0103050a02160f0218070206071b020d032111 70
    0x40d1068a000948604c7c40144428038000c584443c440c541155500c500000d191816126a116018120b2400c2c04480e440c0c060425815900c010042240001e420030319010551a0200c0c4500d00300c0030320003041c02c6890700d0242180e0100001c0c05010501c03c1f500303606000c0d032461551810007580c1c0c01d940b403070802d44d0355020390045150781544e1140c3c4c0d80102455402800d1200308082601400b40000d4555002c01c00600f4104204609281e141d403513405070f5141502800140c0440803900c0d0a02c0080c1e0300c18008020713466070011405201e401c00b40030000b40d012000c3c42c0d0100e622f182c54105c00d00c1000d0074a000a2880710810f920a1908450705a03c940641102483d008241c034100b100ba0386603104182a481042420480092554003c40000f25040c5c9c0302c4100d0360000d4002c0d8041d05403001040d400003415101e120240e4411020000c3c02d940c40300c41d25014119008400c00340490300e9000c202d9440661000031306025016100b070700d202801001300c1c0170740114400d0a0002c15402c00c6408265 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 974941393 1250 974940143 974940151
    0xc070f080406050c0c0a14040911041a09090106061b0c090e0114010501081006110a0c0e0a0b0f060909152106011211060a0c150b01030b12030d0b0f1206 67
    0x1c1c003c03c3e05d111036516024240c001103c00300102c0002034900300b01044000e01e6482d60440701d000b690f041c0c2d03045513181c5115851080c4007000e01031004481001c100022500018110344046c1c1c1440170a010b50307588500583c0d40049a40c50100b5910323903900d0a220000c00d960059440903142031000908401c0542000050b40040c03071440c000707071762250011203a100b403c580c40c10348060049001c10100d4420415000d100c01381c413050311000303c42a512820a080c080c0c3c00280080170311020f01010a499201e40c6145050460307000d80c203401d003100411802d01456428600c1800610001036900c20b0180c010612407a0040c03644051100c00000d000410050007200c1c151407003010004503103204180d01001500b9000403e9800c0714240000b003001070351100d101001040201103010000030080a00701c0311010340c030300317000c2404045400014111058034626070b1260706c1c142d80355481c1c0c1070003100b00c50081c001240c010404910003000316128410a82049400c003564000c43c1c0c0c0c1190022074003a0103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 974942643 1250 974941393 974941417
    0x60c031c050115030e03220302100305040b010b090a0b0a0203072f0111060a0e160311040b0d11091302031005060907050403031e09080d0c05240c070f08040605 70
    0x308907021242102244d09003a000b02180e40100008008420011001d07c2ca000650b000e441c000303030710b80c3e000c10070f440590340003600031a071030b8801c4c0302c10820005001ca0141052655550070314102800140c0108241e03c20030b0032090000400d80d08091007030045541d103d411402034440c840100b40030030b0906400194100d100b004084030700701c1d251701ca402e600410f1408040180035a4580c140c03071400800d00c0762815400d521944c403801030001e43c0280c5032002140120075410f42020b0b038030103000640e000c40083c50310074079203c0a00000a007080e040d00103231070f505a5015800d0f41c0d40b8000c800602940c160040d40c10710400061440000494102510405054500f6256038a41d0303401070b2440e01489c003005021400308810701c0a010419104902c14075510300d030000d403196543c54030728200007030361129800251800707181500348002009100840c44d82119000d40d1004014000080f400f000341c281c140e6101c002072070307005001d103941645c49450b80011556580d03964030b0360090b080703620a00000e44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 974943893 1250 974942643 974942669
    0x20a020c010908070b07080c01020c1b030c0111060403030b040b150c010f02090d0605150402070b150306010f09090203030d11030703050a05161808010e0d02210702060c031c0501 78
    0x203e4420204e0b00b08101c1c1d00c0200c0300e070b0400c0704940d6000c8264000d21191081c540d030900502c030245108000c05070107226800b2189000705c0141d01071501b48200e400c5114184602e280003486c1803640018940d0f070003501407400203101030400740018081d0503500c124503803190b0000404111040200001e051100100008100403139040194806138098083e1159000e6100c1c02c0200114120790840c036400000d0119501c411410b2100180880c1c05c40001640d064810700b0030000d01d4060308885205480080380108210b6140003500d0208009901520303603440e8071442032204540f4108141c54158201300400e02c414010550590340a402c100e540400103800e2001141248080380b003454051274841035000c0045a4940c0c094803c040300c52045001c2000598002130404000c5c480c145100e1102c60103030070041a0003d0085c61b290786005407a90075030100b2840d007605030185040300c001e258155402a00c841942451034214090035101c99246101103000302c5111409030b002074140c81d1041c110503 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 974945143 1250 974943893 974943899
    0x618010801022d091c0b0a02190806060910121406010807140f03190e01020409150f1512020f1905031303030506210a0204240608040312020a020c0109 66
    0x60010031060b40800d540c100101300c03101042c2013130030301650480714490141714410b50b0343d503504681ca182107030002c408030b03400700e030066140c00e072100350b401150703510b24080c4420309105000842c21702c100c0c20094882e1103a03008644c0714170302551000020b98464001000107400c40b0403440d643c24812031b01140054400000284501d0140c0134400080c050901c12509200d02821070080950000d0a079442d000220b02020440401c1800794079001e000c0380e0b0003da2101d00d86074181e003c3c4d5900d114100170800e02c40b07006004007007054aa11084031039402c1002000e050904c0192003407030064443d80740c0c0b940001510301290809070700400c4070072a091169000d032001d01001721400c1c04181e9035022010302a5601401281c441c0e045076802548c000c04001c1d5040c01941003640c0100300314503520194101003801429813616120b09a08040f0740c8041e02c042c4243d200c424089081c0320301810b014050f0f81d9000c2400d042c4205880600780c00e1115085544032030414010355a1002e03000c055000540240000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 974946393 1250 974945143 974945197
    0x9091e09080a27090b061b010e1b09150414070c12110d03050604181b0e06090712090f0b0405160b090411070b0106081602070302010c0b061801080102 66
    0x10f500700c2001819804541400c06031504090580103202c2030b4040020b01650103640030a10190030300d55215000024400c2e400340c52907081030000265a50004802d982404d11920703440d001c40c1d030285020031a5004084c42e00c002800400c0f50035440025500180c0c1040103a40d00000948a443e004a00030b014034285c6010881d10004500c08d07034141600304805801c0e040f402600255000503000744007041c1d182d2003a41d188581905020152102c1c5400954000041554100d50307010708440070800049150500c0481c070402805451001000305054040c1e034101c100e0740c805440e003a0302090b1a054500a800d11410741c2c00d003a02c1c03e8449000d4869940303034035588607880d0b40458008961040c101601e0300e0400c0003d100c10002002104820001c08000030000c2c03c00314040c050907201e003480e0b410100013402140e080a00d07030100350752115405201503a0410502c46035a50b0101000c00385540300d00100b6402070100040c40d4403040104008900460b06402412141c2c1c400107030307908511107084803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 974947643 1250 974946393 974946437
    0xa1b08101e09050a05011e0605040e0706200304030c0e24010f090f0b0712020a020d0f060b0a06020c1219030323150109120309091e09080a 61
    0x48140e900d80a046107884440c40d40102d0040c80c090415aa0505019218242964030000603002c01e60340e801105080a0740e58441e0201a0606540400c1000c1c900c1540541e00c580c58000c030003e01508000d01e0b11000710f41d0f003108410200141c00d0340c0d195a60307442e00001c60300c82d600890146000810018ae414500700f2099107900703030390311201114042014015941b403407801d100e0380200080030a02107441d110b94144d103c01001c1d03001a03140c4e640400d040c104a1410200c0c4d114003150040b21291003da0740382c5182581541e004000400146594600000200112200310703400070000b44000a03c0d54010520750039106040da2244041c1074400c481ca521646c40078121f230b00c00c0324007080c0e12020070301c244d0215241d095090383c0e10710501380e01080c04030108011281c52590003106501001c0a50707112074640000e0010745504074202e481e07543d01070b0800e503041c0100e07404c480d51403025103030107580206a220002000c0104105009407410590400d5011a58a03004242c0700c3e6040c080804102c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 974948893 1250 974947643 974947661
    0x18140d050313383702060c030403050301140a05100f0311090303040b030a140903030402030d080105060a0e010e0d0605150f0114070201140301240906020a140a1b0810 73
    0x31400414140e0f05849056001981002000c82c034a881e0312150241680c80085101c541e4409103014640c814002031a0060042440714982002e209020000e80c000060b40d054584c5d40e030248420141c498003241c0309000c07e0b40702a51022001d08040d0030039401101b41070400d20300b60381c24400e03c8000c1402054901c140701180d60541d204000c10000490050085d6400043e0305070045042100400715501600f42521282c0c160381000083c003085103400c020000404101d41803d01107585481c002400b10700074100344406115005155001c5c1361b00c6072070800d203021001428901c094413075082c014001c2c4009c844100a41840d044144c5261814901c2c005420805942d00000f1410941c00b41d0441d4001c8841281844815280800c0c4040240c0196019010300d190740501c10100b40d20b030030009880707601c0380c0c1c0902c2030038601845440d13804141c5580283e044603070510441506602c091514240b00c40c094000514680010140212041d00e04201c64031001113450314205000884111a1001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 974950143 1250 974948893 974948969
    0x3040308150301200d020f040803040e1e0f090f07060905010e0402030411131b03050a0b01030e030409200d060f0e06010c0b060d020d0b061018140d050313 68
    0x40b13060107040031100051a581c40c10200160400030500c0c0c116009401a402101250300082000c0c0704004203801074651103c0088641d03800701030700c641040c2d04481c0207002034400c400e1100000d02408400c21251101506141c101e80c82d603541d4103001000900c05000d4580000c0c1044810512882d0038025240500d80000c1084910382016080086100511040707000075505d90150101042594040342600780b002e450214262912002c801c00b220480d1024906240c034101c505004089e00100b507074251461158002420180c200c80e4210501c0e89a203603041e9480c002a40c500004403607048007049901a2400d4001c40d0b441e413a110b541000c040365504c0c0001c200d8004000415800e80e0559001400640740c2064040c082d004100e50202e001e2003540c4201d0713040c061141c282000c0184180f02602d0346041300d0008912076441466001da4418800390f441185d00045a940d038040c4009100d40d403120440f0341c0c962444510011240c21441035115034141d00101495083c415022400304059031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 974951393 1250 974950143 974950181
    0x150f010909050f0d0306061b0b0103020609040605221d190804080303130c090209011407140307060603030807050703120509010b0d080310080c010801090e0a0803040308150301 77
    0x324061a0062034200400d541c2842074541d685568001801076a4080c02169404940d040c14150f020740400a6408142401c9485081c1c21020a401082c0b00e410349a04803012a072f200d441c40009405414a6000300c0d40c044003542303826603e400d03940000c00000c04c402400348a840f09048002d01e002c0030380c14804045420032040440d885c450780a1111000d03128140a5091544a4214030b1464008030b4070a03000700c5d001d20350f90003404141c1003440c0050803c2c9009515014012000901e0041d40742a0208248030108104e0300300310011a011440704200021252500c80500308031028256600c4141c010894850204a101d03100b41c04607001140c254582a420101110781c071002080010240c8500d956600300d00341060f603a01c00200f40b5907004d0640c190b2607040114003048081e10a84c40b201540d0f0145e6111051070760400e250b14116480102c001450300b03040e40002e41000c22064000704412000000c00080681041e81c4a019000c030100d641c030226040001e050803500103404c110484190 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 974952643 1250 974951393 974951399
    0xe0306010b090303390c031f09120c06060e010e04080315030607020f0115061b0303090605070c03080f0f0c091201060801140a0209091b12070908150f01 67
    0x15a401484a0710000d403c803481d0008140718030403e0702e0700900400f09001045400b804c061171034140d04148007008030182c00b019040070002540d8220b0062510072103425840360b03080101d1207600c01c540641d000003c842c400031842c40010500c2c81c14103800c41d0300504e440d8010446810050095040e20b003200072945d0581c5590301e0700400e030342004000e030b08001d2803c0c03003001554600f030003054011000c0360001c0c130303c20290b4007d4a0a41d001451a05121104058104456544008103040803020b1881c2c851030800c5a040403809001240070292040c2c1c00c00c8240030160380c2c440c900740b481c640642d031502c8690700c0c1c4003400f40700b111007500c0c02031494000341c020030003074444100200000c4a0041007221881840c80c04142074074191343c04118a82d40d1a0728003041840c0003410598040440c0008624000031400001c3c040c08016000c1140c45051221b0100b545036170340c04890030219001103004091070001c0c001000c000241c0110242401003509401a0580c1d240840780144602c84080c842a82 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 974953893 1250 974952643 974952659
    0x70c08061003060e101509060b090d173a021204060b0a030209010b1209120703080406022a010605040926071208061c080901180b040e06040c0e030601 66
    0xc2014071690480c0176001007003140a01c0b030303c21010440400040450f410f841e10321454115055584265041013040040b41160b42d83c0803c0300d03004a52000c40b2256040c40e0a11a40441c05112850700500c504402180c05160803c400710408000141003052007c1e940c401200aa01842c4e000b20060700c5c034580810000f51700c94010340710850000e05901030301075881d0001f8580340c9081e4000301c4c03555000150f410f00c01c880b503a4019482079030100101808000748031005d83e903114510001d020042c030880420704100f803d0f01154101c11042486402d20b2003500003240420111180d02d4001d03600e40480021141418083d180703441d90040300d02800036802c3c0d141850b00c96403001a0700e0b142d13002017240d000000d4080020301c0b450001035840c04000e140c40c00a1059214620000000c0c4140b81d0f0308144c0014200c0f4201d490303c1c43c0a1810b0028500080000c0e95100800c2d00004c0742070002040c04101c40841d004120311984040701c05100c0c2e080647c074150b42203006051010380640000d001405001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 974955143 1250 974953893 974953901
    0x601051903032c03030f030a0605010f0c12050d1a01030c08060612090309060f0703080730091401090611070c030b0403050f030f0402090a111b070807080102070c0806100306 76
    0x6400e10720914403980483c0000c0c10341c2d0011950075001c1c4004000d00003005103034411100504028201885c40701c01109002c0d1520b80c83c0d200052960650081c42c803206031258056403552600c400d414070200891034010507042414000444c0080e00e8211600c803c07078400c40c4028051100504124078140000c01500900c140041880d0240e00c003c100303140ca66182ca100810408041d161142c0e21100340d480c0c02020824040d00c10b0b000c00c4501c10014520301c1c150a000030f01800b070b2800c1d41102c4100410503070040d000b1988050302c102c5903103103120030802044d0440c410300c600c64641042962a055801402401220406040740055540c10700015411019840d005030090420134100003d140e000780da0741d4000c4540c2c40b800c003210000d0104504048440b96000710000b10300384158202800700d00ca66000b01c1403140204080a20380808074242440000060701490080c0c2e1451750321080d00d40d0103907020030002c03100070211000009040c2c502241d150301036a1081900c40c180b500d51345510002d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 974956393 1250 974955143 974955197
    0x301090b0d0510050405070f06050901030509012c1504112b0807061131030c0b0406140c060c07171209190215030c0f0c060105190303 59
    0x801c1a074101c0c10040b800400484070707440d520880105051415180460801c10158040000c003494500b0600007241c1101c190340420400386000106681c07400c50603405424020180d8010110704040c14003480110100700c09035904035821122500030800c56261110801c0360b000e0002c0c442c05804482600c0c0c21001c4507007132040425180302501c0030304072001c078000c07000c082100c0045002804004000182c0105244075020b050001d04140da20000105058005802100599010f038aa61020f86d040301c00100030359001a030030b60702e45450368a01c152640c054040c010100701c0d0814649454528081150364004080010701659111160715461941040c04210b0b181040c50a4941e07488007590082c04000d21f25255807200f07820071003842c80c142400303070212003101800109500b026807074000300380e442244080d085640d00c1e50303000814999400741a0481c940c003200010b02c8980520005076460585408075010040355081c15400000385c0316600c0010049240300380b000080602e00008140a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 974957643 1250 974956393 974956399
    0x11041b120f020f0301081b1c0f061d03180a0501140904020405060d020a080106180501050c1608060114041b03020d0906021303060518030403021017070c1208010b0301090b 75
    0x2d260f10b02054403540c4e0801d0f08210f0b0a540105019000c0c403452000b00500d062041c4c81121081003401d010306840084110043c0c48214032189440030040c40d0fa203d502c0d803030440d060076040070303410340d1215850b40d0080025030a2100303102c2c000356541c50401c030788508540d4140c50b04112a804100301400c0d036000380d031000d944940d0034040080c1c1d544468000744070140c558100140e071810841c0002c0c0144006800410401c0810032030100758504004a60061380c100342406a22601c440f120742c0d1806a0070b00c1840e501031741075140000e1407400000d544c1d040e240b0413105501c91b04074120034041180c01c11171210080308071681030304442c24081d03801003980c07800f0080c02050501c1241c4440e810703640407491424688214000170000e01246205d42900031011603a608840000108031035528004c034080644211031500c5085840d6008803c60044038902c210090b01e549010700000d00304101c11802a42c1c0d804010000c188000d104408860684d551100d600d411a420644468010080c01315200c0e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 974958893 1250 974957643 974957647
    0x1b0804031d0d080a1701141302091203070b13120309020303091e03070f0e040308180a051c0f02070b09121c0905150702041a090411041b120f02 63
    0xa5848041061001c00c2c000d20f03605075103504002c8000c00c0e495504400030000c1242c503005000f4034502031300c0d9030814001120392901c0d030158441084001c0c440c3c2036009a1141003480721800c850800300140107402c1c0a030054074819038030514000140b4117803c80013811154010b1111300c89034040ea1100740a2030002d41201c0c109003101002c00d43e080b0f1780c10b4116000d6120458210140d140810040014003502c40c0c15100c198500640380940710005000142440001c000007200a50640b0b600711003c401c42c8111030b50141c00d0300b0302e10740305c03d18110500060080c1001700c0011030b008108110540c01302c0e42c010000d552812a1a10f49904403c20080d44141c00605800c0b035200100314400910f02da0140b0165039500820020b040e420302540280e0181901625001c01610010306503251141c05807000305810300e0591643c00e03101d5405080030b9010034680280003d11400c8000c660074150181c504000604e5130454507135001e4040c16540002400c600c0030904800310a8000011101007250054 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 974960143 1250 974958893 974958947
    0x216060c022b0c0b07032f07121103040605031509010e04020f0102030c1b03240112110a18050a06210f0c1e0e01051f020708071202041b080403 63
    0x2107810a029500e01700061f450742d601341030960900f0a0003e07010002400c43c0ca100d804602d50403440d00607070303c0c050304400c000325624202d540900d40b4400c2921400003540d80e5143c6030740c0c01404030340041d605120f0032402580c18602a00303101240078141c4414003a813031030b942e4030755017081b00c580098404141107020a01c02da40c42e0040c10810030400d010305201410105c1041028946845000301c01051898090301120018038503041b601070540d40c0801041d842500d0908001c003110101039201030704590700400000d40c2c85416114290750b0702d020304050226484440a5030155040c44c000e146d01c00101683e1200c0503244202c80311400d41c4159441851450192543c104101841e4002d01265103268160580c444489040d04040c01407044180a0365040201250448605506c400303640c148400c02608038a008210390002060003204840c00300380c88046296844402c540c08900a0f8100b101407010401c45480b00c0389006050750b103403900743da01c5440c100c400350701890304900008903040c0c8036 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 974961393 1250 974960143 974960153
    0x20604030b070c08031e0f06100c0503160303020c012307120e010504030201050414010624021606090501024c05010e0403110610090f0f0216060c022b0c 67
    0x14511a5a40f124413080401c1240c0d01c4115031a00107107e80ea490704940c3c10484556108002d02d14060568640000304862030329046c1e00d14804c801e0b0410100136030100342003c05606400900303605020700000d000c2003007625070b85810710351900c0801000c05a42000115554851a030821aa1890b00c01c040340ca00d9140340c4131401c542d801c0e18198010303511141000248540c03c084c02200c02c0303e410003005201c0c0740c022290320904408110b207041d60030344054038401d40d108000d003c065080c0c16411400c403e580349006012040603200d01800750144210a03c0c5611426880340c112085401c10444075500c40c800d81146a12507541a50806440e6403000c002520a4807641d80030745810000351505062600f00a0000400036010300303100c2d48540c0810024003801c0c0c80080865410807400f0801e2003440e850700c0081c0bd01035400010701440411101c140c000040034070300d5200e0194804000c0015400001c030380740d108503032450b803140303007003c911200c0b0300e9480800106650181c90207825510156170f0b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 974962643 1250 974961393 974961397
    0xd08071209050f01061211040b0105090310090c09020f0405151b010903170c07142a1201060e070e010e0a090902040b0108090d0302070c050a060215060904020604030b070c08 76
    0x1040d6001d51103c100c0040b2203500b445428050704a41101000c0052507564031010112281030040c012512070b082c7e40d420340d00410a487da000300041c2920350341d2100840c00b4005000e5040242e41c1301078990400543d40e6030300d1088401401c6d0a4220610307050a103018000090021610140c03000c1d010080160129041c50702c4502c2d11865100124201c13030a420001c203107100e5a01307410160141e84040c0b0060008040889400c607a20105403001124407208150400010f14079000c900800c00c0c84421704043c00c1ca41c0c41e02d06110494051500c1001079842d5401c0b40c0d00d40c012884510185400300d18a03500815421a00340c9051412203134108011000c180002581ea01c40195507803900b10f040118a054081c03d4102d40003032030902c6903440c00300040c69403440044012801c1c50f50000d1110b081c0030790744c4020030142202511000c0019540d800003580c0703460561301e000300908884007080c40c600e031660b005409290000c040c14285400c0d038560744040c0c13201a011000740304030006080c0004040c580 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 974963893 1250 974962643 974962661
    0x1031505013c02120405060712090801020a0207170105040209040f0503041e0302031b090a0b03030d091406090606090412030f0504030f0318020d11061b2d0d080712 72
    0x111045101070b07903401a10f0082000a018041302d0288414400c548603441a6800150014140c440413180c24400340c81281c51750300b040c0308035400001c0c0890215000100f40e0300721880918514418641c10311414200c070300c2581c00961007141c0e040458045000e05544002e014001e03001d17249000d5681d0419202c504030184460500d0501c281c081040d07150920240f00e070030b882031000c0c0300404258000030f141114001c0041e02e68680d00c000c0d80d000c0c0e0300c6c104103880705c500d00c524080151020700c0c01e004150f143e54680c3c0220500c0f526000030002ca01c04280d1a0142601400c20303a559200c81d59824035108000707032801c003019605d00c020900b10a85005107409180651540110260610002070544140c081d40580f04c0d0403040c0c00400503121a001c10740007640100114854090140005005100d003824030101c0c0c01c5010170809207480040368040345c0d40e80303805e070f0070508940c5490b14504804030350035980c0c1d440c0c02140c2d030f040c80680142d15082c0e004649242055082c02e0750840d01e012100011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 974965143 1250 974963893 974963987
    0x60102190506060a05060a09180b1e0a15440a0509031206040e0111121f0311090a0b0a080318060c030f072306150103150501 55
    0x1c003480383c1d508211100340f02500c0e042ea417142c40c0032614074000d0306c400c070b030b51003000e8811400c010b44949806140d401a0900e2000804209007046c1d0524078007410407244820503c04d5520704070000b050001c2140b800c40388030b050780f55001d0414004550095440300e941d000c401c018507840f0340109030340e00d812a525010351a802050241c0c2441252002202c100170b081e0070981c0e004002c0300000c691450780c95503020700115000301d140d1098211031409844481c20710340500b80302250070081070f00c45803821803298003643c0014a03040051940c11400780c1c0244006456820b00b01070340c2c3c03060308181c080142c0c000c0d90714401198540109010800e00da000340d024020581000c01c542e580500d28003203920a01008807549030401c0060b510050f200e2040144058035403400203980300800c03107401da103041c900c0c1e0390004482490b1480c144440d01d8080071180c2c08840c21441000600a600900c200c803040102e800584684030305040c01074400b00710307189250a484d41c407021901d035904050700075401001209 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 974966393 1250 974965143 974965153
    0x90b130f0507020c010207050a05060c120c0303070e0406031e140303010b0909090a0309122d030e0306220302030708030406020c2b030c051c0b010909050105090703050601021905 78
    0x402d40007414007240d00321460454001000400450f1380740054001a1282160f030540c0e070f00d032003004442c0303000001401c640c4080c0e00407800c0d081c0694080080c5129220036122600002a2a0200000c440445c00014000900d8815030504041c0308100001124442d01020014440b0400d400c0c0ca541c10036400f050a2000c00a101070141c00e12400054114410344024140003015030382c080c01204c5103015202e0b074000c80b40c854806001402c01c0e0345900200c0074505540c25254440036142d21900640c2c2076011500102c041c0009003000110342d8030420450062055002820302510000c1c024600140c04610082c4002d13000705000000039800307244601001a51001890800c506009071111248100a1050304000d0b0294411520b010350155038540001c10500102e8255468083d64080c412100d0002d9005800004550700c0880b6980090300c070240095910081001503c400340110307600810808041265140281c20540d00280140182d6020031505554601c1d2101c401000b0380c3c075a400b13 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 974967643 1250 974966393 974966401
    0x1060504030b3115110301030c06050913060f0e091c0e0607051603140604050303060105130e0a0504060f020f120a060e1501140c0a020108101a0d111201090b130f05 72
    0x44c074801c9901a20b071450445003036624503144c030448020f0030700c2403400380400000d10a41c1540c3d06442d4210003d10722608110940e152050800101000e018240740207400002064803601d0004100000d10003206503205409a0070030100c43c4054180e8400f50040c50501451340040c00c1802034104200303d009000076401d1441c28a5081a030400c40103a0054000100b4880840c2000c02200d5100c2000c1c00c1803a80c0308000500198502910b85c0000707910b2a000051200741003440d000280141c0c0030305018020010480c00c80c800700e103c0c03c161411090002c0004203504013100302056400b4200190004030a941c4240e094485041140c0c05000d8402c43c084106240da04a102c107005890340311141418240402e9540307680c0d2403a003c0c00303070500000a00041c1c440010241c036001504828070101c0429282c690100c2054201d4161030140504010261041c1d180b1441034440300a40350011110b0b507407030501050010000032031042e810030300a000c50101c0032014015a4102000703840d0004e02d80c58 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 974968893 1250 974967643 974967683
    0x120e0103470105180a0b07060f050609060f13150f09060608040f0602181207052106010e150d150f05061003020a020a210801060504030b31 61
    0x1041d8400d12401465031840c1001d00d0342e02400b035601c0440c010010072000003400c80010044802c07030784400400300700095100108207080d0050340b1000015403003402140c903020704000a81004a80702074002140500d2048545401015041e900c0d68401e0001112060b54409074815403160b0043c07031250508090800080c1c00e1885104001e00d00d52600106a04007a5619007540c2403081014100a802003035031810180035070940d80e2282401019040c04074000002d180d1a20a58400c1d184a0310010030000245600da088003070000208801170280c603820a1910200b02401400c420a051480c2c509034880c2d840308850882268018152140440d078542025800c1c2c40307a0382a28810181410306011894880b03200044602d1b6650030090b0725032408200407407902164000c05050324450090fa03401e1228041c3c544d445054551f5515007143e030b21100107590a02c04c0d0300c030041c1030240d00000501e1002c2112255410049014000c0e218021703040b00402500c4e086410688081c103881c0d0403412055 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 974970143 1250 974968893 974968991
    0x31106070f0b1e0108030a4a040b03060105061207110d0c15090213241409070507080a0c0327170a031e05160305070302011107120e0103 60
    0x8000c9800940c580a00758000400942c00f123103038140714801120f12401c95a0314440320aaa4041030105c0d0035050403802d1107543c0850b608443ca6000d070385031403407407030313040c180400d5a6041e2507000e006180b60400c1e018280d071020100a042000304280c110072803000180a0000c1074a4110546e1214144e000310304150050348007185580d290307580340940300300040e00c840062820b0755194641c0028181181d0a2b108442c0c54004e00058012030489808100b204140440d008040703800d880c010b21940d9004401c4d107561040c11006420200c041c48010052841103000c002c03080d01c0307480c2000c484228207500149900150b498945015640e203001d1298400c1001030094807452500200195512074801078100c0d084030480a6481125001e00d50324580070b00219000e80d00c9101c1842d0384000036007002052600041411801542000074058000e625003003640d2005400c2192000d2880d62944103032003d20144c000941450307141d450300718840505182c0003982034406e1004000e2001500c1da42c49080b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 974971393 1250 974970143 974970149
    0x80d0203070f08040f14070816180203040308010329250f0f08180d020d0f0804121209060617071502120c07090515090a0501031106070f0b1e01 63
    0x414400100f001040c151040c041410790001d869400f001380d6003810b51f0a0508503000300c0f04920540040d2414603082c0080001143c060b152401044841113031000280d1109440240000310307120014004200506080c02e8002980c041c42e0304186400001049071400407103104c0c1d1801003004007000c50414008980202d00901d1400e2109030140280103010714000c00e00250030030a210700025032400101e80501c0c032001070032084520310201072000035501e2030394402003000201031a00ca481c40f9030107500b0703007401964040101421403051400843d650012140500c0080e511001004003094003131040c240502422080d8101c0441c056900a281c043c403903100013040d518000400194642c0031030001d10844039000c0c001e0740e54030341400c41c600d049900d0b0031404060703203840c0c21f00140c0007200301414186441070710612031b26039440c500b0008462007407201824060405281100c0c500c1c1400007004207074070540d4100c00ea00084d8440c850702d4001140c6c110403452103000802003400c00041a5401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 974972643 1250 974971393 974971397
    0x51309060c1d04050903030a020904110706201c0207110d05101d1015091b030b22050705040f030b01030b0f1003080304080c010218040b0307050f090a09080d0203070f 73
    0x2181c18105c421941e00e01c0000c059141040e80881c2c903200710303074840d080820388a101a21043d15299107082882c020b00ca403034400702c5e52101c91045900e001302480242c3d030b0f140044180c0006416180c0903428040c0d4008101113580320a0300004011039540c081640810714000c50042003840b00c00c010a0b41122401c1412007442e460350306503014103c10020362603403440f0354814089503400004d0b411400e124041c0d00007028a43c00d06021103c003a829014500c501800d6940600ca820012000d01c4000e1103400e402d80d1500000591445603420a604000e4011002d860100d260990311110800c100c006500200c07900c1180c1c100402c00e11802000543d08419041884140c0b405c007501e0702040c1039110300c0000e000c1000800004d003404405030550700f8542e01c40d002956112554410090070714055140382c2c2c8078524140c002800e0342000a020b005455010309141d001d041582d007000300d007141c001e01c0400385903120900c900014060101510807041d40c0c0c040540c80e42010800a04000100412581 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 974973893 1250 974972643 974972651
    0x112020c1e0106080a08072d080a0e060306032508032d04152316050f070b0a0c060906060e040b0c0f09130605151201090e07051309060c1d04 62
    0x4221b800c0c04a94030315a004002410b45002031408540a500710003040310000e0007644030005100703480c03000740010300d000d80c2c0310f55941c4000c1c0204203a900040d80d0b5142c05500240e510000000c410104142002c0f510031147c1d16a60345403c101d25661092070518030601c04044845060041080461116191300e1006802d00b818640400307180705281201350100890a4031040fa8851a5041b5410b00044aa00d2580d82c0700007604054140c034442d84100c400f88110b009221603400c020400000b921700851a45181030132100e01110b080601e16001e4411035a507006200000d042e9109140c0140740401d4400300d80d00d000d042c10035081030005d142c1e8050380d20402191800181c0541269006c0c0c80c22190508801d045d981c0d0b036801006160000e41c0c0100b280c40d49050800c004030050101440c50404024881ea2a50900340548036400c40801c2c41d58880b40b000e0150b8a80401c0401c0086419034001540c02d10ba6203c40b8255801c0d004400d0116071140040c0ba402c40982c03082062101c0c042d20244 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 974975143 1250 974973893 974973913
    0x41d07140c100605040c0f050a091e0617040b070e0109090e01061505090604030209150405040501020903010b040212180f01050a090312050f06010e031908090a050907020604020112020c1e010608 85
    0x1510300c4281280402c20000300040e5114540d01a00c1c02304003400c51007a0f056140401e0202c0540bc040c0240038440c08641e1244100103204204c9107020b02c219801b6036078885c1501c030004103036401c103032942206040c450300c01c1c400f0407445002c0c8611054401c3c0c50001091103407408600c8405140c04072001c00420500704560902c640710f42d02101c08607a41601c203481c8a40e241d1800ca1080d46104001540c094105814482402381c1500500340100b000c600822000901508000403445003a04120b4060440400501029039070f0383d0b9054016451800c0d59a5488000b807600e00b100c400300d078104a00c0c0e0741c0303441100074550300892005504840183c204241c0c100541410030b24840100a6810014002c0c07038544a61400c3c8014950750074411119410541c03240340c0501d050300030400c602c0c0214949080044c5030300c1d0443c0c07401d0050035203801400c0980c0f0fa80e0011a031003400d01081100e159001c00100c218104100005904000072040d0a00000c03c007000e80c2d82074a139143d001d0074580d800010340c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 974976393 1250 974975143 974975147
    0x903040e06100918020705010e06040501110c070302101103070c030b0105060301081908041211090906041e02010c12170106050405150d060b0f04090c05041d07140c100605040c 77
    0x1503065a18030082041c401061042c132101038031034503d00500550924210105c0001d0020b0000c0c0160b1180001740050510114039000034007914940f0030a0f9032042030100098104800342d00c4602000f031401285800f08400b000f03103103910146040300c11056400040003030102025505002d0312040302c000f4915454201801e946581c0c0140d0b403980808004075200410401c0801c40740207200d0402d58000b00c0089050801c08401c4241103640a08031440019030621000f0130100d1250354032204207007101c0c1d541124600440380c0018101d040c8100381100201041088036910f403d50086e964040c000e50070800084031100042e48000300b8088144018007055070b412030000c1c40c1c60078442400e0b4031076543d943c1c0300c0040c21166009041c600b000061100312288200010000c2e20034029003403050f4231004c5d9007202c051040e8420030803a04c140c5440311a40c0442d004601790007051914102240051071030104610b0741c0840341154041d80980800074a015543c09901c1c0204011030b410442c48100c0580 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 974977643 1250 974976393 974976407
    0x9050601030b1f0c0534030b04030804060b03030d05070f03050702120702040207080a050a0f09060203041a0d050705180102010915021b0307050106090e03031005041d03030903040e0610 81
    0x3015140e0400f00001c1e08001c2d104503910f1070b0043d0014200c6030401948459090f906444c44540c05404510f40c1510f403000107000c3c2c1d40c00489a00c42c6403401242d99075202104e41b02406801190066182c100c000c0450ba4200090428941495030004a40c280500b02400030344d0460304040c2403506000800901c01c0c0c0200b000c11110b802102011360320641c03440000c00034403400d140100300c40000705065a40bd54030101030824040301c0d4840000c481003030b400c2503a080e1014854040180d001300028070031b00c0301d0425000700d0382515481391800d001c00c82510605881003114014005000414008154455460310a41e1003500307000800c079440441d00c800c0c8400110030f004014841d00000e83c29840d003a00c4d0b4112141d40e000c001540d40358200c514140d800381581d8801c840d00310b030070180c105000c141d0120442e4003501c4501e015a00c82c5145c2810301c00a0071a1495031000d22400124076000440140700440c421150800034540d12400c110b0000780181e4007a080500070400c2c10350384202c482c1c010b10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 974978893 1250 974977643 974977669
    0x10501030b19031e0804090c09121203150b0c010c030f060b09060c0703020a171204180b03030d090b040b0c120408031b0705010c02071a0d0b04180c09050601030b 71
    0x38401407040350195407040f641d600c020040505c0390020340054094066806000312016960702d101e00f440d6184810610b0701c0d02c4200103031a492003800c02d2408c0d140281d0103030902075650102440708907926800c000140d0401c1c115a011a5122001002030642c507101e00b0032160802c0104000301424156840400e004a40c12240070349030002d08280009000c200704402580c0c010030100030303180c5035000d90550104280341d00f402403160850584152040000359401c1d035141d071460a10100c1041c101d0340150511030b11485d01804204200344c0080014040c41c00440d018405c007046500b0705161946c4a2000203041c1090b1803024013081d241403030b0b031040c015041600840000e40726110303480c004075480e4094041c21030080001614108016041d040303210074041c25001d41d0352a0b42d5820700581c40c60300000c4442c07d032081c1044403075583e4142c0d5100401d42140540001807468544038010029101e007039003924544042202000182800e008e45071380044203280070b0003e0030b00710f00071507266420700e1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 974980143 1250 974978893 974978903
    0x708030a0513080d05040603050f0f0403080402011e090f170703150f1a010f080105010207090c02010b0d1b12030801091109030607091a2a030415020303010501030b1903 74
    0x201d02c20000c61122a40700905294800c1d9040c01c09102c10250203680b140c41801c0100e41868000303030310030ad00600070511560142009045d541d4595808840303c2d01c008000f00c0c1032003038809517002a0501c450303685600b03042513110540c0d541d041006400d017040895010720041c901c402d488000ca1000494540101d0b6405a10010550595507100002d00801a82091a203160244900744001e181d840c040000400b070321106a0000022021912083d0900607180980d008040030410102c00760700c5119a0401c901c000146208104005001e0002107441a22400c9002080d140b1100340d450000c00181059403140101420646c1d0113031488405100f881b5159558608040070b412703142c02140c981f2072004059510b24a0803072005403500302c0b1030003400c94454035410b54a41e5076500740308071040190452101122071030000c1c080e510313a02c0054003c2c03126000c00e00001500302c0c0407000140525117250045c545a41c103220004044420700d5010314440c0c0110382102e000100401c00750016a9001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 974981393 1250 974980143 974980147
    0x11070308040e101d040204390e0d1217011a0703140d05041e0201020c0f0117040b011d042321070507081c080613021801110708030a05 59
    0x14903103511844a41d03a1200109141c00081d5603001030301030b13215030300c07507442182e013000000e100c514200b541c03440c103036104c0030f460042c1400000340362600c58070500100c0043c034051900c3c4580b40f0100f50034041f010002c54040084a050746001c0c2d8001100001040103020411095894100740f40c941c1010601444825200059004145403085548a900241e4400bd03141e81d000002000401030074201c4058400401604200c050141d03003a44030413407160168010320f6410501c20421400c010350303050150520460402514000124205042c4142c2c040d840d520107a42c940024071034040a8100d0401903086c81e2010407001030f003400452804a8066442004483e964011480c80e000041030700c080410801d0860a5904115200030728800e4801c00568200c81e42e42c000c6150342d81c3d00131030080d0000540c0c4021f8103010f44600720b69135225000402c400b615042407507003081240d22003500410340c00c01036482901e003540c0100789109020600b800600e2481d15140b00c068882c01758604003801c0041c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 974982643 1250 974981393 974981401
    0x30204052a09180c0d290f030c04060803030a050603011e0222080a0c080109030503061207050d0c0e1602102a0e09070c0b04031b0b10050111070308040e 67
    0x44000183c0148072600c0c48411034201030f80d001c035441d00b101c0d00684001c0d00f081c00084100c1440c5c00ba0444500155001c102c070000d5036010020b1840008a009406100d50300b11450980e41d14012030008004105c00740d80e80e03040814082003580c5009001901980c10080c031010261080d00003076807000c80c03000c401070b03c80c040320024003079402c14030011241818203420045a004404100405034a00c07030001160882d6403448000e080c0d0341081d0001c1e0219005000007001410300603003e2508101030400d80d10950744403000070700c00c03100910040c0c076504c1e101a030604c003849101c080c03281c203c0d44032800740e160f801304603100950701c4401c5034804121135250042c0f240800039a005d1103034000b0202803176071468032000c40700604030800c1c015950b102d054114042088240120501d07411030b40c00040c0740e007050b07480e92004d8807010300707010100501c1c0050499907008101e00b0341c4024020a000d84070507103030503d08000100741d0a4182c0700005035400021040002401c40340445044a4625890342c4081e0ba03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 974983893 1250 974982643 974982649
    0x130218091801050108030a030c020f100207080d0c18050d050a2006070602120c1e0f12042312031303090e040318090902010806191a0301030204052a09 66
    0x7100e01d0020459824240085a02c000c04009402c84015079a810806940c280030100e030364281e10404c0b6000d5412540014a03649115002030039528068100c4910f071807a0b10b000001180d078050b100100007000310201e42c0f8503000c005441801020f040720010401d0b20151201500d600b0b241c5401054001510780d11220760000e00050080000028080740d1100a907007011030180d40103c200814244d040c5000404011184050761f04d00d0340070a001d0f0f85601c107800754180d5107074424100400c0240040c4852203040d01d0000341c59110b18031a844203c03000003800005280f0000c081c440c500a41c1043d84e81c03a4410000100f80c6c3e134403c0c107000c101da94401b2141001da40b10070498000307406401000c1c08000c02e1540000c2010401d00d02031444029880d65206140100c40e191030009001902c3c0070041682450b099207a07044507041c0241c0ca0380501d03038444010440c1c00043d400c04070341c00e03008801041581f5052040651003440091403401046446021198902609040092580002c14007a2283d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 974985143 1250 974983893 974983921
    0xf02211b01150803090f01030509060711010204050a08031309020a0c0605100302060a1710050d200a0611060105060306030a0b18100b120d021903032913021809 70
    0x20031114156202e45803605100c2da282d5100040070b80c0a860203650b95860f80d44a031040c07510a0421a01408040e25180011109d451219405511540d0240320101d140d5580c220b0400007819014000c60741d5809002902000148903400040780c81d1040c00810291904410130306100c3d54071400001c0c0954801450101c44006900041d40140c000309501051a4120b070f1944120f001368400c0c0b140668482c0d100c540d411803180141034220394241407860004480b00318482d0240e908402004c55443d84801150060059500070800941c0004904541c0301092240a001d082c055644600d18a0401c5c08a5903d001d9080010881d030b01e50400641c40c406111011981e500410069440901440c0c00e82c0018004110280b4070940c071740801e8030060440000c05d4452010142c01501002e6014080c2010346121038400381c003450f8a9040110805000000e0785600b19400b140f47c0030700c002c01c034050100400021079110794147c0b040042210018603820301c880581401c441900403552040c8813290070b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 974986393 1250 974985143 974985161
    0x103020a0215150a08060601050702121e060106110c030d08060d150b010e041514030a020303040803192307030c02030a111003022d040f060f02211b01 66
    0x28050003090051400c41105090030f01c101c204c46400a2503100c601c82915000c05881040c00328104100400c018106000303500e420a600e403054500b6044002240b0301500350008040708582c000c5d9005200254001040d0304548840c40c000303140c8072100c0c80100c1da481245511800034400340c0b400188080d41c500640d084002e5102129500303001101c55500c4c00342002095060200d5158450f41045041501c80c140c801c282580c206c0741c5051604000301c000c42c64420155416020740c1880034056102000100b004014860007156100038180507111f2488400785182d003001200907002008a203241620004445542601035035924107142c1501d00c0381c0c644400035018000c4542540c01d10602d0322140400e0b00054440c04003d0f11180002c40403071261030f801100d1074190310b8980c6551594029800940d041d0412114074083d20307010071134150109540440e0021341507074000c1b03000e20340c141f0001604500651004031100c600e1149140140119001600000e140c041c180303105100941048107a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 974987643 1250 974986393 974986423
    0x110d0f0209120f011b0c0611040b120402120309010c0303020c0a120305040507141c141c110a08031306061502210c07231c0308070315050103020a02 65
    0x4805036007002c82d00c500300c2c0baa03400859440c1041c5862031060411101901040b1540c469079010103e56440c00204428516008030366000d000200b6542003501c01800006111032400c031075807401d8410002e4640015444008a404c01d21080b445a41c009024412507685400c0150310b131020000e03400d241104145c00904108003180340000c10340e07010350200f4011805241503800c010384a404603010a03d040c089241c00070840e140245418200c200c0400e00d507071054100c4400f03c2041c0949501d401c90107080c2e0213903650510401c08800d608228030792500320301d07280a40303003c01316502c8841c1c0e02d010043c00790305c4c4040760508030401c105041d802800070786544020012442410f5400a40e00d802d8046090300162a00042410401094041e200e4581e03540005040d29801c040e8410104c0705140d6600120004215903486c095a42090b41c20b0149140c40361301c0b5501c2c845050042008102400460a06d031401c65541c1c1544040c80498055450a0030056900c06da000703001c900d042d09920303540ba9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 974988893 1250 974987643 974987659
    0x19051e01180c14030714040c0311120603060a0c1223010305012004050f060a05040906150f0e0d020108060a030b090a0203010c0f0801140a08010212061201110d0f0209 73
    0x40041000c00b180a03220445030294100103030106042d6034030714034040c0701045048202240c1403894680c1003250f0480d007038980481d1000703481c0188140c641200d415014030310b10352401c0003540e0504010f856400141030000b40701201402a0140490344d824040c5000c081d115410844590880c0300d00039801e46500e0303900342466030f5904140e4003d00b90740f85255400300d290303050303507803030408030001d60b0284d80d0300400614010340b100041117004d5000c890040103001092100203508200f500c030700c4000300f0318541980040780071070314014040202d03407001c0e4047c81703007801c5092019110022200310090f4282840d064940300e10001070082c004a44c402007a401c1c161081207291a03010a102004074400d41c0280310454542d2025609182d014002400289010004200c11854518000008030340036100128603503c0e082c2c1c05099034044100d2200c0b0840c400c09005c05c900b020000150031000b808020484589a02040c1d0350620411210106e2103031034084429021b03240d079049800c61400100380d00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 974990143 1250 974988893 974988941
    0x40b0d060b07060603120509031515130903080a0603122001020703030603020f220c1803110a0b0906071401021b0f010c0f1b1511040819051e01 63
    0xe0f0141c4514082114030038101d02d5205038140c00389061f540b1480c4001c0280410f24070354410741d40503290003030106004940185070480a500c8500b0f0300040c4811000b40440c40110604010302042c0018200d0b807012440e04d0010800b1601c414115a0f5a9015140804805500c81d10020014840940898141d4400110b0701d00300350b090384c04141101d00c26901000e80c1c00c26001082503d81d10302100ca808900b90301c4a401c0883c2e0107502420200a090400d803214102000420740701440503082114483c9810791400d00c2c9107406c48001d001002c200e4190341c5003441c0b0034041401c5004504000300018001c0452110408080d019120079840d0091810200d00c5103402296499001c620040706035442c0c4549091071510840c0c480640807859101d40d42c052039800c0e8400c0d0405840e01e0103031900c18400c512840e04150602075941144885c0180e01e40315402c18007090f09098080324800d5405400b04202400141c0c0802c25401d8801c0c0c4019504201d11484c50480c0504441c400c1140c1442001c5820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 974991393 1250 974990143 974990153
    0x11404031d01140d2c070e0405070f03080a1209050309060703170c07200a0302010e01120e010e0d02010b03060601140c01050406051006031a060309030c0601030f1214040b0d060b07 79
    0x34442c85e40c111190304411808a5082c200300780211001d07058030741015605000304071841c801d41d0340040c0b0480486404039917480c00e00003170000c2600220340201d800140228019808140b42d609081c40213000c221a02d255642c1956901c900c101c50740c06254040743c000c0070305010ba010b0b1304d0b081d04c02040615141c60078004001c46540012000c5441140d50080c41c0152220140a41090341c00034041c0c098041c01c2d074005407507111b4428540341c1006205642d0601c11440360052602c2c07500040000b09029009400035820300181401c054210385c03400410040580d00050601c1e04400207080039200541c41007981029807040c0314000a10358203080600c0200310883d070103240f00c1c1000e020070309041c9890f10000c806a425800080c12003a5a400349410f1910b41000150b030004206011203140022000c8902d050800c08d03070080d120744200101503030603c41c1d4510501210146403409601200c04031031454903500890040c5051100f0129000c1c1c6d805900c2e9100300081c2c8154100d80383c56407014680 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 974992643 1250 974991393 974991401
    0x717090c0a0f050420070206030a1b0c260306040209030102120906040c0e1303210908030f010b0901050a05160b04080918070e1201060b0c0f011404031d01140d 70
    0x1e59003d2481c05c0fa16411041d4080c811029010350000310900d800c00e40d400700074883d00040c044100442d643d43c0d01c101400e070540540e1100d211b550b120301407028117a0070008103070900443e5180700b0005c0e2891503800c0b40b03105011694022030840740140c440c0d04001c0801e0081c0200da0040490103008402e00006800000b2003d1155101c1e26440b01e0440c0c84d1911450364900c1a103040036640038489008001034021341422070035600e0304c82115501503000720b8080c1660451441561864000014020044d00381e81d41035001d0142c51019500e0031810f4000244107124160262081103c00f280315815001d5662903130701d071542c02c01d080344840d04160521182c50b80c07010080a110b54450807502c405144207126032481340304140c45400d903501c1404103000301600c82c141031641555a0340c1d00468103040d900007030440e8000c3c91700203210f1103991601d5a07007182c98560f6040814407000c020007000a50242c50306000706e014041d02c24080c4801030041e0303024010000302e1141c000e00491000110026980 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 974993893 1250 974992643 974992649
    0x16060813020303030c12061009091a090a0621020a03080c030f0a0f02010e0c0f0d0c1518080609060a091e12020c060721020a05030f030103020405060105030717090c0a0f 74
    0x6c43c460058462800b0800e4403605022041c0225124440c100700c40a01940850f0355406661100c0f14181800b90000d00d19000445244040315511901031060102c3c0301140c14001d101003c500c04d01400580016400398111b04c40280100400500300380100418403d84141c00d00d03140c3c0c2030384c40c2c0640840107130201202818040041d881e0440d075a00c4c801000801c040d032213001078519600851118140401b20b00c003003506031408170b0222000a10710000300003001d50903110f0b50360f25800c511050210301249125034400f0b292540040144440802e0215445400c0410b040000074041e98500e481390101c600c0300c4100744402c104000c01c000340010f13040180e41107000c950135280c0f98410001001003500a081c0041d105603484411001d0620030050542d008201900444d0740e4240c150740e44918660100d401c118486601100401c2141013901815130864801d0a00303904602d00b51800a0803200308507083c1d204090344a01103600c207d014040c00c1c550380406410308103202c1d15201c55018020442c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 974995143 1250 974993893 974993917
    0x60e1c050a12210524010302120a150803030f0105060a0905030a030905090c04063f060311150306040b120f0a0515012105030d021b06010816060813020303030c 70
    0x200c5800f51080f80303200f001d210b0b01003a86500d5101103164944042c50381c010700014141542000061000d003504100760348241035810000c18120071030310003042c0500711580324000a80c4240103019021080c0b4402505490081d55402d0322000346c0001210000003944c0095058086d0120303950030b16034019041380585400380c03841601a00c07a0314540c140c602c154460a800601c090061004880310009400f802c01000440f61001e041402203c1c20401d4900c07d4034020142d035031700d04208100240085808096007103a11905004080c15110010710004104030320560744e42e9940c144641da0006c0329285022960100c4404c2e07072075940301d5640c0e5aa903203c2503803244038082555440b040100b9485040e10111860402c48044001c05003541429030282107a00307000c180700300e10440600b40f01406084d110b507c840c6050303070880c0352224103180b01a00311140d00d410903030140c076a800b40e0000305000c0b15128503281041c1c0d03030303078200c6840c1c25220990000c1d4180070010902401d400c0c90405424444420 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 974996393 1250 974995143 974995187
    0x204060c1202061003080304050a171e0f030105040e100e011a04150303210507050711040501140607020f060c2104030c03140102070203070609080106060e1c050a12 72
    0x881c030140e83d9600c0440344480040c80000052000500c0000a1900030703105008599000c00150346036040f0b011a40754142036881c01060441400d00b0800089040d5011003041903d07011000301890842d00c014000e05000e00d441c1c410f088948041040004000e982c80361040016007100c8803000d01030130718180c8400780c8208014400f0421320780307440b03000803240c1a500480b090b1480c594068038031031100068201028261440000070340b03101c1c021075100b44038540e00c00f41c0c0c450703e41c03501c0b016180d02c501225010301d107413800600004801180210a02c04111246521200c1e540b000404c00004102160f80140002c01d42d90b0354041c0018000c515071030352643e00d02c0f80000014181d00b40b03008502c0003408603140c660042000c12000c0c88400b10006403c80090b141844035004a0302c2c1c02101d41c0000e0004200322410442c141c0c00384505000740c01585001000010950000b50240034503181b4051034aa828035000d003004410030588189682c005000c4070440c54420001c0d01c03183d10310001c0340240c001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 974997643 1250 974996393 974996423
    0x15090306070e120f1c170405160e060904201e0307050108040b0c070c120308040b0a0903020a0209060307050d1506060f020a031d0301020409050a110f03040803190204060c 75
    0x10541090b41c0701344c2c0c8000e2011240280382e0710f418040459000c814402d20944042a0780c940400f0641304030b00400042c448000c074814192103402296114071501009441800702a94900c510a038005801c05030400251922a809110b40010f025605600414040d08042102d05001a06145400403019034035001d907a14010b440b2a0001c44004180c84080e00002c1d02d4149028040c1600d10300a030780440e0425101c40031486003202d052816030100300401c0401003048140c41c805640010310600600c00741a55a03070103540ca182a41009200b616000d00103203180e2010058040281802070860501c0344060420100443c81044006c4030607003070080204605010314503022280c03a25900270840d51915032800c541c08131003111070140c5084114480304056900340040c0c80502144d0800003114200144d020044401d01e01c0b00c20418442403000784042000c14050b03030b5000d034000c1e80b605d54990340c100c0c040500344241c5082e000e88504c00710700400c0c22a400800c1d148503034424849942c180c65 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 974998893 1250 974997643 974997679
    0xc08031c140c070312060e010605030f090705030a0b04110a0320040902010522081e0c0a030201050f0d0609060b0a180b0307050705032a1c020c15090306070e 69
    0x28003114052851401000400b00180c4221205645e00000880020340561504100160040c0c04e9110b2400140080180014070100340c05113500f00203820000c00031645000b0100b9250701c41c1d5240074240803a00000202440b00202000c0d00640e00280a015100e8030703850301c0882c2458600b0468403c3c00814440d1600341400d20842c40c0301c41d01612400e0424010b1003a0914010003005801c1c000801c404000441c903004000030703c11f48480b5001c0c0080f44d040e4000e82450590a902d04d544100300340181080581d801c0400c0b1640ca03011464502d5403200c40454141c0606a40d0b801524968680040050f542880030003400400a41e1307981c0e495020140c0c84c404508000c1c038080e000c0000420800b058000703001d0001410401e02c00c1003901d060031040c1005500001060807080c170314203c081c82c0220510007d1111101e4000302e26503900d0f1608490600955802110a030140101c024080f40a1000780c0001a6031080380001e007290103d24205d40c1c02806013032241c12140c0250255401c40301105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 975000000 1107 974998893 974998931
    0x1302100c06090c050f0a0e0a0902032103160302070c09021804150e0c070b0411060409020a030c020d0906020312062404031a090a030c0c08031c 63
    0x11032400e1306202c030811a0040c0c807441041c0d2902c040c0680070107c840b854100344020380000e0300340c401d40b010900d05011443c03a014290500741a0074040724480d0011403080c20304070055030038010030320001e4040c4d0040440080401321410300c180084c02450b03000e44200c280d04594604000b8403080402c08599881c02c00400b880c0088005001c08501410360075006103d00f00840d15100c3c05442da018030803005080140720481100508006a03141010744001d010030660856880d0f0f41d100c0068001d003c0340d25040094000c180724074100e6405608480c04951458014500d2300380c0511413220450001022a035000000b6513000258400400d8908404204119002d540324154141098000b401c00b4102000d1aa40d00030041c0d4010081070007a184c1741e040c24006416519860844007581c0a40c01003241c0788008203022440b0414500c04842c521b4200e10108440001588441c1d00c43d = true := by decide +kernel

theorem cover : BRFrame.Cov 974820143 975000000 := by
  have h0 := BRFrame.cov_init 974820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 974820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 974820143 ≤ n) (h2 : n < 975000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
