-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3262
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:33.48899+00:00
-- url     : https://prove2.me/submissions/ee3bf3a4-73bb-48e4-abc9-941f746f6dd4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 586510791 ≤ n < 586690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 586512041 1250 586510791 586510807
    0x6090509012f030a2a260708040201110601091a0a0605030c03090a230610030c060c0303150311090c0f0702040c11150108120903031905130e010e0a0504020d030302 72
    0x180c1c2100d200c28000c074681c5210720580c0c511030300c2285d54414800d000510600c5100314400a0304698034502d6041c0e011281c8a681c1e880812150520010002c030704008031010302c0c2e82000410000c15000e40780c041b00120b111042c0e000300f40c1d1100840c00c00c2c2ea2049000e55000c000c0c0f240c110302280d030000040c02c081c2c1d075a5650b0340d040c3d07458410311910040c0031f0500180329071680000001000340421400090314410780310b0f0b052007150411f15002c05480601c0c03003c01001464014601c1c41d12183c404d00f03010501045044104d010f0200c158415200d08507400e50110f464030b441c598195000100b19051800c0410441c0d88403558001e91100900860744c444418120a0260303c400e40525020323421625801003c19900010020a2140031308a100d0010240710b000d00d141c0c00c0c1c900103540a0b000710f041510750f07030000c550340ca50100e629040c0b01040144810766080100240c1c00f5180e0002000d0705075251221304210314000410760741807a864038081c000181c0d0b4005910300310302d07050b01e0701584030800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 586513291 1250 586512041 586512061
    0x160507081e1203010b091903120806031b010e04060911070201030e0303071d12030706060e060301110702040b0a0503030c07080d030207151e090b060301110c190503090406090509012f03 81
    0x40c100c0c00104004807a10008c100040302285641c0c2c4505965000010780f030b0001456981c202105c0042c0c0c3c0c110040000f10101d510803c800c04070034100a00110380d0300d07501c071141001c540c810b441e076041616001401805650305402014060060340000714174628003c04020003180403101c403d901140f19040c54100c50307407103840c0b0901e842d0b4140140c035600c401e54038182c00103100381d1250031130b02c0b4107000003d8070518041c458001c2e980c0d49440f10324603002d000c2c2e0030080101400300e070795a40612541004503498500300040c0140d261901c008100e03030703030510358000d14001d207001e51a01003600410408000810035481136030341403c9244007046400280304840410144c01c14048121131619403000c0030310005080b00c500030501035008200c02015000d45400038030803143d01394255440448a000e10300d00d03e4081d01506400b074002e803400c00040c80001404d03124903500c5600429142c13024040009001c1c41810203220750311104214100c1e1003403175030b072001d4440c007000311a0038408800207500b401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 586514541 1250 586513291 586513309
    0x618010204032019180e030f0301030f031101110a050a090b0a0f03050f220809030d0306080d110d0e03070504020705030c1501050303070602160507081e1203010b09 72
    0x15003c1c214143c0b452260f00c010008225090b0701a1040507803001d040c1c5080d0346940e041050b994501355200d641080c00810710302801d95480086128402007254100101f805009540a548240da005c1d940340c10381e080c000c0c01c006a180052a95034588a4102503c4024104881591001e414160307290050f0200540304052582d124100e11800040c0754a0010351000301c4243d0451151010000c9072038150701c1100380c82e42101c000f006001d0100c000501c00c50395260540086104489480c50210f4510200c0e080600038803004010035101c150038840da030428401000c507a1b00e00d01d13007900e40075504202070b6501e00c0d101198006104400b030205900e520280a060003a10000d00b00b035568244924109a4950017070343c81000f80d004003558034050000c05460241240c0d030090045041164a0300c0c2d2000940c04981d0f5070812200050042000600034481e100050103240d000d88034038051011840715a2440d0040c0c480700da04411411030704891080240e07415100402500c0d41c60324481c4000c10002c01d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 586515791 1250 586514541 586514543
    0xa090606060203090a0b0f032a0f070c060e0f0f1504030c030611070f08131d100605090d0f020102150a02090f0f06180402090a0b0c1905061801020403 66
    0x1504280300840c07070075000001000d546800741c545082917036a621b4249068010141c1c05402c221082000c500c0a002c440c024a200c09016032000a240d4441021343c0309951111a20103450080424603000b4007180c103c0301c0d00102464246081020680c40002d5030200c0c0c00b402280c40b50381c1c0410b030311680d0346608421402e2000440800355a641c1c84c0c0c10410340b0306903640300843e840c83c01e0505106680052000361008241c0c400203d000da232115984d05500da13003181104159601407407400142d5020100d02e60031468105060f000414200804c040040007103981240302400001c0140c49140c2e22008800030a1070703048564049500403510040f0b0904c000c148440640030041e5042c00302e020301503401003141e440116460038010000c50709100d03c52000300c0f400b5500c841c00344240d802d10340d83e81107a0a4803000c0144014607190310440060100300b03040c0c0180a0035900410b0400a02c40104088181e064207602e0010502c2131682c2c1d055074501d0700400420740e81a80b031000e46148502501910061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 586517041 1250 586515791 586515803
    0x140901022a060d090b1521030d09060b030c04020301210503040b1b1b0d150e010606090509010e040804231305090c01034820010203060a030b0a09 64
    0x50410302d260328050800c041d03040d030345e01d101c0102154010400785e450b00c002c03100240c40516820391200c0c00c60521012034403400b07407034003081100850701f02a074461118001d00c03507040007420741501130503d440c03c40d124591a006510400c0184490740c3c088a8010892401c00382c1d01003200c40381c2ca011401c5025540c00707440c04141c042074502c0d01c55034a5102001d0020510b0031107800c05c0151a43d13100b134030300c0400f016070845540a04180482d40d480d00c418004c089445c804501000c800a00d1421a210b070b501a100007400303840d0074030031458104210350050544200c008000d08007500d030080340384243e206480c900800407041c01e200080740c403d50101c41600600b034441041082d49040301421040302e0310304141c001e0400b01c220960091240c100074464000c1c9100c1685d40b003015804040072550124465032104244035a03030046c00c0d10001d40200d1305a83d90074014001c0c20300035a80b0607444d04804420364014020410240c4032500d91100b00c0303810442200464441180c0f0350002c0143d0003020b03200b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 586518291 1250 586517041 586517047
    0xd020c0316021c03050a0c0311061014091608070c06020708030105040b0618101101020d0f0c09080d1b060504110f030f070b0c0715030c140901022a06 66
    0x40703514061064248030b0300903102600a071040902e400641064039800801080c4180403c4040900c241b4032001c09600ca0b05150b6002010542e106107400c50031201040036040045080c040d0250361040743c5800c5038280c0f6482c159092140050f22100160303c2c1540410800e200090a5640710702240d203031a40c0c10010855035164141414900f0f54024017500e030060341040461202420304c0c0c01200e800d14100c40140065072003280c04c000f8201c0b00d8980768010171942400d60164002c0c02e1004211321580280300148004c044807051003952002914881031000040d400c104005010030034102c07030400c1d0303d4a000900110040c031030f4480740700b00c00604120b28002c2013000304442c02104501d040f40881d03030451100b45d01da04055580000030218281c640181500300070441e00c1401803d4008030f0541943d003c940c64150310502c90606941041c0001d480d285d1411599030400d258005510150014500c0c2c0500f48001030f60350f02030b82c6640e80b4202d00718002d000210941800e100030456000742003a40d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 586519541 1250 586518291 586518307
    0x19050a060207091407050d0b03030904150e011403060a2a020102090f09090c01080903540d0c09110d0501080105011a3412030e070b0d020c03 62
    0x1560b0182c034050a000359180851003a03c5070003000d130b041d01c03544243c1d4070145000c0c040703a84003000d000d5403082303150184420302034401641d0701c038040c90b1000c09a00c400070881070302d8240440420360381a480381c004040c80007981c06154038003244141d8003440701c0c803000c501d02c005020b80f1a00038001c4241411310380507004442500390742c1034005040c0c0c50011558817030036081800800141e92025507010185601409032111254016041954421220f80c29030b4104812038004103c80503000d5801c003c2c0900e5140d80103e0010301c0380085559488034000201a511010345000703141034854603541c4942c07001848541003008103142d00010304061101881041260302d45426240c10036440e003507900781030500226049005200b0581220090000d80d6113565101c46e07041411382c8410081c2e6110243c017204000c00f01140b1104084c3c0300c0c0c0c6c15440100c14100d0742031a0b4500c428204c0440d04150400c03251442c800c80000d00101942d05128150380d941250505c1344000b03205891a01200d80808181c0724 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 586520791 1250 586519541 586519543
    0x3060204030311010605130c0e09010e041a040f030c020607230d020a021807141305040b01020d02060118020c01060806090f0303070807030203040609021c03020709090f0219050a0602 80
    0x10007224440d48612003500c241d610300c0e5090301d1641c05080c4e00602c21584000c5180c1954200b915040d241342010350304100442d005c01c1c55103009030418600811000280004c007c2291505010b188414241d41e909040c15078507135103084206a0064100051106680d09558a51044544059000000142c0942c604214100140500710001400d010315a142880d140c00420300b980b0302c0b54020800c2594400010404003182d0010300302004202460040342201e03d021001008001d1949030600046807502c0100020344503802140c904540020803000c1340b46800103003960544100700a8941d0107100401c98030000d00902181d600e140d800d00400186615002c90b0442c01041c480066606c13022050002c03d03030f644030030f03a1114000b400440c001422076101e0750145805c5403041c40c001c50074042c60303000200050030903045e82094088004052042680410445004003241501480a81050307190140040c8901002034000c0169921041018410b15450000380c0402008070000fa0346440c1c0007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 586522041 1250 586520791 586520797
    0x5090f0106060203040b0f0a1e1d0402040e07030504050c0d11030d08240105071703070306050906030307060b040f0e0d02060705090f041503290a0501031e050c030304030602 76
    0x4548254a4050003140091002c003c54013501c040c4142c0a103012a82008080320342c0c400d0440008001d803400c08400c0c404001c01c1e03200761038046a03039500c1c1e03252580d40718070b4000318a003041c2d14403407407041004000d811840340c0701c50341c0000c540c1000540d41d51203041240c104885210140c0d0700010070200c0d8005c0117018581d285690300c05404941062020a8040d203d1807011358164200110320740e031909420b07480c40d90640840e01d041c58210f040c032005555101c01601800d1380341e909918080200440298141715400051004480d00350580c2050b1000c2a204e11600c00301512081d140d6101040a860b213401101010840000800500c1e0482004948130424100804018081d050107d0443c922070002d80e40d401c10000c004030086414101040000c0410458444070700a22079400030218021411982c51404200003c20b101040581c0010421800a04182002c2d24190052011644103000400a901e50440d825001c1d1400d00b8940c6c41d00c9441c850040d0b1602c070004021081151980203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 586523291 1250 586522041 586522063
    0xf0212160f090e0303090705090403110a0b06190b040b070c030b0709051306060206061c061416020604050303040f0507080d170105040921030b060301091b0203040e0105061305040509 80
    0x3c2050b4010300300415107034031041d90548020f0b0312410092060b45400141a80c00a10a050003a030510b400d449140c10b008108005a82c520800d5082080c1c6060850f0810b551030032031141d4001682c10100040f80718042c500400001440100e0780300104180d242c07600d0090358004c807a80d480c600d00020b004205070540d0051038003500100c0300600081c451070180c1000e403003068014216a80e40d1200303111030640d1540050410034010008140401c40c584202008143d040240d5a00c03451b2803103c080c040f03148800d0181c00c640c0a8420000414400300989400075444003141c040c01e001c0b400c0c031a2503c200741d000320701540160f0040420440d00060b901e4900f1100071041c1e08240e0b030ba0b00801c8101c4000800140c0700006005404d507205070500002e6091050604001540200800200d00d49802c04d81241d2080c0796650f02d54000c80030008025009500c0501c011880c085c145060598441c0040c42842e0280c88040340600007008061810b074040d10010704204030741e2805e9118180d440002c254 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 586524541 1250 586523291 586523309
    0x70209010324140a0b09040c09020306010e0d03020c190803220503030c10180201050910021606080405070806130303110d0c441e090d110601030f0212160f 68
    0x58280b4175042c000d00044c402ca410201508620b490718a2207030103948000e01c0281001001d0703254007881d684050201c041507000743d006100d100d4045c0280401040340d01e0455107281d0a151040181c0040001229071440c9000a540031066954440102c070003400d8100303d506000104100001e620001800200c0c07651030030090003910900e40f5503a619140300075001c0d0004100f000420f5590920521004041c440f520480781100b115007071480044450b500800300103003809080c00148502041441c0140c10a00003801150078000880d21030540c443d80024207168860000554900028042c0e50030720b0030074907046c0004810800e0080c1000000300000444044804048417403003010001c0340c82e03583c0da1007000e13088510900c26504035444020231081300e1125194001c800b117250b800c00c1c0341c01203080030020018181c000102402114005ca1a43c40c181d104d00c1c01040413414030710b1082005501954606160214608841e0421401d001040d203e0000003000143c27403100b070f103600310489100003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 586525791 1250 586524541 586524551
    0x3080a02160b09010507120908101a1806090a0905010c0504150f0212130911030f1e040627260325210f11070209010324140a 55
    0xc0d281041c43c0900042d440c000384003480140001034003072103131a2a012660412004959503584e2881c50000584071900400d5120810001c400014124501560790103c40d07500359000984901070544000801c9640f145d6100800304405014030349c40481b02e05e4015000340000f84d03034844017401d070350700910500a440c041d00b00250081403050b2940b207107041542d80071700324580008a2105403a080054030f056012900080000c1084091003984402460180d010381c8902d4101e60400340c00100501c0100b40740180342031100c0306090802d0190b03106901010004448841c0d8296218250040c200c10702c90300451480706042c44241d03000c1d00c59007003601086038175003020002081140d005c207851200c03c6a9200c401442000d031a0094001c04000a150031583e0100b500c0251030001124a05062441e50b140b01c03441c20714604e401140d05004020210b5490402281d020449842e4144000b508010644107044007a401008805807520b0f900c280a004004014540c86604502506e010307520301e1030701d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 586527041 1250 586525791 586525799
    0x80106060e031b13020d061503150e160539151504140403030b0f040e0c010806220e06060906010203070303020706110309010e06180c010c020a03080a0216 68
    0xc0364a9200c40e040c01d40c0040340480ca0601221140019000d4404c1385c0902c0008010f003507501c0f0b008020000b181c0000c8503142844400740442d800c21086401018031340c0c0003800f041401900c003c1c1c018480e04000d40b0a510f4140701119903028180b03944001e4510304a05143d001c0107902c0409408440031501c4200d00d0020840c55030761030394912802e002900703820005e800082c124002c3d00300070710040d02c0410b01c2a0540c0c054241110b0481f030880100341e8903000e13a00b842c14405e02000454000791810000000756001d001d548080203011141044075010002d482c5481b02c00d441c200d41d101711006603081c41c0c0780302c0b141c20107030441441c00c809070b1144c030300000c4240c542030840d14040e22068026614000998804070040e5108070010350700d0607140c13000c140030540100011440f4070602030000400714941040d9504151024210320b804000c2d2413101d2111010100311818a07500074201900e000d5807610204070b041c01c0daa8006841541c01082251042d41c0102d21109500c6102c08043c441c40d4407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 586528291 1250 586527041 586527043
    0x6060201020d0c0216031e0812330405060a0806130501051501080c0a111c080f04080f1b0d0e030607050309070e09010e010603080a0e180a0908070c080106060e03 71
    0x450614170028003415420404621480048002e0a600340c20050060016444000041e4044082c07440c413241c00d00c081211170031509200400b21800000e00080640d5550204d032400b6804441851250b55200d01040080d502c03460340b038006040101c04d072001807030300110341ca42601000d01e06650650902001400602064540c02c450b4141611a5540340d2182282e51031103400c1114103009116003514489086041048400130202d0103080c851510740750000c0c000e1844038090164900701c4d50b00030900c40040c814034150740c0c494424091058561990b04c121600c4580d1100400358640115200707001829480800107040c10300c00d40848510b1788403003004482510003101d10f0407640e0450842400f8468503c882c143e00b01508400200700d0340c0318076a481d800c49001d03a1080f1014900040e99401c4140c000c001c80d000742000325a1a8602d40744050804240303c0010304130f1007400c0d81c40701030b43d0030400d00701c0946020540064041c0445a1a110107038003c0555004100110301c0310402c40e88240f034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 586529541 1250 586528291 586528303
    0x2031e09060d1e050405030a09060503060904080d0b0a0b09090c0301120602131509060311070201090b030912030c0c01110c0c010f020c0607050105010e15011407110406060201020d0c02 81
    0x2101802041c40d0916607040c8600401843e50360340001e1060070340e00100c01e6600c1c01454026800b0340003450ba41c802300c00020740320100707941c0081d06000c1c040c82003240f82d5868045003980a60802c0c0750380d9540006002c68001806040d030150350101f09000013203203540660000c1c080782d40702982c0c580503070b1311070200d4036095000911918181010914002f4002040ea0300944000d0400d03220006109031a10000f2070040d1405d91043c0000382c00a60400407141d140c01382e03d440b070820100c9c071803a000d81500002d00302c41450140c21100f50000002c220004c008102c400c4103088030455168681c10440c4400242d0380c40800409080d41c03c102e040b980c0304268004a4011345052801072140c05241801980c107040c0c1da00c0c00e0004c3d8050080b0483d40c5031542d0009207907161054000090660500903a2058010050650a140e080c000841c10481e6040301d440c801c2c1c06103e50740551200a503242040c40345142d900040e4009013042400075085405401800030180081d805004405519070201d03500d43d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 586530791 1250 586529541 586529557
    0x80703060c02060f15061b0c0102010f06060c0b15060a020a0b06010503010b071202070302100c061121090c041e0b010c0507050f01021e07061211030105010f03090f0302031e 76
    0x194a40211788070040640780b511038050080c01c00c0381408043c088100d042c2d004600118001e0701b2810f078503401ca43c5d0a10401440440b0401d04020003800d100c4003d00e0b000350720100900070308122000c110000c0c1000e03c425a4032400904503941c510b506000207440c1d0010071400c40e003c1e8180c6000c11303419806035099034141c5803812000c504080c5107844a01c035005020a940040d4028000040b0241c1c4030050110703610b4100e510703155030400351480d00b6000c07140300f10002800702d80c05122143d00628190000c15281c07251000f0107589403108000541090211071045900c00d1600d82900e554600000c0b240044550100741000503c041c01c005490700c47c01300d00d000300203421190b4284900c0c03504107006852160180304444841d0b040c42180c40a81404542800741c592110030204800d9034011201c440702c104903201401010a00081c5c1c2c243c90006008a41c180030140c80c49603140c2d4404d40c060000c840d00005036590a480c5810041d44982c0164441c01c007180d20110400ea06d450204101c801d13603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 586532041 1250 586530791 586530811
    0x91e10030204060210020d0b04052508040b06091e0a060609060c05070308030a060306090c0312050a02030703030513080d140903090904151401031415060f1018080703060c0206 77
    0x901174001030f4200170340c0118503c240d240c2c0e1752000228262580d200e01d80c45610091215020304031250b506840d08100d4034000c1d400c02820b60100400120036203440c0b1380102054403c0461034039009038044107045840c1101004551308803c002201d01260884403c84400d92100c0d00304d10b80303580046407101e900c1d1101500c6944554802c03c0042d035040010350f03000517400000900c280e141d80c1ca00c800c1e1504041c0550f5004803405040c0241701109014404840d42428034070f04d441071445003c0d4584c001d02c3c10180030f042d42c4d18001101816110074074840036510003038081d0b0328106042d241d002444111440c00003501d6840c009408001c0c004126400548004c10f9012290f03900e40d200c42c030030505500808441c6891702c4502d01400882000640618841c030108842c040c1a20306840c600040490303080c0c42c40d0750140612016850303c800405c0d0a950030b6896042208404200366400d1020340c298008146801d40c0000d400c00d0049080c105503407044a05002c1803c00c1c3e5001c0343e888100762052092 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 586533291 1250 586532041 586532053
    0xf10060311070f1509051c03020913020306010203070b0c210105012a0206070f0b100b0403022701080109151103010b07030e0d030c0201030513030509060708091e100302040602 77
    0x4102c2032121070f0101d900c1a000703611400e041100c4101a5012280101d03100d038080c5010a4406680f140c0c0c8080641003441c0031410b000103003000070498070040c0c401c2540d2680c004003240e480e034402d00494041c542c00c484503001e00e0401404138407481d807010320052942420440d00382c40b47c00c042c4446c58102e0b10f050350b541d2010b0b00303440048580089011807408c5448140d00180700103895480290580ea400b03003062400b0448942421000c1c83e50080c000d08000403450b805000302420101a05c0c19285c064030040e2859144100c1c800d00d4182c800a015138050b02035000041300041500401035507071185640c0341e2408000001c11041e203041e03044480d19800140018088208024050300801e030003803074190303e800c10075004200c0b030014140085e00003031105001c03c0c0555815000d403503040701311501840c401000c40c1d20b0050107802040e030490710948000611005001c090300c165082120010001c101d8604e0113203600d100b040b90341504c03034041e003614140300c40c03400c1c000e1080d00c08840d2281c01806c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 586534541 1250 586533291 586533293
    0xb0301030b16082701060f0303020a05070807030c0902030712050a0b0f0f0f040c0c240b01020d020d050a09031709031501060f210219030612050a0206030a060803030f1006031107 78
    0x4203031344544400300d1496689400008011800402e544000c501035005000340d0b146500300b65060084d240c200100340c1d4480305040001924400040048408032000140c413526210300c1101c600c5c0e104d210300004c0782c1c1464240f00240815900405c2c1c44082200c0c0d51403002c03124024400359103404090180d000d60601e0012906040580041c001a4043d01d04030a420301190769000f001071040c104070b1045580b81441c82c1c00304c801c6100750100c07904240001d100100709018003e58607481c03c906101002404079009140d01d000c0c040c0e90003d1079000610140c8007440d100529101d1308004000361103481052899000c16116000322810307200ca542d00c02034140c08040b015100c908203648200c0c091013002891580c10001c0307101401c101d1811030211401c2c0b0060060040640f501d1360040c5030300c0b081200005002500c0001c803622310560503039400307469075107020708a0020700702580141030340e000005c1007105484001400742d114428081c0c2d03090049884440440480750240381900c04100100800c070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 586535791 1250 586534541 586534591
    0x50a090201140c0307050a0c0303140702090a2c1b1c2607030201050709170d0305090a020a32060a050c0f0d11070806090c010c08040b0301030b1608 65
    0x8016051050104c0c1e1520342540d6819144c000b81300c00130303201540070f04002c1c010542d104091120102c1d42c500c0b0181008042c0c2c000641222002c2c044c400d060f0f40d6410b014003589200c01c030380404c1c0c0e0302d0401c1609080c03480e0000e45403958503d44003969403251954400308585082d00106840340002c0d11103050640c0b299a4a0442000414002c0e04500645054042d01c000003c01072880500c00d80c00800c060400c410081d180c0261900b00420291903c4071a103607140b40041c0075407a03907801d454040b5850b29280095828642e54002c065001201111301003000311080c012035261240200c88125401c608100107040c001d5503501281d0307c0101006084003162107070019240005c0d0502c203841003203c8003031140c2e25202d4070b0014a40800d88080c1362014000007402200003c1501c00040e2003d0306d02680c0035a11001d80c400018140104454840180320603481528050441012041e03500c1d612424403400f440400c030f44400400c181e083e03204040d10f10440e95a40504203e208410400031422046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 586537041 1250 586535791 586535797
    0xb211b0301151814040606080d0e01121d0a030203131a0313022107150305150105030711010c02012c100209040e070e0402040e070807050613051012050a09020114 71
    0xa020303101e132240000380d040ca6043d03016034000c51041c0c000056240c50917a1442c10803c2070640c250901006a0302940176980102c1d00800c03c0c1c1020500042c07903880036280c0d070075004180003084464401c4002840405800100903c0300052002c860690960ba40000001400d032000b880340e0303114000c9c0042020940405c0244400920003490201112a0244a114004030f841448034055010328030801c010a031410150b10684002e1809002c42d180c002440940000c0400300e15042100000c00140c40324441e100d564140407101c1c00a004002e41501e0090192017101c290b000411000001030700a001d43c2d54802d000c0303540d400003070254400c61a803d0f900941250414941054460400103142c030307806e0210b04003810300103076620941e0a290040c001110304507641d407900760748442014010811700284031000c41f0012070301c00e56a07a210b010b40d400442d105901284e04540c00864031022160001c050409102c110f62003001140d449907041415075515030000303400300780c0c25107244501000700401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 586538291 1250 586537041 586537079
    0xf0a0f0306030f06140601260c12011e05010f0215090102090607050a06150506030a050a180305070501050703062306070b070804060b0306040b06040b211b030115 71
    0xc0050345039940c0d01c481c020105001001c640c0701e5901c00362507103070301400080c01c0d030081c80c28a03081441d0498105003d01407106480c02d14100307084040001c0c1d11141d001c044403038483c881110700c40d80c0d5039203101d107503961000120450011072035004045920f52213065502402aa00e6005000e44031006d03d4043c40342002900c001040d5400708403d28490702c4150040c1002841340c0d00074841c1e0070003400c2c00000c45401c00149540a10f491004002d95a02c2d070007901e812920485c0300040030b40303880c40440b00800c248800c0c81d40c10800c0458800074541c200000d00240da011380c0084c0a1f60f5214207003101121014010118800c2208804240c40b10051011318001540540b8083c9081055200e69440610171640c000010b05510104410051503010f0034040100a4009190b41d04050391a9511400f000b81100c0c002c0741e075503480103c40c1d900c8440440303410041c1c1141111049a62145988601e800f508114250549206211040c201480744b245040d942207132860802d800c2c1a6a1001c000c81008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 586539541 1250 586538291 586538297
    0x905120708030301080f100b030a03120906052403060402012a08040806040c17031602032e0b0a03110d05160609060e1008010b090a081e060105060f0a0f 67
    0x3011800400c1040210b019080308070040549200c0c62046524001044c48102170203800d2540d41c0c1c44503203001a07a0805168181059030720440300394440c10041048080103040c0c5810807080c0001030300100c0c2c1c448403900a04d4107002c1510950720a0650310503081e00c00a000038903894291541c00380e40c855928801c01c01610081c03010744a500e03018000d070440d80160b156500014180003c202c540007141c002001ca01003690602c03500c011030603449014414010511100b010b48080841d03400344655580b000b0548080c422580020aa50780f490300c5104c03201c5001c0340f80c05681015840c00c494150708890303018106036407111400301402110208a80102d0b50341c42510b21a520300300014240002901c526501ca001d298505040200074801203803150f40a40d24a000d45810790303500a607028151402141704940e01c1c2da1800109120610640c814800ba00450044100e5408034040440c400d0b94070380708039205c9988130810051540701d00707541c07081301400c20000f000886024031244203102d510f9003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 586540791 1250 586539541 586539553
    0x30611031b0f1c0b0f150306010e040f1802010e0409020904060c05090d030c0c0603022a101416030c1704020409120203033903150d0b091c090512 64
    0x40d0310f8451041c82c229074001c0c0d140c0d01d22400b40c1c10507110140c107040d0100c80030504480700b1000d0b002288800b4160604210115950601d103864a4000340c01081c4107603803c102020802041c0e0700c80178803080d022800a00d0f2008401c07070783e1400303018503103985800810301c0003141c03510383d91440100854051042481002d0020142c141e0b12079806905080c0203455022a6400c1840c28004000040d0024414144107000e441c8084032004003c2c3e04035000155040c580c0e2201d0b00d0090300d000b094100c0d4a54841c101004200e24005004481d4040d200c04000780441c034901c0002901502d10161040c000943c00d008928521b1340c0c0e0000c5590000c0c000340000419140c60344408030189001e4400340c0240c1d02c004280a18418686101455042468000e011130319969004580140f17440c1c8046100c850040040341040407016030107052407900418030300c40003880e450000c102210440e0400410300400c1c11015482108001c480c03e4906c0c56990900e02904003800c110000c80035010f1902a0321441c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 586542041 1250 586540791 586540807
    0xc040509010c09290307020609240f1f12060b0604050303090108041e080304030206100602100903120929010b0706020c010207020409030e03010b06070c033306030611031b0f 76
    0x10001314000c44a0f503014001394074200c04102e18040a480c1c1c410001c4111004411002e002b960b00141c00103a12810b1140c81d890b00c0190314107009041011a0341442001c0002500d001c2d8818054980c900c0f4000030302c00c1c08180d000300304260107580304280d09900308000c94503196200d00001580b00d4406c948a50b00b0003405001c0420010031100e040302d200000105100c01d164040028550240712418010220b6080040081d200c21354a4041c00540752034500100c10140104001012021390040800a80e4200e042c01020301e1148249045140c12100c1800c2c105000307101c000e4180d42c409080380307152060a5031050000d40c411000c1c90800d540c28010342006942c1c5000f0b040ba1306000346e403101600c103a0b680400d4216064003c480b481071004205103000a0303201c201c0d50044a030001d106506094803040c2403805c00c904d840382c02598014072089407070958200e502c540140e0703025030410045000f807082c11024a22040e2000729a6501e29213190012100364001080f241c504200001c5c00c4c0108 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 586543291 1250 586542041 586542119
    0x705010e0102031008010207151508190201031d0a030f0e031b10020a150902011e02010203010602060a05070c020d020a1a120721050702031b0c040509010c09 69
    0x180c00c2044145940010a11441c4481011403101801c0c80c1c000840c0351000301c0c2d862400c3d8152a4001209503929840710142180b0507100446c02016484280c0b1041401103d6a00d00b440f907100c000c9020a00e06807022103071410941c0c03408804e00e07030700d0010031701d0801903101582d604003010903607002c00c40c4000301414141c50074000c0182d8105900c14050094103c02e04100090315900c1d4500110b504c4500284007080d41c03c8954019004e02d54000104440030340012a8030501c0782d00640b5001507040c5210900e103034158021812241c0a90940e021900c68000755000e403801698803600043c811880c00c0090b2401c910ba0350300103803004050186550b0360740240b40c02c202c1c501194040650700030030710244402050841c02d80c0488503262580004181d00d5581d5048042c40d8081c5000390755460008200c0d500801c01c8030030b01c14410703030110072020034070141540d2551100d2580d8060b5040102117003000d01c05008070b071449115501c9a454250400e0307540b100c100300384400d5401905810780138418042c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 586544541 1250 586543291 586543301
    0x3020d111f290d0f020d02040204080a03030501061b0b0925051f141809181c05030a0b010203090d0b0f01211103010e0609160501080f01050f06070501 66
    0x3414900c0810070203003920890b00418903181c2c58000c40021040d40911660f102003007000e00981c0003c13000744600b064004580704120f0400b00a40043c8001008103040c1000200e001c0c416100c1e03074040c80b0342d87c1c90344422511172040d52155610140d0802c200400036499082080d0700c61071007000c503240070000038820700070000c445205140003c021035041c880e80c00c01342c9284d00c00802401c04c05d143e243e007942d401401c100e50540641000e030800f141d51940011640b0050000c054024104071072400c2601801c1c6405a00c020242007620440c00241c043e52420900700b445c0540d00d4940030b041d83c2d03d00074040c0262500c455080d0440c00100701302501542c54410151009025000800207451f10311144a005103040c0c000c4003c2c81800e6004d0140d0600c42a541c0700c40c66801010351000b1f90b00b846c0864050070080d601c2e14418081d074410007504100c0000c0441411a100b584d0141481d540c800548400740103a5a03801e095400d0f10040c041820404521440204054a55860040a07454079401c442c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 586545791 1250 586544541 586544593
    0x908070c0b0a0207090b1c0507081618180212121306020105060603090a060b011202120901062c090c09040b01140604150806150a050304020301050a060303020d11 71
    0x107404500000c110341d04200400140c010000304020207804003000a0031a103203042048246108414414200b0034140881c00080515001721000c1d40c0c1545551030070707190180520400c20b0961040012501114080c7c8a02e128004400c45001c03030076a002c6c020703200d0042d040f00040e482604801c3c031440c1c2e203400040007046042c0030b52901081c2480d070002d0079a040642024490075040c8103100d9603880200e5030409942d840400000c00380c48490040e40e91890754821888002c0c4013007165a00d224400541910485c440402000310b90748603407a06854407200c02540c121154070203040307070450a03030780151608003003100200c031800030b2044001424900101c0c6e00715110400440104a1050b61200702100c18000312406802c107400e0136450000604509448010004002c0c041503145c0c41e03000026115081030050720741e03142c80c0c20002401a501c195000c074065868000000e00031840c51040d40181c0340c0c5030740a420940450b001c00c40c0c0310740c80704241c4070981c002d01c241c00038000744520b00c000c082 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 586547041 1250 586545791 586545809
    0x705090d2d0c050406050603010902030a1506030903030e071d0c04030602030c190206011a16050f160e09030a050a03020c2a010f09170c03150f0c07020901090908070c 73
    0x103001d00d4039000000030b01e20381c002c1d4003a80c1000402d00c0070707540310b10541b070540314910781c0141c803581d4001440c03020b818058480f110603076683d080814116819003001030300d41d000351802e00c541d070200d501c4660303648118410021207068000840c0c61a20300407180700d402c0f14054500d581815200d460303010407a40151050b2050b654002580e0f401d9040d110b8132142c0c10300d040e00150440e9031400c00d418601c1225001007252158000800f406110540a01c07464401e030030008403004010701c0e00140d0f545029901520744481140b200001d0710b113010550035481511520007075801d0500890050f103043e04628610014141c00348145180c00004020100000b4040703048683c684e0603040d8043e50890342030802c40c0c10400000c99003c03009402400c0d0400300e41c0428088010800325013500d40c1814a20b84206525000d210a070b580050404681980985026030706030320140c448103040095031041c11070081d0456059001086001c4c05548549001401842c6107490702440da0340b602340c410926084a031039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 586548291 1250 586547041 586547123
    0x41b0302040509071e201204090b03070518060607141c0201090c05101106010311010e03190605060609091009050a0603200d05120d0c05030705090d 65
    0x30b9880c1c030000709500440b0500700100000d080d81c1030b502c0780f00f45580c048004d200304051920300303034220602e1001c0f1801c00c0c4000c2d294803200e0810720001c0c980c05446905020781c181442d0b0a1a071501080b82c20491b039008090030701c03101e14881a501c2401000740341c95440101800741030003003051943c9082c14550824017604400e010342c4034000000c1d0084840c6000c6a03d0801b207007000680c4281194140d440c100c4000151071000d0004660038442c403444501903005140000080021070002000c0701d10098a48400040e100818159201006500d0001840e002c4044002003011540026009040900110724151090000c100318880a5a030403030100b00d0101c08100d614041d00c40c05070406050682840a14507688410780c1d004100d9041c9420200c5407240d07074080396103049454103225444800c0d20030b000a014105952501328178564000d442c00d102004d000c69120b00708a0380b00b20450b80703425041400c108103101003040410b108481300802000820407004000e841c040c0e1a800a8112800c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 586549541 1250 586548291 586548299
    0x80a0f0201090b03060f04050402060c0f0f1b09040b0a1d0616110a0326010e071704030929040b0a170907060522150824010e041b030204 60
    0x10b40d120315800040e04a005000380a450340e42c0141100f40d2070022640420242c03618000032b80c3d60300c00d1a81005140c404e02400310060f1202042041214440505807901c0c5410303c02c1c00c1003881c0350a10407650111a000000d4009001d071401182c0094200e000011000c00d46205040c0100000031903105d10380c010b0040121701c10880f400004c0c0d5050170703c2c011361240402031120342e5032003100c4002018400d0003034080c3d074140f4003401c90b22056941c00c03c540e280355940b907645850395103041e91107500190305100002100760004800e6402254541c2da5451181e182c0841c48504041c005030401c1c00382d04401c88000c440c0198400b800180007030303010305503642d442180003400080001803510014964a020010b100da404903e00c030442d6024201030343d41d0081d03542c1109030074003c03248030a1100c100000105500d109420110102038084d108d00d8102c0c0c5a8030699203071505c00c107a05076814544142c201d4142c0d40b00f1510490003e8003d8400314503441501d00442e40211070f0810000040d41c0818108 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 586550791 1250 586549541 586549547
    0x20a0e01081006240c0b0a022503020c0d030c020d0503040f0906080d030507050d0603030206011a090f01050d020705010212101509050f0a0b2b0b010206130507080a0f0201 75
    0x802c50340040e800c2008024a0250002d038411841c00764800c2c1d00304000380c0c03d94124002d0012004007984204610014540310750300c1002504800d4407602403c00c1c482c4800b002002d2400d0024000341c043d0014600b5105402c204901c820701c1c8842102000040b446010040c1c40d0140307000b030014840c001468070380782490000c0d5003078000b0b5400705120350704249081013048030104d0460841d0b5a54500441d0a50b61000c05403034a01c501a20420b1252030300e0400424503601040050607200c000e9504149a85440c0b182ca4180c024030750b041d584211064100304541d0702540c01041540d07241c032805810a0043d03220710382242c11001088030003400c00310400c000030425822844c003030896420790700c0203207104002c02003d0781c0c0c080c001c00340102000c0d000c4160555079a440c11004019a40e40710755500141da50f850b1035208a0503100b1624008101c490542050324000d810348030106a0091069a448010300c1e201c0c0008000142c5080c050001c1c04079100c3e2050001c8140c2031701038007001d184490f80784001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 586552041 1250 586550791 586550803
    0x80c010c0216182708090109060503150f012a05060606030c030c0c0a021302090f1512180109030206011701050601050924031504050a14040b040609020a0e0108 70
    0x203031004242c100001e020294001070b51020b024058840050824051092068035103800c00c40c500d05811200e041400b008a02c0c03000f001b08220070780e6a4010305690f21016201750009a50341d248001d10031108400500f003d007400a00340380145031251001240b032003000d0100023020401000b5480c040c0305035060002c1000120b40100701a505640b039498070000400c0c0b10700029010054103840022110201402005444980e5400400a072030507802c80e0940070096001482e0180160070090a8103110714004030000161500142030915000c09841100c001100050403c22030b00f07100041c035204100e09115022849100f038004002a506103034084040900141000085a042108000843e64084142c4d036000700300ba0b5549100031007030780312140c892441560f01d0f05100008803c11100440c02941e400301c546c0300f51020480b9881d404100d0040d540c0019000700c21031a800003041c0014000101241e020f4040d44001455504e554005601d40c83d0316400711001e1b03a0484014003802c40c0034011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 586553291 1250 586552041 586552063
    0x20a0b0f0a020606190312090515030108010c0c0c090b0d050604111206012121080a0f0213061808010603080a03140702070501080a1401031a011d010506090d080c010c02 74
    0xc2440380003840c024640c46501d80002003103101f081826a032014001d801a1f005010010403202c001060309401580d142c10074420000d081d801d00844403583d41c001c071b0314501415001264171842e9420150782c0c002400c400880150043c0b603010805001c50410b100140c05188901031800e451000b100130031890f080e240c040c40d603031604410010808045003c52403081d1400d03650072600908001d081c0001b4480344020300804030f24403001400613142c0e0201ca924411108004100404d0b0034078101c0c0c00485c010320840081d0150f02c0d80c401d00c6414011102d088550700c0e131003890010503440d01007943c20741e40303140e00480e452440481c040340b21a401d401401d0750302d800b0413052285458842c60095440001d48035060501c00c0b07140110b0030040030b5400c80d841181c40c41c059035a055a4078907014800700d40c202c1d001e80e07142c9480c8001203a0b12000c4881c81c804400c00440101f000d90818041164650051a20b180d0001c04d4a8000000845500103401c90080103000090000c0d91550003034141004091 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 586554541 1250 586553291 586553299
    0x1f080f0d11060105010815040203040b0108120f09190f090902040b0906060304020f060d060f080f0303060105030718031718010e030a06020904060305030f07030306050f0a030f020a0b0f0a020606 85
    0x18146520000c0003402c0740c1155804d00e040764490b00c03524110304c1c07641c503040ca8094106000004000500c1040c0d0441d44c100c13000340040390403406181000c040310340074040d0f0f5414440c04c01c03c01180c9a25101741e9020804400342c81e400d98032640c0e884145e00c101c4860748262903e40e1070340b0510055207000c1c031170010400c00503680580907180c00c0e40010901c0c07100820007842940481c100903166203400d000d9803920000c0540c10862181c846901c07608424840c45164020f2060212044602e000030003a64011001038446504588880c1d030700f91000910304268621007201c40b100000809ea40c849003031081e2801640040da21850b0035400030030300d1800542c80c0d040c8440781203040802d07100080c00356846a017105006869901403400100a00b0040e40050401d20001c034003592104124400ac2810510a40b400c001841c0d0381c0040c41f150f00d0b920080c0700d500c500a80d000f0030100381040e161a2400e440189500c11042e212110015590007100203001d440c4004180c26000326010026603800c030108032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 586555791 1250 586554541 586554557
    0x1006140d020405150a090603110a0f061b06020a051b01090b0a1806050108011416020303060d051f0b03010e03090f040b011e0e01091d0f1f080f0d 64
    0x2804504800e008600080c0103540c1d0f4400100c0042d002d0a103544440c0000b41944042681c407094000500b0840c0415114800084100d101300d1030a50301000c1180e2640148040da40c0c43c0513010f461800d0603401c030541d005241c81c1078000040701840200700722185500c61a07182d8040980b96000f03c2c0c2c890045843c1da81c5002a0880402d4003c05e41c3e07548075848001c040340800c10f00042d0400e60b0701d4100018042d07070400c400440c0c22117040d04804100c0f000c0500c3d445e29aa1a00703041204654115500d4000d03030802c001050141c00e1498100951900400860302c030202505400c0c03030000c04102002c80241d64034120828585828000c4480311083c1e000114100b8422400191000c013003000c5842c481c0b07540d50840c0900e64001d1920040701e402280004203485412003015048070079030300180d800074103c83e002049911180c40fa070b510007240c48407607211966405104c40c10418010300b0070b03040d440005c46d00c2e85c4451420f41440f0068000d2101511030003420003111071a102401c00c0c1d20042c40700705 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 586557041 1250 586555791 586555829
    0x170c070e1012051f020903060c0d1515030510080d02070302031002180d03140301090b030d03020a02060f070306080f100c0804030c0b07050f030406051005030c010f14040503010501081006 82
    0x80310140c80c00107000c1c4e11031100031401c804c0005d01c00c000100b9010f00a1100f00308005a890740504402d0b10713100b90521003400079410f01c0303844003124040c1c0c101010341003110200c55482a84103590003605403541c0004145c5034039145281424203c95100141d010441c1441181401c0c454641e0b01003c0d0075096061109070a80450061001501c1c1809204192648820b1511940070303e004091300c496510b9803541c4418000c4007400459031102d0180c41500030f4072000c50704c80c0c800c03a030b1b642c1e11550160901d500d8407150700c48500c0020b4191801c02d901c40c400411940303010700c0b1800f620b21b100300041c913402c00040005400c1c0d0350659009814007022600300000700e030704400e91a0145600682007002076481c0e680c1a6598003402c81c4030740c010207003c0100030811445a2100d401800580f21280c4001d543ea000c059940c409000042c1c00200304005e11001540607004d81030254199405140c2000d8540000c00d085030f900b64800c513004e61144900690702d61492040102070b01000c510010741e5818 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 586558291 1250 586557041 586557043
    0x3011503060e0a0e0d0e010905011103132c0115210c052d0405090405161203020c0a050a05060a0c0203010507020a0210141207111c020705010801080a170c070e101205 73
    0x641d09c03ca0341400504100300030710039024400c584600c580d14a500002030b840b00000c0f401c0c43c0d0803c5020000100019040d815204048400c9c0e040301c1c6000e40c103600c003605c20f0360201c0e070100f0300c0c5010307800907100b14070380b18000c40550090700d10003030050707403020745500400040104000500135104008030b0355000306200c0421400c00c076810380703d040d11980c44540399440e050b480e10080001c200000700d4420000308040d0010400e44024600a60171070380d100b815441001750350940762050692190151308104082d0034001d01074447c1c0755540c20a54891445070700406d0a5420443d141d0006820a03640c01085281400e5004150303c01440d1843c0c007d040601c680700d9901c0385101c6c101c2c50181d070400040919119001342090070813098191000400404a400d5034001c50003503060140c01622000700e050b51050b541d080c100d85440000304484030032610380c1850322961006801c058001000b80f40300c0c40c14100b205e100108010141c03101d541c6009085100300c0302c9613410000d400340c56100440003085c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 586559541 1250 586558291 586558307
    0xc07062c031e15070f0906051611030c18013318080a06060f05040e1c020a02150301051e0d0605090c040f140703020f03011503060e0a0e0d0e01 63
    0x18400503400b00e0010042d000314a00003800f0082d09000c0d4015003000030f8180d118801100000d100c0c0c80e9031300c4c03658480c00d040e07030fa80c040c803021a00740c5021a1034100102d02804000020706a0103030540302003101c2c0001103038806244080c4010a03040302401000a4403001344811a5002e03220201c40107a6215004884100e01000e003110030030500784c01000010f000500800000c11020045440780d00142c1381c044082d04c0c0354811003013191282d500c00203031800c0a00510484150080213452a101c4881245075440c42c0f0680714400c40c4108040d0400580b0b402c02c01842805050b02000d8a96240038100b0541300091030500070010942d05038881075407a0740c109040400e50141010803a0b03a2003114031407074440806145a0b000e0b0030809044c3c03070084142d10440d002041d04000d012203603681c403000c0c0e05038495007014034901981040101701c1c4070004604603074655414540442d842d42c0d6a40005214882a074850b042603584103052840c1c00f00410039246460381604000071085201030011b020f200e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 586560791 1250 586559541 586559563
    0x31006050c1009022e08091c120f0c0216061d09041a1603060b040807030b07030207050102040f0503100b0a1a07120c02030f0102030c03010501050f0c07062c03 70
    0x40c1c3c43e61600e204568441003108078102500d0040c1c0c50307941c2d84282c003094991940c030041d03022910143c04070704051780c04600d046440e8100c0c820300c94034403c040000c844498044451005030790303480c05207d074000e0716405040071040741c6a004146140302d04100a4004103254488010300c1800010301e801d001d2840c1c41590300e048101d420700d00d10343d19824100e41015955039111580c01c070303501c100013038a008101402d02031100c1c2c0d80e041111680b1241c0e03d07001440b41d40a0282c0c550311401c41003002a0f62181c1c2c1176444060b134079025051038030a9640c1c6082e070f00316802107094000403d20501241c2020405000c2040c0c0c000c10500c40440004013051a501030b5010311081102c000240c801501c11140c21588000e82c8000041c0040d0341c0721900416094540c00d0480c4a405640c0007444080014000d5a0090221920640c40c5902c3c0c40300548041e40800e41d5100502414882c04c1c4080c201401030300001c1039a0707250345441a03003044403000700102c1c0090b42e07804000f50300c1c00c8416540700001c40036194 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 586562041 1250 586560791 586560823
    0xb01020606151303080316020c0f0402031e010e0412030b0f040b0109050603040602040509010608150d151b03050115020a0b0402190603060501020118021f030609060b031006050c 78
    0x10707064811012007944203188280440680c849400410880203200643c440d8003850f000c5034800300c500300100d88071800072700c0031030380010910070045d005c0c035040c0d00541d048a500700c4452200c201d1880e40429010b1309a004e00d0100c460b4500b08414070440c401c1c0000c1035885881c041050303d496038000790391012600d10080c0250343d5a07250520990059000170060030700180280e07107a02c0d02d807404601a40c007e004e071500485112000082c00e03801201c0c1036010b04d0400704440a2003c409050041c1d1401142c03080c0d42402407601c2c25000c07000c1340d1042100d003164101440803208000500901542d8069101d1028028032841a001031035001c40c1445046500440071815922680000391940110410756406880c58500014040380c1650203141119400c1c0c000344410aa085c0790260464a0094081c1d000305014900072a4a86550032408040b0200e04000492076110600b6004031219908070364200f4100000740944e02c804814150010001861301501e0800904003140d22603600314034000308 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 586563291 1250 586562041 586562059
    0x601090504231f09021005090d3206060102060f062407080f030109140c03040f020127050a080109030221070506040f060518071707031407080607030b01020606 70
    0x10941d8103015809030b20724907014004072081c10200344002402108030491140000415010240d40520181c40800078010829a6000e2468841c0e00c2c600ac80540c541941051045501c580c0c03040810404200c034171800000d014603c0c015001a1400c08094240c92000b681072040200751303516002d000c0741065441c404031a81040ba045105068010410020702461010030f100983d0050040a54129150f0500030b2000401d01d0404018003482921104590b140c20400200410107071140f02c60742034410314011104100351200381d404a9034040b4000d050010021080040c0d18040e50080041c0c4000d40c020040f21455a0300030795144011082c20582d6181050016100e8400200382ca07000d42d00801a1a110300d0149011104650102c000700d440e540b81c00b0108104000b440103003034000504200074440903040c003d220100c0c0b001c240b083e00052161040c0800041d81000240d003c94219a000304416400c060384c580c1004401416081058a00703040003c05aa0000312590003500950f90030704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 586564541 1250 586563291 586563353
    0x80c010507050c0307150f11190317040506180115120309030507151215090b042909060105120411010903050d021e0118080d0e0a030c050601090504 65
    0x8140003060843c242c0c1400340240000c0e000e030b1040d05503100d0b04040e030f841c03200219503418281c5100d2420325105200740e1041c2075568040030b4040c1c051400300c0c00f03410309445c03800d03200950030b1401e402118101d480e45c1000d4280106149040100f10710a4400c0c0024005040e035001a02940d0440340300d0140400c010501c09024180070312110406181c016058030311042c1c030f401d004d01c850402812074600044101c86e4640c03081c40c45124520b400d20000c3c0f094411246401440009010000c2c90903074001e5840103006180a1074101d065402c00c0300004001c2c0b410b4404007000001c46004081d1814020200a0501c245095005a9500503809100d00e40c0c034908605c0125a15a43d40e0401003451158402c0ba0050507000036026094039403403044050048420305d88142a14101c440d050100388000d940c0d040000d0700000030b041c081c1c0018500007100045034800380d1804100c49401d40c042020200b1800c103100e411b00006014280c03d4005000504107952030101d42440316144600e60103941d04911 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 586565791 1250 586564541 586564543
    0x402030a0b1002030403051c02030304061509150f0e01030206040603050702013909060e090402030a02030726010501061b02031c0f20060103120e090f010519080c01050705 75
    0x100521409040c400000b041160040e50300d0303015000c195400c0c8141404003010343d540e02030a001d1f500255000e1400c544440c1d4420014103241d86400b13601248003103001c035410b411031082c001d54980d4901c0040201d464a822004000840d812641070300d85d6000c014000341e15540103d40071039216150001c4d059650010490040c25154040c019038103108290034080040401c1481000b0f60480140b92203a0210070241c4000310a80f2860000c10311040b4044060303c0c0a174901607106002a0a0f40c511443c2e542c002400c00101390080118071203d1240301c0c10744c4140150810008000754002c1006504014024001d50a00110300c0d444508003120b880464600340641510401c0d441c0d480703141e102c942d10b0041c10320100c42540a00042c480039040c1700e540708458107034140300300c2c0102070b00c2c0c03590075900c079890f20350701110450050211420000d43d1980310000301c3e6200c0c2c6e1007070070200701d15410300c410800340314240d171a00b284a9000402c20b006070b5a0105205401c0103090070020b684445903e021 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 586567041 1250 586565791 586565801
    0x21e0102070f060b04050702060609060111071814180a020d0204020d060801020c0d0206010f030b0403051b03090a140a0b0318030d1b0f0f03021b061008160e04020402030a 75
    0x1031504405a030700000b0480360f500128130f007070001c40d028003c40d581c1c0202241d07210700889886034080c24000104803103501815080d45003100e110140c403e544c0d202c13070919924103218a40b24285603a2141410445550000800d0300070303080c0100850180e40b060441583d51200c048060710419461501600310341d550b6040b1415249000000d124995a42c00300c14002d40004d0361400c854090b1550b00c50b01248003080c441d06844218212801c0c103411340e11040b00d00e0030010070441c14460200900580310703030840941c8450481e07010055981e40080d10604c84d5100c034030b600c00304600200808500d20741da149581e100540e02c503000c1a40d00c0e81e64460707113000c03041c802c5c0f90b044103140000165031140b920a0741294110b41e00310407820141216500089402804001a000006010b500f018240d10300c00c0d002883d80c1d407941003424401c5105802c01340c0c1403d000f80e03141a4110030480042100c6407040c0110725040880d2200742c60380900e000030b800740d000d0004100030f00c500d80c00000a540f2008607400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 586568291 1250 586567041 586567043
    0x150905041404120e0306010b0c0a0803040b0103120504230f040e030919060503070c05010b18041202120a0309020a030501090c17071203030e1c0302070c05060a021e010207 75
    0x6001840c50901a1551080281c0c2e0648040c1c034070b030748020b0003980a48568450800c02400806080c0c0c030700801d480980d001002403049500401c10904041f0740ca840140d80114042c01880c501540340d40742580341000c0c1e1600c401c0912605000030880c52a15950a505a1001810780898044c00c1c000045c04403442c290001d500518085071703410300300c4001028203c2d4180640d43d200b190300c420080e624007442035100e0f40c40001c03010000602070314411101c039800141b0540000c83c4094582001422401c150700c01c104483c859581000280700e0200c9250071400058009080c0c801c070b03000100c2080d4030400907103000f403540714040c0008544804001400442d006002008540741900e402d1019034024400d1058034501103403c0440c03030002040751001ca0b0b810031020200520300b0344e001d4025002e084000070440c050981c1d41d124140055071640b07000501c2d035400503070720500c82c45c11424820080e0420350045c0003c0c000124410b400144810b4201c8059080e41103582c3c155010394003a11911070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 586569541 1250 586568291 586568299
    0xb100507020d03120f0b09100e0624030c070b070f02121605012406020115050411070605010303181202090c07051204080d14090108011401090e04080a0305010b0310150905 75
    0x441071072800c0d406c0e8019079490a045840340650b0701c1d0864444a900c85c1c030f00030365041e28580e1010407160b00c0e00d201d1419525004c4160300f444101c503001d8680c1c040d00704650700c4c5e03c0c038135000400c4400c00000341d481030350104550600c8005000e14200007551800c05100d01003441c1c0c070000b50040d8041c44164503041c5181d20800902c0b0480a00c0d40d00280d0100d126200120340c0c00049001c94454010700800348051844407042c0b204501d0700080101803e0004488032103c0b0b400c00081010032902c2c09030078042e5001c0c1c4ca4080e00650900d801c810400c20325880b6091900c151480280103039078ed8100660858810600551222410300b401400d11040400703140388084001000200041c0204403540000803548903400110202104850980314206d4240d000402c100010b1000d1030f01d80e4500810500c0600d04004500c1d107447c005e0b03400c4801038070300b03941260020030040f019a615002d40ca002d8092141214294104032014030004c01060244140d01c804094103510242d00c140d070303080000d0a0040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 586570791 1250 586569541 586569551
    0x7020901090c0233040201050403080a0c0b060409030c0b0903160308040606331803030e030c010905090a09060908040e150303030c16080706020c0f010b100507020d0312 74
    0x75101801070034030b1505440075001c0c1088640e9940c40c03034401c0803000d206401c510300c0c101481604500101c0b00040c000c80c1441000d10001c408501c00c480a080b6612407900c1b11003100e1030900780864603507c001d0605200764100b45614000940c0400d186000170340c001d4001d090b5031030701e40c566421401085c180c60101d150f550850000c0c1a401002c0740d014038001c2c0710400085031030b4800d00e45017507070b02150800f4407a004000d41c40c402d003911031030402450440c0760903e213282d00301390074140c400d0b059803007500000c800c80c0700120241740a21242c3d9101009003814602d451030714001c50761034280208680c003446d40d1188900f0a01ca01d942018542590100d040f40da6181c880303842155801041c1c076003440025010700014068200082241d0051a80303c0300b1605206038030a400c409205284000c961030310052180d03000082c81030014280c90380c510340141820640180510303084401c0b00d074142e4882c00d0451480e0440070b070860111400c0302d4050704d852561f2596428243c3d0045894440f0150407440c01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 586572041 1250 586570791 586570799
    0x304060603060908071709010e0f0a09050901020901181d0a0e010606170a0606051b0c0301020f071202010203010f1205011b021b06211b0705010f230c0f07020901 71
    0x50040194a10480c0b202d0f5031b000c140d2a03001400c4c020000716602041100049070300a160215113601e141000400c0741034001d4841714840d00b5250240c03541c0301035079000700341607200d983c00c444101c1410040910101d002840d12150a4800711580c81a0031a810a500400c00320764003a00b02d6085241401c00034000c0769555880280345140b091200c0000ca48081c011803103407a43c41c0500c0c01107d040e50ba90a0802d101d1804880c2502a0790b60b00303c1c4d05100b18031060f10790351800c2c0060055a881380042e1520b41046007441c0e4000f40c070869a070011648104014001001445106425503107400f40700f080300702544c03401e03500410740406040c02c44510150102003965000489083e036040344d9a42000c81502e000601010740030f200c061124044d003924120b400660f03403421140d88815100481d101135840000001b0b86035002c0d10003940c0ea40d4483e0b02d40c032201c40e5940188204510001108500440e848400c3d00c0c0d18000606036040c3c840d00000e440e801001000156034096800500c1d04d412541e603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 586573291 1250 586572041 586572053
    0x615040803071e0f060c02070f0b0309152e0b03040f02030714060f1e0403061a1507030c080913060f05010509060d23040312060b0405030c0603040606030609 69
    0x59041110240f030261000d0300d10f007001c3d09003000f160f9032044032242280b8050350740c00003a2a544907400b08501c0755800019041d038040c40c41400a1006400181e56401c00e1022141032040c11034284071022444400c0c084140b248075059401410714241621041c4546040c800c501080781e4814031078820044240024030807241c80c6980032074801c50813501040e9850120041c0f1141010f035081c3d02c03080070b1040300b01294404004002c0081d0441c507d131134a0351609407440b0680c02a8009598466851600c0d0030862154030501002c00c02c121803c1c0c1510003110214125445001c1006041111900d00c4101f003007048403d58145406c0182902003801240010000420700741c803070008102100540060a540200f0880d070f00c904020305910301d0950590121000b5098055040800c6004441d1311012400c0d002d60080c0101e100340e03500400f030304007810080305070340741078000d071030300c15803c000c10405907030300007400d42c0c042400381c03421a00c030303902c0e82400c2d00241011b034005031085040040030020440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 586574541 1250 586573291 586573297
    0x3060102010b040e1f06032310110f0c011508010c08060414061210020307030e011a0a1403030c01060b03041a010f0504020c0a0f0b0912031e0615040803 67
    0xe90081001c0200e07081080b0070b5030103881c28074005804c40900340b44817000501542e04007400b185404503070580e42c1da41e01e041c09640101e41e0714810b4240c2444800c0c00c10140440c54800c0341010081c403480c206a60308601500c603841500200d4980092068042c840070b400440340182c0110b82c85850542d00c00c94580644020407584000030b4003000060b800d4a0113104102a4201d100801e220740d507a00b00c2444101c80d1042150b400d54071030034400c48a50740480c00114030440503a9400b003a0141005481d9082d58010103542d265841c1c040301100c4103803144110501101e03da140724418626000010034110703c03407000e142c1e0955003001c4011074a010802c005601852140e20104002d1840b407051003c3c940085c05007079400801480200301500e0039401400741c42905c2c00554088030425500d29101d5051688101c0b03030110780104004d9000740a002c545c010034602c151440c0341d841c040300c034803082c40e001d8401c50b01d02d86c03c82000b0030b629482c1d42448d0410450300040c0e940daa04c1e120b104080c2d4a0f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 586575791 1250 586574541 586574551
    0xa021c110111040b04030f0201020a06020301060e0906040b01020a02133801020604030203091302090613090f020c2a031015240f0302210103140c011b0606170303 71
    0x160030700032200e00d40c0c10b00c042258101e60780b8645903414103085a40d00801c102c21440243c0c1144105079a80e4081507017480114020403030b40d02d6064140c04890706102e400440140341c0c92044c0e2408908a00c4d80c1d03004558005c03915411202e8211110344040c83c0ea0060018031622901003030211410620800002203603518080e40080100c0c0c0e1000207401203a4490b021100140145c005100802540c1000c10260040c400860405030802401d0341c003045a0381c00608a401414071a16010070100000c0d2160501541c00348a0941c5030183c261051030780c1748190f0f9240268070b4440f2446c1840e461004a1600c1c20340d40041c10b03101032401c102030342c201030f000c80030403203840460103a000620340780c40c1544c00906290010709800443c50310f00c07050310174410b06104102410740800600c14041880e5044003c481c00214608070300d5419401d0204824148400210300d541c400825002142c3c0c01c80d46280d0051a0402c86402140d040c0c0790500c0a007900b0380c40101c00c0c1e9810b04801112950204c003440c0b240c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 586577041 1250 586575791 586575793
    0x10206041421180f130207050102040504020a0e040501051912020d050d021b03150c130504020a02070306050a1a09070c05031b19030504050d0203010e03160c1a0901050a021c11 77
    0x41c49114200040e050300304e02c01e207510090400c0a40380403805500036186842c0603600060400380d40304d000c2000d0b40e0141c1c00d200d00040c28400303035010925042c85402d02401003a0b400b00b040b0a8041e00d640e9490b02d041c06002e00400880742807a0443d625105c3c5504002e134820103880040d040c801c8080d64a203c032541c200b091b200040c401c040c031810000b07022061492030116001042d2640410b90505a201e1580368080081043c0003040035200c0b40003d0042f0451580104080d515500304807085800160000341d45e281094080e64041480400011458204480130702041e00c40c0b038001e950701c0091500003041c501012402c8600403010708091350080e900d0b541a2035124110342601e00344200d8200d0004c0c08920300f03000a00607410321401086100703102400020310401141d00b0355103035400140c111902715841040303110420110303910315001020380324000000d207420703100d4090070703805440312681c10040701064094a940c07080140c0c2c10010b850711110143c0100406000b00400c249403585011707 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 586578291 1250 586577041 586577077
    0xc09090b0a0b030c09071106040308070e060c0a02040b011b080a0801050306070f23030f01150216121e030c050118031e02150106090503011a010206041421 68
    0x80000c440c010720104010040182094130803100c2080101400600010104913926000e0414210100205800741d4001d07100c0741c50a1401c2d81000f07042c2c0c01d5950b4003501440050200300030030180042d10482e155811a40403c8050080004035070141018219031488100e1076203007007c0c030010b00000c110043d050b6845030441ea803070300145903880d1420703038904d0b0000c1c44003d8144010307449010645000c80d0404064104401c00114080c4580c0040e03601181f4017041500401008400c0307842640821424000b5100e5000145545455400c0520580c481403d40807015001c0004000a05d442105011000d808070922424000c01d210380d83d010440d109c0d03203015203050034904042e10100c03d01c2e03031603036030b10710343e540030010341c1c0390709103000455406501c039800b00180340c42c01644c07100340178040303503038610b00303001d10b03050405080d244421200001d034110301c9001d00c181d1742c0c042481d42c0d010340c025210b50681c5103403a0b5260b1510019244140781d41030409205061000320000070301c000045410752000d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 586579541 1250 586578291 586578301
    0xc03061f12080d0e21040504060e010e161404091401061b0818120d020c0604030809010309050f03040b070221060403141e030a150602280c09090b 64
    0x701110000d1000d091101c06201c04244220700c3e821460070783c2d0100007903500020242d08070444061011130b4020140c1000709040c0f00501305441640024140da20019665500d49200d000816102401140e010310a0f4200d031150180106140c076040d61a00e40d4040e519a9100c1980c0b008003075242c65405048041000022030a03c1820802801600c41980c028801000c0d13581d80001d42c00403042821040e0704106041491380c852070740b0346401508101034040c8141c200c60090500701e20005e030600c108420b01c41400890461000e881184070b0a0900007038125090900600e88111b0003200a0300b840001808101001110094401e143c070039076400000c440348403c502514000800308164580c0548000f0300032070b118103642104a03490f08650f52601030710380e10540380344006104008800030004144144180544200c0710144c1a040c200c80720b0600340715009481d03000381461180860f802480210b22103407403088410038168810b5100c0e4401765984030060145c401d85030242c1e41003d180001070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 586580791 1250 586579541 586579559
    0x501031b03120f020a1b180507120b03100c0306080c0301090503030a0510031514070e0306060f180a0504020a05030a05030d050c040e040b22020a03140c03061f 70
    0x4055a80c4600c2da200000c1c0070000403651425000c10450843c89036001400108108194099001d0626583c2da403009081c039224007a403119686016881c0392402e4100700c40707903030701050b5203c04201e090b0700032501c0c2410000113807030954505195040a4580114607003c0c5130107902400071201075000345c07a00c001080c02010f0032a00c3c0f242d40030b80785400410018411450a82c40554032406e0720100d0720f4125101e85071203084031590785400500035520340c1455400c0004c900f4007580805280391030300007030305da4078082030711030001400da035005881030080c6212a03070b180342102c0d2454842030301d04840303031034001e00c40c40107001e0565050780070f8120850041650704001ca000070a05030080c2c001c40c90010b100280c00000d100050400b1a402b106010101d040c00404c0130140c055405084a46014104100200c09074034025808002d5480c24485100050b281c140d02f02c0210384c0c2184010320403941d0b03290324a06001d0251640d5a040c0103a50030410560a95103252150700186a41840c000d07450f99015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 586582041 1250 586580791 586580843
    0x702030c031902160e0718051e0f10031a030f0d051e0705011e0204260106030f1212020f0414030c06130503010e0c0f1e060409050103 59
    0x4840680041003080b240251104406032900418030480799081c040b80a80c0005004079000005480310a03028010300e2a0b1103018a001d4100c02d07806c940c000c80c94000003841d03508101c824101c03800d400e405c1d050829601c280c403a00700004013a00c403003504a51450000c000307010301000b100078203c007211503100d242000a251072903010710200030004012003901c180c81d00d800050400c6840b12542401c03903020043d55010f4490079125a0001c510384041405050902d45608401030b40d4920600042024421300341100c403801d6508650304041e5040f460300907016203215000605440070b0124401c00b0014807036003100700018030381e840c400359204101001e0203034400c1c0c0c200507030f501c40f041c04140803001c5032220780758001d04014100e40000c600b61000c58102d400c100c16540800080313040c1000a41000e000b01070f007001c0c107a4040c0901613100c20004072030496413803070b6900a0284581040e4180740740ca041503c940801050a81c9590307032030880c0d6020b401e003404121094203580184001c011509121 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 586583291 1250 586582041 586582057
    0x30303041e121707031406130207020d05030406110a0b0601210c08060a050321030c1c0f14070807050a0923030f0304240302040305060907030605070203 67
    0x1561850321561260280790188003080310340d60320844000c0000820702551030840301040d0710761070031855441c846050343c40300c0200302d04145810144143c4420310a0b4100d0340e8800d0b4200d0b00700d0203019000f40c101009010b0000020342000b05815a070080c000c000010300204c454681e1216207c0c515420483d80320078a81500422508243c4086a51580107046a410341504029600300c0700e1a84c400c440140c510350a43c8030046103c1c94288002c44c10329088a2001d018160024201008162480001c003860080d03d8544820003001041200304090b04842c2d070286030b001e80c031040300100382c075881c0207210900710158114544038001c0c8030900c1f90394425200e10016251407a50740d84084098503079511500341c01c1c040004107440810032a010100c25090524881c0004034080c0c0034000f814030300051181645100c0d07209000401000314640c920030440c01d140b02614081410110044c2c0280c081c4d0740004215019010030000311010000f4040100c0e805130009001030f440d4844142d803680300e0782507 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 586584541 1250 586583291 586583293
    0x10090c05061602040207060f0c0c0506010602030c06060907031e02030a050a09110d08040504060f0e010b1201060c1b0b0903010b0405070507031107031b0311041a0f0301090b16080a090203 82
    0x42c00340003628055001d00701c4030340614000302c1d81c05140326000084a002c1004140851190070524080c000100001030140102d03000a41c501101080641d80d941c10007444d0074800c51a81002a01d40f6110f50480c400354010401014000c01c9182c060740080e40007140c10348041840d000005007110120301684c502c0d281c101030b0b01000850b5031010302c49107030846641503410440400c03001074191a54802d0344000c0400d11170100c0058104504d5000031503060f880450a034070705103c212900d221300350720941110000d09201d171010700c080c946040005420103001c80800c0d000580050a015114001d2641c910224001c1004000c01010802100d405542a40000c2d00500ca4800082d00a8a1003688406c18001b00d038070080d80d81c3c1d9210f100c110800030081d81c110203410100304210b04481441c0d03250700704031000e000324050102070090452231164034600c034040c0d5003599031782034a0030350000c40c043d45c0008001d02c103440c0016009200e822107000440c00194030400040901c0c509118003244254010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 586585791 1250 586584541 586584577
    0x60a050d03030207241d0105010e06060703020f010c080a0b0a08030901030f0905010207030c020a0f1220130204060e0a0f14151204020918060c03090f10090c0506 71
    0x14070124000c3d005840100c50192800081e030110480d205c01c0259042444240402c254a2000042e03418507210004445a03070b040c0f81c0188030802814041c0d5034000002e8880343d81301c1d400307814120b14041000ca620071040d4640b0210880481d44410301d14807035401d01c10117102c0026850148180512144140d0b01e450b0000d0142504641c8030b60007940c101031880323a0100700f030081070300da0300d089030f008003000c07030100f410b015480b401c60814541c440004d2007010343d0740280515005130b0004042c5481d5000b480c42c0000c00c00e94522000c50702c03c0d0040181c01800312a54a021401490700a600a01490f03000c200358800080041c80d0981c0d0f04010341e41c50401508045190900801d801c1d4103020b60254001ca81c2d4001d0388131042d00c9005800042a007030b1981e10310f402d10740180700c21850b0150850340d14042803081900402e00018a054000c025117151a0b5650780d942401c90070007000f000600003d006449044400e0700e429000010380c42d01981c0100203040e601d000304002d074410f400f18101861002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 586587041 1250 586585791 586585793
    0x30b0106271a0708040e010e06031603080d0905060f04021e031f140a2403030f0e04060503030703030519060302010c0b130827090601021e10050906010806060a050d 72
    0x6103030b11000d1619070300c6400e41000703220750741c20980da000340d00301d98058050000100302580f0349580391a00183d041e0050004081c440e50009656200307400081d041c03100019412003200501d90128440310b8001e8165142030415010000e9150000d0b41c040c2d2143c14117200209038540c9001d10050760444c010700a0210021240c2218a03410034038291031107903641c40840054501d414120300e4032070b1410140000700f5080e00038005d84a4103200b092080030024221040c0000703900b040303100709100d080b1b04061410041241c00500070300b43d10303001203800d40808954101010742607004240282c0381d0411144250a81004a43c201da039184000307400074404981510124003450346090b00500401d01d0004044800d80364040a41e20811860f5140030342080c0300060305a81c800e020304007178400c940414482c280140000e545480d2840c55580240060800c10b0800d00c04014a600c1c840c1716140900542c90405002a1140e10074410312a0702d02449001880501e0301c01005401c0d0385008002d01400511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 586588291 1250 586587041 586587059
    0x50904140f37050313080d0e1005030907080327100e011d0301110d0e0109031d0103061a0301030209010e010e0a11070f140c010e090106081f030b010627 67
    0x4a02c42c200e1606101854420200b0400d00c02031021200f03000000800615080045103000c076815291340800c0304000503155145c1d00c11242e000441c0c8680381c12500d988404205074241225680117140c0c6110006240d982c0b07080c003100d060f140071084880003a10540510074480c0b14202481007000148004402c1c80e56580100e41160700781142680552260642c200801c0c2110040442440041e6010528000504a5005100c2c8030000c05009000e89052550094103800ca100f004075071002060740c0e22551070b440307540120018060100e55441101c20b90103101c54652084c00107900441e004d030004641555002134045c100c865003400c3c100c0340d5940c4804031004281319501c0840d2880304118007004201d0703940e40814500c9c05071140280403958065154036001203010f245042c06103811010304c17a0383d80d08840604494090404036142e617100e403006603400e213200b6085960941440e0000c414040e40209441c1616510744848402261200f010004c560261f462116082c1ca404002d000741d0301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 586589541 1250 586588291 586588363
    0xa09080d3b070509220b06090c090904030e061e070c06020601120f031e080a0f150e061c0803040512121501180801140a0e060a090804050904140f 64
    0x14000c070717120360910144062030303501088246058584000030310038410285441859242c11a0300d13504110300d0700008002065011100410280c1070051110b01500113444010858544122944510300a0510b0900c000707001d82040340c0c203a800e411860f801068817030002070031a040cdc03074814664403c0340c2613560750f010301300c10443d0301242003082c804007005032080100d02425006030a604c1e11810340c9452a000b108554190a41001050400341403d204444034003242c410b5074a0300810640c607949071800b10342c0c486003020b9002e0f41c0c2d0395160b480c01d0a00c28408091802075208030241e0380c0c0e2070301d08040c61503680510003044502c91151000b01d114443c3c284495504d0711418184a9a01071a40082c1d1001c00440e40c040840d913511407803012915402250426070000c02d000e0100f1880045009181da40c000041402010580d202081414000e5401c252002044018082c0310a0300e803514003080701a400d00e0301c0044611a8080d02808950007207910b1411200d0b1818101a54041c0704d081c809c892 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 586590791 1250 586589541 586589551
    0x120c030c0909070507120306141212030108160501030903140a020a150f050f040804061d10030b0112050c1602010e3a0302060a09080d3b070509 63
    0x60020400406070b40c4038840064442d2246444031a03c40e041401c000a500440354505030070145021010f010110012202c5000c0711000d64283c07030303042c1e804401c451074210784c3c1080244101c0044000a842400080c40e04400310b00d118250407519501c50054056884850006020403981003800d009192a24041e04100f20240f04503402c2c1d00c002e45a40e0044500c3c08407441116440e410081c441109600550390028002002001c0c545459201c28002d80514001c1c0e008000d9496049105401070007003071006041c0c014405890b081580c1d601900604070079507a00d011a284e42000c91307a14615200e0b10740b103408440f00d1689041050303414100700100011b0102d0522140c40c40048581d141c40701440ca1035000340b401d0744021840040340080d9207030380c414409503446802c1c1882e0006a4040703a01900003413010008501d0740d00e146080602801007800400c4400d24040c0c032960384a000c042c1c0c4141c002e560042c0101c44d02202c5a034008403016252804030b0650107050204910300f85040d01903842 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 586592041 1250 586590791 586590811
    0x3090303020918010f290310210b090610090c1404030605040b0606030403020a020f0f0d03171608041e080403060606140742020d0b0105120c03 63
    0x200c5442c0340015881c5003018903200c1150002001889080d00325014070f40640035a80c031100711000c030903600c1240b030440d550210300c4045d00440891588095852507030003810b41e01500342800350301404003500091032214143d800d00b1824011551008000c21014084e00901c0414200700381000302c0103001c0c0244061020800040f1001804031a8840340034002561040c00f0108040c00c0c01d061030340c06898003500e800c0c8a0b070020030a120010340c0020300e00001c80e90540c2c0402e059441000040c002400602070780da0444602807000040603485194500d03948018500b85c4142d40720f026440200d05540444240411a810040f501180c1320044100c081e2208495003890b0030907030f03684e010080d0090ba01c102c0302141c0340c4c8070522440303400c59440030b002c6aa003601036081400c030740c80f4284400180040c0461000907198021144081101015020302c0764005140c0003542c0008410700a52004904561076032600500481d07540c0303d80c0440c0c0505031107001104103078681240d0325000e0f92014180f2040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 586593291 1250 586592041 586592047
    0x50a140405100507180f0801140606030118090f051510050114090d020a180f02070803010b070515011205070f06020d140c0109030305010603140c1e0c01090507030507240309030302 79
    0x1003205c4030702c41c0300013800e02d07201880035040c82d10f495a0b00b075a1800d0f105141450304001000703d03d4407100c041d40e04490b1001c5852032401300c0c05c07401900912440d40081c003087c10304941113081c020000f0f1101000c0e80008880c0f40c580da00e540f001c00500c005030049070b001811480c8017134115052000601100e00d0018484000c00c046940000c158810071f903c498113901a002d10440e40101600c1803000c0340550319025490501b203a90b60652603c0140a0744204c41c4010500d14280302e81040503441180700e19004e214603584030a500c1080031b03503a010490740303445112000306113a00b0642d40041219403540040596403081881038a032486102d4030001c1c4501c0c280b14a90650600340036070003016010b510000381d15410310030010280c80c0c4080740360500e500f032107040c00603003c0703050111000c0040704080d860080e002014280618803075191090000e41c24110350b41d003404408989003080300d1069003182c078841e544640c034a904070b0003854054125100c9491803030503c0d000b9044071020754807a10740185 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 586594541 1250 586593291 586593317
    0x13060e070309110901060306061107080c1215180c01020c0a09050601050c0a0b060108072c0103020c070807080115120206070305042414091509040b100201050a140405100507 76
    0x284c04842603004400181c3c48900400134180c000541c80c10f408014030103881500e0a0400c1d041c1e4482252402038026044c1480108020030148500000318545503140c5003582042a1003002e18119501c21b010303a80250088402a507000180031625001c01820404800389091030060007060010302c80790521400700401d548880003440b030032050a00c29803e009840c2081705c00140038180040461081c03141f42c150050309a0391003210f56419100079041d00041c02c00e540700490190181110300701e290321903038001017103817900866503500b510343c104001c00003400072008098004280b0700c90000d80825100c64a00541000801410103a0090504925281c0c6d55480102c43c0006131342128900c10309100300c007104039480304120a20f4441e4005050a0550090010360110002030303031000710410000c1c0690711034031180c008000341100201102600f078040f4030301902070701088030141d08a9252040b80c000c4e41d001c1c02a070078001e1f0380000080c03000b4403d0321200c5000b0440680004180701d085e1405c42 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 586595791 1250 586594541 586594549
    0x606030b04050d090614071401110c0f0c0418080c0102070b040f02090f090304050d150509030304060501050a030c06030218091801150b07021012020f040513060e07030911 75
    0x900951041005108250300c9501c0102400f1a6412060810135031940f0003c507009031b041580e1146811004544c1c0302118510105e004240080d01c40c061a074021030b614210a40c0400c01c045582021f0b000c0c0e840408060003080300f2038a02e01c80b080c9001e010032051001190b00c0c40060600304000000061404d849034440780340c10070381140c0869488011805410440c1411820690421442c420302d04550130000c40c290744902a0b402401e0140da4108a444180001e0b00080c201c0550088010407da040180040352203034421074080d91900d081c04000941070074411010011203410400805403e402d02c00114069030160b1190512075506a80402403a542c0d1a01f0340d000d1007103081980e48980c2502c41032401e50b80038807241012070716a0305040120325610011100b00f80e50484541c5151403003114143d4a10220b00f94100720a8408a038003514110300c40010070584030202d408041c0e400a8194903010399010f8012820002d02d4240810035250090700910b07401803117600d900382189080341c042 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 586597041 1250 586595791 586595813
    0x170c040f020306030c01030c020601120f06021218070612020f070203012904020c19020a360b010c1e1e062007030f0302040503030309160602070f0e04060603 69
    0x864181c1c0c0001804581d19040225015aa0003070809100b90b8004d02d40c00b80d240c9005100c1c0254081109000c42c0c04c000303011b4001a65158081c2c801c40d181c141650821f5103211040b6102c01200308c03000c1c60600301d03500015420303084984039500d03d04408004d1411001940140865a07900c0300f091081c1c00c01a9801c1c00340c64154084605928007907031000c0d440448814142020602840c4100304282c01c0003004038141da1a10350480c98050140100c2c0302040d9900c21030f074003582c0c0000d541001003121b18111243c146142d441242200718203100c407001e0a08569121401901042040c64800000740b402c00460701d105091003400c5100483c1d1f6225002c0c814010380c08500744264804080e41080010310420545514003e50541e40221408246070700e0300c1800e501909000707030781c1100010a0710980455000d002c003c1c0540c1e4903410002c40d29a901e00298014100e2184454008038203517200091050803110401d064480c3c0902d0600304500c10b54000d002aa402a121400440030511041d60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 586598291 1250 586597041 586597061
    0xc020105040204050a0213050f1f020f060c040b03070c0c051504170309130b040f181a150d060b0312030108070509160f03150b0406021e07170c04 64
    0x324003450144100310842d44028592501188140403450b40741640343d4031102505c00650300041c034180c110b030000d1300707a0202203540b802420401c12100c00c210b40c00709500c90369002045c100c031199140e41a4600c0940030328020305841d41001c1c00010701092142e5401024a401003260b0608070792110089030b521420000603401042c40040c0c01c10515842064408241c0300d00c00145080860321000104041444100362960700d0301c0340041100c030394860b400b2445145811804015414200240030440c00003a00d00391a5480045404000001c040d0041c074410084003410103540e403030540401020f481c00c00402d8030300702d80c0c58000303074019141000800b03400351855150310346940c50320040f40d2620010b5040640a00c60080a1041d5941c08201c400c1d400300361801c04051040010801b20000d0100860000038240d0403100010003100c42030050081c0c2d02c6d242e00355446031094081180400b00019401d07511a88610420054220302c60b0103100c0f001c5820054401806101c0300250960310700c1c0398 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 586599541 1250 586598291 586598293
    0xb0f131401050d02030607050d0b06182e0c0303021b0109170702090106080c090901060e010924030e070f150806011715060f070b07030b090f0411040e010c02 69
    0x102094203214031541540c0109800c4600840e030b041e1542c00b01c0e841c0c90000d407810341402000710f0400341a00040e040741101580240c40742d6224540c01400703140240b840351145008609002105074a84a80c802035100d000c20140c0c1c601c00d1100002048510704e206041c00d07810594203010b005100c060b1804103184d00c1c600403001045003142401c00d80005c594040381445114010085580141c45500105045421a0074001c48658882c0300b0310701a44581d071410f680c00206840085680c58120f850581018400c0e620402c220b0f071501ca01040c0c506404600300381405800d44c8501511780b02c0d400040c003000d590415a00c10690302c404d6019a208035411140c00c1c125900078541032a07a01001881d0b0000003403030000000d005040000c6403094000d40304409140301810500841e40b25101219040070300c907000e082e42c41445081100444406542c4000041e051130808615480c0044005000ba156150360000d26215559082d5403450081c45030764015803900b80090762f9100a01c51104600607a070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 586600791 1250 586599541 586599551
    0x10050d0f02130602120403031d0109151805030703150908040e010b19050f0a1206050d0b01031205030606180a030b0109020703110f070605092407030905031f0b0f13 72
    0x20fa0b020f81014013604c2c0f00080810188410070201c0d0f03100040e04000c21110307803203034145d5005000498400b43e80d034124142d13030f82d112a607807910349074041030f05004142a1380c41440e00310b81b55401c050b210f138007511000d400c12840140c0c04100c10203d0f070004d800b840c8104c40e82e44c50b2a84c2c2e8141c0d0356211360264481c90803130001164071290400d1820f01108400d00500d0281c1c80c018550941c1485400394481e524100f02d462081d10041ca81c4030352100c030207031400600f0750a4406003860642040c1e8024001143c405d603075200070301030403806881903e00804004120b141010a04010840b0500380801140d9020495174000004500381018403400303400d120f00b0150b5684094100a044000c482c0b144c815160b001c030110b0400076201040d0001940c0740ca24001d40d0322007190300062090749440300c101c082c0000c42900c00f4100c40c1d418000f000385901c02d440d6030b0021581e030010140c0b20820289030034035014503c04205e2507801070798010708a1010040c603c184640c9040041800e0811100d48414080c0e41c074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 586602041 1250 586600791 586600799
    0xe0c090307080f060604021603050309100e010e070b0c0322031a070e0a0503030901180b0a110d030b0604180f0c080711060405120c0f010e01020306150910050d0f0213 73
    0x13400f2466101e182500d0541ca4031400d51544080c0b24410b8030058208280071021030403503c0c040c0700d090400400300c40140980080030700c01500a01d03408001c090180300300c90f0005910705034070040d901e8a241c0f41d009142004003d20140c0b80c00005051407102d50130349200c01100141000322a071b5a008505582d04d505031820340800362180501c0c6202c00e206030703041c0c50304108607038000003200c08003c000c0c030b0001d100d00d40c501c0e407005001d00980c000705c84039200802c0c0c1c13102003540a407940409100036000c075092050451429000c80300c907500307010b420113010001400790820b00c0458202001040c8070009225104d02c00802c04c950f041c0a00c4000180c03e501404072640c0e101415441c01101c04019101c40e00741984c1d0141e8407090032001c0340600b01c0201d007803d40d10f04140455041f41c00d840000f0b003c9140c80b0802c142c000d41c030440300b00344204100712004500340c3d0503109960308414080d1030b00d005c4a89003130007a41c26030000c1c400d842005c2d8681129007031101050010f0151428480384001141d424 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 586603291 1250 586602041 586602043
    0x7020a030e09090a1509020d0f06200306010c0f0b10030b0601030e1c030e030a12060905060d0303090206091c06240317090a0e100506090102070e0c090307080f 70
    0x7400d404a120720000c005200c5410f0002c80c02d03402c15540810310240302e009044440b005840c0604c006503201c1c1038a610407003409400303207451909500c940c00410894411110300b01e50300b030fa49141007258400910014a881d4010000120f083e4050165090b60380715680c2c0343c48500000312030040100d040050100f082041f80540b05401000c01d007020720540b02e0f1010015901c03000d0f95251900a0200f040d5208050300a41c0f10b82c61041c02d0005496840c0381c0d528000d041d0100440188410301d180980c0003402d050203124250048400038690304000c2e4503510704501030404e104013139a1090701000b0540003566042800132000d00007800061b0104840c3c2130100845007401c1043e41800e0014240c940071007603c488a005803039110020380031480309008020703014014200380c541c1000d07070507001041c6c0c000c207040e440303100d80c20f403401000b441ca49070000d004450050090746809603101c00303000e0141100c0075a4072980100c00c0c41801d42070200401c0020301c2c10342284d03c24501d94200304d07010340b49140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 586604541 1250 586603291 586603307
    0x80a020307060b061606090206091002030c060f04030e130e190201020f0102120415020403060504150c02070e2811070c1d07030b0d05010e010614041b110a080307020a03 74
    0x8003100d4203800d10070021001c800516285d0001001c0a50b2600c0010844d0f40d50011b850585401420030410b00d4102480030759a13910080100c2090720501b000103958111a52001e4800d5900d90380e809a070300c02c1001071102120040321040d9200d916600d42c0002d011041000c28107400009508200203002400007905208100f200c010881c1d00411003840300d4920100300c26000b80d44800700c05418203514894200070302454000400c5641003105000901081c0180031401041c0c2d150304104a513003a0307a01303a9850816204d00070300d00f000000058040b61801c2c2d0006c0006c40c000340d003441c0d018800340c03844040754094110900d00b5500800c40c1d006100120100c90302424400c2d0515141480115001d200381a000700160100740e2601129a070344d0321100e8003807012680c07200c001e21a110785902c080e4003030070541c0039a08040a250341c8038100d5151600a400c540041030444029840003c01c080f517240343c407415403a80d14440c65141000141100d8001d5200e001c096000d450038144919005180381 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 586605791 1250 586604541 586604561
    0x303200d0c080609060f060f13050a140114161403130608070909020a12050f091015290711010207052e0306090c0306080c0118031707080a02030706 65
    0x1454400f00086900c5102c207031901300408462440342d00441c60f000909030300c202c021844070700201081c0c8a1120300c505e0f0b400401c4c0c65080b14008150b6454401100030101a1144540000d2442103d91001c000c6400101003d64094420110004040d15900f00e60b801003c50351609500c00242c001524210b082c40501418a501c0e01c041241809040100941d03442d0060150650f4006890542a03000740110080c20791000c009010350318240441c07014029003222560030b107009814a28014410f54401d50418a4020110041090034001e0030b0741d00704000051140c040340c01c50b1211266140d1503028082d102c0c440d201c070f4041001404002800c009659200c2c6006000840e00a454840713640314150100c25010b14101e451030281404030080d0040c0d0340424102072511809110050f45034004000351008001140c40d0781002e100112400713410204802c100400d803007000d0000811008405045104162081b8184000c54a50b84800d40c0409816400342c0c0c80001d00b4020001d44d401482010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 586607041 1250 586605791 586605797
    0x18041101020a0f03121506030212150a0905150315070f020c21010f0f02040602160e0c0703020f07060c0b090d21020c15010e1f050405040303200d0c 65
    0xd41c1c6582e200428210890402010b0111008485000c40e84640c41106c020481c81c0080d89001c2d90390714007400a6005610a103500c10020340000d25921401e910045105000303403e80e15940d18103c20400140f401400381e8541980c1c289502d840d540d000c210300d10b1907940110071039410742410750300640100c140b02008800c0d904440c02c50320240d074a5040d8084810402881c03510f050b03061000d8140140780132020401304a240580c442150034013075000d0020f07582780760201e50740560041c2c9581141141441060030104800c0001048001c2840103400018400e0040300c81700c01c1612101418000350782c00600008051410711401e01810a46150b00102007174050328450485030002002c2c0300c40f540d90a2440d50992000300003060070755048440b482c2004098654010340f0f40011583c4100a10a55030700c403180401064542d12a102001d004070745007180b502041346804144005401e00030020f809055a81260701d0030b1000d0b0071598110304600260b101c0c1e6500b0444084011030300f800ea418010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 586608291 1250 586607041 586607053
    0xe09010b01050706020d0915050a060b030603120906040308071203060902070506060120010e0d0305060114160206090d051c0c020306010b03040606031b030204060e0601120e0c1804110102 82
    0x20340c0c1d0304a02141e10580d08203070050f030f441c1107203c0d002d0040d000303185000b800c1c00c03403020211180d152541d2180e030154001e83c0091004a035180f0a84d00a4001501d00030340c0341c0c11140104980b18200d40080c680903001034180b6040030741d2b03038450f0003198024400642d00888010103054000364940b0910003e00007070345d021810240d0640780c480d03980703034020f02084c1400b4011086107a400784045420301c200c2c0c6504028081c1480580c42c158450000408070408241480d020800c1580100882e80e9510b01080d060b600300f8503000700c80480903014a2043e80c00483c10450f4070789c3c03501d540c814901c2c118010001804080c1240c0d10301d4002c0f880c040a800200b20045001500580e0302041e42e50440320070144007038598442d801d10760300030402940300a203407076181156588160058032039581243d000301c504120180e82d590ba600380f440d90481d0003d0004990f40c03212841258550b0000c01042c00c40402c907044211050045240300c407071848880e4560702c1e60701c20401003180c6400c2c5005c0d10745003840500340c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 586609541 1250 586608291 586608311
    0x3080c010c361707090525030519020a020a020a0504110d050414010606110c030a030801050919050703060513020f120405150f09241b1309060e0901 65
    0x18911240482c02182403801550003040c99070086400c8040e00030070810122890350440c00f00d9580c0c40502c80c906100c1d041c080050304842c4400502042c03030031100c40101204900b51300c12002800700a101c801100d00c400a9411001e0300c1d44060545110321343c0007000144c0441c010000901055400710344598202014529260281c609450200000c3d8001140680b6186040003a401e4180d07802e001540c07a00c01f0000704a54030110040101c407a800036100c0401003402496100d0032006405008640c00340010001d60401c202c4055001d244004851000c5905680480c140e6030155a20000603031102018000c92811504106903031424200862178501c0c21403c0140c68000c0684030140d1024440011301400014816180000d10301c1c20300104078a0400c1d84060250020340d0003803030900c200460780301103224140c031106412011254040e0140e035441d0083c001440307003601c80941c1c030301c083c48482008010920084080c1c0b929400110361941888882211810014100001e503818014144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 586610791 1250 586609541 586609577
    0x203030901050922051008010b09070e010c14061618050108071205071e18032415060327030509040209030604030206071b021c050c030703080c010c 65
    0x1460030602828040d4840d01c078800010002d00300c0000c0c440449071440100207101220340d11441c8a4050b1107120121545c940d0350450895000051140c0c200d2814004122114007800591042c00d80c145000c0300c18200b284e4405481002480078584290300507000c1c030152000c0039201d002e4980b1503141c003a4a105010303070043c5000d082d511034a41404040c201040c4098414544e4902554480d5020b00540c00c180344000c01400074400c1d17002041042405105e5036520899280c1054210540065005070850b103521141c40703622101c008666900c0d04462000885030301503465126007441030035216a107484070182c00e5940c0c1b0f80301c08a06400c038042001075200e075a440c5240946d0180b414075151820034012030020b2103591070035a031600c10003042108040d03001130b01c1881040305a851160143d500003400c190081c80400003540326070001204030081c0d0700d400355005010b0040003140d800310150f0300864101b408a4000f42c85144001841130000302d424024109142224940300c141341c03260310111 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 586612041 1250 586610791 586610797
    0x41a01051213050a080703080109110904110c010914060610080f0702070905040b070908030307020307080903070f0315060f05010e040f0b060a050d0f0603080906030a061d041e020303 80
    0x1101c0d0600c05102040203042a1040301100c030740d1280440b00c80748420306000380980c112800480008809500200f250b003240d009100720402c2c402c0d1240d080021010400c00134000428204410940034009001018000d0103090f104500491071031003550001c1c01c1103802d09000a2080d40900000c03100d1048060380110920381c01f9074100618440c0351200a012804c0c10031a500c001204d42c2054180014807400c60040b03400784017a51244640c481e6074811080d1130b4002265020090307003090002d2008503070000001c0904c00401001e481000e615944025180c0c0c00c0c0b0782099410103d045401c0c11b034902a0f00c44d01010703080001c80c2c00040c6242c500000d00c0491701d042d00d035002c0d07074943c10421940c008982005880c9080100b0080d11524070103c018020b800409084039503e0411070240c020001070b2003240c0681c5d4004000310b1800c2c04c041d0601400b640003800703103664207950700700010f503400c2f01001a141c20407200b01144c5890a03e42003aa10102241c000c3c00746200b024440309005031740c00821 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 586613291 1250 586612041 586612057
    0x1905030705041109120a05070e0f180c040c12090507060f0504080c0f18010b03070905190308280201020306090604140103021909050412030c0f0e090c190e041a0105 72
    0x803041440310111701e51800c3c4416501d00400c6441074081c049400440c4400c030320301c200b88200d40d0340c505503102d00307212003c0c0d025240000c0036a00302d030f00120428101500101c150004908007921172009010340d04046841d086016200b5070030800041c4007896114080410005191410368241420514200d840d52660f03580d940c0300360713150050001591510101c00b4400c2c581c2c180101c51942c0d44400300ca00940c0111030340d400062180c00c0200701440e02c0c2d0020014410b20102040b2054203565031000d250f81715024a2004a281050141d404114102c21031101b49403540050384a041441c01d10407a884081d1a00f88a94205140078a00715100780c80c4a0460760105c440200700700d00f0038001d01014075036400c1380d84082d0a010405c1705008034900d0072026918913560400401c440d209003154500410803680d030008880f605110302c2881d090a195401642c9290082d10b000318843c010400e80000340c912a0105a100e645c4130795134600340c4107600303c1ca48491810421303250303400c0008115225840c2d03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 586614541 1250 586613291 586613299
    0x10e15030f1e0f010315090302030f030402040207080408010f0b090411040c090503160810020c0d0f0302041d0f06060910051303020a12111c0b070c021905030705041109 74
    0x40d42d040390b81049041e90309180081d4100c0c1d41001c51607018503a200f40810f071042010325080032100002482440440c58045e40a103081c604030306898070481e4400f401c00c1c2d0744030360248510302c041200303c00244000c1c1110000002e010443e01501000d81e091440d80c1842189010204404100c0c000b10b11181c0100c1100c0000301160300e540c1c03d0700c0001c0c5a402254041c4581122240c5040310b0700400811b880003d0100c0d070400010104550691240050980c00c60700840e00145103640136134014106aa043c0c10050300342030700c48000810301c0c0b581b5111a40f16886c0d58080c4400d000e407a44420f504038501780c55141c40d0020325408904007016007428202000800221403010241c2e418044001c0d541c002c00640d01e00783c1d40c01e04884042c07072440c0140c4009400c03540107800351520654111242024104100c00c00005131102032200e14010728040a110700c1c01f500d42e00680d184c035591407003407129029101e0250f0070324082c0740c5844903540049000f1803030004c3c42d8445105036001d44079588030442d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 586615791 1250 586614541 586614571
    0x9050a09020706062c06040b0d020613030615050f030f061906030203030a0203070c090e0a02130b03010c03021c0605090f13080705010b120316110d051605010e1503 72
    0x441d2100041601e0361007000b041e0959041d109807500e04c205c60401a038403100d141260754a40c07004001c11600ca04410365844954180b04200508010700039211541c500c481044640d80d42c0e172545000c0d91610305151400c0b448080080c8442c0c038246503500700c0282c0c194000c11680340f07140315299490f43d01030440e049200740c8820700c290302c0c07110f0741016010716405401c1c1c07522000320190103540c0380c0244408440446d90541c0c00300f0942440d02c549a07c190030100144420040b540a000807200c08006c0040e90549802036008561000d0155003140d81d09540c0041e5600b41e40c141103081c41020a0204403181d080007002c000e15620704005540058080c1419201910759603001c243c111a9039000400d06180440e0003402d00406612411501c002600e101944441010401342c4a200c0c5d222000405c440700000800810580240e8440311640541620b0440c2d2042c0c440f645410400d079400c03441c0326800300c4140314550b4441815903d0310426613544448403010102480d060000034004501c4407085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 586617041 1250 586615791 586615793
    0xa0606083d0b150720100f0315080a11010807020712060b0303090d0b01140603010e2a0f0c0f0a020a0b0a09030609060b010f18030308090c0901170105060109050a090207 74
    0x1100403003014840f1104015503400c12850305132119907118500341c412a17004d1012058904002c81c240c20161526070303804c5424500c2290640c002c090714105200f001c0008140450450710402c01440d1080c05840320a03515504a8001031030315900520700000c54200da03104203d00000b901010703001503800b01c000701d034120044020034514003a142619601000da543d0319418441c8003407959040c0c805800b6140202d46e03e120500c5194071080c41691104401a800214000011003c400d004005100f45079040140708024083c1504152034254490700b0003e032203011034008000101081c4681009440712610b65000100300302440e2241c140c420600107001d501c4144124900c034042c42d440031041010006d24100880103058042c0c103940801c80a03000518501d000b5280804030350089045203051a007943d50854201c04050070200c0700f480345140441155903010451800f80481c40100d00d074800840760028251780700541140d040c4988036030240200d44a03c900340040c0c60204002580d59121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 586618291 1250 586617041 586617049
    0xb03150f01090f030b061f0c0c0504050601050a0809120c1e061e0901021309020712081014040204051c031e0c120c020d0503040f0e010e06040507020a0606083d0b 71
    0xc0300404004000d20b20407c2d080a03400a2000c201c041c020441c0515141e15401400304030b03001030719000d0200b80203100c80c140481c0300712590355010086006842c10030020f0307a452116500309130f101c0309082e04000505a038003051981040c207841014402000d41d400d00306a10703041c11048415080e00031440c000068010035094045440c0a010341d8100174500d9581d611010003508a0b0360100d92041c00c010201c0021442600d0141c0101c00da180d85e240c1176841e02c50450000b40d01e9202c3c040e00140c086c800081d0666405229041580c0018078100207000c0d9440c00500c0354044400542e2801c2d68102d0390394926903c502c0c062030a5034000d5848003018142c9900b602c0c0c0c0b500d990802540708400800400801030080081e00c2114180510401d01303545030040071a80309024000c4525061601001626603d4507420281e0020f90310f0043e00d029042c1d54171050152405c0f80c1001e880c0342d0200c032610800b00e510b0030440158518139801c210503001101544a203002000621888154441e4031840040d90303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 586619541 1250 586618291 586618309
    0x804060507030c0506010f0e090c0a1806123503070f11060702010606110d020307081303082205010e030309040905030415120f1803180b03150f01090f030b06 69
    0xd0050101c0310715680d205d003040180702c401c2c06002303140030225000c203160391000202409005002040080b40b28100701842d03264404520b010b04103107881e1036000641800f441c4c1c0c2401000d014500d1700300004207803001004040c10348001110302045542c146030074040454183c90b0445074501d4006060041c8813811074902880540840c1c3c2c60241c90103120350b0a805501c540c00319440c1d901c540e100043c0100840780c8070158801c6041c0940c00400c88580081c50004c000c0552a0201c840d020f40b00340c403911b48004a800c2044141c803420251414001201c0100001e6801442c0920f004400c0c0354140001c070f1784a00800020320300a030344034500407040000c103000341d8002d4031440c00111407401e40000c0c0204005e81c51618220b000f4500307100303444a43c0f010b024600f011840c101c3d010b1040e122a5070700329006040031719181d0020000b181c010924180030790081d4010040f1082c1c502e01c40040d8810044d8000343c040c80c00b030601c03101040030444038000b44420f108498002e01d0008160340c8510109060300d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 586620791 1250 586619541 586619543
    0x6110307020a240305100306051e0103120201060506071707030e0303031f120203120a210204061d090c0a1404260102042304090c030b071b0804060507030c 68
    0x20b0219000421840c407030002d45200d40d411281c1c080c800c211400026412a207050b9140001040b421600740040b0710f403030b0485074000850700f1880c0310041c0c00b10030b811271508003a0000c6807402000a075a403c80e42c2d0900550014080803101c2034603184099880c0403100c0c071050320b100e50803100800d0f07401c00c1c58014284038000e5100030341601e641e490301030f1b5501c80500c0c0004d441a2048906040820701031100350582d41c0d05507000e0014070940703003a01e14644650308110343c1030080001c01d22500d115408040000203690301100c20241c1c40c0c0b0304184024100400e41c404581042c3e503044603d005a83c1c4010140350031400f6070015a0b581d8002ca84201c40e6010421411000c80800150000b1000c0c24040c2041c40ca500515103901c000c440d4841c45400d0f44903520454160260345210302c0c0369140040c50302201d184009000003004e050a42e504041e015169006680b64400202049131181d04032911428864165070014800c03030307856076160224003480c09190208403000c1140000c0500070700c00d1102c01 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 586622041 1250 586620791 586620799
    0xf141e030a0b061203070f02040b0d0f2d02130509100203090303060f1f0807110a05070f06090806010b3001030618030e10021218040c0e0306010611030702 68
    0xe070340541440e2060200640382580a00c05603403000b00001e101200b918013450303024514200f0107241e6000c000203070041c0424268031415880c0c4040000d140204103092141c03046079000a00400d100503518150030200e40b84e84c000350031007200001692420000c241660319107000142d1602d03114426441d04200c0710410042900c00030600031441c10010182d03128a01c1194518141900c01051001c103120031030440f404c21401ca50300c3c0b1040e60003a5140f5901103054a412101c0c2915608028941501d04106494079000644103010035032904859102030011428408186032070000d00964420052044030500680420001c060151030060503600003040f04c1010440100c824802c58001802e21045500914201d07108105040500c0c800a0594151700c401601141d41c0d028810740102c3c00c18103500714028402910010808200901503001d152603c4c2d9051201e81c030140411205106564801d02200902c0d001c682e50f4001403035419a91540f802e40f5034030007410381062035400348480003540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 586623291 1250 586622041 586622053
    0xc090312070b070504120b040821041b1a28080a0b0a0e06090603100c0f09050d050606010f03090c0603090213050705091203040306050103080903070f141e03 69
    0x45940e40308040e003800c40c0112944030680d161141c0a480324400c52040c00b0203106400e089101040420441c1684039003d02c0c002890700002808082900c061641c44d0718029410005000a002d42154000b950101ca80b140c10185414154091f03080030328698407a45e0100c0005480d100000100d052045143c620320542c130f0040354805014105100803103100000a107010f8412900f0b260020b180d00c100d0301e07518003602c09500d030801804245400202003907018031601c0144041a0310780c1c4101d01c64031a1642d80d81c01f050702003a0004200c0c5040398002c501c1110f4404820001c50301c04601680c0049090901204801d100b00e000d44c06000a560301403c03400e03880314000b03011130f050380042920520032030302407410f25507481d029012141c1c1680c85600040090084d4040c500b8801544d0009c01d03424411203080c603903241e036000b00381d030402d80041f500742e400402e409066003400c10040015103428258a9002810030440e0101c1c6907210103140e114102e81150700701103042e03a5007418114000501950340f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 586624541 1250 586623291 586623313
    0x206031612020913020d021c02040920030a2a081b16061503020d060204380d0f0e06041217010302040b040b06030a05060102150402010e01080c0903 65
    0x111040d094901030082124485900c1079468244215114482d0040c05604503401c41c400c03800007500114800c408040d401c20400000010001480c100040d0918015a440c2e04050b11601038900c07141148001400310350f14a00f00320110000d580c1d000501c0300c000248912101c2c4820003040200884400c2c620910603040161540580c040340300c1c1400a4800d11180102010440544180ca4981500c407010f441c1c04000124140c10011042442e0141d40d842d0030b80382c1e0002161804d0300c0000b00e40750781d0b0000d003c0090300c401300c0407031100540800e02e040c50502a40048a1070318036041c0c6103202620300240854052100d644508000000c4034010000400308003400d90340c421045d0344c10b5071484004d403180024a4890350b4622100344041c08850021f0746554240300c083c000b08901e890b0f0281c0c0340c0311b09440f60384504018500c00d02d00e45a003c0740030b0500d10006401c0061540007414020b10540803c409130340c0141c04105120300038038025031181e03141001c1d040c281c0504a48294107004001141c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 586625791 1250 586624541 586624561
    0x20d02090702190605090106060c0b040b092a0a09060803040311011e02010c09050402040803041e03050105071d0a03030c1e170909220f1502040b070b06030f06130f020603 75
    0x510510000780204501512907400356207650401e000200380d0355900bc00030380000c181641440e0000305140c111580d41c9c006550200541800740128150a110a0b038522030b50314110440f000104050602085043d080a150b103440740b0941c00094410a1415202040d80c5d104084454550301c000d4410341564042030b1000340a081c40442203000129600f02c08500c51400d4400c0b50308840e0414001d51600c3e01d441c024400404080e009241c84200150000000c0b44003070046038420f40e07083e5584808030702d4210000303240c482c6032030903540182c100b0710060000942090b480d00c44941c0002c0010b0340c1d40c40c0564050340303030a6022001840c000d50f004044c03140c00f0300c0c0800ba0102d403408842070700169441c1410300d004a2100d102290700303a600341441401080c1c0031340c0003d48440c0100c41145901d04c1250048007aa03002e9442101500c1c03000650b0400e01c116000707a10380042c0200c0c00340c03240d032030702040c00ba50303561025000f0074200205815440030050b91001644084d5070260000c0e8403882d00c001c0503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 586627041 1250 586625791 586625801
    0x40807020d1211010b0105160305042409171506061c06050112090b0408070203102c03120f060a12110a0509040327050402070f05010c0309020d020907021906 69
    0x141c001c50f01c0341d0340c0542e0703808060150055000069640d42c0c1010344001c030031040d40183d44030a4040c070004000210b1004400d03000c11603072407507000705101c5000f0781c1003004101000c160b1200241c04550008000d5250380440e80b2241ea0a098804140b542c66500000e1200d119a90781c242c0b280552900d10101e58029420040440c5e1003625140000600b24860714251808288010079030501480001c00061140c00a020300c980090211039029101e03a141c45c1c220b420941c0781819641c0707000840110790b80342c0a5003005440f40000610b0807c4401400d40018031006000700341c2220162001a81503102d28031854000c1c005483d41074203401141c1000a100040a8196406080d6010001c40c850509000d13040c019640760b40d4545060000d0b0605225000c1710340d04c50b4901150802c0f0010300342d990750015003034241c0245540400034400345000c500b100c8520701d107501450300f401001c01c090390741c2e80189000290191070740c5e80543d40e10031049092048683c2541207030118842e160341444070a5000d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 586628291 1250 586627041 586627073
    0xf19031d0d0221070f03031e050402090a02040e070e0622091505011403060a031a0a2418060801020a080f131104020d060b04121a100e040807020d 64
    0xc2c1c42e10314940f041400300806110410000d08401040710100081c4c2221300c0e00440c40c080d240010341c0e54801c42c5d640c4213260024003e40c5109449409200039860859065504110321070002c62034189082d010710980c0d280200068280029440e40c14103545030b003030450382109400b5040c00450001c1800c2d00203441641e001e89901c43d4542422200d00c900e02007245419100141c44142c280403985501348142d600c018022a0031490114000000445422800094010001001e052490502c1201c011100c1e03880c010b004028046010850b018004d0b624031091350721440fa0001c0c2d484a00218401418087d4003200c481d40c0300050501407140e1000c01240070f184580441682d6442d5a44c0440c81f0b2081003002a110000f111544c007030b06d10781a03000300201d196810000c81c50664a80e40c3d100142c00c158031001d43d01e014900c41108000030007004c048194007a030030b042c815042182d94600c0c20000380c010300504110100203c0c0a2042d00c0098603181c40e401004001000031920701141d0030004107503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 586629541 1250 586628291 586628293
    0xe070801330509040206031806070f03050709050a05010507020301090b0c1b010b03062413050a0c02060108061b0d06030c0f08062a04091503170f19031d0d02 69
    0x1540da407445804210800c200c84005150003010303242d90702081440c4d440031b007030350080d03184032001c80042160a0041c544204110b07144c2d541e2542080002805076140102003400300500c3e40f60a010b213a68500804003039a40c00e10b0b0003601c031394082c400310780100392880d406022410560200310703000f0405001003410309170741c040d807040080b080c0c44070f07900344d607003000f0306540c99044080014031002094400740303201180d82c201b80c1440c0340020301140b4a400d01c8910b004607141c40d07c0800a040d901400740310540740451009010541c501980d154403103d02506c0f0204400c1066200c140326144401560b1178001407000811125503a8600303080c43c40380611454014010301000042d07245c10209100c0d205083c071740c030022440261010400ba01c80b04002032650445024000410389622074440c09141c419403440b8490070504504110b005041000d0312090450300030407498564940301c0d405c1c0c41450309030080d0200d00400d8008160090200d0900b803502d501a8149440c40009000594817042d00c1690 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 586630791 1250 586629541 586629611
    0x51b03090a05240708040f0605150103051005150c010b100c152a02210304020f0402030417090f09042406150503060a0b0403050604120f0c03030e070801 67
    0xc441000b0040403000405454504000003042c150180c03001650040c4202d030b40f03100307d10066541100f100c6054680c00401003c1d036050602c2540c2510a00303401104400150210515000000b85d0340701e102700241c0c0501c3e030081040d481c004800d40041c050007000a245414420083e48014100d2102000030b4a100d80780820070610782d06da40c403541001c02210312403008140d0225000d10b5245c0b180c8407002c000c511448041c102d0042411b094039403010140c0c03049660300d00f024010000020301201000744150b1040050000160880c1400d5680302d0001c42110789800d0f50000244801440c090440d40008901041004010ba9075a0426080071840d0740c10b000a4030802d01d50003220060700400054045004001d2003403030090018642c07180f4000e1801884645900742903c0b40d411a9100321078961207403003400100100584650207828084c0b0380210903600c940002040791501c0c1c88041c050641d00e0032910003908050203210040c1c0703d0980244009105180b40f60141c3e81c0d00d09c10311990b5000c00b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 586632041 1250 586630791 586630813
    0x80a2108010f03030c0c0e13150221090102040801050c21011a0d060b0705010c021b01050304081b06160905030a02130c05071e0c0902070510051b03090a05 68
    0x61204981681c0200c0e900c40b4246045a44c10b03100400d00410a840c4a5065440000c031802d141810300c0c4903048040310000d602c1894a4066220004042911070690050040340983c0110400002da02e11900a04204540b00d4120160081c8515003082000313500340310070480142801801001561803481d8036212000b50202c210520440a00801403c2d8a0031858101400786d520081d02845549040000b041d6075035604a600b198008142100c0036511104003288907a0144028030300c0400001819400c19810000240644030003800108080004680100068800f591400c3e01d6541c1c04100c41007030805440b00c000f805101010000046c1844101242078140407540e42c0f05607a024000c950000c1111042201402c80701c903503c801c000050050b0000700d010300181d0146803440319103640580e5075505040b0004122900407101070f0740104a50400164002280200c1c020305281c0083c85d81c036068100200c500d844030301c10501c0c003004001d0080031800460310503599403003482220318980745 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 586633291 1250 586632041 586632047
    0x111002040612051003020909011d0c03011401081f020409090b0f01090b010206060f0d05120d0b0405091902061e04091a0913030509060304110a080c060904090804080a21 74
    0x3044a111034000c001110410050812460a2340c00024070300001c1100d081400840303410a251103910001c0c1d50108041c48107a042c01c0c40f07121781200c484100d0010135810000020707550700a5080c0c0a08107074003243c6007034204007154160380141410b0842840ba0307030328600703114102580944001c0d00f00386000f4000200140a44034058061206801625042e9105010403000d82001903119030400c0064082100081d000d00900a407000f588840c103860300c1805403020f044900d07200110703010341d00d17280134404d15000c0007840c13030004842c4040300008100903101140c424003480300584020700c1303040400e01d414924007000d403041c0c401d14007040010f0480000082e41d098100e000ba15002090b072004540c0880426070341c100c1050281c2046440c1601020118005034800c07502520124681e403101203103072134064000380017842c2c10700c014402e11a040b00011024030424224622455881040d40d041011610540c2d005284080c10380c0c00119a41c08c00d1524410380c18030b480f003c0e800300d1804486240c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 586634541 1250 586633291 586633301
    0x15061202010905040b01270905012d1a0a030f0501080a140106060504051203070f030e0414010b0a030b010e040e030705061305030301060e0d0b09071a12070f111002040612 75
    0x170142e48201000b081c103603107442000e425400d2100c0301d2110882c0486c01041d9801590b00801440b0084910074a0540c903801081c81703141c0c0100e00ea0906507008200c3c000d0208801c000030003240350207940d54030300e29905034018602c0b110184481820f01000003080d00b0081809440350b8014000d180ba500017031285076080324414015540851000d0005010a04020012007000703440d25044901d001c2d85503d4035804000055411030019040d03460b580407a0401e80140155040b0040303c402155040c0380040a02c0e024191100c401c05a0f10a28000240e21814410100200280040101e152003040c03098903a40b080c84259030b940320320004aa5168925654442407540000246043d039090220031106c0c071701c0318a0b926622206a40d082000300314000491401380b0380c0003004041031450414100005130034101100c3c0c1034401404000080c0e8220b8144550006a9140c40703044600b0f4100e094400041c0041210854807402a0381114103441c1d60050050302c00c01d0b102c80102e510301031000000c0d59 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 586635791 1250 586634541 586634561
    0x1c02010e030a0c031206141503070804020111070b0f040602250501260a06090605120a06051b0a020705090a020415030c11030a030b0906030a0f0f1506120201090504 72
    0x29000b00105801c103440340ca0031443c2c4134403924080f010b4071207244e4031400341da0342a00034403250b16011516400501c0d1038030342110103000512115080d40b6000380c0c007815030140240042e05000d001c0e2800b203143d85041c80040c014001e000041c64031400710080b164059002405004003500c1184c0350300420f0301c0d1984c02c2d4151001618194400142801c00444a000484c5c2010b56011031001805581c0800c10309044e108101c4690006801460881441c040c1d480070780c0070703a0240f0401048000b04a00101d007104880da080200030803151561003030742602484103410032020b40c9003ca0795502d0a603000c18000100c800481d15001c03940c0b41c4941c503c04a10940c03003031100c40c0900750010050301c1d0082e00b0240b1940d40a00700844180804d84500341141d024210341303c00241d54001c0c0c0b004034038220344000d8114900350014030704c401d295911000344d140340c0030004c1c2400e60700800745401c210107101101c44c0c40070310f182d0502c12940c0c1c03181d609180308072210b4101d001c5150450f01168030305051003041005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 586637041 1250 586635791 586635793
    0x1230f0a11060a0e0304090c0219060e0709060f0909020a03050d0507050c0109050a090b150c07091805060103080c010b030a03031b0807080c180915150304050606060c10050103051c02010e 82
    0x1191809510701c004100c0792a021095010305c080c244042b00d290100c489060340a00d1000c1459070081d9851821b280a54001e1a90366107091001d11414084201803001d94140030000100c1128900014610b403030103500003005c0b0310405154200d0301da4048050b00d00d0f240325100f01c650040c04e050056403034610314001c42d0307004844414200710085071074110410101025001c0f0641e894200c000c10210380c400b0440202d6070b8401c0703170104042d0405106221000700380c88040c2501c0451a0740d040e49584040c80040d003448004204034480407420341c4200c162150080c115040e6019031314000c3c004d0021001c4440b003c0c82e840000302c0034a13005030001480350946503107800042d683c4203009021500141e250f502d0203050540328911a441e03900d0410700804603070041d406c1c80a007030020450a84840042021400070510a110000c0c500040c4550015070445e03180b03481b0176070109820301e41105d11150060302c50401c2c00001c144a80402c2c0615000440c02044c0803420009600341d007a03030003e501210075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 586638291 1250 586637041 586637047
    0x604030e0105090d0209070306080706090b04031115040e0601173d03060608010506150702010e0609060d05090d1d0607020a15030b030d0e01230f0a11060a0e03 70
    0x181d0321400c000c0c24840c1e40141596800040c1c0d4021400609041f40c03d4000b20b947c841041c441250204040d00c020411071a250031080e0900100100c80d004a01c00100130013134140ca890b1184e9103003003001c4402070390501038540703880c2d8071000b03181c00900a9031440e010074602c000e1000e00180340010a0702c1210001d0a2a00c15500d0780b042c1d00c000b84240e04144074880900300f0707890800b4580c0041c0d000450240502280c2c5a0602c00c00e1400c44601500c01c80c81202c00442c031103500c801c40402d6132451502401d01d800e0a20040000c43d04600c00d203119180e11902c00500824030518a901c10b07030080903d02c4c05c840b548000502c090b41c01e08820b03049600c0f40c10111300501517501c1c210740180305140c8042d0031450011b60340c0264014440350b00d0450008240c65801c1114141803c010103a0482aa490301c82d604100d40d4001801c0100585480c4080e03138101210014075118603400c440329a1410141d4582e1003000c40340003841c1000c1e101001a8030301480010413800002802900000301c070b402c4c0a546 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 586639541 1250 586638291 586638317
    0x21e1e2109030405041d0d0e150c1e03070308060603060f0f03030d060f14010215011203030b03120702150301030503040e0a06050301060b0a02010e0f030307050904061223060403 78
    0x1041000201181d01030b200c20403000c241a03c950140c40a00d0400094980761200045021030070110040208400c0001800c40300010384d0300d903d2110071080340c2c0a29141d503085044415403d141d0782c0c980601d10114400000c0c0c0040318000b00420700c040c06075846c0d20007510346c1e00420029200c2a04d0240d400049100050810b2030700780c0c00d5140e039600003800c4a04d011003031406403040d0340040c0e010410b00300884008000080840030140c0c05268248060700c00300300c1d51700c1c41c60319402040c02072a0041d0b00b0004190304160003030744941c8003600005c08a81207070601072440740003075100d5a0102e028030786004400000c4400b00003a24140c0f90700501840c18103040604d14901c05030020000a005174440030009107d890030f2141074041c0c00203620095a60044000103829a8080003112115902c6400c40f04003540010041d60341140c0240b030701d150b841c00300d40006400fa101d55004ad004d0001c80700300500400008045420b1502e0515044000b5291081507050315248100d401401040f142c0403104 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 586640791 1250 586639541 586639597
    0x4081b21030a05330a03200909150a1e151e050a030809061b06040b1311060901050705100c020f0a0b01030f0c0b0d140603121903021e1e 60
    0x1101c4c4002a209449141d52601c070328401105241e13090b0071450b14508172a0f80d9040403202c1e1135002d01c0b01c07402454601641c10318100d85650042c21210515566408540788441070991401d854100120a001c1112a80e0032800008110301c030328007000c4806122640085505400401250310003070515140e81d2440d224a0360070b0340310100c140c0d401001080b41c500b000045503001c1c1c0c54007851900074441c0385014030380300643c21006042410308079102249a400a020340313a412110310000e903481d031b8884800074010785180c02541001051401030b0f00784400c60150652203c0d215032003650031541c4065500074455151405e416014090f0340c001001440854443d1100305081845558100810b41c0d80d01005200b9400c6507608805050701c804021b10125280442c1540140d0110080d000048002603401114840c10440c3d6000032381044107800d40074041c0d410303100003024010040100c1c0a0030780142103154042540182111408084049604602c5041c0d03468440b940640c55049010500302c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 586642041 1250 586640791 586640881
    0x816090b0d080403061407030203060f010c1502070303090c0509190b060412050d0e0a21020d06050c0a08100b0406030b0d050706090305010e0604081b21030a05 70
    0x481d00500c0c4540c07990001408000280011402a100040d00b40c0340b01d945540f25140107044801054018014400c0319030719250200502ca00900344401c00096526061458020305c419280c0e1407403001c15000241038164014008130b500c40c8100d5042c181e140c1d0708000c800401501c7e001c0405400310b501600400080d404202e40240082c005800e140e0384e0b440f04181c84401d9070045549811080d4090043d54202a911050301c0d4111401321600d402c1041602c1070f80454018403e10311020300b000d0080d5140c42e100c40b6040c1d5000a024041498804504a1180d02429900d800500c034000080c100c4080030b504034055030303e4401c007149002e180c005c0407800307000ba4040269104030400381403800558100f2030352008010607190050060b1460524908684140d0840359460b003005041000041100080720600e90b59007a104500210310310003113241905100000b034009070055011207440e40c61202842c03081468000c1400640d40b02c529801c8180383c01a0813188002d10204250324002100d224 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 586643291 1250 586642041 586642061
    0x703111603330209130605010e0d1509030e120f1e030c1615020102040b04091104080303090102070b180619181209080303040b0f04080f03040501060f081609 69
    0x859501804898404a40c0d000186000b0a03029400280c034a040c0c00c0c4000c0c030f0a41c000207440204811450000040c2030001007149007441464682101030401100d0034510500810000742000780118a24014007091501c07559188500185034800f135000f840080c141a01582c030002402c80c60718806500503842000140e80e4038240800e00850314240002c001d0850303030642040384079158a280416418009101641320021a40104014004a0065004c54045481d1486e0000320401c42c1400403107a80116002078015010000c00d00c6858101500540040c2c0c1c001c80076443c254071042d1840c0c403100c60300003862865811040005100304403808400103c02400d00d80841d0002c640b02060b190841868401c8400701654040c0309155075001b11100080e0082c9001146181840c0d00c900d0007031200200554040d09860000034100150070040d9903052001007100354881c04c2c2407408034040d010078041d0130008401013900140c024000910010001604000c2d5180282402c00709405000e1300c00d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 586644541 1250 586643291 586643333
    0x81b0102070e1b090d0b0703051f0f0b07051f2909061302041706040510200d0b0405010b0306041518020304021801030b091603081207030f02040b0703111603 69
    0x20007004200e88000300d0381f1407591a60002080c0c0340084551102d00d600c0c54140a140800010600842608030702e58410b4a001004013501c400a40c03400310700d13044ac10710303240f4200c070300c10020761420205c030380c00420484000001c1c10b1512011240c010380e024118180a0f41c1c45150f02011440c079003452902080c10410303801004d803030140c89010040242212048441260b0f2180d401c100a12905021501252421500903c01c0004008042c0c1c0b46401090a080001a00149500c04185660f22012110002410901c81503a659801c00d0b01c5400482c0d4590160382000d145041d25648803082c00d040d98640101c0d200e0000138090004003c0d040107000300d802c136001003a0000803098a480840c020740c4a42140c0d000e41c07600340701c0700c0e04001c842d00c021711010a5442c4144006500b202c2a100d6600040c4030010382c940e04e40c00d040703010300300100280c2001c910009001c0f51070044c0c00000d048250003030302c0e0300582140009c900c1d66541100b51400e80410000181400014030503039080200c07880c030107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 586645791 1250 586644541 586644559
    0x305070c051c170c060106050a170f09010f0b03060a02070609051c09060c0807030f021501230303070b01120206190305071106101806081b0102070e1b09 67
    0x20012030303884000301a450180c0c90356800c2d00801c20618041002c940280203001c103042140c4021419505e14060041a01b840004500b00f0070942c86810b0210440701c9480050036903040003010741444a4054a030782541354240b01400d9400c201500807004180c802500401140d41c900c6110b00083d0044441107400a0f10307414100d002c141c08120403401090000014988503001c104050609042e42d4004030606c800e40d811800410120002c0d00c140581500300410080300680c41207041000c078090f40c003c07444c00301d00046410f4810b0001c191700e180c2401035501c4030f080d40c5020135999004801c4024500c1980740014007034004041203034809148084d09170390030101350a0610b860082c0454031500040d5403203041001007a404168490111800360290005041c699001180c058080c00342d41003208010741140032000481d400340004111003410754906098040c3c21a070098400160507005100b064004240704403540d413100d020300010880e50a03224541004000f07107801c0440c4103907008600f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 586647041 1250 586645791 586645799
    0x51b03100203240306010806190b030a0c0312020c1302070c050a14040510030f0303050925030614130f03030603020a0806091509070905130f1a0c07020d0305070c 71
    0x500203035010fa000c4a2824150309030500e0341c503103241c0060314030720301c60390000004114941000c5001a081000c5000e00c1101046c1e00b881100904200b59013550544900800341050000f03c20081c402d60b071040200e003405c8001902e0403640d070520614180e500c000418080349a00c2c90079030080c030000348070b1005150780707039580d6001980403001a0702000703851740003c0d10664540b8044c858554801c4140c0000b0701801d0854954000c043c003000c4000b42490f60707400210302e400c6400c001c003500440d504240201003840744d02207094021034610048030000d0410b03188120411a4242e69840380580e42c64104002d20542c0300e0501400d43c6072015414940d80e4140840135032680020040030780310346801000182440da0441d0701d03041800e0420b0611441034000e00201807800b0982904448290201007207030b40703642480d21800103030014001e011001d03840c1c41000708903090050a500e481d8000c2da4441a82c0e8911900483c0e11404100030341c00001014501e0001c0c0c0200050b083e4180504c4550000e6620703 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 586648291 1250 586647041 586647073
    0x50f030f0102040b0705120703080606071a0c1c090f03120204050604030807020909010b010e30160608060a0611030714061009060803030105060f0d150e13051b03 71
    0x10b41c001040b000710006000052100407c0040154004840b045241c0203041d1030003040308001400880c8120000140702043c40850f120081c110803070030060380710506002d04001c2581d4480c407416290502981d0035020a5100c3d849001e900c19082a01159080f03100d03a011a4001004000301d040103a003071101041d00c0c0c80701b101400145120b0f01580b5276500ca50300400c50500402400881240e0410001c0360340e59074000c00c8041704400a85003540c0c251071903403048810010302d03036000751096044212200900f00001d510704525004450300348006884903411121408112400303a00110580c20030812503108002120003034000d40140c81c01d222040d41c07080f40c00ea210784c406404950105003446406580c030f10703040008148000e03003040054904030b0341c50380b03038041480f8043c4243c9000ca12107101e09108011100d003500c5d104c0c0200000d000e0005e9209294810340604201c82701400c3c0014a00b080e04014001441d4000c002040c401940c0920404a039031503c0701e0b550540a140c0d0288210b143c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 586649541 1250 586648291 586648297
    0x912030207030c0e100308130801050a140601050c15061503070903030306060e0d0b070311070606080d050901121119030f0b1014030c09120a03030b040510050f030f0102 74
    0x1110358003400d4101d00c1c50030f01c108080d85a0300040510201c1c00140302d40c0ca0608180704007101d600000a60712491040c14011070340241d41d100da0905c0d401d01d82000038000e1141c1c003400c0005035000305080203440312001181d0302e0007800640034280c2d00414648140c4540e2082460340844000d000009514401c84440100d40040d58a040800c259160234410550580500c0001c1d1510389044503402c1c00c01c00010b88003251030180581010400e40c08141c100d4400d82014080490039580c07503503600c0440c0351502c010045407140d030f01c0328000c59904619040c0300e90102ca0300120140d450820002c12901e0000081c10a14950403400340304024500b04e00c139104c000100d88141503100010f40c8002c0d04202c0042e51401022144180c9000c080e06050319001500c0966071280b131008161207a982c50f5440200303225595240da2b00c039110840e1280300101c005008130306103100f9542031002d65000818001500c00558813004c0303070076134440c0600240c280515410307641c0c03400900702c51801e4241d81034103003240c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 586650791 1250 586649541 586649543
    0x70507120303020a0f0815060705010e0f0a060c020c06120a09150b0a080303010e0708090102160b011409090c132901140f0921060115030e0705031c0912 67
    0xa80105138014002d40084415003000c009003001c6a6174540750b00740004102038285183d10405011a40340e050110075448100030480d824115003440d04070300ca0482d520700465104075021400c0c05201404207101180e0880051070143c074032400d08080980c4001e042000034070319605107541d88140008100b114444011a0b0030703103000016a201c241c0140711806800d034000780c480394400c100400982d8072405d021607000003d032400b030160384c0795182004c0c00392154204424040110400c1c1100703004003d940d1174129443c05017000c1524500c078003030026100c004c8820f41c1464120710140d82e5a4100f640d28200c210410540000c0c22443d0700039244440343c01690080c48412842101c0201940c010281e11800307401003011509000700110611072510541141c40c0c090361401803d54640608061075107a0041d44100340e40700c0d50303102c1116860f4440010b0100000038240460f09031104000f09000041d12005806440042c0d407030612803050310761520b941f204000016200241422412810b1b0441e2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 586652041 1250 586650791 586650797
    0xf280f1a220809210a060f0c021b01030203090c04050108010f0c050316030b0d2a0611030403061515030c200607080c0c010213050a0f0308040b0705071203 68
    0xd082035854595400d01000740c018010848841007004644440103440c8141801c41d50b8400600411654103007800c4440c440703460a10030541a00c3c01c02c0450b4002c17241607498032800f0000407801c144121380c0c1d1000e18000f0f20f540943d211580c829540301c1d400556110901740100c4201d0504100440d046070000d0f07001c0d00300e41e5502c03010581003046030b00404074855181d10700141542401606201c6083d203440810303040c103640d40040349058840c0301c03c9040068008a4100400358121031945034031045007203001c00b01085650100300139010b0003103501002480402907042604555484005106070f6540d01103034a00e003180012601d105054510105600ba64040340c00008988003404061a2103109400841105d0340d80c45054000114150300801d10300d880222a219401810414404c0340d01e10303e03041d400010000b182a011145c64400c607001030310010f840d00e075501007018500f1082d000c0202001070810080245001680c003401d1200c0c0110b06844d029235880720185500c081541046000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 586653291 1250 586652041 586652093
    0x1801060b0c012a080f0901060b070b0601030501270e0c0307030c08160515211005030709050906160207081501091803050a0c061d07080f280f 62
    0x82d507000c143c002c0c19200181c400c407220048042c0d0300504603513002050501d203003280c84001030241c0302c04d400c010300815101b08469034030201410041c44041c0106c505501007400c000000030703200000c00b1004a0588000c03000302e00c1d0b00c0001c4141c0007a25401185501d0351003443e50819159a0078001d0070000c41c420071f03000d004146440d174a2400e14020f4801807001d1100c3c1c5e88100603d4030703041503e00304901c65500080c1d588140c090b40511034500095040e5600c0c2c0c0c410304008440030318040b62021f035a8210101e034142580e0b0f510900a503002114034034035640103280820607804004420640e000b02c180103070303400d01307841d20025850001442e0400c00320301207040040240080c14890b10080d00f001e68110007500d000c603103001c0d1541c41043c1c48401008502e110942c14812179600a80c400d10000c80311506034846541004d40c1c2e01c1e00c5008100007070061400d0200c10a07400100e805c0300389107400035a12070b0031280c0e200e0060004010020740c1d00c0180307100710500040f43c03001440c0d43c00c4070000444a07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 586654541 1250 586653291 586653311
    0x1050901030e160e0a09080a210504060b0301140c090d050a05010f020d050112020a05100306080601260a05070e07090b0a18050a0605090607050703020a03060504030e181801060b0c01 80
    0x20349001e01178000002107203014825030104900104591215006007480301e02c80581e0032000d030f03014010000c0b038115540f80005020421045402450609004034020311031886078010501c2a03a500b030360783c00400038040040340403504100c98512085c074020310030703140c002d80c10341c9401b42521425000c040c0e01980c001a485104190303031140901401060410354544d030900d90100380c20f004603000d428480c100b001c64000810344242c10a101804400e0142e401c2c0b0f50352107210722000481d00134100e01c140ca035502d503d09410360006500364015006001044030514100e6645182074003d82154101700414002203800000e070390082580743c00342d44d030300d140200c040720154004da103c0d500054414030381d0a40400a0541c031100340c0b01c500300c044034001e0340c44190f484c103d0b140603c283d00c025040450a41d0000501c0f100e035010790302c1140240c44005c3e00200000801c060030900700c110100c801e1803040400e1600d20018483d4001036041000010f1550310b50001800b10b41106499211360703912418404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 586655791 1250 586654541 586654559
    0x603061d0a11031905131212020c0a03030203040b13020d110d020d0b1e0c040506030921040914061e030a020901080705130606020c060c0a0f081207020703050c01050901030e16 77
    0xf0b61110202c19010006c0040340e95210300b421107907240c60100140c0012640d00c0c4619581240e40c40c2c203540045404001c0149009000b9410466050320201d403440e0003d28000c0480f074000340c5603640141500040b05080e038a09419000220805422100c2c4941000040e11045030451a484c05101c4462035454100c8040c0d0880a00411612407141c0c01c0d0f0a000d00010890141c809498003210100d44a64500c01480e103498140c81d2010411103459a8100c3d40a04250003842030ba07907442014020082151020851800c0a5940760741260482c02d150125a0b9200c0c9207010801d070060607211106126000501420800e03041032031160080c21007000145441c046210848403841c40600c072192600401070740341c80c0c0642505005400009039130103152000e200c8142019480294180002903500744003a0755003142100245501c6d0010104801c0d500028140d021071754000700a1441c070700c0110044030301d904103407240c03814141c03103803400d400b482c0c0107201c0e0107140e0340800030b2a00018603144001c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 586657041 1250 586655791 586655801
    0x60e010302012a0f0c09231b090406090203090d030c08060108070c150b3303100e0702010c0e0405091b0a050604032012060103020d03091e03020405010603061d0a110319 74
    0xc80c15447d4004900502ca000c800c102641c0300100d084050b10041561004014034411000e10560080c98802e01203a0701c24641d000e10300032103030030003283c80001c042c0506504440405440d6800b00d140c0c10b000554944c400c2d1780072940b002c007a02e0000f103615030a944074400407020200c000714190303c81e440b8102d103003440480d0204140000314542c0c1c01004000c4501d4860341041a0300d6000c8200200050000e2a01c8130030000400402108080340d10b00620002c0c001c0c407011145000080e41d40c041c00d8180d141078000d40303001d940d440010b0505031407641070700042c03000f014048030381160119034001101e50300c2d903024000440c0280021000044401c00b07501e02d0516540c046403080301c5100c801d031054600051060305490b4103031000020503510307081c2039030742d410350707500004205500c6600d045080d0900c8020104485c8292803e02c01641c80d440280d00340c07000c5008140b10320b403000e8041c0c20340c154a12003541c1c0102c0030140006907404a03074161030a40d4022201004520003140103281450018821 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 586658291 1250 586657041 586657061
    0x120708070914090a0b0d050601030b0f1905090c04060602010506090c07030f0e0d0209090307060c05090102030f0d0905010207081902030306360712060e010302012a0f0c09 75
    0x8148002410020030802d00d450341c07506240038003220303c0025001d03200d40d440f43ca04540010400d890031080c92820954606090108890348034007440032800003074414038a24024003407032207a0007002c038443da00c10000303110040070f40c1050720400441520a8464bc0701c0e19011f09034590010a651420a06002c4645806481001d02200401419005c00c0d400038032441e102d112858074400880101e00018040b01904102a620581c40014002c008400000170240b0380d108001c00d109400b65110203031241e0013122503e03805608108045244034258400070884c803020f1110003d401d2005448403030072600310b000c0446920034000782d41080d0003203018603481c0004861006503c0e518040b00070511404000c2c00c1240c0700030750796103001222420380e2507201360f54031002080542480e002c17034001c0c00b00c0380b4068060002460150007207074103044108114140c94043c1c64117544a6200c00c120011101201240400080c164414500041c040d5038614034080c0186101103806050902c0c5008550020b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 586659541 1250 586658291 586658297
    0x6050a091212050a032009100c0b0712020c060106090602070b0712080919200102072402160f1d0402090a020d0209040e06040b0112200d0812070807 65
    0x240c0d000002d94058030245003000d1450a540c65a8440741d0560182c80c0417409900c103020361100124500c025803025203504034007100c82110007044010151025154450040d00c664078020004401c54001d45681d01e04804400005240000c480f21560900200b80c200d40000b9401b01c000300b02e816130400042028240e8802c03254a08ad84559070780010f03201c2c481804080c004064002140d4010a00550604440380140711411414514000c0383e04201582d0101c03020003494820f82c01548001071030002d0351601c039043c1d541c82040042180c5c08a1082d0038600441c804d00c411030442d052070805001c0100019900a0340c2a41004032080031283d01303803c2d07c0744801e501c8040001603900c0917269904190382c01301c010307900d0b060313007803104042e02c103505a464215003401084803d40030001001c501c154019001c00e000f698031000304100c00000b145001d80740e10840c0022110300900d030302080b401c03a10010005080440f05541d110719035041801c0d07405041c06000c003000f0300d064103e0701d441d600c00494a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 586660791 1250 586659541 586659569
    0x10212071e02101805100c11010603020102060c1810020321071e0201020c0a03170108030705100f180501090b0a02040501021002092b030e0d0201080105120a060606050a09 75
    0x14002c2d0758070040c04050844940f100c13007080c445040035111008407608107040e511008401408000030b8881548500001814001c1819692006100f15016a58140c0c00f41005e0746075000c041002d030304940071a410401110051003800e0b90f0360784114040300e40c1c0e900616201c298a1190310444803140510680182600e03007044002c030f61040c0e0100003090040c00c0d040d00b42440312812802030041400c115924440d0085100a058000e8071507902260046101103c0340c0c1c8901a66881c0e00a100d0000c056038080c010103424180f4a400058030602514000610024842c1c1181d90161840307401b6203807a50b44035440b03420310042c40f0900794130204112080d40f4041c68440000c0d55215034840c1c100c4100d40c0030482080c50342e1805003a0041401401c0c1d0300d508141c0c156010b400e12080c031501200415051110388c542420140b11400d4556016114081140e1901003800680000e002d1084290b0241c55000000a21140700321005004503941b4075466250100e0003400b418401d82103004001d40034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 586662041 1250 586660791 586660847
    0xa02040b1332061b010c0c050c0d030c03080408070b0c0c0c0f010504060507080d0213051201050c030c0307030f050411040c090503030d021b03180f0103020c070509090f01021207 78
    0x4080780400c80344181d07042c3e03659007a50600c1d0301120440118001c110350808500c06a001d500c1450440400c1c0604103517142c16190340104a0503561450004000c40d041d410100c0c0400c1c0101d030003651190040d03680c0c91402c0070507620f1000d03480781250f00c420121800b144036800d200d02040804100e150584540b42c1500c4508000303802800ba030f1181030100000041c03072504200f02031041d06d40740d13004c0c1442903444040e500a801411603941c0206800340c50031004a0030511814051103000c0c0140c030510301c0c5540ca500c1420940303640010b0800044c0354442940001a00483c85118421806a000c996220340020100010740e00710800d01030402021002c144002d43c0c01104a8806c0340c50f40d1401641c42100c1342c00d015441030a034401c0040d9000104001d50020700341e400c40743d403a460407170b15102070041c84401135007240910624070010780d1002d1b10a02c06400c0000701142c0000c4290201c2d248841c0b808101800d9a0010702d804102d00785000510689503004440c0312455078410079080062401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 586663291 1250 586662041 586662119
    0x1080309030a081606180516061b02010539070311041d06070201020309010b1516020f19080f0f060412090e0a020c060901020c0706080a02040b13 64
    0x81d000000e0060007002509558250350510021300450781700c2802d206a03e240c0261004004600c801a1000e029040c00b05840941c940c21400c1922000c1d102c118000084c044040035000100c2d9080781805000c1020564030040030046080312401c01c20b4814070010030b00070300c41404141415510305603211290510002d01d1400e050024000c05407000a920220030305400060b2885e12103880300ca020b03110074007d1942e07040d00254400d0382d2040007404000400424456001740b80c00d10700440305018002c0300d62481121344000805030008115104a941c3c00000072214140c480c5c4a581d451180707002006034001c2072000c484c2012040d809081582c000c01481c1d6120040140002e02409451711680c0000c0d0081c0b42c1c0e5000b038000882015510b141c400b140e00c00035030000181d40c0c02ca00c18180090800d4905001301d40a0591240143c40c0c2245403a5066500e504040d2000401e0f079008d01020800c07000d0103004e04440549904a80324003450503000c0c01c1038122242251001600840980e445051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 586664541 1250 586663291 586663303
    0x31501050a05160819020a0303051302010e040903031410051503072f0d05041d0709150203211017071401030b030106060e121f0504020d0b0a050f0108030903 69
    0xa442c64442031150602d00f03000306204070500b1781144e21503030101222190b40024142d03440c0d17109807010000364445000350a10303030482960080c0061444078a500103810250070100185100e0700b00810000001601c0c808465030803150249010444c450030401454407181005460051090280c40c60400010050020409800c802071140f00c102c2081c00c03010204a20340c03611240b00301030310643c1044200003007280d40548600b9103a41c110140107151b584c6080e00f1503000d514507441e011000751030030b100c40300f8801c014984001513000a00003020252400e40c80700101400d483c0c44080c030340c580005010411101034000d1a00b00d84052a0380c03d100ca800100102918030a411600c1069900001207000c8c254000c3e6403078055091500020702190800420354040070112028080c03c981c00c149140d903025641445988901c01950346544410141d10598000380007501e00c40e000c006e682c4076000704c070030140c2e40b40c4107541e0f4902c1041146a18140d52038058596040075601c3e03c41e04c40c0009517242 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 586665791 1250 586664541 586664557
    0x515180f01050f06120109060f14010c020405070908030706060312091802070f0212150a090b0610020f0703210e0d02100315090b040c0c050a0f081e031501050a05 71
    0x4440007450f410103540318401d403200c0c000384208035855503841d00c40305406000184600b9a85030b50954022840f01e0358000f007124000010382d1032112880a5408110242401400740c800380f00008402141409003400201b403c14015030001c210385285103850000c114640340010300b00101e011090002001d22040c81000b5105542c0268459049083c01c641e0f0194581d8001c0d400804100100c0f2116400300300204224440d6000040d182e84032074818094800520009050318200c00004d6814500002c0528170749940b4811200a8410407001c0d0380b07440240d0b00705031890302048000307d1000c05c102d0300c492200c03840c0d4900582100a4100405c90000b07140400034402d6441705840c40180780303e54004c60400ea481c140b0640816030b07400c1110300520014898234000c2d800d081403030340018012000740c0c05066005001780200c6003070f81c41780d00c00c12044c464200c4650804218000036541030200d01000c20341c074101c542c0e6503401d01412188901c2d02401ca1541440707024003148103595046000d5640c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 586667041 1250 586665791 586665799
    0x60103050910050703110703020a02090108010b0a030620030f16021f1a100903051b10080c1c0b031507140a0c140c090c03012402030c010515180f0105 66
    0x70fa210820203a024003000d0700150b40060b80841c7e11014103030f0004d10004800e00035601e441003641c9841c5594242d0310155002c5400ca1010072082000481d50307030001411207000e400c0c0d810470a800d2450a030040d0703c10b90703d0440400180081c0422585006400018400c043c001000c00074400c01c01042d43d80c4c0d0980c1e01006035950b50086003c0740010a40a48000700010003040c2c1c106480d02000d004030b000c0f800240e401d88100307601540118070702c02c0031001084004005c06044144071b2021103151100801c40314240105000e035194003c0c01c282606142152a44046017005035107081c0752400307240200d1044c0d04030a1605010565410102003a200342c00e0103c0180d44003801002580d900380701e100020f1051004464100701488003060303100f00d0b40c404481d050200d4450715202282c0b80401e000d9201528000c1c00c90840715049114000c02c810060300640b800c1c01c8030035440b503007169001c56a00b815181c0401844076135180080031500c0c0140d105202c0d005904041c44074292843c0140241801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 586668291 1250 586667041 586667051
    0x105030a061a0a06120605030318090c040b040b1c0207020d060b0d1b0e09120901030b010c0227070309110d05031b03040311010e0d020f041d15060103050910 69
    0x160203265040c00d40c0c0b524060528146107540b0070700180604414003040c0310091911002240c585004403c03102c0c05610409030780d10b0304541c80204815400b0103440c84d140da0204000005040c60702d0350250000701103140c820f6483d0860750b81d410000042c030043d902822441001000300681d01c444401d11240d400240004880c0c1c170010100300e20440c550009400c08490343c140c0c41181c02040000000d4460303c0021825a844182c400c40d40d4520000c6040d0b081c100502075203003294401c0d40314418450b0149007080c440c50440d00484d60742e10004c1c4000d0142040f400b0758030400401401d20039003110312031408000c50351142e210310030300c8884503000380c4c400d442602c103110601400704141c2d02002401420600349040d8201200e0741da91251000b1a118050442c03060703400c0d80102042d8842c01d2015001444503111903007000030003043c500607140e000360b6980c451486181446040300c0d001901c3c00c010220314420000d51540d03800021b00c0340741003604100800c900130030301090034001e1202c01c8001140b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 586669541 1250 586668291 586668311
    0xd060f0303080406270809030c0105030906070305102c15061e0c010c08010806060405010b0f07060e0d020120041a03152707080106020316031b08120f0105030a06 71
    0x110b1545c0c40b07207204103503801301c10005004001004002c811401c80c201d43c1445038400054034140012241091150003070000107503040e0007a00305940c45000c203012101203e0f140c00104005001004480c0c900f1004581325181034210703000704c9034112781c0cc0303800115001b09030710028071907119060400032141201e00c803009050118405403041a1411300003440b851100b0f680080c802442489603a4083c0f01c1e00b0003180d4641414480d8505032403601103103514065540050030425400900d040300e6003565900585070000090002c1c400c00c6540381d001181c0301c1c46420140500b028200c4100c0030341d20042204010086070154200328802d8600c02160700ca80d140750a0341034442000d84407603081040320300401c1d000f825583d9003d0100c9002c12030040151100301c4100c03603100e4240103030304c007581c0b04000035050311400e5040001510f00c41d04d04035144a0354400c10442100c4001c00849510002154141e01c503d0501d03155588401c0396004009150700d0030300000e40d501c0410a000d400f5030b40d1140508 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 586670791 1250 586669541 586669571
    0x209190e1209010c0515010803090120060103120c020307060e030c0f060703030b180a0b010813030c0b0c0408190507050108041101051c020c0a140c0904061a030a06020d060f0303080406 81
    0xe01c4000f140f000e06c4c440e6680d80d00c1501d072241d109596090000d140a500e0200e00710000420700b202204402c01852242e0840da5098010801c19443c002030141c1c040460300140da0401001001d0201c995a007002881804289031500d6202010144604000300503807089032605015a083d803509460080707508000b420110341e020542d030140360a500d4214080081c0140640c0001c02a100d083c3e80f001d5184e568803010b014004030300c0400900042c441030000000c10001000140c201d068842c0386841c05942c0d4486c01d01e01b042116403c40c001c092196118140441809010b0003480c080c02d003210746d0701c1c16995400040703a000c07607068103200d4046400400c9030340e9004404845410b0306000c5507140c14070580c1c19035130300402c10211085840c0300501e007505440030031070380c0311000060501c9040c0d48490303403044040e00103081105e941c9031500f50014115075080000c074041c14000e5000598601c001c8000109440c0341e0b4000c6801c8440c207000410000390b00035540f6a009030000c4000800801d640d05036 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 586672041 1250 586670791 586670803
    0x6090d021c140a030902060a0203030403080c040315050c0c0102070f0c060f0f030c03020d060b0d05010801200f070f0c0f080d050421060533010c03080703090209190e1209010c05 78
    0x107500b1200c0451341c850589e40000080d80a5400394444e1141d1740d8450045080e07911460000802030078080c102480c010f100b0303030401600180040001d900300900203440c907089070400c0006444002c00e01251038103014200e034003000503200a03d480103e11056040260402954504400c101540ca00ca01200d482c469070640c2d51050303100e641804416a16080d00c1940c0d000001070041c0c1c03d1405000045140051040c3c40092000322032054510241920b000701c0354011300301c1c083d03100c90704100b070900150300100c0b4060300c90f11038021040c0141c20911000383c489001d41112800d54881581d1452031a00701c01610201d036401140e039000d0340c0c0700c021020400c41c00e2040042c8064103050900030716911910312440991481c640b001c0e482d17902840e00002d41d007021050356002c10090340501c404079102e0394406138015824200440c1014242d40880c445140031184c000a0b002c0388141c020279000780303000b04102816204020580f41e10960705403c00351081440d00d5040c002480c500c0d4041000034414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 586673291 1250 586672041 586672043
    0x1140306090609090a06140a0f0c09050f06130303020a030f020705030714030307150b040b0a03020a0902031b03241818190602090f1c170c06090d021c140a0309 70
    0x100b800700b40441c08007e41081c4058034042d800d03e0406141922020907445507852032040396503000e120500d40414090019078240095070001d01c20825016581c01d00ea41030740045100345c1c014805c00e0100c0c10300800752440c04500004541281c0740411441d036000560100340e580c120b008420500c2240c000a01d18450b01c100108038040e40c0003c044860a1640000d100707403001d0b1000d0041c203242e001008003425072404000d520111351203007404144840c0d40550740c0b00061707448a52118000d410a03071600d40040341c00000708040140118580307810302c03000c070208160036a0900e900c00c400b00c07000030048000400c0542c541000c00e209802216080100d400c003440007915800ea40c0251b4186070300650b10070480396000700c6034110500c085052803503140c01860300c2c442074010114415910307504501214000c20881c7c000030b20040c50340d0507040c01000c4c02048540c0080c50a01e1048201174108220121040c001d02c40e60181d40c808031b90440d901000442e01c11540310703612040d2503026030082c50002c82c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 586674541 1250 586673291 586673303
    0x302070605090d180b0d0513240f020a1e1e0c0506010b09060d0b010302040504050a0b0316050f010e120706050406020c09011202130f05100501140306090609090a 71
    0x51002100c404644880705202c103650300803140303500c0000d120140313000c0c0c401e030007001034100700e40101c50805130b0040703820030441c0803600c40e040d606403607002c108480c412452001c4181e9008070044640755200f07860103500141400c4d810030842c290041c01c058038000010013100b0006007403005141c410b540300c1e58040469070201d14070300042100141030203000d54089542d489a4000810031810080a0351400d44004065900c0c000d800c1440c400034000c1d040025060603000d1002003099600c500509214001c5040c0019030452080f040501d84030324001d090b141c3d200f00000c01c0c400758a6100c61040c840e0401e0a200c0100000d07240461401915003105d580d07280201207000ca402c6034440b00034011549a07a0855202070000d404215441c403080c0b140c4001004030310205401424a0b50749020340070740d50440002d80451f900080d03810390ba01154026a550000c0505121035a049000c0190148811901a055281560100385010800b4002030312a15940d00004d11051041042000b00d44e4021 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 586675791 1250 586674541 586674551
    0x306120f01020c06090f122b05040614010b0301050d020f0901090e07090c120e01020c010e07080d0905090f040f0609060f06060509030a080a030b0a0f06020d1704110103020706 77
    0x8050300d0003034208142040c864013030100417500c000c50005552507815501030141005003402c1040521591001c21602c22980c041600c00d041604414644044400d00d001c0108952519143c6102219440e011106201440000602001d2454400d6906441d01640d004000017118000030f0b5004201082d080d500c60081000450041000d42100c0d841c0340c848030844050980340d259100680e102c0d1080d050005440025800110925810600401c448140010700e4030314202d00311829100000041a11544152410041d00104000120780c690503072070003550316410500042d1080d44003919840c0103442c0c850102d418441c00820b41c507081c40e8090390802800c0304514110000d4010745a0f06003034185040400206103024804035903424200401404100b6000d540700d000c260000c1001400b00b66850078845000d07241c00e030807080505001ca21078404076190440080c0351a840f0012a000c004c12441e00302005580d990800d60403035404003d03010006001e00c0120020700a1b0003015280074204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 586677041 1250 586675791 586675813
    0x3090501020f040501080c030f040b06062701080a14180c0a0e06040f0603021008090705100201090b061c030e01031103040605040c08010509070608040c05060a082202060f030612 78
    0xd00900484e44280c0300d00c0156a079003d4980b85501007103d01c2d10320640b8032000900050790348500981d2169009180a00b48840f100c01019081c4542e204c4500c8081411085065903030040c164690000303404906005070800580e0b04030480d04054200d01441c210f00304981c00380d00052103a1120007501812908007140c3e40c40c0d00e890314000c00e4425074022868000345a0410f5503038015013090360b8001d080c0d51400109220119246200180074017864000e04a01041c0350b603a01c1149140c4900b00c1e4004181aa11810610341c02000a020705e0b20902c00480c9804800802d242210122501420011581410040113030068540304180c2c1400c034800004020810116902c403c0c01940078541551a0702c2e00c07606160300b05c0d4400c0c1c0e4070700481e030f11a200401545115804043d405171182c41d1109080ea500c502190380ca802038a01103001c51104010040c8400743c003104000d00c4012850308504954043d00810b596201e007902c2c10f80c0c18000040010f010351030328450040ea804004044480380300341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 586678291 1250 586677041 586677067
    0x6090b161103030f0117070b0a020307110d0f240207150e0606061c020438070807031b050706081006210c021e070617100b0a0309050102 60
    0x551104004641c9020014805040000940740303d000100600b0080e43d00305407030030a0780d0060078a24001803040b4140490900030040280a14100f241c00458843d603451802315903c500c2600f204d030040040d4064140840d0580c0c0034024255003203d05411240d001c122000c0c1104003055070301c1c80c0306d400010100c2c00c00084402441345030241c083e040149103603215110b91201c030f003940e103154450024405558141c0c20040003014082004000501c1c056540c1240e4400012400442c40100310b10807000e042c150002000c17020030089100a545841d6442d43c40a510b4001d04001074100810060301305070f25440700c2d031044080c47d0000201c400f8a0b80c0c3d07000061030002d088480900d002c079401000078a181c0500300880c44a400c41003030b144641800d01c5054020007606406c0d40862243c4001e0002550241080c00340b41500314003e48a6a4100314000c0e0645c0c81d1941c111000303904a1040281441c20b202e81c54054131100240c0c95620422507200300c024050542029040354800a0f059162070a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 586679541 1250 586678291 586678321
    0x206041505130e16050a09030210020109051005010815011508150d150c030603021f031d03180d081611121006060314070c240b040b040b010c080706090b 67
    0x1290f0000c4109444005800319031030300806d000080070403030b0190180014170308501c00c07034415550352000080e11000303600c80c2c0e031610000740b0440d007400356070780f0040c003100d0070610400c540e94207601c0304284154500301020350014402500c0400700306501c0d000c118070f12680300d10484810401492401101480d05049161405204010606500e42541d00b00100d0203401040d08980c0c004015940f00981400c0c1e814151140c0346502c0101961480743c054880901c074000784400424800440d11443d411842919050402ca04140f1580d58840114001820300c400c80b403200944028005040746949030140c080358031850141d900040c8003844080c11100000d0300320800085450910001340e680000340c088603102455148003030303000270000b0038140c064000c24003d103104800d0b40032104131320010700d421005c1203450b200c03601d61030355000b0045103441d000f49600b105040300c3c01c2204030441d0f00041d01040200d1001044584041441814000b41754413224255400c00c03581d242901e001e40e90b030f0341151 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 586680791 1250 586679541 586679551
    0x3043306080606120f0a030c060f05010b07030305060307030c2711120c0304030f051b0106030605040302100b0907032c07170115091107150204140301090206041505130e 74
    0x4146035900c44139030030700080d81da100c2d082094044d007010f01c21364034229944203c0c01d2003910055203400381240008020b2082030300810010003007503160034407450010103480b0301400c0d107880380d03004203428404120b07400e51050413590740080059110180072900c012490071100e018011a00d032a100d04405e42c100c90023006c1150880018010301d035142d42c0102c01e40d00007500c000d80040d08040840c020240a42c0041041c1c206031400411030700c0445070080d003504d6080e0012115245c4a800f8842059010801d60401502ca1481400031014890128018038030041c082400c15071103099029030714600c000d1200b0514007101000b01034661503491165100058803031850503000049041c40b2800c010b101d482851030408820042c03840c03400314044050644103401510000e8201310800c001103132510145d8003650a00005601c83d46400080c40381c15291083c002e01a0b410300315480300685e03a090440d4143c44c4c00070f003203042d84040c2880c1100e1a0094a00c40340c241003242c200400c42c1c07907940d09064450 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 586682041 1250 586680791 586680799
    0x120d0605030105271513060b010507111309021c05070617040f03050904020a12061508041514070306050f040c08040213020c010c1805010503043306080606 68
    0x1503540d440605003203400032256070240c154540790002c80460303400d610742c2103d070304903048822400c58500c0500200c14240c400050b40a0454901020484940a958017041003400c0c294107000c039036180c0c8141d0080c0d002d40b1070303c00d4015040030541480507602c0b0b40740d45d54004c3c1c4200e1104d0500700b070010400c8001c10003540c01c0d2140c9000002c102d8400d00c0703458004540d41c1042400360f1199900c4140001d01c04c032086050000501c00203e0944031480503000304031065413400e0558589003818802c40360140c003c607440b600d40d88003c003c01a003004c0c0c4035402c02c0d4130039442c83c07220402c034600000031b1464000681c0e61140c0c00047c049a1581508202d09480e400c0b1400746038104581d00300001c030354211100d4000320f1903200016001d0710b807041241810206050026103006048018982100c00d0315454401007040d04810a020039420345c1d12a0203003900782411071031030801c1d895a440c22018030f0401c2c2c01c1034207000002c40b42c0c0d0041d42050f0300c00c4a1011014000c0d0b58440984984444045844a0003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 586683291 1250 586682041 586682051
    0xc0a0807020306130c120512070f06113606041e09060e070503270d02060a05100b0711060a03051e0402010806040e0a020d031e030203070806060a030b03120d 69
    0x405400d04144c5440c0310740c0007116501091030034a045440c4090345a00350707460302a60080e41200c4007000000c0002178411102c5001c0d5039200c0ca400401c0320030311034070503012250520041d07104500d11000d9011403a07070a115548460801c0031070300c5030300110400454000340046800a0900d8a041402130101c191014124080e40c035120f0740307001c460507441540c030352000010102d00000d014800031038010452024003401507030603070200c010a41100850f14456405841d818080799414461650000320600051055040c41101520104418001c0d410030080004200081110000451041800180c81c49032100f03079030a8046c004080c104c5100288004140408200c0141c07140520300c2554141c41d0f10145446040502c0002c0141d03111800662007800a9100543d80d80908180d0b914840d0b0b441a5030300001904880051381144806814140140140555140c100e08142c0d030206054684a4860b02d900070110040c0001d5252a5090b0140c3c400380101d043c84440200585584000b061007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 586684541 1250 586683291 586683301
    0x9050304290c07060302070203150c03090c03031207030b21030307030609020a08010605130f0b0a11070f1509170106080c0307050102190204091a15011d12030c0a0807020306 76
    0x859102e440d0380b00a1030b820203041408500c0c001c2e80506803840c009412220b02c4042d00d040401514001e4480303420001d000f004015019104006080003510701b5400346003003110070707414140e12000c007501d003000785907c03801141044e480314440115484004861240d011130000381d4192681c1c001c0c0e519400080c1000c40120b0f01c4240b5000311042c40345280e41d824000da180400c1220b07135800019404a02001d00c00c4001441e000700801d07500030340784001d002941c8030003100e0041c01107640c0360303105281e540041c40100103246a480200c01250018a1a002984450740085501c1c1d03519801501d007421410302c45120301c01e41540840181e9100404a0b142030b54800100360b50f9011511035140180e01c54500d01c1b841907440039155148030700c090700214420150359122200000f8018030501612412401c102d4aa80105020003060b6000c0c200250108144890b10302a40c80d45c8103154020b400f403030240c0d840d0003010000c0703e80303903000d200c00d40740040c0b2076141c41c070943da106800aa01c81c0c803a08006c02c13 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 586685791 1250 586684541 586684619
    0xd030c06140408030a0b030f0123010e100b07080702040626010204080c130603080f0307030506040b09070c030207080607021e010c020322151e0f1b0609050304 70
    0x240c091070f002011141550303580c201080c06400000286a0180502d1400914018090184045c003500031260880703c0380c90740201c03c040c0c09050f4010810f4030794007030a00001e0a012400d00090303443d411042d543d1a602c42c188840180f00303c8100a4200f454290000354043c03800008585402ca0a8000d10114100070303210303400d0b8040c0340a03100c142d400c104209000342c500049500d000d102000008640700c0d541e174840c1d10154203c2e007064003010304004208400143d00d4428150b00540445081010400040118000ea6030041c250710610241c12840e8050600030400780d0003e024840841d810703460b200c03000035102c10341190184104441ca10390700c3d55003031040c00307002c1041d43c0230303801582015180344111081c20070401503e28580400400440c800c2000b00704000144165141c05a000f40404804c5890140c20f401c00d60402c100c1da51961030a03684060341418400c1d04c55113100e1009190f090410085c91942402030030391100180c00100a160074045001031503012560413041c9101000803 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 586687041 1250 586685791 586685831
    0x4171303110d051b1503010e010e070c05071503090c03060e2b0f110f06011508070230070f0b011a0f03040317040c050f041109060a0e0d030c06 63
    0x8025030024042e03921402d03880c2104c001401c60050000041c507540c110000b0301540f00f030700301543c21450340300140586604041015046200d0b803415900301109a2035503501c84240d4040d14100e0011110010907552003a00030850440d002585e107080749a503803a2480042c080c120b0200c85500038220300000b4002c000d107414840d440c41905050b40c0705940d0303004980b40300f0504003080510a80104410504c14200310002c07005034510020006541040d188519034004515034400f000301c071342c0030041d00d5a808a05044a1134800d00042e0154504500d000e44540c030402c0d43d100203a101051150600c2810b1081c4103401340103545e00120350742c0301d0a035a00c0080341c00d803104038100c408204102c03400c0c0180006650182c040d1814016401002d5110030a10b003049e41c0656845242007800e201626258040d03141c8090100c3d002c1000f1000da501800503070280c0000e007803080071701090051015000f600300031404400240340200d0403009180152604143c1d800c10f850031803420340b86d0b501c250512802 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 586688291 1250 586687041 586687043
    0x60604110912030f030106180e2202010e03030703020102040905010f06080403050d0f09050f1b100507060b0a061d0301060e0f090a050d0908062d04171303110d 70
    0x5828980011401481080c90b14008450310314842003003801e00d00156440034501a04680e59425490340c0e0780c40345030b6040155a044000c0707011400c1d0078040440740c600d20610031881866815a600301c1503000603110a6196040c1039058003000425100705507040d8014425a40140020041a41c03502011960188036004560104c0d01040106010074082c601070401107461010100f55064a00599426164041000c0717a1503402000100a41c00b130500c0389039881c0c228045490110a00a00058004203100045405002000603c4800d02590b42c0021045e0300c006095070400d030b5034492000b440000c0243c4815014540910441c0503450b06000c2c460071a8008070258103a5103030050391508045001c3d080f14080d114072248040094028041440d1209060316465061440e2600791805c000e0000c10031407031003103103002c02c19030b0094101a0341c88005003104001c105565502e810048980700d240201e01c851004079084414610910b2240d00303492051307a41140f00c4040c002407002e0401d411030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 586689541 1250 586688291 586688321
    0x2151b030c031c090206040e07020f0622020d050f240721021e030709121509031b120909091709030c04021305011103040e0103030806010e21060604 65
    0x46640c0c40310540140d07070001002e143d0f0300014000502d80c00154540d2080d0703c0a00425241002c2040aa03014020701030040c0e03009001d0800742c41c212280b18020903401402e45482d040000d040d2055440b0701c91310300d407490343c40310842d404185465030036540c5084003c911009201074100240364510b48a80b014002d00841d1215a6080000441301d003035440c0060b00c020845a0034800c01c8075006003e6034040c1c5480300b43c18002c2c5c1c1c130b003810a00100700c01400e8000380c1c801c54901d025800002d1103160702d03c039140c484000019100c4500e19086a160044401555600b01580118018040c0600804c1a0361126440c0d503a00d01b03a46040c1c1c541074074050b040290160f20192190318049070008001e000c800030040c2542d156001881c000f07001c903004000120080c4035031001c1401256005008500344101d020011410a4a448806100d48005000040800880f00040340860740281144c40e03410030b005154080c01415041c024034002c058145d0541548036940c0400c400341801c0c4200300d00000581d07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 586690647 1106 586689541 586689547
    0xc120d091e11030c0904060e070e07020f070e090d11030f270a0803030c0702010306050a0306050f0a1107033e010509060c07020d030c02151b030c03 65
    0x5a05600031303030088459841075030f41c3c6807081c6d9019603c114041003a034030f040030f214100202c9600241d80c503002c0304244004507802107200c1c100c480003281140c50440c0d40300f44410f9941c1045c0c450070302c660080e078055000d0318403030086034484a02000490b0324040c0c402d20f90740d20b1031b0700c50364044062010b2625180c894050b51050b00c1d0358038000719421000103080c85c0002d0344074403010744003180c184c0300000c0070350469001c0c2d00b041c0c000b4000148502d1002e69070f400c001015040466005850440010014204a286200b606114522240102c3c02c1002e15038094543c5d0714032581003280003010300e10305001d450074000351204a10810a680a20580c4c5107881429104050103001d03c54108004000f14407600500b80c40e0501e4040f03485000401050030260b034611800030006e90040d5000000024580451000b80350111851003000701400591203c00ccc1c0320300030054407640b00d030010 = true := by decide +kernel

theorem cover : BRFrame.Cov 586510791 586690647 := by
  have h0 := BRFrame.cov_init 586510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 586510791 ≤ n) (h2 : n < 586690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
