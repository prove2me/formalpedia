-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4271
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:04:34.263227+00:00
-- url     : https://prove2.me/submissions/ecc79f9b-c11b-4898-b8e2-94a319c57f13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 767985611 ≤ n < 768165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 767986861 1250 767985611 767985619
    0xb072409030e1f020d050c15100812041d060105040504140106110d020c0d03180611010b06040e1506090607030207030b09030403020901150207091b0f030519020d0b 72
    0x191007019030101408440c0320084941e030058a0901001c40b8509a5100900016902c0304290741c03649030050000e07180020400e411148000e55415211243d420207507401030701ca07035a035032062007841d030180140716001c0001901c80381854038102e00d24100300c0a4001c0c4840c00350010000c40c0159214504850181c42c002e082071000003546600d070035621b00244143c10004489007140010100c0101c0d80e079404552030750081510505103000c106002e90041d104405210b081801c1080b180d00c1f4001002c0244002c0d100c0c07050540c8200280340c00d444c0c640d908544565001c0109200b032064140e20140c00c1141c0010400141110b2030205069100300800264414800309080c400c05500050722020340344218031940d85a1643c0704441d41c1e90141d400001c1d40300340000300510442018521030f03c46071079684121342e5040da5458007031040355004540c03803004030300641220341e0036500420329440b1444145400c00103440c011100d1800002108059030507244c00086103100709a640d00000e1180000130 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 767988111 1250 767986861 767986871
    0x42c0412050304083006010e21241b030106050315041d0c03071208040506030c0d2a08090d03020a05310b0901021207031803120210060b0724 62
    0x1100f40a19103210717a0129602d140c40780090080d500c600207100040d040600040b403c510301c17198040e90b142d298000040b59104110803c100720603889404003402038401580295800c000d2440c43c0544003180c00070030b8000042004000c1e05600c0400c0780c2c0d00c8142c6a4814154085010002e0045c007296140610700580c0c40c01c8400c440000442c807656000c0c000c4048481d2590344031000a11101703141000382482c1020b000403c07480c1041801560f0100c5c1c0f80c0380e410314007100c1c00c0c440310488424001e6140c0d0340700c04c1594880396a0501d100460150b090341400e0003507240200c034031640c0300701c0102034a08140d0041000003003140140140d6182152101044001e002001507640d040f11071000817415074040308800080014041088034180340044e8040e024402010070311981070351100c1c81c110200140300f40418565004072424502440c0b1a420925600e009004000d00e0182c0c4e00010103401c61800c1000c1240c1d0b203c910844080340da200e42400d284201c2c42c1c20f2150041c141c1c042d03070400607040c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 767989361 1250 767988111 767988157
    0xe0301180606181b030203060a09140f070318140c0d0b090d050c0307020d0c0b0c1c1701030f03110f010501181406011112042c041205030408 62
    0x542c00c0030080e10900d504820398000850036100540e10f1112601c010280d4a40d486a550740c440e40055a0064029214500a42d59410038600315040c5102c0948446511014008401d4003141540d422010601c0c06004000c0030103540c2e5a40002c2e141d0048c0b4680e00c41c4100d07020001c06001d40003c050008012199001660516800016007100e11055130300071f068039501180d0140081d02d840c40d0900d40118103109580c1d090201c02c4850b10ba00b940c42450503000015840802c00c010105102c1031805407401e03018011300110401c01440d1548107003d500400030031100d00c0070090904582d0030044000c032031295402d082d98442030302020724049001c1c0318284090031205420490403555078030940721410a440c1c260b40b084078504115a1071b040780c8540031422540c850718541d07000a0440040d00e4540800940c100078644c03017544001042241c4a0180d4042008011500300301d5414880103002850580e82d4642c240d2511003800d800c2c40000302c049401d001940c016034007203801d088030031000101c0c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 767990611 1250 767989361 767989373
    0x112021b0105060d0c15200318091b0f07020303030106180b070b01170c03010609230408030c070c120b2d0106030f0207020414010f0603060303020c010e030118 70
    0x94044481440d8280008502d0304d00705806010b5819800c12442000d0504000b5586480130181018a042040317049241c200315030550a50700c80036503864020b503512040d00e400a120320b803001d10f681e845a4020420002c038800350740440c07008804841c01441c0c2c3c540100840c420b4a00410401940602c400320001c00c40360b80249208900009020300000d61564a0140d54031501c500c450061003a90020f004000c01883e190700c60100c1c00550059825400543c3e021a0840301c581d41302c0d0107840e0700c0d170300100801c0031a01680c0c16050342007e090350140c680b54917000314230710010300661505040040c03240140f111040140d0b016145010b0640d034038003c04c1c100800f4419080d0350981a00c603651550140104220300c070116001d0602508a1032603103407290540090164a8031040499000c200010059403544100e4441c0099500300d6411135040c680e0b12008004203404c90310038189400e200740082600064410a0642c09280804070755144001107405040c10185525103250100a04010414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 767991861 1250 767990611 767990647
    0x516181706040302070b1603140d05090102090a0902041202060f0408012906030f04021c050610060905060c06010b030a0f05070f020c010e0d06050717130b0c0304030e0f011202 77
    0x2000307601301c40f102c94032034030b00c121b0b244a0f0b15030000d84040035484800c00a4015940142c0e24860109528100340342d05050405841b41103a001c0d00c81d0b5400100480646030446443d03001c0c203081c0303030708500f01402c00c0b038008010021380c0310103403182d00045591601d1100707101c2101c0203003064200a1084a10310764908444400d101061011412805412000341c2414002d40b4800c100c0b03100300e070b82180c45980a01a400350002d6400a03c401a1400280843c3c002c10480c2e0080c00c2e80b25250b2915071915000920003c0d50307401062088804010216602c60300003101415500c0e07811000d0f0380e81d00d40031380c401c0003000e448200d010000e0038501044900d81d00500e10344940d480c0307070f02982c44804c21000110340a00340d881a056220300c01c0e05c2040040b611661146900c60308605190a00d18501d03c130f800c86100c02100c3d0b0118001c020b24031070080100c0d4055640e00408001c42950031801c240e90043c6c001d038200f5030b200d4002c044201c80c40445a00c14082e100c40020000c000b15542c0d103800d540c0c4a040c00e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 767993111 1250 767991861 767991863
    0x30b04020f0402091806130c0206060f03071503020c07090c030f060b0408030409090618080a09061b1e0c091d070806060d06110f0304110103051618170604 68
    0x241486225241d035040a00859604450042c030203142ca9264001c2c90b004038030081c01858004031070108a01c19034404e48100c3ca500d46140c1c0040102c2d26000d010407040c0e0049188d201e0181d0829441086804140c0000d80b4001e4182d050258a81c000e80071014601100e0358000241c050070000712495030f0fa0168400b84d009003442c01d050001c2c130b49914081c80c1921607072181d6802d0342d00c05c03c020064403010340e0011000b544500404102e92030744031801080c4803005501a100410f00141c01c00b606900b00d000031004102030700f44107400d10040c150715a00800c0451018010a0a0600a4000070243c003401d0b82c2d1b0950000d284c251064440f0040030007890030052001504501c0c6d04909540740001907004100e6160300c00504155545909109584555000c1280c140340c4400c0800800040c02006c1d1425000c0307100088c2d120701d4107040c450075580340104034a05041c90070b81840402c40b43e40c0804003100720b40341080044c413401d4200200c030000c0950b0201540c19910200c0202c5003c000c18124052 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 767994361 1250 767993111 767993119
    0x309090506100e010c0c150f0807030c1d0111010e060709080f060127060e0a0f1e0c090b0c030c06011d060f010c060905010905240c13030c030b0402 65
    0x1d03075565042c000000103401c8000045283c080705185103601c0ba201004030382c4c0c410654070710107030340d80c8908002c4070144401039400316042c5620380f42d070944e0005140c1d0b0b00c840203103024403d07880384560152041d2120b510304d0683c41d00742c100e48082c80e4080c01c0707001c020311000030081100c050b01024013500c0d03020544a5000003422000d00040420703000548407031843d4400007402c1c090b4605141c00c0600c0100c83c4a400c2404651054203144100c0c5200e910f008000300780036140d152501c1d0a1181c100e455940c251920301e4034001010200840901c20100e00c24541880060350b540c80c1d100c103507066540c507404500b50200015085643c44001b0026100b180902c10880d0120f907210000700801c0e542c000c900d0300007001c040000409615040c280c0461843d01030501c86448c4500d500c0340025507481d01400d03103a03a91070790070180070084200180c82c004840024905c4401402c00c408552561025180e401001d81c00300d4481d10031401c030038001e80190f50150700104610b64903d0b08001d4400100e400340d01c6 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 767995611 1250 767994361 767994371
    0x14030307090531020a0314010e0f06040504050a03030e0309121c08010e04081c0c0309051006060c060b0a0806070f020c150904090c170a050105091501030b04170403030909 75
    0x3181d40c528100c124205080c560401880101c3c0b4148030003034000900702c1003010f40b0f945402c41d8909011440e18003030f00088011100b03a142c00004401108000b43c90b640c00f0354075100c100804540d0100d401501180d2514001c1074000183c00d01700d255000b10f114103584152210f40a40500d0720000b650600d400d00003400c180c2003d000682039808520910510300350030520000907002481d510700401804401100f911422011080304000f140c13100720385c500204e42d0b00c0306524180042045501c3d000d04803140305100180c280720300141085800480200b840f43c0303031218040c003980d071500c13031601919140b000c4132170781d00d03040b900140125000c60400c0098080e40340340c1d07001410130300c00b0400707142065100700d0300e000e07808811b0000806080c1c00540d06450f41034400700380e4010b0035652941450100e001007021b0001401c0c0542100e41c003070600001540055440c901d1548001c0029046a0304191744241c01e030380301e00b0548010710301d14511070440000001e003c010150440700110640b0314035201004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 767996861 1250 767995611 767995639
    0x13150204050a06080c13060905280612180f1415010302150913021c050f0a09021201320402090412090b0409320112140303070905 57
    0x4124032850040c00e4225840741024801c0c41c0c001d0350345a4211314510303070007464040b01c0c98900d444003501ea0084400500340765010021441d00c6102e4984070501044006044540561205003640da548625401d1000501d010060f0403041c0e0701000311061051102d03110742115140c05e080c18200d0078000c88010210820601018200040319503030451554259040743c0d0840e0200010143c9916a20f184000100115486901e4040e600d94107461159400750303d560044081c9039112100711386040c0c0f4603190004102c03400022844040e0030946a0000144140581c00440c548010a42c1e51880940c20301140410007200e810001d00d8010264038600300f000190018076140c44000da4001e54428080741c041008260887d40361500142c4030308242030072980d0780314000040d070000e40c0905005541d644074000404000703501e03840d01c000c02200701c0400c90096081a0f04068060003090310782011501c200042007031011403041c104548030b0890303842e07150403e8000c00c5001c0d2406158010460041401c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 767998111 1250 767996861 767996903
    0x14070803130303060f0806010e040821040212011109040c0e1509040b0d20040e0f010207060c050406120c051204080c0120041e17031306020d090608040f020913 70
    0x581c0c040802410306646461004001d00030060b000b640d0300381d010806190803151403045050007480c11103c4051514182c010482c00206580c1c00700700c16410f0824051c405448801141c07600c001c1110300182102445000b101d8029590208a4110030389044542000407800007414803444125014868100540188480e007080f0301c1d0010449081c0724444000700d510080c0781d0b40d0703013072001d800010324170340d4190403e180c1211000112040d0358006404018030000d805600d654211030705000d841c151030719000401c3c10104180c9043d083e0f54031358100c029984501c04036407148807000419041070800e41068002e40d40040840f81302907182c0701011100142d15115204842043c42485061519011070002c4002c05003058210800480d800445c0c10701200c00c0700c6203550640402540c49428040140c107414066030008001e5511035a05215001d0f4086240c806440700c5243c1911643c81d0751508240403000286c00a600c4800d81b410402d11a000100d80c40136180a81c0300303178801860b400c0102c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 767999361 1250 767998111 767998139
    0x80c1c050303091e031831021b0a0302120304060204050a0320040621020312031e1003020a0b1621091a0403020f150711090108010515011407080313030306 68
    0x82c80106202c604248107c0c60074100f6a0b691307100c1c00b4903070282c440c0d580e035080705842c96011030004155400b290032501c1c0c00c044e00038190911a01b4000700b00840543c1c80c080c0d50344200d50900441c101c0000001010001d19030107540041801509078508203407249481c45503a881c8541410b25401908a1601c0d00d103081d01411044403491116218148021040d48201155100d02a40c141c824840030790300c3c06401d2402503100d40e09100c0320000b444204c8045104560019090040c914501802480541e5900381400200c0b50703101c1510340e85515400f0416240ba0041e100070702014015140c8a40043c001c601c050b0740c4c603100f555103c000c182c462030140804802008200b80d08081400103000508100700e01d01242d04000b42704130811f41c0c41503840b0b9110350000c00112040c0f40030781c05520a50520314813103809041c0f440000d01c45403400910040c00352034848810340c104010880042c412160401c101e03940d064008205036640d00d001005c50702c2400c9150800c40009151041c005403010b444440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 768000611 1250 767999361 767999377
    0x1809060a121b080c013b190b03040b100810050a060312021b041e0f15090605010e0d020d020f13020f041401030903020703110103020d02181207080c1c050303091e03 72
    0x180510025030704410503c098404002d8228120360040e1050351f407001e444400800c42c100c03e640d542e1510340b80c07540c070401026200c40a029822941440800f0010401d82682c08903541d00003199030700c204440002d8082c560006e440c032610080f80c0005598046010540302c40020340940f103000d880301c00c2c401115614031b0350b00641c0d01ca0f0a00c8030f0b2245459080310505034a10080411404032141c8040c40e03400d0340341d000410300e0f0341e80c02d010016543c0041f401da002d03510440f150b1010045540100f1361504841400a118040e0300d81402119911031b15201100c0b07240c2d403000c6446d088261a0381e2080e0303000e03004403008141c0089014076950321a0040c06031290340f580c0600f50141c599900c81c000681c00092884c1410740900c00400c490100e48060055200d1300000c40340c40c4a440c0303043c4078000b419403100309101e0b04131541c240084000041c100102c484141d50714501c441c502a0103030000e81054000819901001080c04010100052180301c4d0038502c65200b5680f42c45000001d035070303204e5992 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 768001861 1250 768000611 768000677
    0x1802040e030a08010e1b1308031b0d03150e0709030b07030906061a040b0a2303070f0c051e010b0904050d02060f01030b0703050402030f06010303051809060a121b080c01 74
    0x21103000c6c003101902801c00590f01d44101d01016854610140c2150044400b1603940f40ca4a00f8603101c1d070000b040030308118805418200000340c0b4104c005112910940520110581410b000c80d62403403082d1144402150450405111800d000c1c80060117414a030005841c180d06003240816241e0020020000c920580c11560345010f00d0120000c0f01030304020b83c0c3c402803244000c002000400f09030300c03140795050840b030041d644e483c1040002e00018a03202100040042030b090f032400292000541e18900514002d83e01ca003102100c0e4a14050850380801a40043d14281800201300001460300d450749070f075800342e40c203680d47c40910703285a00b42440b0240869030035001194003e8000d03481160003600186c2545d0a103410310185505c0c2c06400e92046000a800140e114401503902c52000f018040c1101c600c2e00354102800054683c0c0428003801c0040501e10101804120b6802e41419480642140d0222034640d1a070b24aa2140c850400c51808100035061400348480001c803c1c0d044a40449 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 768003111 1250 768001861 768001891
    0x15061103090f03120c0624010c02060d06090905030304061404050c04051b121005040e0c150412060605010e0a06022d03130f0602010c02101802040e030a08010e 70
    0x1108001d600e681c2d11020581601a0544100e104140c0704010201420114024203660400e401d460105a0320450401e65508000742c1d0074210341e138094400c0c4820341e0120b074800d480b0030b2035420720310050056902034988503180a598108018000c005913205500840d400c01150003a004469a40c1030101c0300204590400d130041078040c80c05030301032a0010349120000110224201c1d640c2240d6001e20204013a200790301040090700481001003002030001990180701e200207001c0840c0e65a866400d9040c4265680c030a55500700c0c00140582e001888140040101d40e0755609040b0001e260501482d800100024200013950401022941c11a0703003079070041c40c03e0302004052448285400714001c81d5041e1403203009020180810162411013413500f980c40d021860300b00d1200000540d80d100f0000c1da41000c0242c0c0d074698010440240c541c0081d0300200d10441c018001e206030a000c404000d6102d80b6001e00c0b001194030010150a000804e515940e82c143d03220145160380c0034080341c0f038210f610f03204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 768004361 1250 768003111 768003127
    0x32402040f1e05060a120b01230f072f0103050103230a0b01091a150316110601030b15030703020f120705090708061809100e160915061103 61
    0xb5103206005034903481072000c1544a4001444580c80100410001450301d07492413044482c91040542e880e40c00d0901b00b90130210903444a00c0803c0007100c0702840240460880c0300024580221440d103940102c1c44150803401d0003840c20340750000311240329a00b6003c103a41815501030b02c02d050589400a01c072680c03600d40a60b10305020b01c000f52803803e81d8000e810144000800400c01e25000c0c00054601003000f00c410003c880c8036025440007248100240801c0541c502444000c032a046500009106030000c03e00074241c402283d0740748810014441c110000017400070407000e1f14001c943c03102414141000d20410950f403001c00340400380d40f05400c8460310626291110000f02c03490b1000c0c00342c07850035682e03070005608690111213110100e801035003000040d1070800214500080c10320410903090400391401c0b0b079601034800905402942c0c030a900d400041c001c004a090131141d120146492a49078264a006007400c0402080388031100c003400700720300380564510a6082c1e5580020b600744144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 768005611 1250 768004361 768004379
    0x20c060a091a04060222080f0102070803010e04030207030b0108011a010302130620060405100e0d27091514040e03090411090d050c0a061e0f0e0307032402040f 70
    0x406001203544c103900700075074098102d60f261460031040d04140980f2510346031010080c20300001c4500012164410015003001a4541c41034034150b80740742d841c0c01c0a640da645810f80c907100041d040645042f141200005d51000e054000701111420a6040400c1c0100e2000550a0f030017070940c0340c80d841d500500c0a0081d548541036500ca070350710000ca2060b0381c4450f0094107050200640f0240d400390840720b036407210b03e10b1500543d00c0b445074101c010300c4121003890f00244200c14180e1552640035460060302110000f08139034201400c61410100031032558101822400980d130b00c40c000122a01c0080440036150900c00d1400d046991400341d4035000354401081700500c0040385401c010307182440009000d8540045070b06000780306000811a40808100300444c41c50a94080760401600c038401c94050296012007041c400b500782060040c09800d5841a108090896000c3e50584507146001046c88034003004512400008083c01e0303500e1281c070781c811003603100314090010b604041c3c403010801451 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 768006861 1250 768005611 768005663
    0xc14130b03250806130b07081e130b010509071b0f050304060f110115170a0b07050d0614090c0a0e030a0b15031506012303010603020c060a09 62
    0x200050668269031042c103808a001c1e00d80c041d8201001c80303510701c248202c1c1e80c200030150f0441d1180040000303c150a035240402d100d8000c10070010800304c0b901050b0360998074500030a00445805d011055858405025003003540c481e201560006601c0000203820700f032602c01079020303500a44d680645c2d091041e010903010610610304650310b000703070100d1101251050016202420303850361a1191003d507a840103101c3c80c001d000350703019039240c00144031004a82001481c02c441d02c3d042550b10041c0c40341500f504001d00d000380a00181c0604080007800c582c0700c401000c132803008440800003591144a0051001803049189400c07070085404150a2110b00c005007a400b40700d0700d00040c0b2200588082070030480515070440e00d201d9000144000d26040000070b035104003042e130003403100400d030103a104c80040d030280069042c41400c1d41ca0740c0046c0840e030041c8505880b04103541e41d0701d5940e0031000b8000d5001c100700c900c0714010400820100d00c114001c003941160411010418060000300c2d002d080781c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 768008111 1250 768006861 768006881
    0x5190f080309070e012c061f0503010504140f010501080603030714100b03010203040c050f15040e040311120d0c030f0906060e0114012007030506130c1413 68
    0x121041420000414a000951040300c0d003a02410b034840ca0200c51014500040c0c1141403c450080c070086409510a55001d103080c0c03542c94002500c3e160b5502146014954600c1d100c55010080c201600c02c64000000318120b4005840030003611030400d035803480c140402e450b051a8120f200004110961040c501c19802c11801400d40303203005010f0762440d01d0303c01c00921440851b084100c008002c0d1129101d00380c2c4068080c2e0081d403852500c1c3e954243c558207980a00781c450740d003441080150b40c40f07404143d2541c50071400c040c0d90701c61b02d0b40e51b80d107401d040803502140003821545144812100116802c4100e8440c0b0169a0802c0f0320750604001078052140d05400705540c1ea42c0350440d8000e44c0c001ea148586c0035000015031030b414410001d0250005802a4140351200841d00300242d9108034441440e91000d04506162002c0c00540c600b048159031002e4100e210f04418424030710521106120960722070741d495541150750b04182c0c2c5480401070112503204608200c104003041035608000441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 768009361 1250 768008111 768008123
    0x9060503070b0c15010e0f0117100905010b0d0f1104090f080a03020720030f060105060d0b060c0a0c0e01060311030f0426040303140c0d050a2d02190519 67
    0x302c08804d415030b072010300c00d0307020003001d1a1410500c045a660508101d0141c20041448613030000d00c00c1c4826654503001011400c42a85c2e80b50500c01c1c44020f6001c2440350030018460290349026083c4882c40030750307504082d502800000c00c40c102034a01391040c182c0c041e90256980c1d1040c14940c4030229150000c031a0380003803640800120000071501c841104425a600c00f01c2c0e03254401e6017040c5071420411094040540d844000107220b55942c810969010340c450349070105511711141d01081d520700503801004040c0c85565166004c214501c154241565603036001c04210b60307a034171400c9068405c581c40c84100030508001140c200c41113050400c0c1e200d800b504101840520498914282001001950103907c0300880c040c0100756005042e49015201e000c0d5040c203007480790f00744039242d041c11000315061040010b0101e4440d4010807494034408800b06110400715200c0c825144000741c80020100180a0b0b60409071001c81160007407004682c001c402401d1503a02c00b40300e034102d241107100550f65 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 768010611 1250 768009361 768009373
    0xc0602040801140910050f18010f020414120106030b010303081e07081005030f0709150e04081c1505130f09050c0a05030a081e0c1005070909060503070b0c 68
    0x100d075402d000e010714900d0030340110440b52405645250a1011174540200140e060030103218020300d04500f80e640101040402e801c4580764610301e02e00400c0940880c0340b0043c00400c00190213a11185a140984025602c00340c0c00740c0031072080e9088984601001f1719000e072a20050011074490030f0843e60100204005c09401c81c0d01c83c0303603001c81290480c1c81400080d0300c40c0c1080b0704c25404c110b445000305400d0b00208400c541d900035682d00d40c0ca0038008c0408a80d07542884081d580f951941071001060b11405210740c1d800d040c00c01c20029808442174280500c066403250200004a2040c034000b0b0040b901030300040c03030808080200c4202803140d000b258a0b2665501480100d440c420704114038450001401080e41034414030002c00029404540301740c03c1036103184c0200c0e200ea0f0440c2e409030f096140754152241e200e0307105d46260160b580c0e41040d03446404407084075282e499201c4c2d40076403141e4850070221641e0f10980c0c0c6c29204d850142a40580164500700495418032020708a50b015010550744 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 768011861 1250 768010611 768010619
    0x30f05030703110c0c040e0312060f03011808070b010e060f10121e0b030105010b030708101a210709060806030106030614071d061209071806081b010c030c060204 71
    0x54200c007603138851942210041300010702d03041c45000d1240c4903800c060341c2410190b0402caa5030510040925001d0f0355681708159041d5004c2d4085c8d44284124000104454590b0030001420b0300002c0040f034101c4d140c4000821100e502d508510312504004000341d2800000006110b0709501d000f80c0c0c50144550182c08900380110b030701500a2511044800402d03c07900bc01d2a0b105075400c403621940240d2500005101c0090790382c0440c0d50081190409004a0b00c0e1006000e28591041c0d02000b04120b006441d044560302c0740c1c0c010001e1200758a5000034407414051040f0f003420042d1600c9000c02c1102408005482c040e11000c1ea2050000b80001080ca0341d035140d00054540115160351a0443e1408000c06e5641140100c0d0f82e4400380302d103400840100401241d400d00c0b5001808120964010020768040300420003680900740001003240320b21031883c4114003405c40d500440d00140280301d900c40030f40c552021102d00712030050b5201d0300d01c1d6241c0e40307007a41c1b24503a9131400d82e02181c003008049 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 768013111 1250 768011861 768011891
    0x109030606080a150902150715020d0c111b01121b0203040f09022d0c0a060204060306051206040b1f06020c0f220209010c2f010c030f05030703 63
    0x40c0284800005444404501e2412140d0105504d2100ba4000d240c894020050b85840c42c1008803160207915003035541139641400082d1001e0007040c940c845000086141c00754031075030001d145407400c0f500c91600c078400203003c0c1501d440c2e0411464120000b82a9092481d41c811031207071a0a100c800d40c00a0a801451507808403480031005000259000050400000b10758151000017080c00880440c04c050400c5080c05140520501504207803a1039007001c8010003401c402c40709901c80010480f1103411039403400c98043d400510a01d00800d2074140b00194906046410060040b1b010014010b02c0c0d83e50360f105020400080e100968040b40c0c0c1c1884441d0b0030303450000c4409802d0a800416000a08074204411010982020782c011080ea171011005130000c03002100300c0e0a14070340056195006503004032001c1c414500d0141c011858074100448003440a0190546e1843c0384100c03120b8900030000550790b50640410040c0041d21007050010038a2151001c2d6030882d00f64034000c680c4c485005800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 768014361 1250 768013111 768013121
    0x13020c011406032401090c0e0907030e0c12100c0207080304030c08070f23011b0602030420060720040615090906150305100308030c0301060e030c1c0201090306 70
    0x1a42884415070700344001c5240410400c20300758004943d102d1030109070200f142c5090010310525001c035445030300d201e10503400751000209615001c0c00760703580c0c0e02c1d020100030041d103600700103c01c25029500280c4031341c0c140944000c8000100b40c009109003511242c040004001e445405011401800f00100381c09000f1701c0140b0003140510001c5030b0480c24003012070309000c1c6a9201c070b24403031003c80301000b01c0300760360640301500141e44820300d2140c280d020050703c401550141500f440e015410150301001054ac8c007841c022406030326190b00b81002c005031244251012000194000000d00c50000041c40340c4e01070010010214000355200201940403c0a640441d0861000502181c11210031950301010000003000105010312400749805203102c50798003292886000c05071a0000200ca903034807400e054001716030000282d582c0e80f270701c01c0d44a11282c1080c02600009804076078065100d1600150000c030080300200545030b0030200c82c20100180c2c1130032104074140b004014001011490b2031042c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 768015611 1250 768014361 768014381
    0xa2a0c0608040b070801050d0803072a05010b100e0d0305071203020c0105060306040c1502120c16061412040320010b0f01050c060a0207150626030a020c13020c01 71
    0x6019607030515240c440c0c0d811000130254410402d1010040005955542004c99600c3e0400c040b40d5032500c0300030040b524401c1000c003429050b81c0d1410041e4002d00c1c030140d940c080780d000d02c0003000088550030802c07410b0180010004c001460009149140d13103000080d0505161087c00e0561520ba20380eaa07210302a8020010f41e0042680030488030b01d100803c3c0103095102400320701030710603860944e07650004800c541c003070508003070001001c0c1a4058020042424802000501113840e95414030a90350b885081c000014511654110000703103960142c88601000c1c0d044060403801c01c10500c03958600654028402c0d0304115480044404640e0010041c1896039183e200100343c4168034003e00013080320340d4040c0d50420504000c0c054a00c0e0001c41c200740c018540180240e6196581d00b0111070072007070003102100d4070303141240015041e52041001149810307468081d000032185000c1c659268047c200400c800742e000b0605410480c90000620218005129001400c0c0101c10512500310303848040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 768016861 1250 768015611 768015617
    0x6093601030c0801180308100302060c07030c060c0804031e02180f01140d0f0812070905010906050c25090c020c041a0102190206041508070908030a2a0c06 68
    0x100500a01c1110342c01c100c00f4240359802840141a003101c50000010580320140401240c000455514030b10700d00190000c5400030615602d50300f010008684441c8507100465602d14003001c001160b50083d0760341c0692542091803c0e09091940d101ca544070182400010302100340100100010b075145c80c1d55180885001ca00d900061501216041c010a4180c010340c0c0c0d0010181143c2d1038a40c0c0700c0110b940500d903c0910180b200d42c6134544840907005ea00d21040610782c505c420000c1c280c0d40404502c2c21541c09a890107031040d6102e4003a211031240000e12140da800c1550f00c152566003d0400b202d10700c401c425006003007680c515a1a0440f01034041800041e08840703145200d81c07400d0301811841754140f40c0c900c1a8145200000307035840681d44407146184140c070540d28255910324003500d0003000c904402c410800e90424008100d1002280c0d40008a0212000800c280100000750703501d41e105034681e0400d40c02803601052102c0300c19900030800800d65803e0100151201260200404140d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 768018111 1250 768016861 768016969
    0xb030406020d060f0b0d0b061b0a03080124230f09090a141603020d052502070803220803040803071e05031c2a0207060306050609 57
    0x10140c2c0058036030300e0b400541100000c940c140584c15070707442195101d40d43d41100054025450300070803628066840061500c0121410348400c000011645110440c441c0e0b80f1040d0a81e00c50210701103403009101e00d51100036100c94501d44807402224440a0944c21041c0300c21010100487c1b844294048a11007600b0000400c41c000e29003800041c194000705c2c44001440541003a28030324105c140d005244d004500d0306881c511601d18040d0781110240201e00f41c2c1440149810b07101c4010081008010741448601ca06451400d188003060040503031301c5250182d40b400030114007804002060280000c0100740500c400a02001d0400c01000180308050186850303854604041c0000c09a10030701403c039100200704000012008000c4588a401000c2c00c010004030720b01001009128280314040c09900340b8204181030041309880c0300e4085126130848103a82c0e100c1004070305940051140c03d42100302807201c030310740340b4180314001551403140301003121160100c0c01001c2b151400e070410b078081343c0400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 768019361 1250 768018111 768018127
    0x21812011e050408090405040c030b0f160507020d0605090c06071101021204060c0f03030b0d0b060306060612191b0905010f080114090411030106030501020904140103031b0c0b03040602 81
    0x82800c0c52141c0040c4802c125910303142c0c0301d2003010704c540b803c41c52060b5600c200090800c20f03400300f12805507401610032903503450006e82c40151813100352000002c40500307848606039507100e0400c4801c03007940504200e07008400c650701d04e07005d8000505102241d004210b241c1c501ca031903030310241200c240144040c00c010602400003a00704441e00d0900182c00400304414811243c1140030103007125409014052074000908045000b40480c40240707520075013044643c400e2203a248442c5000d004100c054800c10303203078003040125500c035400c010103840d00c11700c0000c0d00358000000c2c48660320210b060301144049020700c5260310000150f05800104030701032024492544d112403007042032407040c105200035506044484001145c1000d10f90722a02550001504010139548075250100014009021040d00d80c40d00d9401703500654241800303186000c1c203406807251206540b6041b40d80507200c2c40408074494403070181d0302c0912507040d902c03584a2140001c4170840d034402144201c1c020b0341d0043c4c540c108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 768020611 1250 768019361 768019391
    0x6150e24060d0c02071a0f0a0809010f0c120b011b020442060201050f0a02090102010615120b0d020117040804031208090105100803030c0c0a02060721140d02181201 72
    0x651b0050002c01082440003811080c0e02004642043e0910304042d040359444640483c007405650070360503203440c00c0407100300c047e54100381344038000c00c41c007032062020549010045071a618442900c420705020045840c003d410264800c24400760145e6040d0040b003000600e90700c4c0843d14140703110070242c07407444100d89251080e020388050942403009020700c0c100020400a900800340006565981c00507420711168001d50004005040320504641c40b050806800343c00b2111400740d88809504190b66100740d40b400f03031180c415441c1c0c1619403050001010002c0511140000e0045034422420803000c004214488020710043c615540c84001502d0481101c1e800e60348090302c079405840c0c1c40d840510040c0c00200549070f000194141a44d00c8090b80d06249242c040501c1c40070b50495030010321402800303103404a1200b20000501490300400b0090412103501c400e00010310100c100a105080e41d07507880350005c04c6140500c42c0c29111100b614400a180e100c4241d80c0b407a81d681d51014010710700b0a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 768021861 1250 768020611 768020639
    0x90c080f0a020604091e06060e01030b06070209220c0306020415081e1e010b07020f011d150415020d090602010b06033106150e24060d0c0207 62
    0x300d401424119656502046450007140924145130303854107030102c3da06910450884d0303900f0929001b1b0002c50f80d1b800000d01020038040c2c0c01400203080c00c89000282c00c001c0111094240c1c0640684e0981c0d43d602d00a10206000e02c10303002d0390b102030384030003004105800e01200c0518042c2c800183c2e21840c0000e10307200100000c0a50003807104090070408020710300340c5c00c464508880c624405070366464096440210300c008506240e0100801d0000c580e1810400240102d00c2c82600d08a014018001c015541c1401440201d01e1241b213041140400d8244000460034540034842c02e141001c3d21840c010310300030903c0300004010390080e02c0f0003c0443c0c0c011b282c000105000e00080000c0e000c004040340340c03844010070f0080d0b20300504a90319a50008807580b0701c90b1801007010402c0040091a1034800b0703091039107230310f00310094024020500418030942180121030124000c100d000c1100a2070380070360721400080d5030040303040c0f1074010f402c400c0740103100c0c48500030b6000d40f256505141c1004a041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 768023111 1250 768021861 768021883
    0x30a0908040305101d10050c190201052a040b07020d0b15190501050406080603030d0c0206071701050a03060c0e0312091509010e090a09051905010e161413090c08 71
    0xfa48803885c80740c0900e0040f9220b40c50360104a004600c6650340400494540324242c0480c0d0368044204184004507410f62005004181010f0041100380420b150b46030780910f03510b40c0d04c5d42a1401c100030010b2411030402031106500c0030389800d0100e02c06868442c1c4070f0000f00c1d0790380c40e51909420144024613060916409040001000000403410070000802500807401010b090000c018040380b1150340404c107a0f002c00e9007104050010070780f00354bc0252280c40940b200d40c0404e000111036031717403001c1201d50b0034143c42c4050200c8140510f1a01c626000c1c002070741420091255001c8908421f4405100d48010000080c9513070b0341e200840d400f40001280e80034440e0440c0d440c14405a2541c0c1e901c81450080d01e4002c4480003800c1e2135100d1490018000c036074005006c0d104400c5031030254180e40079402280e600644c002c01c003e040f000c0c1d42e2500e64000822901030825068030a10003d0007580100010590103411890603100201645003181c0200c842500e132890f550000708106403040203100d02203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 768024361 1250 768023111 768023141
    0x2d050306040516050906160b0903041d041109040303090501050f01140405010311040902060d0e010b01090503010c020a170c1204030605060105071a0604111305030c030a0b0c030a090804030510 84
    0x72802d5100003004c5000d503416191149000045c0c010304850300311a00c048054200b078142516003030503101d20741c1c0d0f58003500c1074010007034080c4043c40e540c0b100c50800c5449150440c048610b008a20010020300c18002041241816036601e600404543c003446000d00c140c03048001d110507941040c024a00903c818280203104a08010041c000600c69004611001c0710a039004540e03810a88002000c0340108605401031301c2c9810300040074030905420401e00b0711020380314401c455803100300341820307140c18100d1080940d10207110200010604294403100003103008005041c1800000454208030940c098000d805a000c60305006203c21840ac03c0c0d040703142400d0191400e541c0d6940c1d81100107955182401c100410000299242c46541101d04040d01d404803031999000c00c15042d00c0381d014140100d500030b00c40d101095905003000641e40c0c1406402000c1a109980c4403060803041c0e5100901801c2103a4480e800100041c0c0d014000c3c00155104d42e014107041000c072000d080440d11009501580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 768025611 1250 768024361 768024391
    0x30e060d0f15052704020a170718061203080405010b0409080702090901020a1e030207170c1005010b22080609030301080d050a0c140109080d020408010501080c010905012d0503060405 80
    0x50300c04d4103a800c0b0a000040303180f59183e80d450000420018081d403209055070b40985002d008134101103090307400e0380c0a045070307000ea40f0042188001194101c1c000e520076410110303560404a402040032545c0144150008600e502c03234000840c003924400f1f401101c0e841d201103103140461505100b1154003900c2c0c0c0300214180340006100801d00c56a44d4500705c10ba2506100c0c04a807944680c046419103038000702e011038141d6a2818564443d402080d03500c802d4000e00102242940b0b0500072107048400c0c980249080100004c0f000e075070000ca6801c0030000620202001454040c140b02443c4a03400a030059512985017480907030805646081d04010080c0421000c500f0b6030300060001c0721142c10800c1203121a10751111540144800d81001e0080701c408140302c901d031382d055001441941d0015000340070a07603039801815902c0e580079040c01e01042c0a010140050351041030b0780d08400c540764000f00456881c180034449442140c41e821800078800000f04580c9007494050b03250882e210f81e00000d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 768026861 1250 768025611 768025639
    0x507020f1804021908011b02010c140315210a0b01060e01050d1e1a0f0f0a0308070305281403060a140310020c01060609050d0b0103030e060d0f1505 65
    0x7030654014002071240f80845001e600e0741d800c000045010344001c100800c0882d41c00c0362401e140b85400010b000c010f600784001155854481c81240f070309100048042800c41e00c071514580b0003074006590003608000701d040c0810542000c0741801e1003d07812100a02920411410000c1e08003105801c00740a0190034a40c0d452246d9016045401d542e00c201c00000e00740c40b000c07420480c03000b10020b100741920304013958610b8a5510040c0b101d10008103c03065034010711030006200c005030316590720381d03442904000d00b0408508280c0c000c3c01c2903803083c40c101d403901d851070010041302507400350034034103000c08825040304281d00081c0c1285140c400e180142e04528026001640319049030041540c0c04405c9507600710291010004c181000000090942d100c0300407046050003400c10b803183c02e0000c4c51107100000d590810740a03c8107034940001010455070b00b1601c050300c00c150811303c01a0044400c1000c805080800d00c226280c04000140205860f0024000c0349042003040d00700034070900b4106001c00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 768028111 1250 768026861 768026899
    0xc0c120d0e152205060f160e03120f120705030603071d060d0311030a0c0506071e0f1709010506040e0309010518240309060709030c0320100507020f 65
    0x981c4111407a029040c3e21000020a0498a0f20036400400344d1281000303200182c0a401441441841040103002c621122410203e40100361401300503016080360080c5000300102c0c400520850104814452512003601c402c000d40d140c0450b00c0200040010003444031b5890240882d200070700c050780c4000c1c840c0d80141e0700a180e881000e82107070701c12044102510101402240004803d600000540751a50640b440141c80b0060480c0c040f030700d50142e040019001401681854500d001180d0740d2843e03803901e000d00703588031002035000d01c052040091640c400755114003c80f511172109040085001e08ac08010710040d541071140d007040076042488030b14001d981c01426200300c0d08483e201145c030341e003281c0b01003000b8011550540410190900301d009000b8005401580030b80d03400c0c000c0307a00d95551010f0072140c0c0209400001d141c15200c0000300f0105100800c40c0c01851070110300c082402c1c41c40c000003008402c00c40f10710804110f01056000039460041d00307d540c41d802c199600a50039603c20401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 768029361 1250 768028111 768028153
    0x3040f290f1821060907060f1d10050c100506011b0809060703030b36061914030705010e060405010807050d090501050103121707080c0c120d0e 63
    0xc1c0c0e00e0303011405040039204252000303100ca40141c060010803101c0c641c020040c89070f000c101042c61154001040d40c1c0000011403004481e01a51076051010400d8070445001801204c4c5410b0016a43c1e501c0700343c1e541302d443c810b43c24885030312041d5954030800503403410304542451039000240b07841d04020711660010581101e01c0c000506121800d509858100c016014440607550401408901c0c04101074042d4014100803c00303c9528030522030074900c0000458030000c0d80d01108906840b00780c0b42c2c030510340c0050f0308608000d00854114640180100d0120358580c45510b10003171840355500e403410180026006000c00b8030f0003040480c00d24010848a2042d4402e042c100301711540082c6a00e48a001034801c51440c09806001120035030902c1c81c041c24080c082aa80e2504845d09001440e000340c015840441040c0750101e541e1f41c403410305035a21003004003000d6230302000b001100c8580c10180042d410005515600540701c039120460007045615404030954140d220300c0a402440f1420302c86 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 768030611 1250 768029361 768029377
    0xf060a060e0310050c03041407080a0b0612100f060501020d0903110105070b0f0108100507080f0c0d0c031532010302091507020405090d2f03040f29 65
    0x105100c01c249000201c0c0c035004a0401c50003a0600d0320040c00511014900154041c5001d50000798002c1c604180e06902d9400300d02c540712140d40324640c124009214104000e5028400414040c0780e000100ba10a0518906210045901da510300780c4042400c81742c8207150140500b0710051403000488000038052240c1400003038203000300ba200d076001507032065080b030340301d59408103140d0f80e14100852500b881c0c85082c010040e041c0180d00014024a400b8070032217100b00c0b26075503040420346805442036450ba01c007801d0750882040410541c0044c0340c0718007031022504030642c2c1c001020040c01c1070388140a0300755081a44c0c0301014511071058802d031110000608100503421408034908000103034004c4c441c940300702e50015140310001d2100d1040c18060001785009650602c041d5951003151600e602c0400104000328440e00709005c21a41c1425044039410300e0300d80d103e00300940c0c4100700361941e00558031040707102034101740c28048a6164500c1449414404c00c1c11211a200481890514010001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 768031861 1250 768030611 768030617
    0x9110a080c1b031e0a050912150705070b0f0408250609120f090506190c02040536030a03090218090c041112040602090a030501230f060a06 61
    0x1c514070307000c448111000e0202240b84410110242081c86032290418401940a004244010b02c004080c1c582251442106030307461602c1c202e091400c1196100818446420f1403090b01c9002e111030404130010f034002d017015200c8940b82e10700e51500749465a0000c00034481a0500401d200c0000eaa00b000c1d40e045207441d540c044001e5154860b24201801d0f40708001e0034541c20410b81c40700344a0840c0703254034207500030341d038101c480c0e02808030035680d00400744038040d000b98041065100d20052850210203a511604e0407520421040e000a001e0f21029590003050103159815030000d401c401c2c80030000e080c40031100c8544622441061a00da0080002d100141a140d9000b0b40c21035555110301c1184c00342c590740201c0706081540d40180e07280c1c000c00301070740600d240483c1e0040520051040e0b401e00e0802881003402556140d80d050080e4020301c0b00141c00505080b00800000d40a004030039070111400c0e0f40c40e0005139600741015a0070800780038202e034403075290b01b40f118036201e4401f44026a5040c1c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 768033111 1250 768031861 768031877
    0x1701061418060d0c0914010b03190216061505030705180f100306090c1502030708030a0b0d080301120201080a06030f0b0702070f12050c0414040605060d0602040e0a0609110a 76
    0x100200d52041403109008004d0346440f000425034549a61054061003881003600c3c8040e0b0322aa007900301403209990b185d11190684030705d1503030111039400904620005801e90510350205585000c25100c42400000022100300c034144040d040c01c0000c1c800411045a195590b040d103010490788111001d00004450100103001824820087c040744c0b0003940d000c18100300030401c500b001003c849160040311000d0f1629408000d001e0310000513030303096541080080d0b2440d100d040c280c40c02485900802900081010505800f080c6202d003d1802800c5c00b503180c040000c12131000518022000300340302100382c41d1940a10108041c0d100240c141d692000c031860b01502c445405a140c810320398003200b4072460b520030208410b201c080520784501d103d00c007141d004000c0e02040200740c4025034224160901c0c400001004030303000d80c005540118014000d00d403c4009511404281ea000b5000700301e55149040034084481d484c2d200350402000c0c52030017040b4002900920701c02a01c2142d2140080289203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768034361 1250 768033111 768033121
    0x171203040f0204060b0a0305070206010503030c0d181d150612010e19020a180503070b031f080a03030614030c0f01030f02130e07020d0e0a050d06020904061701061418 73
    0x554084005050860b095030f445000101b4001c1c080c20f0211031120050003030b50000a80c9040003c243d4450109007800b60600e06000c610889003031409040e92000c0e0800c000f40011404060300c4c0e48200c0800340305082d40c00b407070100c880300090740b6203068072070181e00100b0007031040c20a00c01c0014151210458140010b84402881c915815507507d40980b401d40700040241406410541880c00040c14a401c006c0c1c040c1d8410070980c90304c80502c902400c080c810070000320396130400701d0305612690102c0560254651901c84552900c440c040040380440c0ea00e4000b400302c000d000b280442038241c118014030400e138105001c1400380d424082014181a01c8094501004210343c05596034000001c9400044035a100400101c0c00f01c15681c1c0f40c098061b002c2031143e00303841a1403000306294050180045c042c9083c09000d8145000300c401d0715059801d001d030300d003d541c590007203d000f0041206214680381c064880305007114115800441d18942d00c03048000180c0351070104080c40d52590358045460b64074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 768035611 1250 768034361 768034369
    0x1012170f120117010f02070804030605060a080a0c09050a0b0a051903050a0510180b0c091215180f06010b07061d100b0d050c0d031413171203040f02 65
    0x40c2841c040c5000c1e04078800811850340c030925007032590610b000240145d1080701e20400481c811481e000c2c00c0407504000c203001099040d082240c0020380605828107080ea03855042d0b040c0b40800344111242103c92400b00f24210460182c03d4100d000c4400c20060100444002540e80c011840780c0c3c0e0281d0038080c84140000030400c4042d00941e00041030383d1074007440b4034105468901825078429404d2401d0030107444074200d0840200c0c0141c4c0210341d1a600e48a8014518450f0410700303202c1d5001c00c0c000440e403c020028004002c1e120b950001c88102801c040074540c407004120082101580d11178099001c8089001528a0445a610b42056078400d00c42c1440c030041c0007982d0a40307640f0701501458000c221b4001a05030180c91900b28108030f80c49010040107044080c01d00d01034850380c480c04040d0b00f50702d040034605100fa0300c282030145505512844c8900079400061070490169400c3e0ba040011040310041188454001c1c1d0140000e000c2501e00ca680c07030701024202400b903e403846d441d2011915 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 768036861 1250 768035611 768035617
    0xf020714220e0d0306050a171209040b1c02150a090e04051c090306111606051005120706120605030304171612050d11031c1b05031012170f 61
    0x100b9041d1020040e0000b40034000c2e042d14880c1d280100c0d1480301c0014480c1c00941c05040210852002d0104100c0388241d881c1d013508a00314056000c0d55810320900759030f0b0350200781283c80c02100984004d44905004100362080107500300141d8a904119000000d548035503160f0648454040c140c285498608201d850013904810701180740b11141c00c01c52610740c0003664402101e00c504030510614004041040b01c0380031322050740349405010010b00e00007621942100b9440040d1401a000c1d031a91303940001c0c441c5090256201035030304541e40901100760320103201c043c0c000c2c41c403c060190929042c0841e075240311710b12904840c596507400c0c481112100303210310843c50030180c61004003213031a82c086000e1400700c00c0f0b0803560341c03140050fa402c1c00c5008a880340801e00b9140d010b1403e102601b10042215144010f00c00300740e03030781c56540c1d070f24250b400300c402a010919a07071807585070b00e09039100c00c0b8440100d405c00000e0711a1003e1900c0040e4849080d000c00341182d41030309442c2c2c03a0106080c4d070180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 768038111 1250 768036861 768036881
    0x91805210715021b0d0c1113060f090f0203090c010e03030409020f0405010306120507030b0c090303031305071d04150e0303040501270c140303190f02071422 69
    0x3180070102c020040903801400c9400c0701c000c44c1000012055141035a01c83c20102c170703e0081035524809030003044800a5012407440c000d0318500107061014060001c4034416040303036000c0c0b0590340d011303c4a11800d100350070b844c2064040c01c52441c1003406800e5510000041ca4070304102011010841b50749060003550000c04a0100954803422640f030344400035003140c00f07110b00107840d01d0b03000a41600110700740c0740c0c1c454002029160750b41c110303203c0d40341e09800101400090700040010311143d4404100561144814910480e504009460400e003425055800200411056484d44072200070801042d0b401981c0301c001c194010b201254004081c1c501c020b041c5240340008070030042400410f4100d01d00c03940403110100c01c0595a507100a1205284c1640030300700c51040c9009000c1c00c40d000310f44e910405001000c585c10140d0241e00d0651003618150705000048010b0142d400e55501007101001420420030125600442034010a4889082d00c1040300d0903001c910720721641080345d51080402c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 768039361 1250 768038111 768038123
    0x1207090209040e19030807030603030503150303090d030302040e0c0f030a18020414091e1b0a1505070507090902090c09041401080a030e030706020c060f041e0918052107 74
    0x25215042e48130040401a801034011034150300018015503c20721440381a2645911010304586039901c0d00510f2000200c0c00c940c15200030021052503a1701c0c160f001050a2096070056a681d04000e0070741000720010300a1980c404080c41002d59407003600007620f42c071500703008001450003540a04207454a41d07000c4065009841e101c100c86c1249607000320b481c456032400e4200c607000000039100410051103000300350007607040104000c1c1c45c1f00798542e44020700080100403900d426101e0300d0320240000549040d4021910000e80134081010900c4480001c1111010803c04900716402280405130018030300c0e8003006e00090201101c0d43c9035031010442645211404072190703103c1c50b06136559500200182d01090a601124020f0b280000c0c40f4001d695080d8041d045840c042c509100da140c000005030441c9031018070000c110214406140d141c404003090742d40c041240350590440c02c0300e200701030404000d00c0001035600030443c0010030806100c45030108131000405440741d0b40c00d0380203110005140d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 768040611 1250 768039361 768039373
    0x3360d050f09091005040b101e02010e060708100803040501020c04020f0c06280b0d0303110d0c0309060c0c2d1a0412020d140f0f0703031a1207090209040e 68
    0x30b505680d44d01c0c4054035820303181000b165401da020403901340c50002e918800210b1061006643c601211209501c900030b40c000490030158151181b8144a400c9945070002a510300030090201c0008170b0400080040d54040c0d40b8090900c0e0000f52541250b481321400341d030b000190950510190012500040d40c032509540c2242450542940101940402c0c10044c0c000300828100ca0f0000c4d101e241c0d8480c1006058040f10016513030154098600005180c0021805001081610086d40103003800d1a5899134001242c89852806104650340d45140200300540c03545120300081c00154540c0000c5031f003081b030000454074840710703e036a428064402002542c41d020380c4041002c12598441c0954452100001e0602025504030398486401840d500045e9410300074180d4007036640010107501181036042807400170b50000c1802107600801049000903034401c4001d03840006c840d81d01c801d00030111a404841600d0500742039031807825024546241307500145641d0559a0703a44041c10300122078040d140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 768041861 1250 768040611 768040621
    0x9080d0c020709050604020a05030402040c050c16030b0c0c0a23031c0507020a03020d08060109030812090d030b0a05120307060e0a050709050f010e0601020a0803360d050f0909 77
    0xb4540c912882000d41c0541014081105854180240c4425024a580344d41c11681d4503001c02000d864400005002d200c010400e1244000080c016841c01e100d00000b5419414510b00e090f101040004200458000080c4030f04281901c0c00f04001b800160024405110b01c0d00081d0a2254040800703120741c024070002591038644c00c41c100b80342c00220101798080040ea51060000c0e0703200d0840460007001a0007150300c2e041e402d4010802d10f50030050605d0045410341e00d13a96002e10f0b41d4400d02944400082000030000e200d00c0401c821940400c440c6414001120100007048448132a8080c262140301102041c0035020410820344410300d40100c0d041c401040e0401c0f4007a02c6038014102030320140100c44001c5065291809801d008200011503003000380c1c6841c000b8542d100d40502800e046005508680000c10141303405103020b0070101a000d81d020048813000d8225040c958072801ca5460340b81c99120f1181313800b01d45c50680000608055554200c0089120000d1050310203c550003103203103041c80 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 768043111 1250 768041861 768041863
    0x7050313020f0a240e0307120311030403080a0c110f011b170f0903120901050327060c1902190803060111011a01030522021e0301020d0c020d050c1009080d0c02 70
    0x50040140785c450f83d02440b00c10301810788404e05401340d20400348803125034000181c81407049085182000042d2820b0580b41d581c0c013003a40d4003175a0460300040d51240c42c002800501c440c000854030084510044050400700080c00844a014140c07240c0101c3c0c1c200301052000391040039480340d2038002d40a03a00d10000000c5031081d0401c0410340d02912a1b00e01c5041c001070404211043d0100585680b0306580e202d4813152004070078074101e4000700002c80000c0c0340d20030041021900441410501c40e0703d07400b40e10384040e04401c3c0340038680c1c115800303400040c032020402002d0400541e01715a18566076a629030060f1402d20300d00062004039841c110036a0725141703080701c22440c16282682e082c070203a02c5450700c40301c1000048000003a03c2c03072084847c20041c540703060210014800041c404c55101c2c8002d0000b401ca0f040000305451803900e50628401e110b41c10700c0707102d4006060f07003051400d100e03526800e1035132450340c1403e1a505643e50300c0400b0074804000143c0c3e03002880307442c0c00c0c010304007081802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 768044361 1250 768043111 768043169
    0x10e031606230712090302060a0908060a0612060b150f070c05310b040f021c020708040e0709031203140703021903110c07030507080607050313020f0a 66
    0x300040a15100d8800e50140c01c501410b00001c41035414240022519841104501118410103101d44030340004016290354021300141a002d440704040075103061112418514010040440b080c80d01d5801d006034901c000c003460100703411807000518080280007142c072801d8624940180f980001c15108098241c44c4010000c0c54231910100d0740d030a54802c2484803d20780d40c2a0190070300380d100303041f80c00d00b40c0402d0f48182c607442c055400b00c2c1441100c4c02150131070301070910340c0540e9900021031064a24420103a0514140184c000310702d032a000d515203000314080da0050034210624040890f224501c80d0441001031900180b030245100d2000038050000c00401d81c10b5a04003046400013008031f4000c2c425a031081c46060450030349260005021030041400032160140a1414440b5a449840030404480510300c144c008124882c10724241364a0068000c5c240c40801c0010410003124440e03050101d42d05660590f202078104141d28002940002642c001c66a04480721104c031400c220f5200034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 768045611 1250 768044361 768044369
    0x2212050f010e120a030221150108090601050d020603130203060a0605010f11120d1517060a0209130507020f15071101090816020303070605040c03020a050303030601021b010e0316 78
    0x3004101c8003502c50703d44074102a140c0004808084c0300140c513040c001e40003040001404943c1040340303d1031106800c0b01180c00c2d82e961a0301c2c030b128401030680b0f5811141180e0080d0114004090642c94600020100c000c0394200902484012000c2241c0790700c903103220721120b030303004080d5001490180c4007a8010711542c45100d00003500009120100e0f070181e11507480a0707032041c1c0a0703d002405402800c009610a0510300d40c01c9a4401c4a40c0d68034210007140e5001e0004145c100c4100010040c400b8584403014155110301342c810040241542c2c1d6680c01803032030300034008002c80c0541d40c4034030590070310742c620702000740038004c40ba03a802c004007100c8841c500c04d100d55180c1580e1856a002e51900300c540c200c2c0018107014041200c511500709454a0001061009003102e02d0201c1942da13400c140c6106031000ca54241154505004510300424100d01a0009800441c118581800001d65400002c01d01c84103d40688400706256482003010001044002d07040382c81c1201c0b1440f5040c044402882 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 768046861 1250 768045611 768045613
    0x12072d121118070c02040b010e09061207030215030403020c010914040506130207111c0305030f0c0918090111090102060a09140a0b0604050702031216020717010b010e1002032212050f 80
    0x14800c0c203190b0089d0340d41000c00002800a002070b5035983c00b030110554180382c645850f403003514030020059513951480c5414105054541e070322400c0c00d2902901e46441c1c00c0308103050182040f0207111241a4a182d032a501404907004903140c0c442401081c14001001d900300841c5000051500034040001c0d16403d4504041d5014a0403412142180b5221652402e004000030300810115a80281540320941c214000d00d0046252000e000c3c0003409046440d82c890301c00e100d00d00e0800504c480c080c850744119101440241d80340203c03d0300000c3d1541002080700c20300075680d0050b001031000c4c4000c0d00440c05001000c1301c458035040c0c10b02c0f1710304000886a4900c0b40b81440c001801c4607101100380d0f45001c11018645080d900c441d01c00d80d80c0244c08404880071803150705000508d03000005070007a4510100380001070b000115200042010541c06039483c018080e102c0402c5869900000f1202d01c1042841c1c0c1ea2503134121940d24040d00c0e0916030051080410115440c070502001290300692406104 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 768048111 1250 768046861 768046871
    0x30501091505010506041427040b2a0d091704050f120d0f020c030303010f0503060702070f060516152a120b12072d121118070c0204 58
    0x740c8a009a52090080f1030300280b003400304000080b858200303c420403e00520400395203e080010340808038807130f0003640d040001141440284074400910036085084131808211441c0030305420260313408820384000c0c2c1c08000040161030628680d00040806500103208440c5181c4509008513640181c0201c5100b45040e00349450b00e407070550f04904440310300c00064444d00500d254180d07440c4400c80301c0501540240c0329070000d02c1e43c0a2004602a11100f1811000b80b07041c541410700d0280c008040809640c01a40d041c010030a54003c0441180d40c0c40c500070780d941e41c940030100c08164040304000c2c9100d81039400255001981c4d0094021100541b40450907154014a40702003011001d041c040803c02c6550a007124108540203007040800203030400148441c40c10085151031001e50004c00390881d01c03c00e21900b00590881c15000f0000d6000b09030344141000611000580c100d50300901c040d180008101494541c0c0001d411a00300702d1507905802e02d410301d0b002e001c11003010320480c0700b54548 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 768049361 1250 768048111 768048143
    0x70204150b13080c0a031b2d15200f010e0d0f020316030305070c021207030b070903030806130912020102040312030501061d0f04180c05010306210305120103050109 72
    0x6000d03440c108014a5500c810b486c6032079001e084018181c9024290488a00200314000640c3c1075081e50b03c40340c600d40346041503480b01c0c0c18098900380c2140800e81d08030703864105441c0d4000706c09284004002c4c41d80c1111002c03a242c0d10301e40b0b0307414186208c0c59400c060781010f00e5031021800e0844404141c6035102103103040001261280b0643e900200320065603003130000400d01c668001e9034401d20070709101c0711654140c1c002450000324066640320981c4050790500070040c0101e0840c1c0c010006c0d091041e480303811954050041c40c0002c00302030240142100041d0b6860b9544c1084d000190400070341243d043e28500024080c0d80036010507504001890843d112251292241c0303070403034156030b41d610254036210000f80c0c00c07a0000c50b81d003903015940f803450b1a190354651203414959910074545840543e11480c3c46c480c0031650b580980e050614100d0700704044100f07041d030480c2c18480c86003030b802c8841c100c3c038042d18140a0340d15190425080a40040100101580101d148078003a1000041d10021 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 768050611 1250 768049361 768049363
    0x503010b0604060f0509060409060e091e070306050411060a0f081f14010207030c090b01120903050f0703022802091501050a030f0f020a030212090316020105070204150b1308 76
    0x141e02c02e00e00058080310800d10005c3c4180c001d014031510041c110307440c141d515040700301554002d41005001951040c28451500d01c20802400203040508101901c0342d10042d403503442d03040a110250016450b00001820400d240c4105580002c00912050300e40380c2c8900000e0510060b030030034001242014020501128402c0c0e2502d4100403040ca1118500307003401c07072144800103025080c038190310490700040300180200d00010301400140100080c0e084410700014018a56500d14400c000d1038101c0d104007080c0d103c0c080b2505018120b50b85a9110550302d000c91412880002400c07210000400784d03c5021611542d943c81280202e40d61741d05034484c032116240d1240d032603003154041601000b042d01c020b40250030082c1d10510740c03030001540e6020700f040c40e02a0b078009001c160001e40c4c0094070308545c9003034a107441c4d00400400c00131070400151040032851031200810180c140007001c00e10408566135a0030130f00c04130510000e42d0716102e94074000040d00d034004004404110b405a140414944c43c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 768051861 1250 768050611 768050617
    0x30c090b0d020d1a04030e0102012007030c0c08030a0201050604050f091f1401120318060210090606090c0228050705060a02120307020f011a0d060e10150503010b06 72
    0x58010141c001e103581d540e08200c04044041822940c005511071081d400702a6240c060340328074040d803a4400b140d00319200090031a020352203051f07020b28045a49207142c038000c600340e0f07600c0d030742c0f5040c009071031442802d0240c1c1c0346130103601003a5103120014410231440e5064124502175034090b101800580c44034158100c2c0e11000b05d41d01512a0311840f0010a11200d41003034000c040083c44000482404c07001c51058180c0090b004051005c54640c401410554099400c00c4500460b0140d1140700782440340013500e50321154141891152950500740c240070881d030002d8010301e60080c080080302c2043c40080c1d1115046d103030110000070f034030010501c55150075810614040d44907000d40031301810142041403a03000b0241410031482070700c1c10b0079400e00b05c0c000114000d81d6203800501409407800c0e0618255000500d020340054001da4403072980e078440c400c05c0056107900110125034004030901a030b141007042d44040e60360604080341410301c40f50b00d44007003055a605500902c00030111409011440c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 768053111 1250 768051861 768051881
    0xd0c08060c0906030f043e2b03030b09070c03140906040605180a08031207020d0c0f02120316060f0506031e0c0306161107210804090213030c09 63
    0x1800c10000a550f00c1048960658010311640e85805075191404a0301c0602500341c601942100c0c001286020000345240310348910b082c211b0b1400710a25035106114100702c0c448d0303401240c00c4000c1c540741041500982100c0c100610141407042c42c1d2030702e04402420300580041c25008203036801c030007446424494040303402c030b400d018005030f01d0f05140c800211001d034026400d1381c2d52a00100700b90b103041d81d10031302c80c1002488210011501ca0001c05c4075071502d210003030b203100b081d580f009006684003070b04042c0321100c594100303454000c880101d001007200c203010751081c0182c038000003842c00c0d0052207a848140c02e00340600c0081000001500513402101d00940390b03030b58035034031802980103040f0801001d6a40c0d40c200c1000d9903991592480405e00d0300c00d080e5403c078894000359140042d80c903400301c40360110354010802440d6051810170301e49010b1030143c40034100607920f014a6001c0c4498201110020901c150046580b0520607142210661036808119080ba03446140002e281406004d000b03800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 768054361 1250 768053111 768053119
    0x1e080a080a18082a030a210903080402061c050a0c02010e010501050307120813030b06091302090703020c16032d081204020a0302030a0302010f11070803010e060409020d0c08060c09 79
    0x1c40d8844c0f4007180002d0520042400c0c10a00c0310340d00142440c140054050110a03440703030081c0071340c244101400842950b2000d00224604800e203c01b00e40d1004e0082c0d086601a200d039503880819104032039414121014203103009040005008017104254000041c07802642c0c000c010340c9008500d800e0a0f40d07020b10820f03070306d944807035400d118a1060005034801c070782c4600d1045113481c80035050751000c00c50603842502c0d2004000200080c9081110075260701070b941d610000c03440940c0d64001142c049001d0071039010907a000c58100c0100c84104140d10704848400e800900a5a4131310705821140000621341c0ca0700310040a0400c03240245010036202d5550041d2002d040a0f10b10070302c001c0401004000740c1e40709406441c0000962001c3c048944e1aa010354008510400c52200790800c1e5004400c01900700001005a18042075030342080e00e040d502c480242194507240c2c0c80006014100d100000781d404132404040c80300f00303d102d5a4074400c440c114004d88100c0d13950002007901500030201e4107500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 768055611 1250 768054361 768054367
    0x908060a090c0e07030209090c04210210030b010e0a080709150e010b09010309240501080f0a0605041703100f0b0f070803101e05150a020a1e080a080a1808 68
    0x10302180e4050f030390101c0680f80060a05d800a40055056842030794114060350001400740f2802107030141d100c041041441d200300e075140d0f0301d9011620580200b11500e04151359250721b21030981c0f0856540c174241030700030920094940c5401c40180c64081920400c1005403408440134620245001100c0498151030b6503050030380e10307080c5002c4d02c942c031103800d20781003540c2d4201c07580015003c0c034604c01201c44c0283c1003801d8095002e0104e42260f00c1078202c0301c010b03840003c0000c21034034002000000503510280120b05c41d11180703454402000c001c02c045040f844048200441f12805aa21200315082e00710f00c0480265a081ea10005109809501c45101c4082260300081004240110340010004440402c060f58400403680c081e42076118800004e0140d0408128610b030404440c0c0d0207840e10079101d07203808190000607584000b0224001c01240c0d42c901200d0050b25074000d003514694100c84000d03614100800e00030510b00088030941840c602d1311208640c889582d002c5544040d601503500b80c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 768056861 1250 768055611 768055619
    0x403090b21010611150f0c1e0f0c10050c07060c1725030b091605120708010501110f0a080f0c12130e041e02041b0908060a090c 56
    0x5080d406900c18a01103444418101800c00070000003074020081c0381d8452500d0814580c0040c01c01e00b0766194a42e5000c00d40040c4140140d520603460b80058207a17500b10b5403031684000303001e6030000405119098600105102d03400052000042100c0c22560f4140d0308402c080d64500022181d066459256001080c0b10300000142558001c5000c0281c40c107000040607818010321000c5c10b0201d5801807184a0400d08000410103080780c83e208444609003840324020500204603002401032071069000d0343c800408240c90f0050702190300d031407e5039032080c02c0c520305a031018104050070f05c110360000f000180e00d8009507130003240741c080724903485000d00700032029601d8181d03840e04070300ba050400d41c2040080b00c00707805041000010b410400200310781c441090914030241441281e101d80d006100420070413000030b401c03062010301c205a40c200960920020700110700106042e5019003055000b000b250502ea54121946104a4202408860b5181d6480fa0544140e521a0360010110002d50b14240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 768058111 1250 768056861 768056879
    0x120604020603040f05010c0e010305011a0711190b090f040603050d3e0c01020a08041206140a09020907110a020420130611210702190602011a09040309 66
    0x190444c1c092030725509100c215854042c2100c001c40c9840011800b2010b04590b0307960075010f080d004044115021680d44000d0312a1001803042440081030001c2e5071070b2042d0f043e51207982e01001000c4051141c132040d038a54a5440c5698018141c59220b01140800055145003d0280d80140e0350310401030020101c2489003a01c070625040540017120041000300e03e904402c6902c0250314602003801502c888920051041c2045a04000c2604540100b20a0303004203118200b02c03000c0711088801c960801100741040b500a010440019204281c02414001d50802642280d96050300889503170105844402c0c00783c5c0c00041c0e8401350320540c0c00021191015141135480300c40c0d251a0207541c080105a824101600b0f0350020300980144850780c06c0c1803080c0c07680540402d2101003450000c017088218104507130b00a0019680c40079080348001b074420210f44842d60585c840b5181d182c0300302c48040d111b0601070302070042214401c40074000082c4954640c0340038540d00380201c2c1c00d031702c0c0d40e02c106082c00001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 768059361 1250 768058111 768058117
    0x303051602090910140c0403030f0203190f0305060306040b011a0c030307030228020a0b0601110a05280809010c03110a0b0f0105010f1d0f030109201206040206 70
    0x3410300c00d800655500301507140c90941500c504010800b40c45014000324640c0304aa41e0011100c10549100042200000c4580d04846c00d403a007505011a4580d14480101c0c518032490300e201c6d400c4040e03185603d0a00390400d0003030300c10001d00d03202400141d449900741a51603408480103840c181d40400101b01d1024000c005881800c03490030324901d04030000c2d03905032441e442030f20801e002982c00503a110342082e01501400600792100440320200c800494025a02d402800001d01040500340200d85160700074a0502da000c00712401b034a1440c5210300340030741c0f20300f0104142121013000000305541c8030110402441c1c50740e40581c9860404030204011151144181d9080703041c040c0e00390702015003200400049002e40d03ca601c0b0b0400a00c1c00c54004000b030501030384001d0500c0680142101001c0d001000d118200266449041140c02080d00040f5030760000c1130610f400d5481c01e490401417002c040a2502d6400c01c0c10044c0300b805800400388120040f801c2400c1001d81c018001140041c5031403401 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 768060611 1250 768059361 768059377
    0x1e020c010905071e05060301030b06011b020d050d031503051e0a0b01030f050c060c061311041508010b121f020f0a05031b031302010c0c1d0a150609030305 68
    0x41e5070380c071a81d903881c03410155030490f00d1103c481c090766074107208050240030b01134803064a1540c199450b43d40c81c1c564008020748024180044044441c150300e450800a1034059001840b21140744942d0070a61741310108418200000303800c1491100b030495030030000408072540400104684042001000902003500710032200f0707070050007191804166892180c0d4065030042c14030741100d180d0361804510307029140ca05240500b60900c0311460b134060208409500080c00480791103562282e29141049035605401203501915103984d400c20a454283e800302a130341030300000c0068422030420014071080c03130f00c102d140c241d104649284030003800d68002e041c00d10a2890250614400103490340c0660003203541000044d0700441041a000301026491144200e440645455410105000d6110601e0a41c01134140201c1c0d503400300c100700510044400030840350f0845a000360349094a081c0011041d51081c12543c00d10f42450f0760035648500740402c840e03468840d103901a280d0307a000c3c1c516800c0002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 768061861 1250 768060611 768060613
    0x8041406010b370f02070f0f180f0e0c03061b0304080f0f04090209181005010f0e1807020f010606090504180f050105060114040308030601050c07150e090106031e020c 73
    0x30b0102540b8101c5000659903a03c03940358900e1001d84000300a1030049141d000c05d40261003107a0410444030006070000a0f60f01890306508032402181c0b24001620300c00311820a158500b041a41c00410041210741c1d40900850540c2c1c3c0903290b5a480500e800e0f405000310141c03071403c001060020300300d80010550b80e140201c0e01030500003091080f5403250003a600c0400c03210b0300082d400c1010b1405084800305004120b841a03617500b01040b25907441040c9016542c1030040c10550b42c070403680184103881d202074005180b003e03c840c1203130012042650503201c10002d4440c142c081c0620042c1030141000b0742d2003603603846004e00c0c68181040087d00118004200303801d501c1201002080c20802008401800303800041800d00306100010002010a540c81158400c1400180009800d500403285c0261091905548401703008810900b40b892640c04510230035a2900c200c0a40c17038100207074420b140da04a6040003140e984220550941c0e40c03030302401d106000f07280d40d800341020307a90740506103440e0008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 768063111 1250 768061861 768061927
    0x303030c0a0c08040806040303060b18040c022811011b020f15190f0c0c120602040b03040302150a180b101509050a051c0b04021302070308041406010b 66
    0x1440c0c0c900103500c05e400c1351082d50881000c0009054060050500404201f0302244c5450b120010164004100c071004500c07403500c80401d0b070115442081a9010041c040c00b4010104180202407054141c0c0705104446640512403481c44130341c0141b040f0000800c0fa0444541c511a0550030001c001da20144101d41c4156540b511524804056001d004003c0300c81c000340152281c1134402500544954400c0402c03c640d0002820000d000c800040b012128444546901000c86141c408003078090f640240f0007881000c4104800c1c15800560840084110110f64510313803103014030301040c1d0307141d02c928002c0d000c80ca40c40310700007841003038600f0390003048481070240c40c9031510072a000b56140b481d204800a00c2c04142405107260100e0103100400d42160b0307440c0ca41c070044405441d450190400034048040c08000101503442e46050110a8074101a08541d54805403a01a102181c01d903819208002d203200c01d0300400300c0020343d41c0d040c4c40e4070101503401d2017964890048640203584801e4007e800a03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 768064361 1250 768063111 768063113
    0xc0a061d1309030509122103100b13030c0902090f060d0e0102130512011a060a0c06020712030f111e040503070f031203060b1b0309030604140c0f0303030c0a0c 70
    0x41c07245200b11842591020382d07808082d000c11401e220340d40c44050701c0e500101800a404001c0b520f440a0b51510015196141d40e07510050b4010361806600003d2130800c0002c10b41203071080320b054001600c2c4298a2181d200c1d840d008a60b040b4001e610a0b15046a42e05507149010300e411409040b52a800c0140400c02040e80b0442c28260380000308031088240b100030080c0040d281c081c030718108030710f0740d60000c00069451b10400c000117001d40e500c0d0340c05000700007100e1900034400e18108410b00c0c1c000106560f0303441c5c0d61500c421402030442c44400002d00e0501070504d1400e0a0060b4072120000f80102800c01d071000c035982007000001000c40420a00c100400580343d10148030000080001458400d000e51650801c40203003000e05510008040ca069001d05c20710004400b075801070000ea251070b0744001c81c4911402d00d1480360f144103e51510031001000204505215081d00c1041090180e900449241040c40100e50041e400d0661642051001504240c2c03d04050a00c1d1600c92810042e00c03581 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 768065611 1250 768064361 768064399
    0x51303120f1a101d101e0923090c03190509030a030b0a150807051c090c050d030801090908040e070f0f0c020603040308040602040f08010605030c0a061d 67
    0x31030411800003540402508080345410341800c0f503808074900349038880c04400350aa505604c50a07802038400c0501c3c160305190907110380c040c85240302d8600001000003a80c840043d00c4071107544a00b80d0109203c3c00c1040403000f000351241064803000e00392201940b0348001d007507419000107240a00501d4040c0d050700d0100310a0043d14018a46140910354405030302078000c0c29607802c040024082c1041800402c82c0c14a149810b490b10502880d00303440680f5911001c480340d10610310302d03500420040350480c410210661140484600c00e094500b061035035003003402103540401c0f5001d400300b1101c000410141a142e041003040740d102c0e5004900c1c154596180485034481a258100050155038202da4407039048251710794184113308020b4401d9082e80d00003801444010401402c100c0020701250802c2603c4d010b8031302a000000c410002c4649a04100b40244024400c4610a1041c2094000981030030b80c010000c2d100c0710350b60306031800034013180c0310117031401914440e80001d00005007900400c8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 768066861 1250 768065611 768065621
    0x1110403030e040f02190c02040f0f1505011416060e03040f14030102070b190902030d1116080a0821040804140f010503130c0e010303080118051303120f 67
    0x1200707031103000b4807482d05030900c4103d4a0300c1810a002c0b07481044080c4c20340381d1340c00d1400201c50451400f07114000d07545c030105000d000c0c0c202c1400700140c200302d42d182280b8065040060003100d40306110214070341d0b0314011100c5001d10304040550f00c03004c00c00e980407070740c02184a82045004000101e01544507401e8189550700c10b07403100003850a07103d8144070b0780740054090100c2079001c9000354102809501d031101000c80c0604140080740200711044074000d03854120903c00d40c0c00409643d8103684054001c1c100715880d08070305541e80101c0c3c04294541d03888940c0c07002075a4215000f04020420350b03507050b40541c0b09031340f1103500b00b4800c00b0903410308001008042c032403445000d680d0b850398034100002600307102d00010948685440356921784180d81c4034013540d910040410420007440c801e8140008650820340000c6038a007001c4001000f896004a1824100c9407002c0031703c0301305032120044d1401c84405845c041c0d2141140c000c040046441100030400b40d101a650004640c02c55800341c2e003c4803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 768068111 1250 768066861 768066863
    0x90703151503140a0b0303121f090c170103110105030601020304170a020a0b0a0c0201140d0e011b0c030f0503070306121109090106030c05130605131506110d030e01110403 75
    0x2a00c55040e405919412042c041c0c10890b0b80c002444550017a100081d10780c02410041c4201c141ea082c001006180c001c80c111410542a0310302c0c807000d903155498400a803100401c0f045c041070400d2004032003030307044e03d00e02d6040b26000881d0381140c000c034000442e0181e101500480c114401480701280641603c0a040c4060445030010031a030300913071040c0408401940e0014410107424401e03904180d40181c249950a6070900c0c1c500c001082c41c2c100d9a0f940d000c0ca013310006146041100c1900784d205511141400030382c2080a41d0802d100324044507541c0e4440402400038a204203070300522800760014680220031403c012403800c0c0ca82e07103204c04c04c12529400f640c3c01c40304981c62a5a074200941c4158009504800910426003180c43c1c0040400d81445414007a201c420f10394940c0040d940d0018001d03003002003001900001c0080031101801451094101d005514040002c4090192002912240c4e0007409000071030a0500190001c0c07108016624165495044810b140c008040041000e1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 768069361 1250 768068111 768068117
    0x210c090c09060d1d06090a2f040b0103020409060f030b0a020a02030414060d0e031e040f0537081203012124091728021501090c080a0b0907031515 64
    0x4003085050011004040c003203000300c002084815802c0b2230b114105039840c008802d540104030615000012002441154088099039203000c4000c22110b55012041048034026031611100d40c07240c0c6448800ca119010f000c2000d40c2c4200020020100040258082d229004158904041c8a1150102940c075100b00605481d040012403003070640c03900d200a0904034103890403034145800c0262420090307240e8029544074035601400486040c0ca1252a0010000c440000c100d1149410200705030502e000d005100c45801001842007440c4565000c0c0ca0496050210400343c0030740446078001c2035422008142e40e50709a10301c49201806802800444240840d140007400f82000d060854240d000c00581c0e1000f55420400c91494103552242c4806080d10040006071542c011a000d03890414900011820441c0c2e40300006690482a44512a41a8561030702034003070347d5001c402c0048603007000d0219404a841c2020505440c0b180d80074018080d18035100d000c440d521504003030101040a8007400c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 768070611 1250 768069361 768069373
    0x2403040b01081507020c12120406050c0d020c03061306291801121202030c01050703060e070c2a030b0903030717040b070509210c090c09060d1d0609 65
    0x120b0010003c90080d1400c008030204503040ca200e0094840513200001c83c843d00c005520590f03001421300007041c000d03200d001b06956945e81d03008040c200740c000100c0303618940140d2802c2018540082050705140c2c9004028050680e508074a980001020f01401c1d00d000380e840030048012142d0182407c3c100541d040303074010b204036050801c18000e030082e910702e00101c040030040054040c281d00f080c1c2455406881b000501d04440c00c00c0349140107800e5059403a600340004d20502c560150700510540b0000303148050706544040040d9403204807040c0c01000707001540046205001d0b1402e0f100308042111549000080d960f031203141d0703004130541d4000c02e41e400000501010380d401c6104403c0405100f5080015864141c441d4203010000400e400c06002c000034100c0c1e8180c0d9a18030303c401c0200c1c03c1c64405e003061400c0022554996415241c540215016408100c5084000c020f44440c0c3c203004088516100c00fa50051000e03100e1f803007800700c4400201d90341001d402810320200d48180851001052 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 768071861 1250 768070611 768070619
    0x5030d090804090e1b040c0212033402010c142b020a170109050c0714150a0e0d030612061107020d050f0106060e0a121104050901020901180506092403040b01 69
    0x81c0003030003090b00340711b030345000746c6261455000700f880c0d50003034100412291296140110303140b00d030001b20940704c10403004105010366513580c61209810068517174001c0040d007210311002e81d621603803400280701070704042c000c01d0201b140e140401d12001190800105c0141001c91010b01a604080c031000e011070050500e2452010b50301301e04070b004214502c81403001c0e050080c0c805059100c0c907100540240054504144980d504001c0041c0100c0020052855440d19042c180c00402980d80a05014080d4149004003140300303001700c106454034400110007040440e515040200000c40031201c0e4200e013405080096680d40500040d0580641d0160490004040056084a81c250464402d00405a0b15407000c0d07212820070300141d502518100c940e0506034103107815180703d042049540241404104100c0701e1041d00500f075400400e0b240c14106801c01d004803990403109006c2d107900a5014801c910180c600601104a02d00c200803114000f5200104c00f50a198401c4a0a588510074400108 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 768073111 1250 768071861 768071893
    0x30b010e06042c120f0318010627050604050f061e030313030302070b070f06020c030913020406090b27060d090f0b0c030f010501031a060706050403090b03010305030d090804090e 78
    0x901d11011041181c2e05d81034001c1070520b4107000241c100c514561a10701240f440710f8003540410040d004140e103041c0d50340001007540c01d0b001e403600c074006c3d505414140403483da070925000d484d016a00420002e1142c0c2e42e101e05118030f44802402c66600300d0a0340c507071700d4800d45091004098034050000c0f00d01c4c8450840c2006403a01a882e4080d09206008000304030128984002804185601000244c0e4500744586528034500030100ca0950100d0051400309040445900410450f241c036114118034580d110b45c10700d01030240c0382c504520a0f02c0310030180154400e400707170b0707082e60f00740144400d040c0100c241d07440702201c5a44508070ba512a2030031038281404a6400c4a41c1d0000c1815002c910314035000481d407141d214107100702d6041c140c490540e030480c02e620001c044a4000080c000c5516649503007000c40141c003080c0c0e016400724220340d10104810500d04210b9050384d400c400110316044100c800040208031060054036020b000307001c0403c00007450b0080c091940240d5001b0302c40250620100c0d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 768074361 1250 768073111 768073123
    0xa03050f07050d0b010c0203100b040b0105120a05040314190e0f0d060c051e090406080307080a0c03120203090105071d010912060b030d0206070201050a0501030b010e06042c 76
    0x81000110030404101c19603030300c0b5040382e060440f01030002c1210001d1100680d4413840d0100c0080d814000e040800b07070380252591101c841aa411a024070024200307100664282c407170a05040c0b4514960030000b040b000c9207411039500f0905c40d00e00428408850000a202c1d07821400003403414035403802010700844d0344803c500300b41d520112048141c10301944005082d0780784a81c1f00414154955841d65a0070b4000c40a94082c0040c0455015000b850801c180d00303203034031042807948a14640303100031030700141c00410b490140354411400da00e0303c2c09130002074841503069201182080440181c060300d9549900103540190034800000c5080d040c00d1031b024000306401e2540001c40e514130300100d84140e901980e00000c076401e41403c11004141c500301031000d002e03188020f5406115501d40e896096a001034894420b00c03296008100701d0f11011038036015030f40c0078400500125003040052040864100c4404e4100800800010748240d1700045aa51513a410024503000584502c02b1007103054180034ac = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 768075611 1250 768074361 768074371
    0xe060f0f040e0a0506030601062f07080c03061609051e1c03030b0d02010f140f0703020303010806130f0b180d0915170c03190509010213121109100f08030a0305 70
    0x2507e181e40c14100c0092003035040d0030843e142020710000411103106030311100150840303190b058480040e2914080769035803140c000daa6000c0e03c501c200003406041c01c00c41c0391000004540c2c6917200c05140608100c1c403001c66021628281e030300c00160803110398441d202110141d445c03947c110b00103110b605014080f150050102802402400c3c01d110050703a112503080880c00d5a0701740300d51180d040c144a00054081c180a50800c007000240c451b06064000004d18102d07054101268201d50394450340c00440c411a503001002c040010032f480d00040e422050003a071002c0707100c2d0b4503030254252565062408081000402c04150040d10030f1243c0e804e0030002594000d2a4101580102c1103004843d5032058010078101004001101189100c0f01450400f041c2c240c2408042c0028240144100e0003544038810007086080c000310001000d003025200600c0107500407a240c2c540009007003c0c051480401480058070a000420120b84150070b46000809442d10034021a265450079201900300c0f440904 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 768076861 1250 768075611 768075613
    0x20c092719120e0f060a030b03060405012a020307030e15030a0c0206181504020d0b0411040501090c1704060b0d0501020405120c03070605070f060204080109030e040c0e060f0f040e0a050603 83
    0x74061290340310401090406101924191b03a03500d40d00341c1c200d000301a10700c40f42c0d5140c00742ca4140001e1100540217548031584032025820080346c2141c49401c1c901d00d01101e1405604140515004203000d58507144450401400517490440e0450b0700b64466402252464401540ca2840c4030090340d04004450780302004500e081e1400c1080e0702c150b6618003011040040f0006114001b0342151640c1824060342a480180d00c0000d09061400f18051540500701c9406a81350200005a26016010713018030000d0580b44c0038462a8400316440e00060002c00130345800c0d071100b0402c03440352644803a81000c0380c0a4000140c49034105400c2160b014201a5181c0c015403054080170600d030350108016088034298107005a645295150036405640440c50160619102140c0002e00d001e041d0004255903219a80b0741280d0340000f1700704000c849010b44104001403000c0301e0f985040c02c0220013058003040045040741449828818200240d00c50f0700052103d1b8128020b0056646403800340a41041c0e04070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 768078111 1250 768076861 768076877
    0xd03121104052d03060c0a02010c09030317100b0d0f0f09080f0a02010b04140402030c040515010f030f051314030415050f070218010f06020c09271912 66
    0x4268a40500c99200a940041c03412034207450501075980080c0d601405681c100e140c550341b8611150407403040702d8055420710385120300e041c1c4104c03461019298943c503804410898003c03050003400e0014103500550051410100310051008040c103000400301030089203038807800c0c1107041500c408004c0315944500701080341c0001080703c400d451344a00c03182685619656180401c0b0302400d0540009074200e803030300c0350b038104031488001507038400c5000303400312200303242068184003c0700d40c12103120100c40918980c02d5a290300c500104000c81034940b801190586200420340c048520035280c0c1c001c807001001c6102c2c108980600110b1044145102075070901d0300d08a9110865104010800200500042d1000d040c1420f2010740c0c0b2016006405014488110421801803400a005011020352444400610307184005211103400e5400b501c6010b00c0d844035241031541d448514491590601d5a11a40340d03003c40411556030049004400c0d0346d605603070f81c1044410840c240000b401040106 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 768079361 1250 768078111 768078119
    0x1b030303011d10181d03280504090f06080f07060e1309122c030c09091c03020901090603060b071424090601140a0909060b0d03121104 59
    0x40700c50900307185507441a140b801da840e203a00402e642c185801007481007139818130b80101c04004e079008802001c0086102107003480035040d002e07981e02500d600c0310260504018006000c041070300913550fa013262800e10341c2c11300f0b40b600d0f0084103603020140100141a07440c50104110103007081212600c8604002a10a040c14a58001d242029a0f8984ea000c0d00c022a40e07918521075560002000780d401c10260000031510b0080100004016150311840841000303003d2500e01002e5044504020003c004007001d0640380c0900c01e003030000905816250050800e08011000031404074100490b49690050303880038958005030400c075040d04030728101458210144000d007084811250f0480c1c01840d1020312401d6a2011447d000b544100d00001d204980c20b000d00c00060301480c10302480a55007580c000d0380c0c83d9814141e00340d042c40c501c03503400b40790a08100607200480c0d2103040054041d08001c2000c01c910300c00b14002040711442100050071900c203001c0984e005200307021042040f44546850301e403170 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 768080611 1250 768079361 768079379
    0xc1d04121418060706021b150c121b0304210f090603150302121b03061b0c010b090c040501020105070905030d030e011401030f0c080304080d0503061c051b03030301 72
    0x904401000c04000b54100703810641c0e60201a5540c00d5070044056503a04c2948000c6000140c50b00080c00c10b5100c4c0d0300b140c603001e01c0f07280106480b40b03080c030201c64142458140200c0c0841e5000e8002c061601445c03c00812069812005510580c0112800320001c03d003480e000e01050607000d003400400140c08035250b41e1692000c01002101c155103004126210b216410140304a0f85a000070351040e140100c01c08002004122204080488004210b90340104000d00d82c54580440ea4020309800300c4084440b8020070901800f4540350f01800003604600c0103002c0f404401050310200341d80c1d4000b2a040101d5a424082c16034480d5031454034078a40381c034000210769030f610051031280605850b032006025020096209850513002c460100e54107594a01b01800d40282c04202502c00003180d00021401c440300004603021284003900030002c0c0c02d00c2a40444850300702906456128000302d003459242a005803241040da4020f201902c0403404020100820742e00c0e040b601070281d00284010459518 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 768081861 1250 768080611 768080617
    0xa0905041a0402012d030e0f0a0f150504050102031602010b0321070b0109060503011b0e1e180603060123040e01020903060915010b03010308160c1d041214 68
    0x1110302208000c1e860343e00c0182c40e4600c03445c2e00615000328554001091102143c0203a0518a89807020050680c5100c40c40307884243e15035a941aa074050f841050010300303040c41482c00d69001d90001040b40700c0d02c0a08000f40e5500340e80a440c240e4022042c0f1803401e0320b004140103030602c540002c01c400a10744011a1700e9201c2040d00e045584900c546102890f011407003128090790340040c1c0c40301d2541e15001c0100080c00e80e0301403680290f18241d241c40144203010201d038003140302e580300c0004d02c00c107501c1000201100c03d03444503815400710380f10481c2034580840301e600002c1031036003007001c40c40d006041c075142c80016804414038000100321082d265170460024940b03400182d03004182d2202c42c3c20520b0291140040d881d405100d010100a0700250200b0001d4000025110f510100e90b601c0c14018480e02003030001514013030381004000b030310035400306c0e504a10178403654043c824290b40e560120300d0318101810051001e1b00000030801006803680d00032032030740101d0410f5040030280d80d01c5440140 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 768083111 1250 768081861 768081893
    0x90f010806010e0d0302011a0a0b0d0209030a020a030605070e041a010c021804080a12050f0117013e2b060f0b12070206011503020d020708030a0b0a090504 68
    0x1040c032502141099206042c006507200001d4410142c00c03509240090081c40d10300000c0c10b01e05020741c9040c0040c648010b500e02110b194862203410b095110303086800a5002c402c002e82d00d0310034480c0c3d040040e200d20500c14001c0d4040c1c0000904c034504848058161000c1c0124944224071300700028174038030042c900c0d060001da0280f030940b0800078a8400300b6050701c0c0d6040d12506c1d1041c0b10302000b040003002d80c010064000203a8070b03030503060404c0301840e050303810030360300c0c101c403089002c0042c4072031042c06420540d180003c1c0b0011508898540d03040070207400011100450122242e04140c19801c1032400a43c0343c160000403e107015910900300500500e0162000303c100400d4042c07004022140d00208094104440c0400d00d486d0f5403011606640c0c0022842c1c0424804540060030b0355001098181c1242d1540e069801e051499001c100c000f0341c010584500055424454080843c031204061441120783c1c800006440041c0810094428142e40c441a500c90503d010000003419145e82c8550315 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 768084361 1250 768083111 768083117
    0x1833090b0a120f020d27051c020109120306051e0d03050304170c01021308191b0e040c080f06040c0e070e04050406050f010609030c0b0d0e0f070503060c090f01 70
    0xca400c982c280c1d80500596103c41514600114a442c00d0329071135400b00c5a00c810034819221901411144640740c4051200080c202c0c0d003000c0d1058140001c925a005800b1100b0310002408040c11764032700b50098605040740c4002951500700344807508200901005c1072059890740c800107950003001400031840058000c0403c174010000c2020418025100203074056900000340d1a64008400b05000b504405086c48000c4802000018440400b00d0002e4001c5c8103600f10707140c11031003030f01c42e0301c215080d0f11102d000000c041840050760850355040ca0f40a14802c0e41959001d526013291701d80b800a0f0318081c404a5000380c410301001402c00c030040e2040f82c2e00c4081440072070703441c1c1d070f8159100d038420028641c0090400c42000200700c02d9510441c4160450114522603988410044644108600000300300c2c5c0e40420080c07040b0b800200c084c0040701d0048c440800d400503807103500350905c1d2040105640c0f40e84040c0302803199103001e1040c207500c0307030b00600c41504240c00780c000240e21000b000241418 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 768085611 1250 768084361 768084377
    0x1e0e03040510021204060509040513030e190510020c031506010903030c060f050c0c06010603020a0e0603060d1e1115041206090b13050c0402030c0306011833090b0a 72
    0x1c2d81c0c001d101400c1c00c150100700f1107440e150340f000c001e04580e0215444910480c602030004d02110b180c1c642c0c4106170f942503030341e65100d00060b40038881c040c8403400d030700c06005440110000d965034601d000140c02204580c003a0075220700b42401c3c90724160800c404d00b8003244455040000b666480744640e001c0300e81600c3c20f01e51000c00da0804800900d650544180a1030600c0e040000041c0c03981700500c0ca101c0c07448101ca0b02aa0386d50001ca00f00d0192014020000d00404041151840d14001031600b11000500c06070b616030341035480d00601c90f64001c5503c030680003400d10005210094032800d503024400e84000c52820402140340314140f0480c06200312001e00c1100b0750050025a41c04001107550000c156203144c1030040d42c542c50360307008440c200c50510072030354182c0719814180203483c090089500300909503100c2600540744110b001361440b40c2069012400201c072010607020394000344031109580010000780e4488003090036502240014003060343e4003003140c06820402c9582d80100f81ca40031034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 768086861 1250 768085611 768085639
    0x20f1c1e0f231203070e011727150619030b040206030403051e0405030f0102040e15220501051c1502030a06030206130608070903170901050d0903031e0e030405 70
    0x40b501c2010b011602c541c0320354a840c66003841c1480c0158091003407503d840c05038001d40001103900c1e1804100c842142084540070a00f082e008200e0b4540d0140300540c40458100c1507103400c0c2c034011020740d0360498402a1411311540d410117000348900d10300c8130300108070240d0854a4101080d100600024066040000082c0606200d481035900d6400c441400150307145c01c8041d0302c03115401c20700540c0d1103405001d04100c0fa025051080b03c044604050715076005030b039142450034140ba0443c04150304807001d03031703900c8c0e42541d03140c41d01e400d84400c000700005d240c2d4100001c1c00854840586035000d81d00382100c4410202d0305000500c804100403440c056625030340c044c081d0020781300300e1740000e400107004a25001249286110442a18038554501c60269145901107030411051710000c6d02c1d070b19142c0c041c07107200300c042002407010280c107040070340c500858034515070110b942078401600040d60750f1103520190844640341c3c0c6400b003000707c0d05000b00360302120840d032644503a1040a2107108034240b200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 768088111 1250 768086861 768086903
    0x1803030c20122512110103020c030d050115030b0303030406050604110a0201020d050a02031e060a03021302210702031b0c030f0616020307030806040207020f1c1e0f 72
    0x4401d200c80505080c0c2c1041d201030a8a80d120b60035007050030810000002e0400e461018030400d42120030402d44580d02c454541c40d6011101000d130b030704504140d0204010401201d0820080030142404400020300358940300c0954a05500c030a402420903040c84181c40d455600041501e4010342c22a6000581d9202e5400003801003001c803207040c1a90030302080a41207542c040d800b078000302c0d5101900b48429511a1900310482c402100e00c2c1d02e94030460030f910580080030340b20080c0d00900240150ba0041d480350000344042e0700a00855501c2900090b00051040001e080302880c100c001d42088646d00746080042e440b401030311854450000400c1c1e02c00411002080400405800035042d5658400716214650300d8820403103190100725214581490300714130000441e4001c40d05680c960300c0d0b40d200c1c01d0411002c3c2d4054882a80c2c40450042c01c0251507641081805252103030f0030010a0070202450a14450017040745860343e1126661451004184034907140746610b648084d51038141d0400c02103417 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 768089361 1250 768088111 768088163
    0x11803031e1a0910120b1515191d06130315020a020d14040e090a15050912130b091c03021f02130501030c050903030c0d1803030c 57
    0xd40c2802e2200081030380b0b40041903481104030580f410700080c4d80700c01801200e40364500c940c0958001c402034060100e00301300091600070300e405100ca10b00024400c0000c0b80b1600c02d0601c0b403e00f22000580513500301c416442020201e070755050a5095841e80344007100c075088101140c5001e146c0000d07c0c0c0c403904030000c1e404400756a01042e0480f80c0d28290010000940100200101502c150780395580c460b405240e880b00300c2075080d0007684c5814208580b400011101400e40e001c075114000107080042d402c6011041e014603113400000d0780e0700d040080c09103000515072680945060400101c4c00100c03907401c20b041070341d26640b405550380202c240800c031040781c000c2d07030780d843c007640101d1580405a000c038070002c1000c485414000c16020f00f9000e08100d200f01601c1c449210f030120030400c00c950283d04004030001250412505080c888000b003800d550180580c249503400c08180144465005a007403102003d00c2143d040d030641c115a00601000d9000d400600580c012600b00264201c0380ba5036 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 768090611 1250 768089361 768089411
    0x3204090b0a02040312140d02070221150c042124020a0e1c032a14010c020106030b070c0f140a0501050a020a0e06070203010f0e030703020705010201180303 68
    0x20010586024803400000f900709020844400c4420511101120711941a030317560440007201c034a241440243d011402540155822608039010587c0c060080045d080c1a001e04103000014041c01c10141c0c0e2928880c1a0060070501000c4040c0010301c12008900403d034440c00040c04050300707a40300e5091501140f10158001400c02048440c030400e02095a00038103012061600c0300d400d8541214208040001405041c10702c0506800220700840c3c070580c0940403815083e414400da01c50500c40319003c0442005090b01c200800000003100240309101e66203106400703100070055142559103003018030b10040c2060003000325801d0b600c0705100541c03212200c01c643c8440344d0260180180c10151300d9a00c0c8030010340700ea520b4a400180c000405008946071050144c0d104024850584200030081d01710904c00d076059961072011003035480e6540315018469200724002c0d600d605c0c40b0b2400a1070414030f034020904690401320501c04a42d090086400740590504010030800c07040240c035042e417000d0020b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 768091861 1250 768090611 768090623
    0x61006050d140c3622020d09020f150f0d0f020a03060905071e14120f1603090809010c15151d010503030301060503180a1b320409 57
    0x306020030300ca01c01006104045000d2240f9000c41c002c100c07400b41801818103d400c8045241000b40303c135244c00380511828160301000580c0800398184003204030781000190700d5809070f8035070f001d82c2035207002c42c2c0052518500305c8540c3d500d01540040d02400f40100b41c0c1f01050254081812940d040340341c1c0068070503495440e011502c40088001c010090991441071030b480034a46404100790a10405c1c01c0301d00c540103000c1c80207905a203008110342c09400507400c00380c2d907202840524014044800e40a01a04c9007040364860341c20140e101900130010030036900c0500d81752100703480019100800380c46030a80242026001203a050602000e656000302c01c0b4201149000300e001028ac2001c06070105440c41c01010028555207004100800b0070207008660b407540c03040c00100036080c440d40045502880d4642601c2c0260062100f062901480003012226080050301c00d08001c85a200100018020201c68440d280c442d00c0000403014000c0000000007002410b40780c0498417a0b0f005000c010b54081 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 768093111 1250 768091861 768091901
    0x61817030403120213151704081b060f070e0d0b07021c090303080f040c0b0309070602011107030f20070905040c090207080d020d060308030c070201030e061006050d 72
    0x504120a29402120708902281c070a408011040c034080c400c0da43c2032103011034100070712414552074100250000d2a6141041044d0301ca0262074000c61042a0003144070360401521101003580d0900c102007100080300880d80080d04001c2040c600009180d00304015042c0031003585090000302d5500000f50f14050b010f0541c0e007091211013035000a90f00c40710603610345994884085000202e403100030750f11001d40090f0f0305402040d249400403800981051044a44030351403030780c4820202e4643c1084410340015040001e04001594080c000c00d01424808a4120316060346594080c210303100c150501c2042000f03024400d45c20300302c526044411030780c07401c044441235a034070564040607000850b000c0703400e00c480c4030001a03494181c0c000d171100694014011410200300c41c07402002900300c14405480e50703440e0781c000004200013000450040c04195000d60341c07a42c0600000d03080d00c3c104445561143d0260f41004030500c022122041618024070744903030f0750028000140090607120910b04030b594500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 768094361 1250 768093111 768093143
    0x61e16050c040509060601120209030c030114013b06011713110d12110a0c091d0d0914032a090f0f0138041703160618 52
    0x103140c00004030700700c03420b10041c2d8a07009000e4407080c0c00e460041c040b50062150394000c101940140c02d40580c007404840d10000e02d48000381c00e44842c00103030441b503404500140034006c0e0310a920052549543c1814000d0742c0c1000d4044240300328003500111482000300801c0d100d0b8400c10454155501021028045007007007200060a1011400101c0302076110481803c83c40c20050f410b094242d42109c40000c0c1002003c00070f55203e00108500180341c015851442c00007044003c040e00038050050300002e030450710b041c0740380d210412031000240a07440303803c1b0084041d0340041c41605944081380e4542d15500c00402003072520400900200110841c4064941e600682903540005403100302d81c4039602e5116900ea100304148140c3e038024840000e180140f08442d102041c1c0003c01091210024200120383c0101e149200a034000036044400001c00b007004440e0982030094040025001d1894581e03150f106030302030710201c5402001944c0b22040303800c0e2a007162030000e40f801d40081241d0000020 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 768095611 1250 768094361 768094363
    0xf020d030e041b090e0906010e10170705040f09020312130305030304120807051216200708010606140915041a030601020106172e0906020d050a0b061e1605 68
    0x1503684160001804c0440000d1440c0d50090424000c40c3c04001030602a42001484145450000c180c2e4100440343c101c005404801c1180300030041445001a2041074141810842500c5900c404805014140780c4146e016980100e41f0340c194a403200342e89580d5042050140000780c1c0503a101410602001c000c00080c01000c50680c200080580d44d0200d080d039400f84156000d000310030340141e50003912800640c0025000c503204942c0010781c28020401d560a042c81e1030070700b0302d081c600300a54100d00c408200c040b00074040d0f4400780c40c1506086400101c4000000e4282c0503a000ca54400c1c492142d40c842120780e050101d501800034481c010000040700b1605031080e40c416150390b40190320b1310744001210181e01c10030400d00d825040c082c1c000c0340350440025400a5800110700c070541441400f404c1c0340500d070b118440c00544181805a220b5515415080407168001d003a52042420000104401c2d0f07550f808686040d164040011400744400c0d10100c06402944c2d00344035074000700c1c07100794240a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 768096861 1250 768095611 768095651
    0x10c1e27090f2d02071110180f1802031801290f06071101021c02072301200f1b121506130b030709270f020d030e04 51
    0x4641c4000344140036107280800c2d414085024001540c90000c1c1c815101520f0701e0b0004c01009000c0d201a00c0d100d80d405000075080c1103059110800306140030700c801d40c16004004000d00608031141040a00742c80c0500010700301080f281d21040c090ba00100050190240ca040f49200a0f441002001180b41200b03522159140e40c0750010606404c0c0c000c80403107450229055159200c3c0608002e0803d651590b03511a139030018580c15040d401a4115540b07201c2c00301212644402055000780004e41c540811241c080440038115240b02000d11090407403070340c01a180d620100900901580c0c08407114141900700640100030742d02d2401469803600010000d41c1c0f02e0740c2030a01c21640c02c07588250740380c0d1595079415601c1c0041d04d01c106c148000b407020300d810f40c4a050054407981011500e00c05900c000303420001d0f81d420121034159101c40c20a036102110b0070013980511a81684000300d0526181c002c4441b1010034000d1080074881d203260b04041c46414528140710b40a00140034145090404041b144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 768098111 1250 768096861 768096881
    0xb030f300a021903030b1801140103020c150424020711030109030e04150f080a060c080f0c03071101020a030f0e03121302030a0203030c030309010c1e2709 68
    0x2050904656050003840084030605003a580080c1088107800300590364001003154150181907030303141c8136503ea8449020507a06400114442c0000d58140070740000320002120805040500c14020440c1940e40090441d07050000e04100c004076036a035180c540d9030200d48411000c54484900b02028021b05d45802420aa503c2110b609144001782401d15089414409021b0300041441818103c0d904041d0b2108000382c000804400540f516415000401d6a265002c603840d540301d1040003050100350311500703210130031510b03100c0854180840f0001c500e94002d003d4046440340040400c8020307010380c4050141e54491002551600c0d000310026008204111641a05a00b4a04542581013000c002c641c200100e58540b03604070380711a00d45004034841940c04a03014480e005180c009a64208040c1c540508a140151b070b1702e181c10b4505500f91aa0244480c4c04e0010880b40b421b06042004888a59160a4500001241d5060a1103201c011f003c0c0f00d46201d400610501144502c001d8101210031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 768099361 1250 768098111 768098173
    0x12050a2015031e0c0d020a1d0d080301150504090501060203070b1602030a14040f0b04030606090605060f130302060a030608120c19060609050f01030201300b030f 71
    0x1c00c00c04800303400c15220440380d800075110b00701407075048901001669a0481d60b99a01c2605040703800044030100c0e17001464200200f6002ca060781191104a1242d01300e401e0103036288100610942d079814218001030086907e40f801c5040017050700351090b01960011700c80c1c00003e10542d40c0d1610081c0d02c0c2d9002e88015038901c5003583c0007606086804400e901c415406600440c03800d0014002150248017502d40140f003100304000000e011030324903d502c0060500001d000ea80c45103103103041030889074a071b40100016070078800104440c1e0b5800040c0c800e91503d01000c00e9541105000804104005420080d84000080346046050758507a20450607603c035901101c2c00400d00c0c09038000a401a440d0368107096004034004d8542c409410480c415441c80344402003030140d02e49114405540f01101d1038034003903560000410666034081ca102c0e07888094410036110b4050340880c4d4142465245045000b0300380c40d41c0d05c9908a03101000424110a5580d003984d2041410100600e294079010042d0204 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 768100611 1250 768099361 768099379
    0x3030507020618070b070f05010c020c100201090218091c0206100501090308030402120f0a0302010c0e0f090103060b030f12090f0a0b03160504120b0105010306061103030112050a20 79
    0x102d81544070300303101001c10361001000c00300d10f0400064880d42c01b015045884000d82d0b040748000403424002c6940b4103d1303a4008d06400350b20082400008245030701d0070411a030400340304902686458280c90804a810124046e081c0c0d10409002c1c0b0340714401d890040d00200b9581d0302c4800543c08a4a01d02504007021020485550361004403030314042c501001c0e021400030000701d0010310f402c50240782c2c2c0580001c141c400084025601a00302480c4440950260351200c0c0c60140d07055200c0818241304d201203400c1a0050b018030b01003481d01030305000040519544141c0d0500543c0d0800512000e502c00030b013112810030600c20020115002078805a00804000107880128544610384400f61400055110700315a00d0740c11040f110403481c451142070060400010840c1c2101280030751032107000700100c08855250000050844946038000c80c00c102074608460f00215000c805c60b0f04559858800c7d04c03110002c1c1c00c00c139042c90000760004000c80d0030080711809c81d0003c1c10418050f00d40881d0100e0f1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 768101861 1250 768100611 768100621
    0xb090109091a22030e0a0f0b1b0316030c150b1302030714030c0a09080c060403030806040204090501120b06031c0c030e040c200c0609060a0c06020403030305070206 72
    0x9440078020000c003802c0d41c01c2088034500403954101c1e94064802c051028020021901044005a000c83c0503000141060f0162420382000c45c0580c004100d00304411448a1906948030041c6c0a546044030741c07200000040d840c803010410940e43c10080c0700d120390380300034980d1030302414842915404440708480c4040d2119029034a200305140002c01928016402501401032402503000905000600800300014074040c1a80e4000d507100d528002150f69642c0711400c405008400d0581c0710b880194005080104241c07148001c1d0703800c0703e51500340582c580d02c1e80b8000a02a000b44e4001000c428588400042d00c80070400c0d0034140f00d8000d202081041d162a8141503c41c4501c00c20009a1000f0501e5081704512421074196201d000e482c18420b00c83c080c000080540c3e100c580b8040004107002800d00540c401c909031901020314400c0140b000c1101107021800740c0c0a00c5c1b400d64418030740801d8000d10203001e501851440e80c2d015070215590b40d128a000303001800c0690b06100103100d6080050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 768103111 1250 768101861 768101879
    0xb240a020703060e1f15060516080301031208090601030203031c0b030d1e02070e2805040312060f0312030e0a05030408100f0e070512010f020c06090f1501060e010e060d0b0901 77
    0xa450302c0f0342e18921000950410707c040da1103a000500906030030100041d03070070104e00c200001e98042c601c10055820080b60b0b01078014410b1784083d0a22803207412110040005a600204483c1d400c00b14026002165031000040303001000c8104c1815058018076001c0e40c0303840c1d4070504081420b8824ac43e800401e0100c00b01c104e80d6810346008042c001082000824003a904803007100c3d00040c081020540f8100344940032405980003543c0c02c4001c04c3c0d4a022080f8580340ca4042c01c000760400c04c142d21041491078440c4920aa0140c01007014103903901e0266044c603c003440400c49036a00310003280d50b110b5455445d240d4410900540d4031f0358501e0203185800148003800703100711801552008011850030302c420803c4d03a041c0241074601c25943c4010368980c11045001806000c809030b40a040107103091710345241480c0c01102c044829800001e007000341980b4141409055070034074a400c5070a0741044005907144a20700014940c48180400d0000c00c0c065150049060307440241d600030701076681c0300303104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 768104361 1250 768103111 768103121
    0x417030a09031707062a02010908090d050c0901080609010f05041203051918050106080a02031c1403010b1306092d0e01030507090b240a020703060e1f 66
    0x103100084000400b0004074034140d0340f006204a1440c482d40c64010135a444070215226500c82c03c1c1c0c040400410f89000c0490078090319071181440c0002c0c41100c100c0d5458065502c11452002e2007a01118551010f2103410460170300802005001c0b4540380d6102d41c4050740d640002c40b01140d15608203083e00420100798001c2c030740110382c080883c1d481300b80d0650081d8080d200042c00800c6802078041e500401210702e015020781b06030030340807054828505003415420740b60303180c01255a50340030282c3d01d001130b280028010207050118106000c83c078036100d401c40d02d1282503c2d5003802e004d400f01c00450713142440c000401c038401c10400010205d45d43c0e113a0584459941748200c0e074190001600d0703e000c8444801e8002c02484004101c0010181ca900c1611003c444c20380040c0c80383d40c007a1406206e1141d480c410001c40307440840394101c6800e40480d446420214032069148140c6000c500c1d0100103008109220203981c0c00441440505107884110303507244c05010030f002d004580f8540202c813415441c0301e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 768105611 1250 768104361 768104377
    0x105060319020d1103100605010212070b160908060403270b03160203040302180103030206130b0115031e0515010305270313090b0f030303130b0a0f060b041703 70
    0xc6000031080d0200201e06440880940d130140214081e241035940900002c1500782072803400140305418a00020720304401c02c0d20030020003000700401030201c4d074807000d12940142890340d9580d05640300326040318104200d0b4005060381c07040c075090008154005c02140312403180c0c4c400c1085190540346201082ca52180300b0424103440c104007091241e5104c10741800d00c2c11040c011285016030b03e0740410001c82800002d084911000c000500c01c01d83e050041c1c1d40c2008103000d4210404800d03480300c80d1140d0040c403480c505010b901d980100b010340a40c000d00880222034800c0311408001502c4c0c3c401500c01124040d0701800c201c0100c3c88a98007074854140114070505023004200f40c0c203100c8c2c0003210006039096509102c01c0c02501509040d1118034000b40244142c08200a01b018050080700c0480c521014440e4000b0720800004499030b41500f050b1603002280c0348183d440d0401001c0003060601c10b03001c0e40508061010a03201b6543c8010402c80e29050300e04441c01c6100940795849000da200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 768106861 1250 768105611 768105643
    0x50a08280807080c0309010e250e240109030f05060601120e0c0d0215071202011802031005041106040f05090702030405091305120412060c0305100603020705030d02030c0c01050603 79
    0x4c120180d507510702560f403009101c000001c3e5501e0400b011481c1c803048141544a03603100040001c400340000b00c5c42c000600c07401440c0160750414001d01501c503031241c00c1d80c0e150842c04001199a60b84140034880045810690041d40d400c480d081c110307140c003000c80d0620f0100d41210429001c10f102032050700d07441c810040c040c003408120b0004115a02440d420181d0380490700c0b505005241d6465801400358511561804c141c1c5101c00b0406803d40d00c41900101040d40000707601c4000d81c402181c5202c080e0fa46503000103040c0d0b20f500d0280b80354100b040c01a034100e200898041440b00d1031401c00c002356102290260129074a42404907540c0c0b045014954000c030414020407942c0e0f540310b0640816610907070640e2440350040f030302d1400c141c106501080d43c403400300c0024018002c480c89a00e0f000070981c40d092000e85480a424800b180d001d10503034041540c000380319400d2000c00d00640700d040040d17070015907072400c001300307220080e41001340100d11035460131012468900d00065040c2d24003485038 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 768108111 1250 768106861 768106877
    0x30d0e0705010e09130b070c0c0f03080301270e030c06010911070f0f020d060902100903050c0d1b030602280f050306060d090c06180509040609050a08280807 69
    0x1340024128040c01d58035400612240c600c0000d540b101102c2c0c804d000d01d64450b0301443c450704264071300c070300340d40c0c001c1d012001d40540c01e1002c507030301804403415500d0000159600ea1500c80903680386030301d070301401099203291040228071254044014100032844808a43c5940d8854508a003102c81846a1241084e4104011000a011b0824011a0900400c0c0406200c032060b0080b80c9a81200302c801c40c0c4483d91070100d9030451030311010101c0c4210080c94161101d90942d550326035508005820944215180741090007008200540f0b0800d1458485070001141c0c0e8a1030980e0181d040401074064401996403007041081c0a98420341c43c1c1d019559800c84200ca030820280c03265440a020b86401c19410054900300a103180142c400702482482000071381d078940079005103121195042180070035124041006566036804c51260059000400021081d0380c9182403891300c0301802004024880c0882d06140f640c1080c00b141040944c42c903d607030060384003008100c50700307a421070f0f07040040380d141 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 768109361 1250 768108111 768108137
    0x150b03090c0f061c0219080403020604060e030c01020f0a0e030f07060c020406270c030b090c0a11060708040201090504020a120f06050a230306060303041203020c0402030405030d0e070501 82
    0xc5508070036941400352003241343c03001e01d40c03103241101d404c41c00e043c6040b0340004404031ba085070601c070110030111034989100e160502c1c0d680207403640c1000d40080d150a8403010296031000045c01103a0b003104a00008540da0607443d080b040c010f401c41200440800c4c6410520744441c20701041486e1656100b102030140141005070a880d6450251030a03078001d5950500400d90014010031141080f02c036035018081100d83c0f109980076120358440080806003000039511058694130315071500030220220b801c1d1209408102203580c83e550042e15041446400140b100158000000a010b14002c1c1d940c2c4941d1782d03c43c0240400d07072240d5509603001a151560361901100c490340444259801e820001c04c03c00e680b0320000c0c400408030742100300310009451405d4900842c80d880701104140039800b400c3c02d032400c100025180c0c000e43c400c0c2a9502c0c039007116481054420301c001c01808400510440d1070782070034240359a40703400103d2030071b1506203003181100da0fa2200089200031114140c0d15000e280d012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 768110611 1250 768109361 768109369
    0x110901060503040308090a1202031801090b042d2d14130f0f021803060f1b0903010603030804031d030d03020a0c060203010608100f06080406021b0a06150b03090c 71
    0x200030607400b028098021f102c400925407140a1020300c29a6008503201c642a54007006020240300e03e4905000161754104668000401030301c04444034001d8000d00d00c20392480b1400c65062a00d06c103801e040001c000801c2c0040d805c089869010303400c242801c15241058030781c80424545001e60b08203802d0140502407940380482c20306058000041c00071405401c10b404003020b40720080b4a00000c250045103005101300004c00e0b41180c5a4120300800d100d0414070030018032803a02a1540e8801c0707068101d6100307840c10010448003c40c0020b4020002e00f40c1d28100240046070640d001c03800100300784501901c1d103e90300082d041100000300600308900000301c051b0000e41c481d05c40f00040c808540001c1012a0003032000e90300030026519074260600d03004018405201554000302452070034103009001341540503034429030043e40807900581d1010700001ca484071030340810703d00300300d4411140400208242c1c1d411406401083d004400c2d03109031607180c030142d54002128103614586c0304804821051030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 768111861 1250 768110611 768110627
    0x106021605090903090406231e24040303090504052410031508062a07060b0d0609030f120b090604111c020c0d0504050d1101051b0106031109010605030403 68
    0x10f801000c4a1400000c0400308081c1d9200d40d20241c1000d2000907c1d00c0c10b110f1950501154550480300c0090340c4100802d200c41c403420b0303260b486000b10700c40750742c1c1480d10881d221000e820904503120942c5580d540e1800401d803100e580030b8a4050350410300803d19190b0300100c2002120031821410080203410000c1c80a50102c600e5020100b5494211034110310060f06c071804082c0208001400ca070389083c0c1e03001c41010307040041030104007801c07200200200c070380703030b41961481640144081000c403155000508c0042d03189101514051600340384500305034004000c2400c2d400e0f140c88064181000781650030880e611f6200d050381040440e40015030b41c1c030f4150b1104805203400303015a030810b0940281c14841048004102d00d01590000b8030b20f0008a04000c10b840556507450114545400e0401258502c18072400040040c94058151050b41c1e0040080d82c840b8616105030f07502e8401000710046c013030540d610090340c0100d4404c21034099400d00d6400141a80c0a40e1140ca2440e26203643c00c0312440 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 768113111 1250 768111861 768111871
    0x1e0308030604091b09091214030109020c031e0d05090601050a120c0e0f010315020f040302060d3b0d0c0b09010b060301061d030a0c0b070515040c030308010602160509 73
    0x4c0c841594070b00c0fa02074070b402d41c0250054a400140c07800140c5001c03c11840103804d075900b031043d812241a0840c00d0f2408407419540e501d5005a1296807010580349103026110900009107895031041d400e252414020300a9254810b1083c085038444400458a4010a000d00ca4024195880900140c03a210354a40210352040020310095640d844012002410503244102411100c100400910500303245810180301c1c02101180b42900b0300c10700356050721803440f0090144601041c3d00001082d107030700541c1200208504041c4628803041c5003260040c00100501d1303a1039940c004405a4540000c0741c070300758009902c0380d01c91502c190f10b42c03900648000300b10540a40d200c003a01d2a0648800f030156000701802d07111050304040e0300040c01550041403041c40e00a5100c4c580c403101188a0021050032107003144000340e5203107040d003040b03400d000ca600070740c1c400c0b8542003003480100300170445180b080324000d40c0c3c0c400d456602c4003030407030b02c0d05040032048000c0c110341c40041c04640380200c9003a07004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 768114361 1250 768113111 768113123
    0x2060c130308070302060117010507201f0e0706030207020d0b060d0606260a0f20060f07020103110a0c121b0f030e220f0204120c1e030803060409 64
    0x695070342e20200ca55002d00c1e0210010381102004000a0000c031140001501d8044000c0c00207250002c0c00034a03c805003c02414201d4680000c0401e40398180980c10804c0008034828041d801050102e5010b081e403d05c10103542d215206002075203a100780f0030f8030f500703641c020140c00242a883d00c40c0c144148026014560180c44a04074500084a03442410300509060344000f107510191031f41008800600d0481041c50b8103c20308070000203280c20441442280d1240c6904510600d83c171404080c082d046c0d41907600f060700002c455480006140181001902c00d82c2d0622200c0e2800c2056240c0b4082c078040440030852481d440000200e0340c42e5050601c5040d40340c050501d005030010789445c0c0191361025585814443c034554241a405410703518100c000b501e100c42e1131480c0d00c02d82d80407135218107010070038035035182d0703240202824540442c1d0003488001d040360b420383d12600304901d2144103072080070f0080b0052000f05190340080f640040480b42c10600580c00c0d640e42e2810f2101802100320b0072a94 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 768115611 1250 768114361 768114397
    0xb0f04020102032104060f1b210c020a0528080d090b0703201e0304021f020706030b0102060408090405060a05041d0f010e190f15050a051602060c 64
    0xb41340724a0710200440001e43c007041c401c50400f03091981c00c5507405500022514103010880c45c440c510f42075429048042880c0080e411803005955804040b802019110342c1c1e03040024205102d6800a5807035401030142094601d106019462000132031003010b60198071f01c51140803034004c190b41c1e10140c550b0658000020030851459036444820010480f61f00012954480100c111031400d950401d403490300c8030410302e01c0c04030600c40420f0a50306c4c0324608541250001300082c21911141c440c4060b103902d00040004500400340040d449841901038400000c0c0382084c98681c1c0d40c40015424000d6401058081c0b0341044441808082c0c40010a282d405c00c8411500280c50b44480c807802c0d11110488000029000300424103504140c0070804460040c1e0401211804008001c80c0c0c26200384088001c02040c04068500100b0708c05000c10080c0c04260b00c610451440e000c0354210b10301c40c160380346007004541d40d8411240541c081c80020310006910000c005914500e041000b00f034032116080d0740810f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 768116861 1250 768115611 768115627
    0x1e03090b010b070302010b0f01051b010b0310140f0105090c210c0408011a0a0e19090f020114160b0a0603051002090306010f0803031501030e06070905010f0c0b0f0402010203 76
    0x44100203038403502e00702c0d40003e0100305142c0e083c458080d0081c001c8032070800c01142240003c1440c0550541406c20380d0100d006200060801d5003d642105805020344010f081131400f07040050800c0c0c0c030030500e014008800179040c11684d502d4181a190007c10310340d0f05448080e00350100350083c82c070802d40d90f8185807202c2c52600040f10401e10a000e01e030611075480f801c0c02e40320343c00d460603603a0701c40d0b00c1085280e140316960703034000c0c01c0002d031b901205c0d4400d8560b60b041d900003481315400c8418076200e450003a103d0140505141c1c80c8840301d000b03032075074108494000c194004038031409001ca01203601c1c4540800000341e0808409400c06c284c0b803008601c081c1c5a4990307a08005042c2d9100700300d560300146007041400d0034031200c1c1c01090012004814245010300d010b8592000528030039249880000721106a0b0003a442110100503100840d081407528460142103214140034090105048010200c0b2440c071940700c0451013a1b00003035040c00c50725500c00000360910060000c905500091000381 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 768118111 1250 768116861 768116873
    0x2118031609050c0405280807050114131203030e0c150d0e0c030d051305040605010c0f030212030c0c150c040608150402030915100303050403240509030a0e101e0309 72
    0x341b400ca4035940080b014042440b8040c941104075484140a80c101c40c1e41000079a0708591031401d410031000c0e205946540712402c03001c04072401d07046107103283c4040c40200c0c1032540c03550205051420000c1210501d01101c820445908884500141c1c4120700f00300340ea01c03c1c403c41d00040003645401c007c0711243c0d01282c0001c2e08040c1d441e000312000600120b0051124000409010010402aa41084905c0c14100002d207007800138070014040440505231801014420040c940b403481c00b0704030171600ca0501d80f207565010b42c8114441e40d0540301d448149089000c001d10018040c0c859465801e140c07507c0c01e6000c2e034030034400a2600b05031660700303180b5182d1904e96000541c82281c2200240220f6807880400700101d0002601d4015107405040062000030b422500319425280c20020070017116801150200d0340e11b07002c80064100c18105424450088000000381c01c540401e51510703055541aa018021241c40741600400060240113041c0b42c0b80412484400345011180780c00b18842150303840d51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 768119361 1250 768118111 768118129
    0x14010605031f050f06100807090e0a06031a06011d041407092303061801020910030e12160807050a050a050703030f030e0d0503092118031609050c0405 66
    0x194400302e1040000401d00c4009100e20340d03010844403400c0c8910704190021072860300c5103940141c14403039507201090003140a100420002c04c80041c14581c5031518100440c043c0200b0f1000b01c401c56400402520b00f18481402103204a006a580300030511007090f05440052403010065005982c821058040c40025031800380f00c0c00050f1210908189011419030359071806007411030104020400c000340c556408100c20fa00f003242824080c0403a02c510b01c6030b900a200e04400668000385100c0c0c002c0070303e900340d00f01240351320661090701c8000a003072210241c1e500ca1002e070821641090103038071000460340d03400303009003c0c007440031a1f510500325a07405150110303100f415282680840703010000c055201c00c3c9040f90b4419440d05002c011106000c1d207548400c981c00f560b080c068007000080c044c0c0d42c01c000c2c0d09400031007560100e1880360000340210039580041c2400350102d4070110001442d0400064020141d00c840851480491400316000c00504002c0c00c601101201000002a0340d0796407044c0c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 768120611 1250 768119361 768119383
    0x19110c060c091908031c0b030a050a060606020a020105070b0903133b040f031806030f061202030d0305070c020907110f06060d030c020d060e0d0201110f071401060503 73
    0x1c91540c5080d450108040115420780680d454420000c0a02c8001d07004815524480039052031100b01c84c0c418854a00a0101010b840d5098454010301c0c4041c0080040c881c851103008407020080340b0b8540d0012602d980301c00b90040c0c0031075402c1100f800001c1001e03400179070060045003944c0c28007000908800c0c43e041f1543c0190400322038048104058146a0403040000000e52203990684805070b902c40c035500d1008002501086c19820b146041c180516880305180010441c002d04646d15400302030300918108105100d0345240203c0810707550102d4080301c040b190020b0051421444800048014140044c80401002440c140c9e200050b10303121107a900606444d01c0b41c0741030340c00d0f1283d00c901c0c003039013854140f1050f072110040c00a0b41c1c0300c0d054a00d12094051410005c042c420340003003070965444030402001c113458601d070b6100740a0b010804100030801680284a02e4802c030390070300d0842c01084240c040b4080d041081e900010b00c04800601c3d004c2c009800451000c1e91040081c0c03c001d0034681c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 768121861 1250 768120611 768120631
    0x4060609081902011d131e051e01031704080d0915031401050f0d081b070e040510020912122a0616110604030c020103050f19110c06 58
    0x441409001c0040c402110a00941c0d01c1c201c50000c000d40000f000c00341c5001d400280c841100042401c20744070505401038403000325900384424219000380c2544c02d10070a020340c01f00e070f18040203e608030359400c5600ca10070701d4554580d4102e03420340c5c0322090220044902d04040d98402c0000282c00e0f50148002c41841186840b100040c03850120008440070928209404040c90403014002c15a40c4422080c103445c025229000f05c01040c40c0404c950112104028114a20114804050b005020295034041003440f0540d424240d03540c81150b0b00950035100240550424442c0d00c0e400c120a5000d8148100c00400352007820211004407403c0402e03201c501151f0350000100c0e0a206c40304610361080400740b944000d90710302401a40e894071010003802112100d000000c8110120b0711070140850307400a400c003038840310304143c50041d02d45011100c0403400300b4100b9000481e024401d22400f07128403c8800c4a500039003807402e40348000e00c0c91a07501c0c40391207410700c42c030b280b074140810600d44204841a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 768123111 1250 768121861 768121877
    0xc100207150c12050a0c110324010f05090f010303080618040c050a2c0601090b0f0301060305070e101419080417040501170402040f0c0e100219080c0c040606 69
    0x41404030b064540c01c0c003d1801d126040001c03920b2194030418420009030403c580511035260070f0002420034045500040540024254011110f180d07400c81038100c0304502820f1916943c1c410501c84008412183d012000e0403180c0100082809541d00940c411001880420520214089003c0702c00b0162070603652202c1f001010310040c00e2024030100a0880075007901d0009443c3c1d0040061b02c10b17086101009100104049645d5034014003640c0f001c0c080d201802030302e900881c0004010350b0400d10540300000e00305004100c10030f02030500c000410001400d9031035104241c0105890510141c3c00c1042a41410064004400389413a40b600c0048010b9860200504040c2403000705000d00c003540b50100a81040204456a0040f02020543d00007a80744078441d0343e14000140107100c0500e20103400c1e4102010a60100e40c030a6504018030710465036020030b044c0541d400c81e030307a9101100e5100f405071916000000b10308140003404c050540f400c1161141121000842c0945c0c660307a0144002c07401708 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 768124361 1250 768123111 768123113
    0x918090b0703020714030405130b12010c080403030b0405040809040203130804080a02010801091b110307020306010e04060e01091e0203160f031a070905010c020409020d2307080c100207150c 83
    0x1002040c5c40d2040040011403c0c035003031400198910340c44451580103d980d8512540706901d4401c1d403840d00c0704048000f00310340c0c1010100500400411101100064901241c81d034803860240300b818080c6410075003460400c0524400c0c00020341c405459158403026100400002402440040c03010304150b0010300340c80c15840c40050801001a04184012814940c81c0100302200140c032811851084c904120105404814141903120340000650103007e010000704104605c6d10f00309024070301c0388000708900ba0080a80a00b00c0c0c03c6100f004200d02004028600364810381140c0d00302d024002804d903080c1082a40600c20041925400603210782d0707405e40d04000f40468903c80ca010031590140346035252406100060131480a806024140324451000f007056442d01d50000340d10b81e6002e003a5110000650400078603043d11850400c2100b252501c8071507032498045180c100311101600204007a403685020016682e0f040c1a441046220381c40001891901200d5009030614060f1106c00c030014803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 768125611 1250 768124361 768124373
    0xf0c020106080a0818061c02090f06130302010302090a0e0f04021009030c030803130b0906042003150424091203050115031a03011d060106080105010918090b07030207 73
    0x100b0780c80b0800b20b401030000c140108210000316019a451141480c80c0404c0ca900001e01b41c3c01080e828401055050a540d82040ca25600421000900325105000c4012a804100c814031503800d02a55440d941c0c60104015402031300600140300d002040181c00300d4403010308030180c1c6401c0701e0307030041d40c080d0700107002c00e5040c50400016800958a0b001072010304680b80e2440c240380303d1000a00341000003002a1a880d00104a080c95541c483d030400e042d420200540c654079076040e642914880301e10715010924200e0451911442480a0090174501140d03000107104010021301c141d50460412f5580700b810600030000c0b04d90010000e00000d9096410300340540d40d0403c40e500c0c0350905242a0040c48134100124511011284a150100300100d85580692021540e010000d42540c02e0681414003010014216132042607980700b11117080c0c0c1e030344408580c0c1c290f0038401e81d80814160182031040725015150350000c03810761540405c04c104c80b641c03100c045420440361030f40020f501240b2441003140d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 768126861 1250 768125611 768125621
    0x120507051c06140d0c0303050a05130305240106091205010e0613030306140604030b07020f330601270b0406090914040b0c1605030d060e01150c08030405030d0f0c0201 73
    0x3c151040f00e102603107550341142d000301a01000c2c00340040400c0c2e480b21244504111900c01c0d01e0180340e92816039803440e11075030b0342d4001d018494194410300c92200c0085140b105103812113107180c2d81c2210843c80e000010000100c81c0d60140d03825500d4010206403404c080150314010302e101740161010809600b4001c084840c20b8010160200000901000a07071303840d8140c9058a030030680300c440c280c031345210503858450070021003200e0f4080e80300040c2840700d464900e103104c071944480c1c0e88102800158023a0312408200c1d0094007052803c1c05428400015080002200c42d05c0f000811945445421504164000b6400500082c41145060000400d41d02407032140c41e000303001c80891424a0360f1341741810302c801040f0340440c10001c05c10302550031040c8ac40aa8080e0010150781d51100c1001c0000c002d840107000c1d0090600446000081900100001034110101035540028114565403900103030340c00604140d403c2e110500c03210048420a100d0b007500040581030001d0307042070780d40010342510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 768128111 1250 768126861 768126899
    0x2160806190903140a21020a021510030809010c1a060a0504090b061207090518070e070806060a0512150f040c05040302121f050a110703120507051c06 66
    0x1e800c142071100002e4011348140801c4c50307400303140d58451160000072990340410815185111710070055450007049242c1c01002c652120b40c0c05d5640365500d48038600419030050f01d84100b0002204000c00100303c0000103000540070500d40400b4401a5403540184150782c03410314010070b0505414003801d8601024401300510003501c083c02424035070744502032990b00083c1018005c009012480c1c0b5040350520402c07010305150201040b583c00c1c00040010210705215440c0e15a00c2178903404030791492601103092207410710395540d150035506c1c1c4050054a421040d900300030712030300b845102d2450046070360307992242242c1107540e0f00034550241080322001e030000300203000320325154012a4981d4081300302c0b001d81c0c6c3c040d901e01c40420f103001c00340307494000d0000c3c130b10050414a202c002d2520b107590304a00e000da04541c03000d004210406400c1c181c14851a040100030907051180703030141e000d040c0c0240750301c5009400c126003880442c113011144242000c518031041c6030b4a060600c504445090001385038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 768129361 1250 768128111 768128161
    0xe070801051008070e0402040b0403060605130204080307110102100e0a05011b0e1203090904080309060105032406150c2d1f0b060d1b031401050f0102160806 69
    0x70345140e80040c0032400044c00d001c08111282c0115003803a12660100c0b40108035000889075942e59a00707100008081500841d48280343c0d250ba84241c416030f03030007541c082d1404840a0740c9451a265291030481c0714142416040d40121048800921020300c900310744082000d01514081083d0302c3d0007030071103098044181c171080301e140c50307443d4040c0d000d180c803d00040f007030b04c0d5501c000302d1180714180340d4044e2040c4039500100b0201084100308039200698000c14402044880da80d80311400c0640760b20f502082210361a100925601180c0c0e0040560303030300031402410100c6078134400d031050321042d0b04c030f540c54120542c0000042c48440821f02c40170711118403611101e5940403070350b19145071180c1030701c103074481c600140b145000c46402c0c6952180700540401041503984601910a41006c1c0ca4540e02100441d029030a484100728002c1c050000ca000d8480e40040c0160300705000c2041c8049600382c21411441025110800081000c244001400b200b41c01450140307004102002ca184042e1415a12 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 768130611 1250 768129361 768129379
    0xe010b04050708010501180305060c1317030f07150e030a02070e06130207030207120303060603050a090209010b0c01021e07050c010504081209060d1410050a080c0f0103020c0303010e07080105 84
    0x8096220f19840d066480910709200070101c0c141c20001c00e0344554202400fa4040c100501c180003c071f8400401c0d80c003102c1141072407510341d11030402c03400c00003001d01003960350801c01000c10f000403404001e007600752161412162000810010804681a100c0341c21701c40d40c400241c006041c0d03010084400286100306805005280032070118400724090a4100c6015070007040900c10180240440c0016007103c80054551001c2810028003500942c0319507800300380340201180e0046400c1c0544001e494001c0c0c880030050b440e12a0681e0381d948072903d40c1d0107a5509100303480d0b1071007198201ca119428010005600d44015040c0f036410901503000c118144441040308214605020500c07005084840c0316190b196501c02c00825550b108410510320054030704a40c0c4443c600a092005000b48203615914150742c8c0c55030280002000e5a0003640010390142c1c0320454207190000031003002c040c0601d005800d00340c0700e0010794074503002a0021465200c1c03120402c0001648600c1d40750042904682d18a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 768131861 1250 768130611 768130621
    0x52d0f0a0b0a0b0f0904060924061d04020d020312040306020c0f152d0f0a0c0503090312220b01060f050a0c03030b01020c03061e0c2b0e0d030e010b0405 67
    0x801c2d40c02010130390052104000003018444140e209a6107950000640d141251261075811302030070300e5031040301600385070070004038120820300401c0100c0c4000c0074002003240c58580800900e80040c100490b4584181d422800100c90034001400055110b100c01589030000360800c1fa08003d0001c504104a900c9185081c01d02168503a04c02e8004c802c0c0c071004000c0348048038802c0c09401c01c540c060075180c10807a062000b008410040c00f4450444500100510209003000711a10320058594803013560081c003068011049040005810024407000c030b2148891800b1130080d4094110350507034080710008010024640c2101505d6003844144c64040d21388544075402414420324070402500b01940c07000c0c3c1c1c8009134000c02410303103900c0c0000e04459140c504001c0c2081c40a500142d20b06903540d4010105010010791019030b6400b0400881c00c4400040d508411044404d1031030180810765103540140b6505d0f94144000190000a66004280d1071a0806268250b602c540840c500607460902000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 768133111 1250 768131861 768131869
    0xe1c0513081e011a010c08180402030411040b03070608071202090d12180617070e0d0b092401090b0d080705070608010605070210080901092f01020a052d0f0a0b0a0b 72
    0x286c0311a800480c16032607030400210301100c03083c14060741d50080c0c40081880280401f188402c210180102d400f8401520604145915807445100c0c0d140400c0e0880085240340c0d00031014090a20b01c3c0b40d000600301103c4000084a00260030404d8600042124482e070b212940030640400c0400f0445191040e286004002406e051714114401c0c0445080404503207181e120300d171035103214080104542116201800c110440f89403d0f9100041889602c1410b4192100002401029084060701c0755040e071030944590050300c000450560301103501c24022001074111006132040a00a00c000c04281c0e041c284040c10059040e08050244401800744400598582c04e40022000003071400690301e4864102e114050318110720020041191407898500207034040e00040c400c044131210001c1420500c400590710782500250107004ca0300503401e079100e10a240c0071131508100c1c3d00c1041003100301440700c04500300a4240310700c4080d60000710185042c01050b400b0290004000d4908003e00a2008001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 768134361 1250 768133111 768133127
    0x103140f070c06061511190206160c031718010e030a02010309020118031b0501080c070b0402010c0b07080604062102010e120618010e1c0513081e011a01 67
    0x110700300807090a000003004071542054000f40f90307490440041c0040042c02400d0110000c040180a101c4c40201c8120541522150b492094016146030310f8240282440c00580c44101000d80b6400e0410000000107246440000c00910160030603d44a104900d9500042040c5281d0b450400840100092507590003140341c1c02c0c0960b0900b800a03c4640e10710040c0c1d02420100710310803003090352040001c24818080c0c040008400982120000385450780f005580049064880114641d03061006200080181c0c03910f5401c00e005040181c0c003540541d6827048508001c6444034000384000092107014180750081c0e030042d0074071408111014580d100c3c2000d144000c0400a410041c0450410a9640f0f401001c08051045041521494640540d000d02111040c0c030200070650320301a4806e10150f40031848100e400c0030b80e62001401aa10513007120590000325600c604880030302d00001c0c00120400c40040c1c19503408924080351800307124010308407202c800040e060065031610405c0142c0e400900 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 768135611 1250 768134361 768134371
    0x30806040507091a22031112030c060a0e06090a0201021c0e0d12020d08040804030b0a0f060801060602240f0c070b040c05040e01200a02010e010504110103140f 70
    0x20000c0e49a8590004555036540c962180d0440000c040007a2422005400246044105074200d02d042100d4170503481c250b0750262201800300321081691032040d2030070042d11150802d40c1d0044a017010700c941882410b08109480d158402981ca855030309030440c05114099001481401620041c001500040d48501545030f590300300c42c207182201c1100d24080d5000012401024003607a01260700c0380380042c9080e070702d0700c80c1070050300c80d038600344188a00c501c030804e100b181c2c440c1c506802c1a103159503142450720040c0200c1c2d07140d501c0f00b0340050000849d11030440109040d4001044013031400d64040d05041c50311254040341200249018080b8880d810400c0e00101162429100c03030b40c0342e540701c411034016660002d14000703507101800240429101e50006584045a040007035480206405088403454504680e01140004095001d100010060300000c482d03030002180800e10380c481a030846134102c0d0103c2e8885041011240c080d42d151003018100a0410303103004540c00e10b280000c03031000c40140 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 768136861 1250 768135611 768135619
    0x30e0d050307031d060a06210f030e09090601050a050f09011a07050f070609091b03050c0c0f03041502010e062a040b030a1a0d0b09160b070c0909030806 67
    0x100c1d911602c00e0703004c800c80c03034800d4503244100c258001c0703807940752001034821018003410711030041412854100e408624290650300302c820800d56a42e1110b590104a01c1a0b0030b0000a11510740c558a80400d09840343c0f4075100031300ba066050108000c121103550f001f031fa000f540074041500c0305899100c0c006045d500b0021040d03854000c61900d241007481200d400a101d401103075a1800e40d07090000d100c074180c51703044d200c0d1213030b8644a89045080751106496400b5014210f000540b10742e000e079105507000214040781ca0324115002c407200d071418181d000340211545c0005001c00c0381e00031031000003140c1d10306880280102035102181a94982024068400c20382541a410040010380c002d010310700c0280603003807501c1d0307030f6034800c20480741c2c00031a14100102e0a0501e081d600d102e00c000d46803a01d0400800d564281141e1b529403002212000300780c2d055900c10002542d2a1590751050b40001340500c1180035501c81c0c1a207480d8031100115404850064148104040001d400c40c81c00782d40108195 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 768138111 1250 768136861 768136867
    0x62202040f020405030102130603050c090907030b13110703091403032b0c08041e0c060f090504060902091302030601080a0507031d16140a0302010e0a1e030204050601030e0d05 77
    0x3840640007845161311142d4150310014050300800c1c100541e0004407151518100038a42e87e03c041a2040c1c803521440d03d42c080820000110041d0103a4040c00e4500c3e00901420101d02e0007030140c50844400810610050002141000805500044c8280039000120301034101740700c00c10200765203004000380140219600b5041203400c2070300000d82043c4a0750f00ea0700f80200390b5405405071080c001034500352040c4104164002041200070280c40380f2a80c40b10010507081d00c0c3c80e00071150860344660110030091451000111a41c0c2da005a40161962410059840c3d1013803003003001c4c414503207401c00082c900601c104026130ba08020740b0780d4403d41036500400d80d46d4540340101c004003001391100f032030302034280d500401000c030015480c041d05c01e440549122850310340040742c000d0300d001c5000700d40c40020b00c01d0603c015440b81590030100c420140c82800c000b41c030b82200190382c0900c0391080904041101d401c20a61810340905a0042d0080c28104241e40c08007000b25142c4205c3c80509041c41400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 768139361 1250 768138111 768138131
    0xb250504080d0e01170a050f090f100c05040b04180b0a03030203160c080a0b0a0c050705060412020f060c0a0216140d1103191a090607080a021201150206220204 70
    0xa49170842c40c1340704220349500349103080c0702d141d002000243d40000024116800003150f2904c00280035011143d100001c0081075601c40440028203803180c4402d007000014000025070b07030f1078803018201070113180340030500100c2c050103150115080c03c90098800c0c56912000c00c00301e0340100403912910301130b8030324030700060701400c0011403007009901c04001442a0180801440301418945014000c1c0d10300038020b40d02d9000c1c04039054000c264001e8025045031700820002101025030400c13809150050f2070710350b5a124007041c10004c04441c1c001e10000300140f03002d24250305200d20074664510b00d4900130514284280c1c0480344181c000e1180c05044091186014880c60000c034041020f0020f08681180c500ea142c0855280020103044a2030f039003020810707524061840d5904c0c0700d030038502c00524240c0d44604080319226405014000b08641c2001584500d07220354200501030480010848540c81c0c4006009140c6a00142014501b10030b441500c41100503094000b0000c64041f140803a0072980 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 768140611 1250 768139361 768139367
    0x5070308061f03090b060603060a050607210207030b01050105040e240303040803070605130f0308150a0608040b180c0f031606210c0503061c0b250504080d0e01 70
    0x4080c080d0800078002d40480c0101951641003988070030700c40d038085402601c4500920800d40400c3e80d03600c0e4800700001061040c3e04058014109030f60046d144001c04604840d2200c0c0d600c0f0103d540c03500141c000d0321003482440301114540340108400e1801c1c074075040c5080180a1b15502c09082260940704440d03120412005401103048108002003c0e280c0c0d03140d483c4506952030388548811214a23007040002401c480c00703003e13140e45483e0819240c1000c1c42c2d01380d400301c507054001003d250ba043c1c000c211010403502e80e0300d6080040e00c40c5482d03024181c20326003041506441c0c003c1480508403242c203042192040b002ca110828080c2c243d4600e9407075a0b11a00281c1070285400d000d0009a404c440d000441c4c551105195803185100c000300c100203040c0b070098400341c0d90000c08050100e0700400104001e0b040c00500010405800300034030b80d0602840c1e46801c0c07a040191414090f115101071070030002c141c2e007101c040b588041c6003011480e00345052b64140d00e601414410b0014082204028030051f40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 768141861 1250 768140611 768140629
    0xc080c01050c0a0905060412060b1804060c0311031302061c1b030606080702060f0a0605030d0804141516020309060c0f060105060f0d05090c030f061b0a0507030806 72
    0x25040001d100c1481c1c0310510754603030307004248084000b40f015007001895040003811901641d04000c02e00e1580000e640f44c1d20080e0003028820758000701c0940c1d0780340b0041c640c981442e001d188640d4000c203620000d070400400380c810440c1ea680c0c0105082085c4514440141a102e82d401e506440c12611401d080806500800609045480c07450a002c5880f40040020201d0740803004035880c10421691150350454920000b181c088015a1000c00410268212012082da10035207040001c607080d92282c01203410210010042004035255900703000820804c01f06032403207134580c58002e003040400e06103103038a4100c0240a150190344003283c0c14805074400c0c003c403a03228601800c001d40d24541000c40301d82e607000c0710503100301c0d0b800b5032000841e00e40b07404012502c010000c28403440c00d102d007000c0300d48020304002e070031401b040c802c4911070703001914181300117082001450080d00840c50841c0e848040d42d801070811850300b400c204074000181c1e1700001501c28107501440e25850f240e590b0808100250 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 768143111 1250 768141861 768141877
    0x50c0906070b15100206061002160605280815030c03030d020705160b0d0f15140a0302030d23032217070b04120e01050409021c0608030406020f0a030f0c08 68
    0x8148134480ca600d400003030746401510182c80c00400c402070100704a17100d044582404032451610b2000700034003031250014000101b840041c0790107988041c107810070307a2821490a4000729200034100004405070220f140b140c443d081c0c1c043d1140c8610000060f07200c3c819807840c0e1900a41c040703800420302004000380030049040c10041441d05485e20038944070f82e04501c00c4d0010b00c0d81401c0b10070005401602035145407041c1007070000a03090a01c41601c045064103440640c11901e03050001025030340c00c000c0e1500030562a116540c1e08030300c00c5004100d4014117203800c62000010420b22401c01c044408401d01c1140402601144e078000f894200d0488504000b1002c2149000c100c40c010300c05a01200341c05644244510000401d18500540b40c3e031400d20039290104130140001c0207810f8441c1c004201d248d0600100070364030000c60072818112041d517000300360340c0d60001c2010f01049404000210018100800410f0105ea055a00074501602d0300701c00030420900d040a1410000e56006840d074203 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 768144361 1250 768143111 768143119
    0x1606090b0f09060c15090307050606010c0302150114120714040908040e09031206010c020d03030c0302130803090111120f071712040c0f230307032004050c0906070b15 73
    0x8070402000e45a031208903102c203510030300c1542e0111b1203002c0000300b202c41d4a54844040d00c8030350303100f90056449100f6184190203500520345070305000c41c07403601460701901c0d1600020702441046814003040394403150380c02c2d5a90f44680402d1145103004072081c0c104440c11030300415050300c1c07460005e030035002e00d078020000d9a401205024240348080301030711281070303d011046074a07074074000115103000d20064003940041c0e464413100d010910130b4200c06018003450901519020092800b4182036161360f005140540010a040100b5030b0720070303144141070f0f22210040064000400f134000c01807040c0907a02d80303241e10004001040003030800040e020105100c0c1d05d59140c00031034984101481040f2400c80328000c00e50004652008050280300555100300c0c609000c80340d504612103400950000c2d07903075052080c040e0020000d0a03400d40801042100c2ca02400c0d83d800d00c600b44010340f04040c04090011205101450041c0c4038942076807842c40e0804440f94807074032001516003042d4030b241045904 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 768145611 1250 768144361 768144367
    0x905040201210f0b090106120c05040503070605030610020c1f0309020a0306050f010902040b180307170f0105010837210e0303070807170405030a060e1606090b0f0906 73
    0x14800d196805030b142412809001d1201138122020440245024090301b408500c9102c20741c0d043c2c0550f82d005d01a8820542401850a512003000070b2800c3d038903510a8000400000411000d4141070b40b0000203844130b400200700c010b04030800104005505072007269000440c1400c0c0104a1080d0012034100d07402918100d00140c4a041800281c4000c0700d03454580907124000290801642c42210126180803680c02d003024900541e000100c085208016454030580101040c9000188261548443d0800040030072014051039203003511016441014540c2101d006040c3d022132060340c03030a02c1c0c19501030100e045094001ea002c0d0308600440043c1c0100391015040c503a4500700785503c1000342e6203441e08480140c0b903008041d0f684c4944000106004014800c18001a10304518542c006201080540c1081d03103840100703150164002c020f40701170b42c80f42c601a52501050050702c4044d20340700381e400b0b0924103059000d411070840380310f1025400340000d403244660842e1420f840c3c034180000c0416a07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 768146861 1250 768145611 768145667
    0x8060105070c030b0c2205010e01030b06040504060902030709060306080709020a030f1b17040206040506090109080a0318060509091f0f09150e091c0c02030316030e0103020f040905040201 82
    0x24444d004071083d84c42c0b00c1201b051040603505c070501c0300030031614141d60303081c100d106c20030044014008400d40719803c0340061201117107070b564a02480c406043e0f41c0d1401610fa2030421001041a000da030300c0320085c0b503c0c141e01440451008902c00e01a00c2d40c80c200560303554800c4c40224002c10302903d030111901d14080b1007190515072401803640c405101ea8072405400d1003200c28040c40d84041e80e009510000c20072042080341801c034003501c0d004a05042030607881c0d44e01c2d100301e41080408d10040300055071100c51104a103038100308450151000d440c12605000c0501c003c1000c000020f015a24003c03014003058001c0d01a085542024244490061920550301e52005000c0e25a60650425800c2054008520041c4101d0041c0c8200b5061004044c03c1601890087c1d4a0003640f010800700000700d2141d00160700d08200412007400da0707682181061011b8180100081d04042d81c2d94109801000030851100700070341035070f0503224080400601e40d103c900c0180c4034031414070b022121110030251012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 768148111 1250 768146861 768146881
    0x414132319170406021e07050d030809010c05030c03060d050c13050f0a18080c031204051e0303070c0201141603080a060503030f120a0e010f0b190608060105070c030b 73
    0x1080c040c402c1400280340700714030300c800d00070340241c2c0211030040c2d01c00d00c05040c2100c072800c100c5500d18405401d0700d04c8907458a01044468581c0740040d40400d1050f403c7c000300502c01d1080c111a03416526116085082c9002c1c000028840601500d104030350701c2601d401440418405002a2280240f0245584285072240800741100715101c001d002d02070800a4404002d500401040c0c04d80c0c041d1102d10040c05503207480b504d80140303940a1880c481071280e03401400742500c2c898041d5006038002c14200d200c02a400354501400c00061242da0410f1040c0505039401c2103440c00174a509080c51100d2030500b5025806a0181c0d00c0500f00501008070280c0605800c481601c0c010003d0040c140801a1618241540e900c0740c07081c400f403141d504012113040f81c08102c13081c6400099000c404254040806855421b450034100e034000c816940c1d4980002c1444c10281101d18440c2c0d100b007800ca0302e0328042001d4000c6c4401070000e41440400255102041509559003024640c407120081c440e0030088605 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 768149361 1250 768148111 768148153
    0x20a030902040b100203030c031005040203042f060f160602070b01050a14100806030a0f052413061d0303091c08040c1809080706090204141323 63
    0x164000c514041c103030010380c1400d6407030001345003603500214030f03640b181e040a020513403009040c2071040c2d50b00000841c2d90760360341c001117000e18050750a00d44400516035009580303400c0c190081e030340501c081080380880d80b5039070b0030b90f0102244040b40d59240c451401124407130000c0218014001c07440024080100042c0c035140c035040e1402520843c200c0c1c2e803202035890041d100d80380e1071517008815640c10201640305102c0550b0180c4080d00707803210340090381c0d44c0c00c0060b0800c1e44102e569801406480c3c1c040c4043c480c0c510503034520300303441c4000c60030401801024400c41c18400b401c0d041d250043d1b4100600b00409100c8036041100c1100c0d84c921b041c5035042d489003005142c0b0000c121443c951a08030910419445000344d8104100c151b50f00d00c0d0000f001400c0b202410300c904959100c05602c0049107401c005454200c1c00380e0000b00f4035034000e20401084603910003101c0c0005c0b950405001e103020046000c030b43c080d60701c200d18401c482010b800070480c40d985031103401002d106168070307440c54103445070360 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 768150611 1250 768149361 768149363
    0x4050d0f11120c0d020a030f0302070e1b0f0c0717030705010605012f071517090d120c0905041d0d0503240d1b1d041e060609020a0309 59
    0x1221101501c1e80308100440410035401e00c200ea02144a00190345006092512481d100829584070981c0d03036982c00026038180d810903005a0000541000901d01c440b03c03245e80a00801ca0010b00308110001400c114010054620324030100403a0041812070100320b0038000d4105415001401400304e081981d032a402070008407003079420943d000a4650090044400110008a003c0340305404400c000359540d00b00c40070300c421445841000500c40c4a80400030f4042c4140e5650008200c41c0c00f2000c078a41d800c054000e9500d5031004003904111640300c6020016141401c2010400a02544045403150701c2600705603801450b03c0d80f140c00001c4100016070b00c204481096030354070321500c60203071142d010440e02c00400c3c0ea1070040b48120010015614080b8860040101210203c1d039140c03840c144505070009080340d00e810506000c54017000b401d24682c00c0071044885141e1400e940c40703020740e0b05218446461448154003900c00c00c24980c100101514207600115141d517121078004014040440c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 768151861 1250 768150611 768150623
    0xb09120f04061d06030604021602040e0a061b0f14041806030302011409071a0f03040b01050321041403010b0d030f0e060403120c230a1406061509040204050d0f 70
    0x302c0980320384552800c000c042200414160555940d2401d02000c2e602c946111020308149c521543e005a450380f02d0907054003038110040c90140d2461510004441200c000c05e10a500c41701c0f0b00c0303280145e1018009454060a1420980c11862095004224000c580000541081e140b0314000710f5031f0164045001c0328001c2d4024400d40101c00041049070360283e40301c0d4055040281c041c030400a503c824040320b0003128182c1441c0510f030300f54484090f00152002c544e41c101b00b200420140c901003121542400039104005411892201300c0c5643d84070303920600c640d03210071882c800350b66542984000c0d45900d0140803848030364107516005215003011020700011800c042c03080346a500342042542c0a90750b0108001c006a00980030a54040c0b040f85400c03640d00300c4c500142005515207003103c0e02c0c11a4030748000c10b8510308500d80341001003d0004800c585500080400031203035a5442c004580c1030748070041580d19030042c80840c011384240e0b0041a0000c8030014040204590490b8117807010380102 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 768153111 1250 768151861 768151877
    0xc0c0807121407211404090207030306060f020303010905190507020c0103060b0406080f0a02130308070b0717040b06040e1b041b0206010303032f0315100504030b09120f0406 76
    0xb10081890b00400801070402c101d011445101c0c0305001e503030140300c2511410500c800c0f0100031100009a07200350080e032041d603008201c400c205078041c00b881c0c2c05801e2509080c1109040721a00035540e02051003104e4200383c036039000c5928120003190500c0c842010036410711141ca000710019540c0e05010094900291130144000b030010030ba4003d943c08e6541c0b80d900c41000703480e4040c6e00000c0e90006040c0452840c0c1c204800e40c550102113503004011881405078507140d01503030511070241b110007400e400900c010400c80700030581111400c42d612036840000303492142c44060100d0000d03d01c207141002d46206102c900050082d186851a14040c03040320140140906030303070000310303501c81540c5000c0035a10400042c80060f019030804582c402483d12141c0e030490510f0300356141051200041c5516a0700003040c00614072140440528051080e01d54601c40010080c006000c1e12072444003a10300b2400e48003160140c0800d001d008004003580402e107072100101000603030b0396030062040c030700464005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 768154361 1250 768153111 768153137
    0x1805060f010e06010f18080f060109060608040b0a090f06060f14120c06030a09060504030306170a170901020f010c0918050c09040b012303090114090d030c0c080712 72
    0x3551040740f1510060399031045803040f10070203850102c49003c5204c05c2c0181d9520100710300b4401c00092010f951042c000f801c86515100c443c400300d42c0990810010010300b0020000452010740283e50400c1a1100000b0054040d0602a01d11206c4200040100b400c00c8000139900c10044489400c1d59001880000b0a4a00801700101040c10090211241d0440c090001c00c40c40c000d000b641c0d01104521001c01c00082c1c5548503c03c40e03908580450100f03503205024029007407a1103850881d403883d1320043c0400c10090710b41d00654150400c0703840301003c2c0012142c413564800d00c82e802a442c040030003031162001c2d0980c09032400689006203038444c400055075210901250040c24000c0032700e44d0803240351152500901c400b505010a9031818440414009401d205002800344402039450302210b85170305011400130709407484074071149c0200c1c0d00304090008401d00812207001d80304803410000345040c21884261049031004201510100b80801e03041d040c8814501d540d4850060303a52003100794024 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 768155611 1250 768154361 768154379
    0x20d1b06020139090e0a0212061c1e020402030c0903060702070f0303051b0d0e120109051207060e0a0326041a04150c0c06151a0d1805060f01 62
    0xc1e01c0d80080c4198a00b1940d101e061852030f010f10740c410064a45000030549901c0001d09580d015030ba0b0500041c0d00041701694440b860302d02640000c0d0131a2881c011900712880c43c00c600c000c3c940302512000d842c8202a08218124121001075680170700155120300e003c2e10810060340210440302d010307014210000340000d201160717400940e00d103031000403215400c6450886a64000b1080a5480c4041e0104561210410401078007003149079501d01e4208a0300f0814003d10103440740401106a041c480e4017000607002044004e000c4d01d004107415210111400e086000e05003052105005000e00040017050603844201070812900c80e4140c0c011100342c50b1117200b02c00384111005090702d144a40040f821031000740f0001d401c0350061741c1000c16581d00c07020f490201d522109a02c80850000c00380401084035030301688c0204c001030340005260340d2400500311102c0d407594460740e52030b940000d910142c12250303a004071003001801903c032008000501e03040d40c0d2a001a5400d441700f6060324000500160 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 768156861 1250 768155611 768155651
    0x1b04150308040608070e04060311190609170c04020c060f100b160f02090c0403050f01020a08130302120732031603090803070501050115020604080a0c020d1b060201 72
    0x340c0004400d00e014580f000440340c2c03900140ca408200704107034102c0c1d0010340c1c0d903010f0b0001440c09446c89203028580102003040700c5e00303404056480030002c01c1c3e0412441d600118203400700d0b18401c01d60350201c401d20542c10b003001c401207105640180301081d41c000180c13001852070312490241052040540710011071007400c1c0498407680030342c140300700b10f540701c10b1004c403400712101442030344400050310150b4001181603604640b0380f251030f0004582041802400c002c09068040100001c511b0f215808a0062030013400030200703400050050b04150405108200000603400c4503907100351140c4892400300c180c0b0484d00e8820342100e81c0d1141044440035070107034041d0802c89c81d4004501e0028252298000d103018a10203a081c080c074060b00156814080c0300a02c892480303a000000c0c9507041135228020841060015030442d4800410000050780312021121600000d043c002c011080f00d10000b48065400c040040084000c100b01e100b00c00d0f003040c1141c0c08ea4855800901c400c88240901c0004d42c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 768158111 1250 768156861 768156863
    0xd11030d060b220e0a0b01030e07060e04141620071410030c08011a130801140f09030301050d11040e01060303080a0207080d0518060f1014011d01020304081b041503 72
    0x512004288402d0140c1c0c052421b071901810081404001c0544003800c16a0b40c0c3c1c01040410300c9075011801c2460903102c0c40a1411008487c0308145c1810610044001810404402030242913000c01d001622070a90740c032800c000a408a80701681c80300030908441e4051b5040070300907800c500000919602038000c814590407150750b10900c584c80d00021400308601c0910401c4041410041552881d080d00e1400000d04030040001c2030103851060700d403e9100e0018181c00700008003d0500501a1000c0100ca04480b0304072088105e800040c1010301600c40032920399a4401c0ca0412207100c600c006412a000700c0303000c2c0e101c880b803940d50801c040c01640b1804030010024041081000c200040d85d43c00907400c0302c4d444801c07020b5140140d04040c80c044080d56501c40f41c140c2c000401c8a0207402c00d0b44e41d005820300541e01140e48244c000060079001015212580c0c0c401407800c08a83c6910810a4400900b241d00840e4040d4a81c0255801c00c10200c0c1540f80c0a00d0a000010031075040b0003d45004507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 768159361 1250 768158111 768158129
    0x140a0501030b0613060902040f1a0a120f02161a070212040303230417070807062109020a090911120a080304060b061207021e0d11030d060b22 62
    0xd6072100100700c2c4c002412842d00205564890000c901a0020700c0030340054402c000c1d062582c80d0070500041003010b100c03503e180fa8844200403480c4c4060348084210f800303e1220001055420035210400040d00441241640351206400c2801c20711080c51541c201769191842122425160741000301d0301d035105507002043e803403402c02041002070310404107150240c0308070b42c7d03500903034140241d05900d580c01036214070441d01c10b0f20100000d0b10b40503c1680b0082c0304200082058600d041005002e04200360607100030500d071421514043e103202c0e049078011a40c0107113075000c010f48682148008140350f0609075a106081001c0910350b08110452f41c04032a0000d0080c4400c142691340c0c018158401002160b84c2e544902e43c003080d68403030784040e26802041c030031001c0e00f614203407030007d207015915102c290420201041c9203400d2000840e0f0841806018545003d181c003440070b410f45188214091401c005150023800101e10107080f01801e0030010039601c1901c8120040000c206407541c1d4000d00c01c40d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 768160611 1250 768159361 768159383
    0x402010f1d0112020d02180a06051602010e1903150f0501140d05100606120b0108040b04080d0b03030f03160c0804090510031b031e050a06050402180a140a050103 71
    0x8650701486006080c0031030343e00054501101108448186c1e000b4907802d87c1840f00c148030010081c5403800c00c100241480303103012424200c83d0849038100c810b01c04000783c18040c10009140c01519009510100340d07040031740403101260341e407802c403032000300342804811124600801800d004c030b09406a54101e480c40c00c2c0f03e1502c0940b08081141020003000122114820149000081e103401e0140d20b0040a4030703140c0402001050010000b6194003226450403c19113001700000602c54242080e086a084008036481e01d1154100900600603030310a00d0341072201041d5003403843c10200c0294401e191400000c2d221020301e020946a0300c2c10300b80000c0800e6400e00090007941d0960348603690003030390b590028a125907641c0b00ca440118034000d1101c440e4045000500030300000d1200304034118480e050707411040281d40c84958407440d10500080405840b000400d0a5680c0d00c1c4098105800d41c0d1700540083c00c3c80310000d4010400c0c08044060b00e00448009980c0303038020321610303040b41c0d041a00160 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 768161861 1250 768160611 768160667
    0x908030c250f120b0106050901080411011404030c091406100e041d01050703110c07031106041707090f090c050111070f140901050609010e06250b0402010f 68
    0x114503044001c10100c0c0c08030300000034440c0148889240102102d02c0034000c00c90180c00c18801e0060143c20800511104020301c1c1400d0740c0c44415a5032183c0c00028160041ca581c100480d6060a01400d200b02c2c41404600401842080840c640480d241c54004002070705035486841444d03a030848101c0da0221028000703400c541c0c0a030000c0440c0410041c40007451110300c9003a041540b0384480300282c50f0f9550300800c03d4490701403154184644e45041c642c3c1c102461000202c4d901c80507030100030a04404e480c2c0c2c4000688031001950f010303040d40007280c2c0301e4143ca81130041d0b88602c0c2c0d2040100460074444c9042400000d440764203e5183c00011a0308814240401540c00a140944a8560b03100354000051196030303c95100000c3c0464084815035050f5044c01c02ca10b00c441038100c140f142a08020041041c1e03001040107802074000c1c2e81031601e890204c0c0c0b05591032288100158042da40c00801d4400300021004510f220b903100b44c81e20407100845010465002c518200d10440e03244c182c14000d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 768163111 1250 768161861 768161893
    0x12012c09100b1203071e02221d03030a09060e0105090a0308070806061b031e0316020c3a05030931050a0e0f0f0c1212070c031a01060908030c 62
    0x1207038210081140030244a05076000c52040440400382342d95400070690008400c6030329000f0000300c1c0400c40d501d1080c01c182d0122060b00c0b07110180030700040035624001101004140d0300018040031505008000c00e1400043c440c0e124820322008400040c05a00080c190070300954100703000d5807010340b805041031240080c40d9098241e040c89000b0521080c0f002a00c400ca002110024500d0421075880e1642880341e90900110700d02d00e90642917401845140c2d2540c0c07a10500801710041c0c1c40107a00202c600c0c01590401640d04c40d1055003600204062a01440b000100901e590740c416150148003100c926180b21b1003950035514514a4940c110815014078419005550005d03035004001441200002e900c500c1c0a499440c91005904918a400c1d5223000c2404840400141a252403002c407601c035014a4031005030307903400010f10030081103680c07e00040e0784440d40034590002101c040112025014807580f482482003100091041d00d001c52101c00c0403040e07600f0342c0510bd0051600b805080e00030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 768164361 1250 768163111 768163133
    0x151308190224070303090c090c05030406051815040c060c020f100201324002180a05090c030a06020708162612012c09100b120307 57
    0x1003000c00c1445140c0c030591414008003032452103031720009280b196924103160720085035800400304a1a028801440c40d80003c222540306612610000381075aa5000d43d044025500d0b02c07a684a00c00d06a0070303414100a4001c01c0d00503400f45095411596071400c040303480064014000350000d4812144084a09107502c00554180d660300010407001d210741c5805205482c000100106001d02030440c4920a0380c0e00c5015400200342540e11110540d07107040302c0c05510404401c2a40c0c100c80342c8411180080e060607101e07c0640c024200e2024820a2440d003e800134161035804032a4580000b142082e50006244580110058054221a00152100002504598010b031504d280070803031400c0c8404805d464500d441e210700d04c40001c052040344605560301200c4180e8511340001c1161040303613071031041c041d41110015460300004090900198400340d0401c03c0b00181e0990f0b000034086509000304d010b80129054220070003191070340c01c0c1044204030f000036055606030010400940400c2c1c0d00014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 768165467 1106 768164361 768164389
    0xa0203012904050d0309080c0d0c1a0705070b03010612061206020f0d060311120a0b06060307090315090b090105060907031a1513081902 60
    0x1404040003080c120340541040440001030061180000c40b005400d01a1030060040307031510b800b80922581e030040e01464001c511840c00641020314101c11110f4000301d100d1201031174044111103504010214180819003040200c8c0412410404240181905501140d0700e41c034015004128a400050008819040c2035080198015410070413155541180c00103035135441e040100d40c9144500c48414504a04003500042400800310801101c07880954401c0043c031184101c2e1915215100743c0100300c66545400328411307041140c0034684c08031407030a103142c000751641c231820400d0002207400c0300c020383c468106a08014188a080707401c00c002900a009a051510010328100c0c002420041015524005010140d0201e04045000c08025188042e1410b1807001d00d4003540c81207459140d40d4804240020703c60000040400b501c0359402d81f5481a40099400c0107040800085 = true := by decide +kernel

theorem cover : BRFrame.Cov 767985611 768165467 := by
  have h0 := BRFrame.cov_init 767985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 767985611 ≤ n) (h2 : n < 768165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
