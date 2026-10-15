-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5069
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:38:39.754517+00:00
-- url     : https://prove2.me/submissions/8b58d89e-e72f-45e1-ae2e-bd2242270446

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 911510791 ≤ n < 911690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 911512041 1250 911510791 911510797
    0x80c0301081b010e280902090d030318050703030c1502030403090605180d08030703050c1206060a0e1002070302030709110301030f06060b0f09030705090906312010090b 74
    0x101c2d06008144d500052030740c840e0701342c24180031851110041c60241c4064884001c0f01940d018101442c418010b1030820707500d030a44401419090300d00810010001c2880c041845001d801c010254450b94100004060b003116008050600400910079080c0c5200d04600591008031001000174915030b01c180030440c0640d01901d000b000c80c02c0c503204501d810101107106001813a005552a030004420407903155410300480c0c2d4440c0c0e120b40650300745403584164899020380940414030541c5c003c180314215900c245003400c0010f00040908500d904a000041c0d00c3d081c3d0f501041c2d0080c0280c6e400491440402c0c010010074400024840340365078615190707121004081c10049030301644402e00014040404405845d5592101050a0b43d03003014904062412398943c0c4414003440001d030801c204600c01083d002e5203c41081110086e803000b40d042a440e071071001340501020f040d0f181d90102400b1881740c40e042c09090030521041c0c412900010003075901100000140002c820300320a004c030f28659406 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 911513291 1250 911512041 911512093
    0xf0a0501090c08131b06030b1c0201050a080a140112020111010b011d030a08120a0605010306051c0f021527031e0c150703030b1518010207090e0d080c030108 69
    0x181d4a41041e0070b50051010000ca9840200003a07140c2c0c123000140d00c4c1c5102c00340c2c40f40010f0128088042036560000e00140140124036045c0103454000400c04a00303a082a60301300380004c4607004944c1c40300b0011001c502d000070140d00003480c420090400c007205104040e0320700c00586442030523419503818a450f1740c0d8401c0e030461f054060049508000303000c10000d0030001d032400c654642c1b1340c50240890f0341150482c1e030140c2d04050411104001e9a00c40c2d00240c042c12124210b00d000d02c00c0541401c02c0c40c02e0341100d0094000c1c80300c20b0843c940140200203406c48480310071400200a016405518202504010a81d451780000d03016020701c1002240c0781203d004900305072418403068000041c8041d0b1094048800b0100019100c820036034503200d811850700046030640005503040d6418140c0c0c1c0a038000983c030003001e07603a034600240c1c001c000280c01003440110602c410540ca4901a0310b41c0004110f00e40490100380100d9178110101052724140c0c1c8241c00201380d40349084048012132104004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 911514541 1250 911513291 911513303
    0x30f02061f170a0c0609060f0c080301140f19090f06052110090302150702060f04021306030602040306060905070c030e04021b0f0708100605011d01170f0a0501090c0813 74
    0x1181c03c002000c0c0819480101826103e882d8410301d0040040d160864100024040107802103a000c001401e500030380c1c0c11b484840320700101c070a500c140401d250f484503000055015103403820384241c0c81148075070700c0140d0715140002e205580010941c00d0640313000d0301500d58404d0320340031142196082d10800254a0109004540b010914074030107208230303070450000b83c0050304011981c0c0302e00100b4895890b00448544001c045c1c52800d155102c0881c40e0141009201c0c003803030032420900081caa00810040c64014000715510383e41c901d00399000700110310403050110306090008200c50700075801c4002107074043d10390760188048441040000d60101d03030810f50091440034841c1c1054402c00124040584441c020703c80641491041c3d880c00c0c5081c921441c4660030840180803a984c04640b40300d4001d075010382c4815920a040040c0c443e003e900b02d40e030103916004c404018201d2003800303000d070240700d010f0340c00c1000b40d8076425650141d80c0d0204c14800841e00e0324021840540260944030310441c0614 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 911515791 1250 911514541 911514553
    0x70c09020d0605060c010b0f06031e0a02210103110f030604030302030a09080a0e040e0f0a0b0a0b0405090304060905010504030b010b031b0f07020f0612041203090807030f02061f17 79
    0x30001103041c0c0101040d98080c5e1f5483e1083c034010700702134484100d44101102c01034254030b44a0340c243c2c0c0d82c4081e05880c0ba01c02e102c1e071003c2601c080c801d406550700b81002c10005440400300c0440422401400d12007681c0301980085100b059040c1126200d443d200b0140280c2595a80c5480c243c0180d4809071490761040c0da0703031541c2408504148051300c01030032070340d4070300c8102e90b07400d0100700a640c00c607150640301d078025040700707031144900240543e4141e40c0405070701c0301a903503003614800410031400c0098115003043c0412400c0140400282b0a50303045841d8840c0b0342c1e0301c49004440a0049020003002400490014800000100d000d10340c81070894461000704c0790065600401a040842d010400c5c0d480407400100b149801a040300040c04242ca210b820000440b00606440350060300141001c012440c0051405110f034119054840c1c01c1350a0640d03a503440d150041c100d460f00c50228005016010105280a01c003064020503540d010002c008090308001100012500d04005105188619 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 911517041 1250 911515791 911515799
    0x31506031009050112020120030d1e05070915031a012d0503091911010827160504181203140f04050715050a080709050904060f060902070c09020d06 65
    0xa8020113029042024030800680c138580f00141842c1c0303040d007012a80107204d005a852110000080c0e4000691000f00403610500400d8040c41402064118411950610342044201c40d082140c400464160110380c48581c07110341d004500f1504200b0f042070002048000200f4150300c2681070140e0306d0a04081940703003500c01000c0c6240d10321230f03c0141c00880c1002c01000414a4140200b0032440380044020011100d030340d0321035086541c0800c804e41441070100100301c01c000d10a040c41e102600d0012050380c2c03071120702105503487c0040c0c011140340b081c44141c00315803801c0c00e0041c00c150708100d4000d034004101a5448140c0043c80c0c640e05030170103913900302c0e43c1800156080190701501444141e480716080505045050000c142c010705210028bc101c0881442c0d0f1040032103d089155142c198000c0d00c4d455400c50b400501343e405641e1112000c018041409102d40c031113185500744c1201045001d5803920302506a0060080140002442e002d04004560300c03600144a81d03010039070300040041d11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 911518291 1250 911517041 911517059
    0x80307120f05041103010903050f07050c0d08091017070c170a0c1401060b03010911070f050115060f0f0509060910050d0c14070201120f0f0c02060c0315060310 70
    0x2541041c0d00c1d0340364aa070140f10610149014002c0014026002405a40c0741b13603c001d4202c0c801e9001c0d01c0f62010001030301c0d50610405100e85886014001d0807024100d1702d600b4031014a41000300307900d00c203101900c0705510040c044d210f0640700024944c44c1403d56079941d141564038000408003039407052000d00c03141c5034440b403840003460f10010540754060b050f11242072101d6600b0b104104c42501c1d0780340c01018001040c0c400107680c1100c0e5a05004101c140d06540544014056800001d05241010300c85108000040d00403c0031038400c50a6125090743d5140d080301d81080c0451204082a000c500c0c031281d40d407294000b04216a0040c091600d04009600840e00000050455030009039000c03986018841040c0034051071150b0b2407600c03107001204001600e00e20700c00c60500a0500c000c00b003da4640075429002882030040c6142c082002824143d1140b0140580300b41241c01409a04006100603207000140d80c0260155801102000c035280d050010591016085804030b55003000d001500c200 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 911519541 1250 911518291 911518301
    0x31701030c09151e170c151c11070203010e070501050a0e1512090d03022704230105040b03061306090503130305070608010506090d15140c03010812120408030712 71
    0x4c10041c2500c242d182c0207020384010860f0111150781c4d040008020a103030303640300c60b803400741e0116658299900080d82c01d402040d5050728a1000e21400c005003080300003d13050180500340e00070380080c42a1250520741c541c0302c0c9524014940442c1c410b10500c0d42c505e1203000e080c201c08070301500f1100e034004e6000c04001c0d280c0142283c0100700b030340c8508001110038107210b0207003841e405007015030501403e1500071168480c82044001c8003081c0d070a07402c1c040d903a15080380307112030741d85a111000350305181c07402001d00109000d418040d9003002c21202003801d00142140c40340180c80c80d484400700c02d13603880c540544074016003980d07175100501c54404040381e10301c1c0d98402144210001d010480c036107403014000800580c002481641d045c40907030b000343c840c62200c02040750302c04e00135038001c00041d003488000c10401e007007003108028071420446001c031120300a6060701c170081c00711030b0146050400b145142c8105200e4000c080c0000c00440c0010365201c0c0030b0b64104007a424030b015103016000342203081b15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 911520791 1250 911519541 911519579
    0x1a07020405040b25090b07030915030c03050928240905070611030d1e0603351e07061406090606040b2506050106020703031701030c0915 60
    0x30098001d00c108109801d90412030102881400d00004d2022107010b40060224416200b02000c00207004003054865101400034000702404108816004400140140aa80400c6e03022074604004036640410001e140d40d003411140304040c0119101910800600241c8081100d04007525107141003401081c9405c009181170260f800508130300503091940c078051031a8003640074486102080141c0d03060110371118096a100c030080f40000500b290200e402c8044004000710310710b081004020000180c0419880300044125018048000004641c03203903a2051034085402c410420034100381c2c0400c41d410f000d03400040e41c00d400e14900c0d03140c490070f54001c01015104840700e642040b020f454844013aa1b00b02409039000341c00c0c03d0610810800c9807280d405030302c10520807410b41302100c92000702e091011561003c418007865a586601035618940741c08101e0100b011841c456420110f1010407d0480f078003c100b210f0700615119005000748901d1070b9020304a032016202142e005040b50035283e100c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 911522041 1250 911520791 911520803
    0x20702040e01090311011b05030f040f080a020d022a1e130209100e03030a2f061006170c0901031d07080d080103020d0206130f0810061409011a0702040504 68
    0x81001714451402c460f41003001480b4011806200d03081a80c3c071406803640584011494405a03e45051410f0850318808004048000000d00785071101e501096403c1e80b98490b4007215100d50102d0b10503021100d401c4499a2662403e83d0041d07401d2404940480d180188001090110b0488102203003001c2c0140f2400907032541c0015002e20340f800e003030560000c038403000e150291542580500090302c07032207658002c10800c01003801c06e2081a00d82c00040029000c00c15040d01e500302c005030b4864031904200d0310348070100d08051000235881d001d0751a441403410b500070210901da17602c104900241c8c21150f450303810513580d0400360b2102040315009480bd00c0c2e24800500400d4034100c03040d03140c013a00d40c02ca04100102c06004000603211b806c115803504d64115034194540b082e5696016500708035034085220310070788510025907070001113020040081040c0d0305002964840441c1c0d00041c84124010307401c55508401000008290041d104d244013003085039614260032600018107551007900c050301d203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 911523291 1250 911522041 911522057
    0x3020a1101241401080a0f06090e0606100c0b16030905030a170606040b040b03040615150e090702210d060605090901090905031905120c0d060b04050307030303020702040e010903 78
    0x1000b0100954000500020f24058020881c840009040701000f5100fa240603803200380e60616180c1c1c68208e039000d003101090400070301780c00811440d500c1e01c003a100140954070b10030f1401e0700180b00d805882420b503002f8401c0368103a254030507208100e141409140c0c04156039180081d000800a0006041c1040715039151024144001801c5904001c05002c1603c40c82c5c04002c108010040d11043d18220364016030955103a50302d90030040e01030024102000c245011005006c035101c92076207950304901c41c02d643d81d4145080d64005000c81482c0507200c07080964000085e0b608480301c035002040601140115450510352811000300503695240c002d5030120b400481d0304091401c25101c014014492940d00348aa650036031034a5449108010802902c006d50640c00c030001c500441c112400b01c0d001c10748101140c038202800360800d82191001000603401c01d000011107401450544080d6000180601455440c5560030b40096001c16012a0040d84a4004201c6400c0a218400c0e8060080d165420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 911524541 1250 911523291 911523341
    0x30d11150c07050601051f050d02040b121806040f020d020f0406090e060c210a0902030303040c08100606210608160501021e030d0e010e07081b0306090d03020a1101 72
    0x20070310700141c06c1280078000c4065061b43c08001c6404002e4004804d0505a944075010010440640301d15000307c6051080003034010003070884402c03010b1161350702183c140e00d160f452120454581005940c003034200722103a82000f01505e0807a90200361241700802c41c00ca801040c2003c034095907034680c44500c9442d07803000d4003a4088070030700050780e200540f00456072500c140752086141c5000d0994601d1448201c0c1c00006032129211fa00072200035400400f16034403860030389401c000000036409204158050000281c1444c02076000716401e46503151290305c07a502c4c00061500300c41c1d0180001800140d218500010f0064040c440f444486030520340381c010b12818003001a150605000800d245024664201c0052103c040140c2d03144003911040400d03850a24003005d402b41c140d40c90345240a0081440008490b0300000d0440840c2100c0e845e08840400054209920780004880d4104150403596403100444c4c440d900801e0140b519040c0710601c480c441e2682030840b16016543c420320384980b96400307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 911525791 1250 911524541 911524543
    0x507050307060e03060109320420090705091309050d080108060f06040b010e09150f190b2a031210080d030b1f0519090302030d11150c0705 61
    0x2002806450401d030b036070f0482c800d020964480b414801d4121040e942d181e081104241c44d085a0941000282050302104802d01007010b00c0000380e40440e454064000044040c4140d901d2100803540c00908040c0c0d1035480355010781d2141d0001079402da2220340c100c40d158a1103554465651701500400007402003224009010f0300050061300300e10398942c4000e08200c42c8030280ca00c5075520080c00c1c2c4011490202c1c040c01642d6040103034041d25440715040d001c200003540a51501041c00703c04a942ca40450107000901c000705a0304906420302c400410002c0c41401c80c0f41e80108452500c1c515940000c840001402c00b90b100c009c0c4e4130001035000054207205032201c4007507840d041540e240072014058685403a00707a03280c105107811000c0c551580001c2c0c81d955103180000801c1030941d981640510103003a0000c1265210703510140360004215081710704039205580c0030007613a90280042c01144042c00003502d0b404103403003080400380304580708018402201c50304076000304440148181c450105140507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 911527041 1250 911525791 911525803
    0xb1c031b05013c09080403061d0d0e06070609022701060210021215010c0c060c0c0803040506040308070f05070603050609060907080c180901060c0512070309032d05070503 75
    0x582c200c00d0501c0c03040110b084401c41c035203c182e80728400036200d0414a04618940601d9002a003d14038014810680d1014001c1c0e00c1c44803030b00c0b1020798002040c544401e4440c41429151660000c0c02408440000349050340030150032400141703400758070b00c0381688202541c04411081c00100d003d03140100419074042000442c6020311505c15404d10007070400b540903001c001070400366032807040641d198599004126011005800c2984048655152600500328035001c103c111076007011040c0014900c9004020f48003601c0004100c280780518607151400e0070b0f0414031090b90380104081410300018005c114440040109132800700c1c480c82c1640c100034410303000810f580d0040041c5000c203e1000d512020303940d0300843c0c00c0c142c940ca0320104002c1c01450051415520703000b10720000007050054000c20740b06c840901c81c0c802ca41c0100c000e91543c2c00940500c0781d005001c17030300112090001071a5a030300e50107040b0302c000e8170220080400100d09810030011205541c1e54124000601040c01d09000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 911528291 1250 911527041 911527091
    0xa0606080c1903080904020d0207020a03200603010f1509090f0b040e010507020d0809010902030a141c020705040b010309080d06091506020303180c0a060915030b1c031b0501 76
    0x1141202d8619280e07803a6920411144500c0355a000a490100d288640c0c15950842d8014000304000c80d220700c0d0034400c0c0604000c81c051011100003c0c10410302d88441201d05a59031034246480c0240b610030b401e801141e00006581c05e0090341440810b0444061041b040310408086022400d190b1074402c0c4011111010503200307680e410081089000c07500000c01e81c4540205140610081c3c0d645503002d030040c104440003d5150142c2011041406405a11148402c1d04001541c40e032145c00383c06c070b8840c40d45c0d0101072400750f003040008004c24603144e481408214010306010035001003541d45c81281761f109440c882d0919a40304130900122040d4030030703148081880120112118108840a981d81c040201000403468002c20709018004041c0729000f05202c0184c0b10700d007625250365010308449141e00074103950090110743c13542d07814441c5c000c2c0e001c07080c1d01900426528502d204103840e4208049419010700c40c0c1c81078040284401800e800d00554007035000010184440d030741480040c180d06803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 911529541 1250 911528291 911528329
    0x170319050c150a060504022104060e012f041d0402180703150e011a03060d05070b0705060907120f1110020a15060506030f0a0b06190318080a0e01020a0606080c 70
    0x1521902d110211070f0012192341c080d2448541e840c4c0ca04840a0411300c04002c4e0a942031003410140c0c0d401c9090ba800c001042c18814980c03481c0800101c0360a03011702d10507041200300c1c1984110400c922607603050380007030000e01485003443d2014407000700364400b640d010002940c1d441e01d2030015009207000d0000b6000c502d440f000b9a501d04280c15510710144205250903110000c0803484036511120302298444c1d00c002070305c40031a0780c0e07038625007181c100300400e80750b038020600001c1d094080420a01c00f550401084040c580005498550100200060890b84103080910a02d00340d0f0b10b074200c403444002c2aa0051810b9001d600d00801400c8503890314030162070400000703003d29919001034036444081c04e401034451303a607aa00254081c002142400c2d40012000a042c0321400c02000e202d4052512030701e0a00c030040d0426600d90054800d0078016114404c14004449003500c0360586080c0d61805104a402c1042c603602c5240032282c00b035004603095031200c641001613090a038842e2415a80e075031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 911530791 1250 911529541 911529547
    0xc0d0e070e011d01030506061e04090503040e0a09020d03050c032208010c030e100b01210902090f0609040201120e03130e0108061317071b03020307170319050c150a06050402 76
    0x181d81c80f547d4000107000103114404108224980280c00b20081c01d040e1b20041c81480800000c0c105140c881c0e01500689840541c000c00081940c20540110f0758010350180441a04a80c0d50301d00312001c0e0043e150355421400100521a5400040d050a5060301100305200300030518201010307085030041070000303052600300316600301c200a000c01c01c03c03214203804034003260000c4504012100d4a00266110840070584204540301070306642c80200304c01d02c01c2c0d92401035602c4460520707048443c100e407016400680d01c400100154402d1001000781c41142c00041401c0d01c26800d8542150881d005006031021070140410002c030260f04541c3c01029854040e00e510b040c00280442488180c0e4000f401d03408a40c0b007420500c21f4140c1c01c0b92506a001401d504803420303115040003aa400d01d2000340d01c248601c1c4c001050341d102601940140200d03070030045103002028070071101b0b020000314962052140900408521000600c00c01400303404c1020003109500d008849542251754581000340510300c14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 911532041 1250 911530791 911530793
    0x60705060a0b10020c10110d020102180a05030c011d130b1e01020a03180902210106090f27021b0f0606130f0605060d020408010b180c0d0e070e011d0103 67
    0x421075a80890083d5503046caa00c185034000d03a441d20400c0c41c1c060580c41600300700444e16a0640c040d0611411244005900070000c804214270f9003042c1c007a80394540c08c10100343c41150302034442d07542c0d080300782c4814005171101800010f10000c807600b605002c540e11800030694500d461f00b181403036410150400301c4001c1c50701c40000d54030300b6940c000400b40000c003600101d01840400ca02001400c1c0120255075460012044115591081c4102c0204201c5200081503541c01a0090000d452685444140f15403400313005209001e440e9911110a610f0382d006118034101328002049000400192149203030355200515140a5012006001a4001c0c409118080c0d440100c1042045420741001c252088103c0446004207500e502c4150301002c0040c401c010403100f0340160003242c185400030003005415409004d031000541c035016a44803000400a840500d8001c013400c04000542c80000c1c040881128031860312000760401a0401040030040048488004000451600d030703200c40e000b95499 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 911533291 1250 911532041 911532043
    0x130c05240a0509031c0f30060e010b070b0919030e1906021b060310030611041a040e060d0b0f0c1c021b1f1802060705060a0b1002 57
    0x18a0500e003100000040c0c031000300c070301c114199104103030010113451480c0040b0507a40040102082c0c0c04002c01c546214100000d4081c80d80304001a01c41c4081e401c0c03d4001a82c083c031030800070303040f1a0700360740d58450101700d503800703110322a01801e582c8140f19950006400e012002c000020410070f00ca030300500b0304080c2c982000c1c80d003521842d1716050000e003200c030100c0050070700303080400200b80c1c5030410040000c0040e80003c0f0301c0e10044507503c0284201b80a03009002461000311400c4a000b10b0980b0200005005071f48000d03182e16100180d14207041d2116408140d035901c070021000030780030108041c4142540b08034541c1c0c1058040310034100c410200d41e140c0000c901c00602082400c5182000900180391850440700c1000a0311503040080d22001c041c1402074102c1140d640c1c010b02c15202e03a129005001480b102100c8008144008000c80102c0090140c010803509403a4070110403055801a10780402034a2040d210b40041d24251800111141c01c8076041ca100d01c5c0706050662901c210076030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 911534541 1250 911533291 911533339
    0x603070f050304140105040b06090603070302091f0f0906050a0f180e120c15070512040b06012307060c030506063004050703050708071a21130c05 64
    0xc15003881c80e1280d0b02e5003418885030000480d812419420041000100005a03816030311842c012501143c0d15280c0b4000e0550305c1c0583c0c08020341060340f50300031600e00456120150958600c610079440c903035495800e10742101d2400c1c2e000e918096114401031015251549407400609260a203406402e480c244a8081030361003204164015a5500030303c1c5007102c4244080c40070900140000d03540c1c0c651145105654400d20541040d200700840041001d89124108843d060300d1032460109007034845403101821314001034002030520085891120b10541b1403082030680440343d81d482512552941401800d48806880e80e00801d840c2804101e40d40d5290009d5038413620444207040c0005134107800300824070001c554010820302c2848104010044001641000c3c4e91180d01628201e03569901507658070401c07400350030300d0950049000c00c22451400c026081002d08148105008024a8030b03c500211054820805046010180c14180718507452140001e203001e58a0004844050740d503818404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 911535791 1250 911534541 911534567
    0x60a0e010b0f271008010e0102070503071b03051204082104140f04150f0b0a0e0136052d0f01090902040b030f060315010510031104170c060307 63
    0x1241c10b401c500b550011070f6095142c41034030010860003508014040ca00900d550f441a81746035820071145284440060003034500465000c0300035030401001d55a640005003520707810301124002c0400000114800300100d28007104100840c5940f0ad044c080307a44d00708000c0265001c01002030784d10144d07485a88408980440f018402c061487c50445400a200104041e10540d801400d10000700c40440700888041c084440d41e054480505545002c024000c0c0180e84020000c80c0800205080306c0d4024081e03101042c242c90301a00d007280096000306c03040760041809228050410405016908040769101000300d802012244000d5110200c0d224214000e072503a4010b07402c503031074050141d0040c1000000f62061079800c4d900d0302d882c3c920702c0c03c5542048584040340342548010403201d06001c11201130448282905150903070030300003803088002500181c002090b030340d4204080c07442c07074120107400a0305031003462082c0207100e0910a40b40c034040c4105148214410400d10076110b030840140c81501c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 911537041 1250 911535791 911535799
    0xf11060f090304080f0c010221120a0b0402070303061a1c2f0c0712020f01030b01020f030a020609060105042a0e060f1c050c1215030708060a0e010b0f 66
    0x41d944030001d00c1c0c214000d950140c0040d00c540080000c412001040c04030a42c0c600313908550041d640c041941080040c4110a02c84040d4200940e0650b130020b401d0060340007020740c2001c5070001c1c126005c58202d1780140340980000741e69030000d100d000484404c05001c0b104620000341042c8107800b01c01c01020300c12030521201644d0701081d0f600304400e0070407618600340d80d501c000c00103d860b200c1c0241d641e012a0040c0a14082d0b1200070400000a1031013807402500900f116403a56647c1780198000c3c010b0380403182c154405c9803036105900004000030f001905483d03000d8005401c290f180140f80c18010b0b08218400d6040503c60184000c940c20610079103a100d82040300500c201c10b2059940085106015070040ca0000328815501c0119002300064014180740e04c0b440c01d0300c0207000b8219042501e50100c00001040b9950514501c011025008441c09810302102c00c00c1400003440d118181c0e0080d6007a07041003007003100701481803007100003c50040b0b00a100c22810407000034011500404c20f00d1003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 911538291 1250 911537041 911537071
    0x2071103070b0f030618090a0501140c0a0f030b1903030207050906010e0d0f020901030b071803030f12020f0c010915020a020601120602120f0610021203181603080702010f1106 77
    0x4180d41c3e100c806e080110003a50100300d5400e0a69109884920030780042e01c00750300f80414a08a802602d0400f44950f40744101c0c40e042240254044504203070410b58041010789132582c0101c0f40e42e4070041801e00060b030302c143d2441d1626614001e403c04003240d100320f21840f10001040101c0e60480d09290801c0402c032003051000125103030088484410000203034100c507100c000841003040b581c030701a020700510b48401d01110011034403040e2034600f500004000441c00c07503508112500500c0001c403d03d50000c00542030821040042065030070418510039640c0d164041c1000744101ca544d44c0400d00035000095207400c407031a030302035a10903040c89071940301e40001c1125410721036590b040c1e40b090004152002c1903030400103961003400308240c540902c41d04038880310002c20341c000503c5806406043d00d400e81140e80d41d442d02082c0d03203515018482603028003000107207005c07005070446c406117104951b1301d0707114400d030f0000600d0345407025501e0040c0300d050501e9640210000079025408000718142c161 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 911539541 1250 911538291 911538301
    0xf0803091906020a1b021810090f0204030c0506040b03010b0a110a1410060e0a091a04030c2306040b040c1a030115080622180602071103070b0f03 64
    0x12400e00c000000c05401c64004070740303804000315a0001c103d080510741e204440300007a500c0c1c0311598116140300941c006000311821100000070107000394026804416503d00e160340d284000180c0d0b00821460303034000c1e4002400d00400150400c0003014060503181c0506043c207001c803401e880c3c070040c001c08d681500d0100d10f00b181e440c46021111900510304003601c100c0c01140c42d10030841c260542d2030141900a03d155090a00c0b0507119540c11240300c0c0c4420b0645483c0c01c40c401008242010040e9a00024101e4104035050380c04500c500403032103a0b0320006112a2420b01c1880342144411840300342c4445c284600c95020002102074000b90800f040d1051600d40303260816804e80030354481c00801c1c210324281c84102c0071900240d41215a51907c40c130702200d42403000c540d1844200c846907407024003030200443e0000c1020103c003910180390400640c040d07251034249150388010301c04540d0142c00150075010001140c00c01a10343e9410380003420544d08000e08000c03240102c4070007204104010001034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 911540791 1250 911539541 911539543
    0x1d01052101091e060c0f02280506010305150105040b06030403030213030c06050403021e011728020409140417183706090b03090313180c05070f080309 66
    0x42e0046900001c140c42e404034000e44030004810800007540d50798034040c89440310ba401448041e82004140d03001c0c00300c030703d09400c88905400c2c10400d100e01809140c4208000658100030f103601850140008081e40340f04410040e80f0700030b0507000940618204250700905840354005d5a402541c14100940c5903051041c0124481c070650b840589280c40e040000140c00d604800204244e900030303220113400081c442c0c1e000500910780029180051601c460800d15200c000c0c3d01c5039048081c42180d10640d40c881c12021707c8000b02a49620031040d070020301007100100320b00c10255034000000070040d9914080d2240c42c10b04410b0248180400e80c00505072036240f012400c0d01050b280010880b8010030f510b8418400c4e0301c107a8030484144c64038840d0b8810f03c0140820302010072600c05e43d444003180c60402c2c2002c4030503040507000050718802444110b812950043c4844d01a040da0b20b000d0240207003012007001070b114002540c1060040802070311002c81e0b0301a007a040b0254005503016520f4039100a01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 911542041 1250 911540791 911540801
    0xb0a050c010e0714031e1507110303010f0518090c0910051f03060b0c030a030207020d050109050d0f090e0105040b0d0503030c131d06091513061d01052101 68
    0xb008601501202050120280d0900c0c90411400e030101c42d4032079101d030341c902290f044444e00200960310880051610f0114004210f42c80721a0349005104036000d006c0840c0346800c02e802c116000e02e0440000e014a0900310f810b90422504c2146100c10750400188054450924031800c3d400754ae6900c0021383d503040988a000c0040801400c242c2c9003000044900845a1100984d840020704000d03000848514805c1625218162440550300d0a502d00009274020340c000c0600303e0704150f1340d80b03044001c104217114142c4428003a9010302501c485550008210f5400760303c026042c0b00c2411401e02000031080d00c56415980d05840c001566034405000840d00545040000c10510002003000b999822603070141501c5804007240c1d044598070f03515600568420040720b004403101040005143c3e20b0700005085c0c000c0c4d48003212040f45003121002c18070020000c103044480c0d1780ca5050070011001d00c04000c00700308100d0f48800070b40d54100310001c2c0200f811000311700e0311281700c4880c09002e81c00a40c00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 911543291 1250 911542041 911542061
    0xd2a030b12100219020f1009030c0b0f060102011407020712020307030c12060c14030402040f0e030c1501080705010206060d080d02070623010b0417150c09190b0a050c01 74
    0x1c84586036084890040071350700003a00094a601c0b0307003003111910360001454102c400307600c802411590001c2c1917001c0040800080039800c100b404200403002c0f0700008855400341c010a681d8460307601e0941e0004e400d640084200d6114032441070f04004140d6808030b1890180c0d0b112034030a081480c400d00010b454000c450308082d082c0d07403031503000080d2001c15400307450403584915414003100500800a07a44811201035a00c92040c04000107801031034281e1084400d005044400185003c100030392902e103801001c01c41c441540401d00c000110403407200ca00380104030303840003003400904005c0000d4403600f014220602620b040c010000401a940303007510a4510020780454446415040c403602403c014913040c0e00c080040e015070a14030b03107010a054140c0e06010030382d602d0249085654071500c182000504c016002c0e11408401e848038035860f260182c0d076400c401c103031208245000c00960400d0400c244615480c1700300100304902101b400d03900795407160b050203500c400304c0d013600e107026042402d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 911544541 1250 911543291 911543293
    0x14090c1b0a080a0806090108030f09010807030f060609062307083a0c110705012a2001050414042c01050a0513031d0301021209030d2a030b12 62
    0x2010700603d54000c000d1841000100c45080c00c0ba40d84d880d40e1a240d01c52001040300c102c200f04000007603540548802601320b502803400141e4010810419070403500070380c10140010b452080704010441d032008007081c101855440b2159480c14490303040311340703106681b001810307100f010444540998150041568060310f1864004c164036101d206805c3c040030824551070350524000d02d140c00940f0603484510540045002480c16504090041d1014141710748100140303200204ea107254403a01c408034080e05c40c8108040041e61446021200b50240c503100c1860400c01d05000c00c0200282c0d54142502544041d03500091410030240c4148500e0101092200c1102c150f0ba02d0419038441544018424850310740200041d4031071201c01ca4042141c1c0790050006104841888403403e0142403002c1040e03402000146803111201120301c0d00a01115004c005405c049822050035420b800307080310380b0082c1800304002181d000601540b6607180c00c6d29504140e42e40c2e041c0d5840751500c00e1480c0302804100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 911545791 1250 911544541 911544547
    0x9060d0602040506042903010303080f0415020c030c010c03090b0c0f0706050403020a0c080c15030c0405030f0d1806140d061e050415050d12210614090c1b0a08 70
    0x2c8404403044e40c015403664450f4101b4101c0441020b01103003568182c07075250f03860388900e484500900302110701c064000e4401546c9807400d00310410b5180f004003058500d00d00038580750602403241030300310703001c8080034030030326003041c0740038000a140c00c46150b4028241c1da41d468451903040c0d40d2481500415000820303440c03502042c001415000038540e000b03503106403c607441e00da49802855484110030040c25405c0000410001640001c0f030f800380d40d2007060303505020b00b02076503500000d2038208441c100080a40200078500b1110f0b92188508004100c4540d001141501c1e000c00105a03031329440300c0c08500302d0003298006419200d9004803000b031141c24100c00e001540b002101c020381e041c512070319124038644007902403100c40c0d000c0c8400c2210f00080c10300a107000c06458902550620341024406c0201020118102d801900e8008640d40035804000500909020500d840e040070307000c00d60b1003143e541c810840c4113150340d01110301c15221280a20901030520106500d400910f000c0102440004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 911547041 1250 911545791 911545799
    0x10b10080109051303080a09081608071401060b031b09102a05060f040c0e0c1305030a0f060e070f0b033112090509150f01030b09060d060204050604 65
    0x600414103840d1002c0b002c000d40c0d111020100280242d00e100200820007980005a112181e6408880540e0088018926001c0d01641414003090120300854401001144a1041c4194808050410042c220007000480d09102440c00517010050045403030105420103021030b81d08041c2034444208010740110401f220284024040d0501c403000441d401b0070700d03a00c103d010322507404014640743c2c101001c1c0000351140301c0381181114000308183c40d500403224000419040900c9928481d0150351000d13a268980d207412028284074941c81a80b1a50100c9881d00c042170204032482c6031254420070000f150100410350a0030030300d859200d681003a001c402c1c0013482c81c1c0d40318000e500c10103a41d90204590243d0762110b122042c0c2e88070410390184000900900000c44101004a074420300c0d04050a00300e0307030f03100004c181c0c16080b660300b000140f54201454803070804020101803200c090805218040303030880450019040108075610503012140307000c060103415811070b406040098081aa01ca8a03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 911548291 1250 911547041 911547047
    0x150a170a15060b0904090206040b0304050c010810080d0c050c0d03050714011107060209010507211707171f0e0702070501051603030207031e0e190f1205010b10 70
    0x12042055904064120340e0890807901482104190f5084400b40c0d03050007071110a10005228118003240c00560410002ca100111000a988214031034401890313800c00d400b00040c4421405403102c0704424101c00140b1601001140160003890240f801084540e01400c14501d007045100803140c100c0d4240010304281a8803038001c0c00031a02683d00350740558141c0000347d08840b602c11800c49005403d01150300003642c00d800038044101c0500d09103040600343c2d102c0d040900f00ca03001c2148402e03000082030900721327084544040010789201c03607081141340c12500038000a5101410341111100c3e400040c469040c0d80142869165075004a250015154071041d050b484003507035450054461810000781541c42503045424424054403c02c803d21074665040d4007035040715400f14140401e180d80b13070650018207a48100190707150740c2c3c1d044288840c182404482c1100b040c05c1880042c01e41c0703083c800d142240a941d02210107010340c440e040035060421b1401880210034403540100744450040c3c1e0964 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 911549541 1250 911548291 911548303
    0xf040f0b010b0c06160807120905120c060708040b0606070204060b0703020f10060522141f0603091a130b0709051005190f031e0903110303040b150a17 66
    0x22810080342c4080e1107605e480c0d4000b01c00120710400003100350000940e440c0c8240004514140030110219400c01c42e50340e0b09050940b45040203074441800316484a40e494200145d940010303483c1014261801d040c0c071418607071900201382d030f4001d03800000c4220454503164029001840800c803844d440d451310303280003519040030710382081e0075229480003000030300001d214200841c1d4008003200180c0d07e1011000c0c2c41c0503840105180d940c0e549504001c034440340105403610078801466020000042e01c0750b400031510b4940c000c80308141ca481c0c202c1c4001001c0d0752100c0340d007420540c0d04c2c000c0e5684402e4280300400c0c014030000c192280090a1111180c0c010460406891080318400c4803c900260111001e008214141076140d18000803000c1a80c01007003e591740802a140128540d0281190710b600301440e650011362683c2c1d1041c046050640c0076003510040c0340384802440c6107041c113442e54902c50002070051302d8402035900e0521050b9503102032080060072814130500c107605080201c55280c070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 911550791 1250 911549541 911549557
    0x3210307031d07090c030e0d111c0c060525030507080c0a0f03050613090c05090a090b0430030c09060302130605090402070606031b08010c080f040f0b010b 68
    0x79040100354118410120b560384038078000c0d5070082c01a03501d05280c48002d01610502d04007816580e25500c20400f0080c02041c01c9882e1030b88a070309030310b8040d00c00d81d8a81034600b410358090010b01001d00e410903034080c0391400301d1070700804040f425850303900c8031001d110440140c0c2e07076510301050075001100b0f401d6008903118035125101c10304640c0e910004003805114440c41035001680d8104004c24075402079110a0300074001518041114002d001e038001140c1c1e58900650b095075100b0350070042c07450b16414903503109544440a201e0604036581d002540c54014000412400035400401c004119220038003070401c192206905008809450140013404010410300c00a4011080465500c1c064000c89248020b0400b015485505d080e070300b102c0300d41041c0c0c0c5661388150204003040205805000d59805940900481d0030f003803010690807214403007994401200c590500130f803840c8060708003c54603440199100e1124451341d03907180c008001103140900411100d2040000718a0503c510068200c2c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 911552041 1250 911550791 911550797
    0xf050d110d0212040c05030105042d151d07060207030209070215040605040510051909050a02060a18060e030a03030902041b03051902190c03021f0c090b07050a020f03210307 76
    0x17a91148140342c00d0b540c003110040e0003241041020308501c2e05684174a425043c070202007603c0ea062564904141c055806240764806481e124031810842003010082c184440c04002003054602c0c009011351241d030503200191240c0e504100041c8001c3c024050344ca070340f907540c0c0103850252030700d8584000281000c1c4c0e42030364103119016042e80220254851540100c00c03401584c402c0c1c8031080487c4015109611049403035000703940030400180c50b541c0103000c00850f02d8540031031030000340884003d404415484482000840100903580e42ca001c1102013182d81c045c500880c1c02007450001c100549144041512010030794480f41c14001e034158045030041c0c8030344112100b141c0004160f032003a070180709040041540c3d220404926035000300c0960b65807512038010380d07450f4401650804244210802d0381e102d400e0b2518003072682140e2058190740a06083c0740031905210041d110b1340d0b6900814080280101a040d00c40c6400d03540420035149036006035082c40010310002c1c1c0408102d0303081500c8003004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 911553291 1250 911552041 911552063
    0x1050703090c08150105060d0f0e060108060606040e070516081908010f0509010e04020409022d09091c051e07060f020408060c0d09171201060f050d110d021204 70
    0x1c0302070210705541344c82541e00d840e91042e420003040000642c480d411481d41199605000701514503207000b0b00030300228101c0035110075131400d00c6007810000000c0029101305402c000c1840071006143c0c01940210441c80d15035200d082030441030303407a0900d141000d02002004034809207180b80f58490880d00851660780c07090141d81c4d68070303005552890340c020664050151001401660b1030520140e40c001e000a0020521000d5600401e44941c0314120300b080314060000031621485044150500340f441c1078600708030910308200442d4881619034665113415141100076a20148100c2c00d6520030391524590403075044000d81c62441c25030003260200c9815041000b580b4024405200392411a83c20201815455480d4428900154880800600306540d41c1000754045002c01c0b03941c8208528018021f42c0e14401d203140c24010240c1680701c00d0411a030002d5480326a03601c0019036051080303d40c0c02141891040880461310b002d0614010102840450001c0c28041900c0c41c041c042d03401070a400907 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 911554541 1250 911553291 911553299
    0x718050907090e0d030e0709141605031017100e010204060201180b040312020c0102070818030a050c01141b01091202150708040203010b040905030a09080c03120a020f01050703090c 79
    0x4203481100540d9142d41d000303a6100d04c085406a00300b40603900d058400e46040a0b142e0f4801030444064000170080540444100000302030300803142894000e403428207a0641c0b40142560010500038001c00d50424040c82c045401300c6c104002030203c5046540b001e002d07098074610118000d401a01c80d500040d0f0030314011884060341c442500c0c0c081c07030b00b00d4294086030f0f40301d840036200c802c004e580562840da400c101d580f100040a101810710b0034460240507a40c0d00340310a07920303100400e003100316200341c00c000240c03c000b80c2c0001e004a45210203007044159418000090b0911f80684484c0300303210b007131401000342c3e03020065004210052055205281c144a6202c0891361006d080c0032001d04410303601c0120b02038600651030581d116100500200b4000da41c0d8000c2415981c10308021103255001040340c10f191070304070801700c000e001c120000f0001e03500d840780042d82e109118443c1804484e0001840b0000510034000b80851340701103002448039080c8904010028a44440c081d80c1c6c140007000c0100d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 911555791 1250 911554541 911554559
    0xf010b010e18060a0f1d0a02132705090a03021c1704060e0319120e0601090b0f090702032109061609210209091504060b01020718050907 60
    0x244000301c0605090240c000001482d03220010150180381d20403050b00000503031004185020300686442d442c0b01204420161010031a008090305440c0342c580103000c4010701ca02220038402c1200e00c01382d07004100d5401440480c0c1e82ca90480d440c001c03810308040400426800004900b0b4070144241d003261b0312108880d10f4100040c00d003001da14001004443c00c0726600240001e0140c002d030051200041004111a803d855075010040c6140820000c1c019490a43e0b000104100002003680003801a01071004000e52611014011007100503554000b10324a601d41145041c032030440545042c502d0300b40322001960325040040e00d00740740f04164001c0c007001c41d84904110b005010580051919031540040c20b9415910701204500f00149084009442d204050008102562911030105802020700601c200254010400355440d440900e841e01c1c00310b11150b1090f80240c11240c002140e8010800403400c241c101c3c1d00c0108900c0700348100210809050340564040e855800484d4100c036642d00c910 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 911557041 1250 911555791 911555807
    0x1713151103180a12030f02210d050406020f040b030406050c040515030a1b030608160b04060804240b031b0303031603060e04060603030f090f17010e0d020f010b01 71
    0x42000c6400c107000380b021208400a45000c0104000c0000d508540c80e00699094000d24100980000d5003030400715101035014001c07048038070b90f2001d20f40c0c107200d6141400c01440c41039260440000341e5500015081c0080340c0d058070140e04090010340e42da95603e01c846c0c80a500159400d8851900c0c180104020300c95900c101d43c103d806c081d001400c0d45900343c1c145400c9030001445c21442c180c949004016050591480003a40c998940f40011150b00700020316150003d031504400340181495414004074180d01c040d202240d03050703d4040783e55a0b0f18500742d03072181c0c02410303144503000c000014441210310a40085140f0760041e021144007119585603444820302014800e80c054000704080f4510b00700d0100180900c828508000c507000e40e84400d11454001d00710740c05d841d0f965492a0920400d5800401415040150702d0071011803820119551080901da209005418a0759200300a0a400039042040959840c81c2681c0c040345c0c07901c0b4081d440c1e00f00c4114034140c551070400001400d42c010303214 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 911558291 1250 911557041 911557067
    0xf072a23071202130203060f2d041a060c03130303020703021f08061516080304031112040b1c1d0c01031a0f01020a12020d020615010f0c171315 63
    0xf404c0719840d0a0314000f0000d40c4046d1607a5003041c0e151354926010385861080d07005525a14210340f520f500d201443c1c230890741c940742041e4031450914014003980002e106281202503c1220750355a038481c500111803071445a010440300058252070000140368000c07882008481c0242c1303200300c008100100b60400903a508001c3c00c085164035010611a0500d016259480522000040d15021289000c90354000441c10300b00d03007007100003040000b01584060300c101e540b680200140310300701842c100d0030043d0180b4014804400808914108200f1110059010300305030f102c020048120a851644840c411030008842d103031088008112813075109102d80e0143d611483c41d100200036902c000c00841c00040c480c0c050441c41140d01c443c01192039100054400540b40c1c00918032500ca030a00a410614000d0441d06005032a1404130f250b03980019180c1c0340f6114914000c615068285400400800c610504140c03000c0d000c101032100c0c018421260301541d603104c046408440c600e4200b00c40265542d64 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 911559541 1250 911558291 911558299
    0x60801150b0d0c260405190308040b0603101a010e0f060f0705010f0c0c1a0c030f071106160201060e04020d0b040c081b090f072a23071202 61
    0x212500e440d40701580083c08003000e500d0403050810611301110303100d201411303402200a02d00c2040c0010000f04201951915072616612194100c0a0301d0143c201c80005102600d1a802180028084e0782c0611100d101c120f80e1000420850072105070320310b085503c2e400300794046080000e41080b103140045003002e0301200280382510b000b403032a0102d40b147c2c021040445d020364039201d44025600c902d014280d00114160b40b00343d40e46c0f10f1805c0544020000903941144402c2c400c0512103280d2451007100d501c581c032601c0040302602c40740b1080301c81d411201d0b10404207009540030f1101e0500032179043d901c55103099000340320554942134100900756080d1002235004100742d828000080840d4541170703001d40a13184c0640c03d55515145141000380d801806404000f840c81c040ca11840c080142c55040005503c4248041c07800b04030142c00c4601e980181800240b1201200c401030240d60f4002ca15150300464000542c401110804420400011030720400c0c01000301c045250184c0d00c40c4a808960014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 911560791 1250 911559541 911559547
    0xc010614121f090609020d0809090a020a0504030303110c0a0804050123070f08040f240e0904060e010b121c11070501050a03090221010c02010e0312070e13060801150b 73
    0x1000c020003001001812141961a420b8030b0000d41e81f413140c008200c42c080d0324602e07130300e10f81c003810000156401401a002c130b038414007180219981c01020389003031b47c0e494140018034503041084005180074200c40d464180c8140e00c642810000d05401400480384c003a00d0340d00e81545c00f00d5000030800210300e40340c00c0d5100d00f4004c00300031400c0903015522090061000e68a0a0345440c0d80da209020341d9003050100c0648508041c501100c44192009609200d1628000305115800029280c1002501c09056a511030581d1400440300394040086418010302000c0645094031034952102e08501e542080d85889082d031a04050081d10110b4900385a6006810400d0610300190380d0354200a08503002c04d60f581300c1d8440141c80c0e4074001e504017402171401e03020440210a1072030954070340d0f460783d0b800c59042032400384540d840007083c0e600c0d40520180300c0100d0340c7c032014100d0f5011203581e40544e04c4005500c613443da810b010344c0504140c504410081c480300480c9480e010002c03a0610440003221820 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 911562041 1250 911560791 911560843
    0x9090b030c011d1f020d021b030c091f140a080f0a12090b0d0b031605130b2e090f12030807020f07080d0e150f0f0c01061412 55
    0x201020f081098014501d0312241060032141d00c0c4c82030101282e07409644000c01d004005501003109110001190055041420406011a45881610003124000c02d05030300401e00080e1007a80700410300c034284000c034600c10ba03141c4142550100c01043c041c001c1c600000040fa4043c00460004600070307050700203140b07403e40d59442d20340b00707403e6000c07200402050401c0420740019074001044824202c81010400c24180c508160510103002640400440842000c014035100c00040e6081c003c01c0e80c00024841004201041c04c0c1400c003050901800c4c0300041c2100c80c5201000785501c140303902da8807030049a4443c03d503148800c029024200605040c03032800700010348030782e031540d40c001c0320707841034424080f11107401500c0c1c040c0030703004500b40b42c00c0030b010041030380d501c0713a5501c008a00440d0100c603d103c824402e14040c0c0710320100c4d090180030000308248100e55603003c079100000a10020072019648041c16008080340f42091846444401c0e0510403402d40003802404124894120301c20b11200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 911563291 1250 911562041 911562077
    0x40308091c120c1b050a05061b03070309031502070302030304080702041d030a14270303071502030703050a051005101b0605060319170711030a0309090b030c01 70
    0x2035101d0012403180903408a8002040d090000030b501800781c8a0200740c031600d1070100f4010500103814002c070b903041a4104210365070074080b003007282c5059a01e95641d040401d407400b010045001c801a0510001809100b015440040035080328041d60f10f0101405003064007006a1280180150041c1d00500114000c90740e8a4024112103200400018034103c2d5400c042100b42c4520040300196003000c205100103130381200c0041031a0286a0505151098505106040e004405900b030080c1503240031190b840c0d00c041040390300050300145140c9003c042d61140c0b102a500c00c540b0800003d06000108001500b2401031070b0080000191641519003040300340026400c03180b5600c0b040002080e00024400007180880c40324502440c00031500340350000515161035850701c1b10000449901c440030002c241415000da0074400c42041c5582e40f45041d00f007100c0117a00e1071100f036174140190f1a4035000c05400a0490040303900184003070107261165030800d501d0b20341900106020440d0b0038140010600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 911564541 1250 911563291 911563309
    0x408030921121b24100b04360b010e0a14091909060905150403080c0c07050a0611070501050306150c0f030304050d1101090314031e2a04030809 63
    0x40c01403004400082c1071800d40f8080b04e0218001030591036181c0a0b0f1000e072001d00340755005045014480300c491034012030011612a80c032800c040303080310b058001d203c41c5c414084264403a03281044010342444140c14080203014504a16022680002c120002400e0a28210040b02c041c03801034603e22441710207001038004010000300314140c8202d1004c1820001c2d1107901c80309805040000390140452808910f0310500c9142031072000c0f641c0007004000b0380d100032080c0d80541500d0010341c4420040755118a800381c00d070440d0b030f03003c10a0303600403c547d0307886420b4034140c050100c121480310b5034840040d070303ca01c03041d10303215040300801178002c00c1705400030010600c407500101191001c0400c0b280c0305041d0b402c165401c8840703800001090384100e0f0b000300c690080340180c00007085021000c0e40e0103800800c0d910b980c01081c110100c001842e0002c041c00d8060920034175886c0360114078000e5100d08544020074814103c60700f0b030704140c0c0350140200d010740342940e0b030284d171262074441200c04101a603e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 911565791 1250 911564541 911564557
    0x1d0a090c03020307061737090c031406070c050309040c02030715020304020a080303071d01050c0715140910050313050106030303020406080a0504201203040803092112 73
    0x9440c014000005840801401c4014030780d40c0e40300e12403030f90b01500c1d642c0c4404001e4a0b0302240c4241038250f2203803a150ba404011030264001620305607403c20f00b040302c080d14280b60050302500030f202e40001880300c0441c82d5030f862801e0b1001e844441e96005019100d144810002406c168000d00000300d00c1e06143e407129079595103a00469090410030341c0d0700c020f240104d43c4440c90140c0c000c02408210708005050320050000b200c055400c5250078031005285940c2001c02e21095001581d115486034000d80480300c40c1280c150039900865110601d616000400007008400070341c014400140728040e080c1901c841103c002d20701620301c1c503900400c9070160006045c12804844c03c4242c800012004d01c00c010086120b40c4016131034902d441d2006e802004001d040480030382c1464108400502054500d47c0e0100c3c620b070b2359130507030002d00002c600c03406480883c0d107005210008020900c10800000b904d0007070001c5590811100307411031801a60a006010340000e9485291150056109440071b0300c440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 911567041 1250 911565791 911565803
    0x516090515210a11040b0d030507020f060f0a081501020304030506160e06120114011b0213230105090106020f06010603110f22081b130f11131d0a09 65
    0x40c072503a0080608003160b43c20700312120001003a00025509080c0242e840c0040111409000d422880d2805402881079003002840769800c030750901802e5840b102600c8a4010b000c0301e00b5111510040050120380050325651250200910001c905601c000308540a8982c000c1c080c01064994010b410b40d06452101000306205400041c80e0098541001800e07603000c441c402c44859514111600c82c000444150050421101200c0361002d6035205450142c4664155110f00c1e0122a00f5100b60003003a00da5420061400005544181c40303c00c44400c90603a5022624501c281c3d9841000f81d950f0604080c0c9141560043d2004000b524040e40c08100415a101802860702200d4581100d00f0b900902100c03940074002411085114111121171025186140c010007442580607840040c038402903500600c00c180c0002d07060302210b2a5000340d10b2104042c0410301124a80d030101c056540c00040d05031010b007000141c001452003a8a8a20031030360000c0b083e0035030a407281e08902000d005400d80c1500c1c0d0f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 911568291 1250 911567041 911567089
    0x12110f0d23031201031203051e09071e0801143705040303050f0a0c02031e1308060105031605010c030e01030207050d020601090b010809060a0b0315040516090515 71
    0x9507a414001044480d0043c5401d00d507642c1075180550480c1000d0000340304251801e010050b100c50f961040011418003400d00701c28540c0c0346c0c141c0a02c0c0c020f1a4000380740c01c00c010380d03031101500d0780d100c0081e050f036445100901c079105440348424507030281141c2a000c9284410a015009864101c1400108400006140345400b03003c0b020416580140d0f001c4000a99640c204141d000f62125103a8100002800521001e040514001d55a004000440300400c0401840b4103c4000c0f15040b2203100c45a14940c18080c1e589280340754075060301740f08050207070140d9000d07443c500302c0180c04d44040e00c40503100c0058860030791711700315030314844040710300e0506500300720100c0841c50410481c10070b038241c3ea0051050350706042d800d40c00c0d2140c00c00600d05104d070075800d110320f00c507001c00c0c2141d228031410310005141c10740c100064038050368204c440340d0114400d01400180b040218441c61150318a031110300741d00b075640c817580382110001c83e0003204002142c40350125503e031041e05604402090302c44401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 911569541 1250 911568291 911568353
    0x408013207022a0906010e0a0e0a02040918060b22050601050f0d0525021005090307080a09031b0501020a0303050c1b0c12030307020d030e01021312110f0d 68
    0x1101d070f0418900341d001007010f6024030060b00c2c00c0104140e0000d001c0c0f070651001140c1401103a0700c6541802582c000c4d8580e170000540b602900d9042d6002426051028041084d800c1240100c034041e802040e0780c1c85040c1600040541007804215040441c4c4220103c0383c000c9500004d0014840a006681041000c00c084c0402d00d1040c0040e02540701400703000240e03400c0c068582d00c0204040c90481c0e4101c030007101010541c540205144841d280075540216140d52030604c000d086208140c0c004001401c0030070001c011a034030150050030340f0300c0f5030701c0c408074082034003201002080c40e4812a80142c5c04452090700080c0b20390012904071b14450360007410140102d19003045030044403000301480d0311030810311495180c1120a1305644031603c01031440c500306080c0094407580080b0030030003415103842a03400b1031202581101d00c2c1c0503040140c044465205c1d9003155000702e080206030ba6401c42c498403c074562410881034012450008d00110b2440056520014a1420b00380013403018104552554 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 911570791 1250 911569541 911569573
    0xa09090e03090301060e0606180319050d02060a14060409020a080607030905150108062a19030b0405161805182217180a080102040801320702 62
    0x4180144903102540d110ba16103002c1c0740c2180c00c1640300e042210340220a00541703851700000c41e02521140762900f41c0c0c10103407101203444c2010045a4126003100035260105000022500c000383c3d542d585c1c25912640c54400c8001c059841e2000310382d51140380c14020030708603c0c00d64005032031240b0141c8166015940e84000300d09100c4119887c0300402d8440c0ba0100410a05003c214060088111209000d50501c100103986590041008052107203040390800034942c100310525600b0002c011441e40d540309035100d89034442040d261380300440d060a100150130b00d06409000e1141101c0400304c0203501203500110f403a103216600c1c405000c008814042510f4881440c1c08108030700c0c0583c8180d044c2031284d04e0100002e28413400e0351044160300c008a00058280100740c01f543c1c041c1014a49400d8000d445190b1090b1700100300e40c1c02011504005120302040d0050400c0b1007030100200a450f02b4070700700f1130041090032500d5042d00016071803d410302c9692007425800150510488a031048607000007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 911572041 1250 911570791 911570801
    0x8061c0501020d290d0f1407050a0626071b050606180c0306092502070608074503060b0f0406060206070c0201020f0d03020d0606030c02070306020a0909 67
    0x2503500742d40019005100050034051806015640180040d00c1d1071140101140d5284c041c00c018882c0101c5100078050040e401e02864586030045c115105080d5060407c60b80c681d124401e09005e1a1241000518030340141d01012040d092201140407203e428000c04207040d00061180c0d00740312603c03688541081481151f102c40b603101e40000c000b01d08102080002220710454820303400c000701020811380501c0402030700d400c81416500e540540d03e0f024441e4511041e07865100480100c581820788002d0f60020752030382142d600e034072038403081d84500c102200d954414810440800d200c410b120740300505407411040c40381d0762000e1b0940010051019600485101c0e03841601c81903200d80603d091440c0440915100c00380c21101001000d203000c60280d110702000340600107020314203064030190390003441080561003001c0c065480907024803001a0094000d03e031020f80d094a4440041241d500030b11405600904580050040a18580d00e0101a51100c07203030303008004256100140b44c2480c1c0c00f072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 911573291 1250 911572041 911572043
    0x120709020d050108030412150f0c0503060f01050423060403080a090609050303090a060c050c03072630090d0c05100c21020705090a0212090601030302060708061c 71
    0x580d4695074034030031005851068025a05a4000708001c00003081c0142a0710309031035008641040c0740c4600d100f0200204152541c030004241003003065451694400000c1d0322070070b03080710542040f49034113004417803d01890103900c4500e5203980c071001680103030840d0300581e824004c265034a441c0d125960225a0707080240c001002c50141401481069000755030380c005414141d0045082119140004851300182d00c100d0b0305001c03055007081c007402400d00aa411041000e4110380001e035550075174400c1d040c40003103500010601001122000c000c08a10303120720280e41c402c0071148801c511210040c200c021891040720f483c2c1007280c1031050310341901c0701506500030080e16a000c0c0c9041305010185040010340c40800c8580c15000c000540e03640ea2400901281d10190301c491a041c0720700381d00d080003a4100641c4500140d00b04242121160001c114400c0ca101c101c4666494404000744d98103001e010050241e0001400901300d184551103540c4c0c4110000d01c2600300010b0042c1d26140b05c4c0c25800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 911574541 1250 911573291 911573309
    0x301020d0605090703090c0b16020a0b0a1107030507210506090604030908150109021803120301031a07082202060703020607081302011b03090308120109050a110313021207 75
    0x200003d2070519070542d80440715040600c002200703540c85d802403c1850048e1040014040740f0020f0081c226901d0782e4480354050007100c1e0b0b441d2900e81d4031170742da001508a04009180c00586404041002c200320b0100d960044c020150203041005005581c1011444090907401c440c00d07440224508001c1c0134040c40b00702014000c03a0500741002040c80c0703403a4100300b190383d0081c0c070030401850b0a403800c0e03411501030705801600d60001a1030f8401c0803030365000b82d42d031600c01d0302e00151100c1c07000e200543c1220310601c0c0356100d4034040d40500c0ca0000044565201003042d800c0020700b040c4465a40c200216541c0c0c921002402491340042c110303400019003900103901150400c40c9a5800030615a04803403038240425005009600080000200003000a07041d05402500d00030140202841409194010101915001044c105a403c00d6003445428105420700d40481d072803c0701403003001c05915201ca4014550b41d65500b499080800e2002c0490f080000c4044210300c2c0c801c00d00030a80500348c044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 911575791 1250 911574541 911574551
    0xc0604060b040b010c020d24020a200706050301120204060308210601080907051509030105180c090f130f06050c090102071a04060f03020d02070c060215240409020301020d 75
    0x70302400100c0d98418500d506200b003900d50100540d4035515121040c070780c0710149030b98040c5480c034000300404001e03416001590005c44c00300c5c1c0480d0004450f5414031b07245848203402d43c280c5100c495030740c006845410049203040005000c40a8030109090a00780094400b04800c0e55a80c1c078044207500c41c090340d101458011103080b8484c1000b0b00507a4002000740780c06d1383d0b01c0c2480b5080d541ca480041c0314041c0b1895104d02000c2c0620302d01e0090300c20b0a02d0040082005140000340110519400c100022240c000d84006c0c41c1c152608100c00c602401620140480a030f4501300c003091400103644c0c096804008801c1e41c1d8000075840d004491141e02004c4000741c0f101208400603240c0606508044005a05100c5105100c14100c0649088412500c0c1000c0c0c0c100d40414283c2c028411482501c60060000450344148240d0660307644c2220f240c0c1c4d0850b001064604207a202c1808103603031034444400f00c210b614212401503803000000990003000051102d40030381c002402c9a1007182c888082c02c2e10340e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 911577041 1250 911575791 911575811
    0x304030209150f03070807053304060210141605090910051207030503070206131e03030f211a090a06030b1311010f05070b0f1603020f0702150c060406 66
    0x10300c0003c0c0141805800901c00c4508004855444404078094140a05042040315080e0340c100c03086c181c44d84048080c0610802c1c5e981407248051307032103401110302520588511801110540c880c06d0741c4c020784011020082c0e1a091501244600f0060100c003c00c0b80c00c0c0480c4d10150796159500c2d01901844034003490207440c0c1800d00540f40200d179000d01d181e400c030b032600300041103001c021900303201c0d030444035555182480f00401035103003410f4103c14076035068500308011403261071000790180ca010340ca031000c40104046007224031041e40540a90b00e5101201e01c54000d0445410890094150001502e04000c81801164004104880303500c1003d403540800c00174032104604164202c02c0c01e80100c3c641081e04e0f202d6510720686000342c00d04200c6980f0a00e184c66200c1c1c016180c1150303129884880500709001d291011120546035520013500d10340c0080c145e14028800c8038140d00d6001c0385241800400e808001c008900c1c0320080145c04020080c1c002c0e01d020a216480c0b0131031041a0004100000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 911578291 1250 911577041 911577049
    0x3030906020708060406090f140c0310092a05130b04050f0f041e02040f020c15130b0a0b04140a0c0311040b180901080c01080907030320030403020915 66
    0x1588000c056401c1294180000f190204a85030701c04d40014011401450500c3c04550202c2080000b80c0242c4081c407124500b03507800b01c0d5040210304201c0454400c2111100c04030102d03106034400510302d10101c22007440c0d1709503104100340b624034020f9044445650f110046101074075001c84d0110115500c02c19840345180c2442525000b44602801403641d142c560030a0900720700c082d0000c2c2c0101c03895482d80388512282108070920365805007050110a40070b800b510040d400030041c1035814003580130b000d404071090710b0850340702e24103000f8241c1000003207480300450080301901c070107440e0741c90b50086000e0343c445015810100258900d144528540004031008584000003242c1c01c140c10310701d05030400c4c00c841d0180c0302903c0307025550300d03614602e0030403603050b1000510513103400c000d0b08030000a5454001c0b601e09503110003a20b6840c426950311a5440c1c03610128003005021590050790f125031a2140c181c0303031662980c030310202e81c81d1680b66000940920803c0741e5024000503410351900c05420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 911579541 1250 911578291 911578307
    0x515100f081503030703200a06021908160e24030907081c0302030a09060f0e0d1107060f11070806010527010e0a2901020607110a080d1b090303 63
    0x2200400b00310030040b841c0042c0e102d00c0343c420082e003000f0304580500103090782c02440541e0607001d4030444074004014503044010b500501910340050804000b000c1c03c0030b001d0040b581c403500050440c80440c80079004240c0d440e400c21149260002149071030714094800316010f0310200c1003410900b039242e28043d140d417840c0c4081038116103d00e81020304500000b0104554580c40e503a05402d000d40c1701d6a0380c51070301004108565003d40180e0030710301c110b80081407950240409003105001d13100e035441c02c00401d440d080c0000344280459840b04400f004514819000403070300901e5403030b018089441c0ca8131054900520341c3c0000e500d94105000401c80361500307100c0d0f00c2003012551000a45804032078030158404030b051040010380502c0070700052441100d1380c400c0007220000c282020312061041c2120207150308000b0514050300c6480c02184440b030040704480c1080d07034008018054484156101d1071290400464a105a41c940c1b602c01c00850082c01d5075242441c4607035a4040b01442c60400411900c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 911580791 1250 911579541 911579551
    0x204121a0919030c060b03030d06030c0812040b0d1b2a150e010f0c0201020d0c0c0b131704090c1403240f090405070321120515100f08 59
    0xa0b02c110121003504000800c01e40700d803a0141000c4001100c076090040241080380040c5a05000002e0f0404807554a5400380095a00400c2d00306051078958a48588d980c00000c10769550603400c1c00200300000341d43d0001c1407121030b8504046022064103c0180030703032440c03216030000710b1002c03080d4060404244c14058035140392621b98030508507040c0c0f01c014401500410240c10a43c80d1009100d00c2d180035002008090034504040180e075807000e000030300035044881c07040019801d040c1d86e4450240f18441da11340d019008180380b002c5440740c0481010300301e007124040311140e010300d060b03009644840000e44003c080681010a900030300c5540289918001000c1112544040c814407880c4112401c50007282003499040d0b1025103401e400080c0c0c40f401114103140e00020030001c0008010300803070100126440380813101d00214001d03803030100c01ea01a10104000aa21000d41201c1c540b42c1d800090b0080c0340c90385038603840d259020100e80d4501a60640901003403203a160341d420035a105160680c02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 911582041 1250 911580791 911580793
    0x5040305010e0c2107151805091005191d04020306070f0207091505121606030204080318011206170d080402090c0906040b1815130b0d0204121a09 64
    0x10f00d00c4000039040c4e1041c0303612400240901120201c144208000010146c40300741c1c014404e9185160009241990703042c403550510190440008407030801115007405110032040308406641000c0621004c6103038005000d00414000600060201e402060795650010303212003c06c00340b400f401814030380780003d0102c60400074450500310030607030b000c25000e0503074504103008601e6141c0c80c28542040d0205400182e8095030b5020020341c1007200213408031102488070308003042c190b80d0341d07416000c81c0a03921030450250810882e031455034200002403098600305040500e021b54500124030300300e03140c68100c2c0513407a543d421100e050000c03c000c5020710950910302a2140e01e841d90201d48070711300140c000e188600e0040343c044150f50f00c0a0a850281c91303200a0745446008002210005165a9200c0c034015140c0e00000105400c1035400c5513001d032803600c424401945842c18800c0198020440890099400d0001240c000c40d0908060143c41c010402a40a00607a0541f00704000c4050422141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 911583291 1250 911582041 911582053
    0x219050a0308090a202b03030b030f100203180d020703060b22050603030c0607020633130b060a0503100b190e010216030f03030e01023a02030705040305010e 69
    0x3005403042440c1d04416211404c003880c05c00c0c0104d00c00031a0b4000c1c3c401c00d14503000728240f0701d90f5101031740d0520500a590510241181e0418036460320f5450780101116000300c0d041010816140c3c0045410112450102160300e4020f6601800c00c05034200e07020050f000f820080080c03243c07038059041c1e11641122401d881320400c0220320701c17400c500110f000d006901c0d0310008001c0d50701442135600e8010100151035640c68907000082d140c51013103500805881d0440c820b4003c145006c00c2c81c4000c9481c4a13107002d10120741e1001c0002410740801003c04058941440b2803680d141c3c032029001c20300084d25210b031241020b0500c42c00895071074102466002081c0440f541d05440c45081000101c0b403130501e101000e42001c0101d0510981022600e001d002007900007042040328024100002e020340d40c100400c00c2c55903405400c1c1d11800368410b41020005000c4111400c0d000101500303a10003540070000301140c07802440a81e002107400c42c0105402050070400d01500f80228a2403041c1d032005041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 911584541 1250 911583291 911583293
    0x40312020414040905070e100806130218090f251a090105070c0b030705030a0b09070818010f05100f080303040f080309010b090a0e0c0a080307060207030219050a0308090a 75
    0x4000ba08100071601c55a00c0f80c1020081c00b2041c401c0e00c01419516603100614a0010b01c40040034485115451561013420300045880a111840d910155801041c0c10410b50701c26200210f0f210002d410190103015614095620314001c2000702c038240c020030f001504900c00d2220910045616a0240010124024500359405a05c9040300c482c00001d0030015101c01280c202100c1e503003a150800940b80e10008184541c0542060186204400c030304c00901840b90101c003880324681080d24042c020895407004100020242e468010070703008240000181e00c6031a020010603590156644c1c0706011511400340494040d10741d014010b0241c88008502d5820300790b81e9450303d200d401401074107415003c404151118001c0d040802904001880d102160401041e81d60003410141c2e0b25460520903042965070134180344911074125040071001c1c505124181d00c5410180d40801400c60031402003080d20440e140800c4603040389035000b24028442c04d02c4910303000d042e412015003000701941c072140d2100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 911585791 1250 911584541 911584559
    0x603010b03150a11040308070f060c321c05090c01020d0f0f0c05010f1a0406050d060203060301090b09030a0f030b0319020a180209031603080d09290403120204 70
    0xa5000700602c0d01c001840603200880345005c0c01a034000506454000a059080c040700544a050180c00b40e14100860803940ca026910071000400e0031003213881108000038951030303003956461000c0406032840c0c5055109401803440880d0801894011541d96091103c0c00c80c080000c546203200c280011701c003103d0f4500010746100b2445990700f080040783e9112040003403003488450205580b150003070100c0040003035460013621401c400c131591207900217213080451415003d20307002c0b42c0d0050090701c4900d0752030b2074210107584010312071070b0150f485100300400284903e0b4818860070410010f0b44c2c88541d0940c00810121802001c0001c06007010b61022081c1d60200750121903440c3e030602030005044610102d00400015440409602c04910080c19008100d40091402c0301d011825600d4403401552490034080c3c0500015105010034025400401d86903408120150300030803540f0000010360402080b45801c0064044c1e50301050400d010815401c4800807440084065096040905160341a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 911587041 1250 911585791 911585833
    0x2306090109090c020a0212101a0a0b030c07051e1c1e110714040b0303070c12060b090103060f050f04020913170a050901021c05030103020d05150f0603010b03 69
    0x2402960b9103c2d41521a14004c00c0b2034155640e02412080c56052503001540c0c0300d1002c0580c20004904006002c185a41d4404038070320b42102c014107601e00e250074500c800d07805400c02007114a01200410040011030810045951829886d00101c1002001800d25a0406140101c03d807040844200805546500801000b43c1d00540c84481c01407004a8007040390941c591364025800ca0140c1d1401050b004610b00450b860107074151000e10200003400c003455545e106010014100303104808060114106000300e01582900420020a101c44807c6c0050000582a40116446951807101e9603803110780f802150ba11086044103500d807458290041036424a0013489038420600c903010440800481000c86c00e05130304000240c070740310000b000300600180c0c4000611805445040122403070492400200301c0b50031100d6694a045901c1c640c203100700b00200790380450301800b0300c06001445d9259120070610406200c44001c02c142802c2c0107250031654024191800307038000000350300b04440e22250f1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 911588291 1250 911587041 911587049
    0x6101404050f010509040507180503150f1009151403030711010e01030905070b031807060905040c05040b13150e280e0705040e0705071e0206132306090109 68
    0x381148003582080100e85a10510181551292401046c0106a640080d008075840b052020727801400d5190300070199203058840f90f01c0c9075240207a0004120542841d111174000c0d00003071750802d0545d200c031000d100781c800300030400c2512403403d1410000407030603205e40e42003c44254080c0d441d125103512010030381103200410a062258062031496264801d9200540c3c0941207419a2059521001084d290364010b4803c007000802500a1400015012a500044880340e072618124649002d041c48050000030346a0000d00c4000c0c0000684440203d00a141c2d001500082600c0d071424040130f03003551003030f804030176003004500b220501968449260750b9500f81c107072501d1201480c0e0722203003001101a95400001070304c00c041060150580d002400b802c29075104001c07088403550f07070317090456950203880d2000d84969407184000c0411038a0000e144191380c005400c10b490300c16521400c681824071940204800c0b010908924860000e04c4c050800c001c20894040c0d03d881d0802000800d48961801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 911589541 1250 911588291 911588299
    0x10813031b03050904060b0702040b04150e0402042702010201110901050405190906030506090f01051905041506170601210209070e040903050301060f301d060610140405 74
    0x41c00d6418140100e00741c039a0513000038801c1c80907903122100726840c0d40000108038000c0307041503404403151500340180000003428130761042e5018548040310310280005001a030b0491340e20000c0031a8100150b400c3c0306070406000903030031010310038400242120240790100050050030f1058a6490380d00008580450310121060154800610000000342c08154400402945448000400c10101044c0c0c10310445964054030121400c01c55014242d41c000c4840d400200e14407515070100b501c40e58800351700140140246418140408444011030f0603c0e0051220300300020800c1d000130030104012400b50160342810781e014a03540c0c100341c030b1200c54242e000b8072810610000445661007800b108228002c010414042d6100d181006801a4420301030f0200141c230341010500d18902401d40d032521400f01000b9402501c14440031203c00a00400c4c02050503601c031071660040545544843ca800a03514018250b02e040140400203108160b5000c0818840c80d482c549040c10421400e50b01104d000f91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 911590791 1250 911589541 911589587
    0x80a05090117271f0e16030b060301111602060a0203070f03090906051c06151d10080601030c121104020304140106091e09140d0e01081303 61
    0x100c0180c0c0c2c110385029079500d0314000241003003542c0f600007080381c204110030032000a10101411190b41c41e4403c1c14000d0011610b00c0514080c41d048550100c0c40c14040c02e41540c1d40c0c4c0002c60403c1000300842c0d4800c2e2901c40d06a014040c0700e140c280305040442c0c00d41d02a55107082c20107446540c0c081c189600181c4601c0c400709500c011103000380300b101d9086600c840b80e800180b20302d10300a84000e07503d005145e1a140f0b0300c100031840d400c0192540c04078150072003480064988555401e009800c9004d940c919200c01da440000d1a5100d400e01030005141c040f20780c081d40c1c501440c4002d41076000794410382c007641c800401000401c5084407002c044d40c4401e2100070000549083c10100880a2820700740c201d8400803c01043c41a890006c00051140c940280003d03a65901c0d040291489161103503002d44130041d41d094000389030340c0705000c076a201d0311000221a9404d01041d083c1440024108080340c440402e0880640e4403a00c0a6130040c1c1c1c5240a64209505031401003110948240000e4243e81107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 911592041 1250 911590791 911590807
    0x6090105072c0f0a0f06081e1e1801090305220f0b0c03090a06021f0203060f090901060503150a0e150414010905030c300a08071202070b011e03080a05 66
    0x4136420030060030307a40c00c1880345070740e80d40b03c0100925400c8030488007005840c0c01d2118054a040710140c081c02180d040c54445c103070000301c0d811240303d01528820114080883c559400314080c0904800c20f40a03071200c1f51507050100000700042820450340c1130b40701d01c03008240b00c00700000d80c0350300c1601c0328200030644441215444c00c0c40d510402c00d40781e500041407240044c003c0d85c00142007140c10400c41c96883c182c3c542641880c00c0e4042610b116911200a0b0b0446d0390f0390802c1e0300c100c0da000e0310240000c501d00b9030b25008a4100203412241e000c4056001d0100302c03030348815024105504503004003c10307800500c0115900c8a030300142000f8040605881000040311b000d400c80070203d5003060507a580d90040104140d6038141000911404042e1189031240507052890008064044035180ba450941d80840c07c50780050300415000a1194000c189001c4485502c003030003001e131040101c4041035042014440d03040380c80c00440020003081034801d100049601080d180011100e007003083d242ea880c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 911593291 1250 911592041 911592049
    0x91a0406060306060e0618010b1b0703150501051903021003020d0b150c0c041a040b010c08040306021c0e070302011b0f1a06060c060606070201050c06090105072c0f 72
    0x140b640040c0269061680206800402c1501103000740c90446480c45c01e0a0058030320315410409204d82c0103904d1003400140c01c40141e2441400c281e124010a8500c0f29450340d440c0800088600c04001d0065500c000600880c1091040c0c152036000c0321000016440c915800100c009104151850030560042200c1100c10200e070401040d440c80105848240910341034840800e4000700c40718046403098034003400c4141014031032000c95080000078009901100d07028400589100302d003660400032003652090100d14168042c0000d1441610b016a6681d14030300311008903401c10824a4510b440d00d1038000140800158800c2207035420300744180ca040c00409008081481c8400c042d010a002d449100200014882200e05d4260701500da03040c503031540800c0c450035014290300307580c0307507031200700455480c0c82c00c14054550340b441450b00510300502b404403541092401d5410341100c2e0745940a104a45401c007619050030070a0044040000b441d1500c8203204d200d608400b58011010703880c0045840d22 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 911594541 1250 911593291 911593301
    0xb130c0306020703030b03010501050d1106030405190303060303030501061b060c0905031f110f0706110913050a0b010e06040303050319020a080906070801031230091401091a0406 78
    0x2402440c02c546480850602401400c80101051720a5103403000209180ca0548910141c19030003c041180304010b4006000716584003400695039842105808515900340031210340c4554881c2e5000309200789140760280a5071010703004201405a400f415600c01c110400d406810940c00c07102c0407901040c0004203130703074581d030700e03001141c06024001011a00c11705400010780c203030104001c10000f03070101e2030744401c050055141c00140401c00304498000301d501d039041506004469074038030385080708040c005003e000c00324030203254242e1200c04100c01c1c0031503072061000010003801c106140b202400001443d07803003140002014040e001c80840e03003402c0042e9280100400310842107641380c1504a0242402c141141c501030113228202c008bc1e00e0620070304500c0c0c100c0390b0102d088402c041080c4810307514901001c00c2600c01014044010200542d030602e2000c03252034040000803610303117078203102248084100a0360b900341c0c1000c03042c2d800903001c404c001060340c8040e000318407103440c0c0d03141a4010305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 911595791 1250 911594541 911594543
    0x8061c050303011d0a020403050a02060309010b0604031202060906070e0d060902091312320d0614121207080a20030d1406010207031502040803030c0c070807030b130c03 74
    0x44400b000100380c241803129180490150014144400e42d24110041c082c1d01c510b002c000d100d81c2001d20250018102940034580181802001040c1d100191020900c2170300a42d2007a240f44500c5c8004c440302c241c0600c03080da00100d00380050a00e61902c203401401c03c0f507044801c2c5000301c0c443c50901051011507030004012039401000c0300424201b407a0326443c164200b56040d21440c2c0c0003608078064a0041e6403072a80c4c040301001c4544600396004d0074040c0a4640e028804010400b0482d0003a91907c2d8480c26029001540e109600381d10520144021410900031b00c9911341d21801010f89441651004d030380a80b5030100509664140c041c00450700c06804101110003d1031038030600c000740e400130001d407500d603001140402441145840b16125400c040e0740b02800340c0c00002d03042c40403624034a14104499200743c1d015203026915441e49146500131104500244030200c1ea0030056103080c02440000d03c2d8031002014400c0c00d540b500c206c00c8001034200e80610300c204000d00300700f01010b0780004c015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 911597041 1250 911595791 911595793
    0x1504030905012d051309090212031309110c03071b0f060903060507230405010e0103050613051f030c0503060c04080303010b0c0a150902090f1302040207020406151101060e0708061c05 80
    0x355544051b00742c040c0c11844000ca05c507000700c54078008058400400d0754081c507094000304000074034052505004061000403204040703010004c00c0020002000100b6545102c0c50b281115281100f12400140340180c001440c0b8541c030840800170244d1100c580c009682d00000c0010700e984440f00c0c2030340c0d40d44440b8405007a01c6541c5000881a0351100040c0046410a0b01e071810034411080046080399000c9030380c81c0d0b2105010058040b01c184c141c0c072043e8084a0003410080074403901041c1c0060041a5208940e42c840c903450a0000d802c0034040240c0121440f40c1c2c09090609003200c4a40f24001401102000f110128145040388000c020441c1d0054001d110204012000003107a0080c00342101c00303901500c0244041000810f61210140c41840c0d02011401140c00b9030342040003075800300b0401eaa2003902c944003c81c4102108410f0340d83c901194855458600c84088000d00303440f126801240c1c0e0314104410098059004030156900000843d07001080c140800326920f40722a90800151407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 911598291 1250 911597041 911597077
    0x2060702100b03070503120304030f05130603181502070507080c030a0201230a050a20120a1e020601060206070201020304212105091006150503040507081504030905012d05 75
    0x2e00031f94100179030155010b6039071000d001485180503034240c401c0b4030700c14142c418111400c10000b031003648003501905030380d814005803a1250311080c041d0805184032040c0c19500140d00d5040000400c4000700801690005e80484260304000907100d45008030064140b016003100c01c140c0411108105070070008041556031107485000c002420b68110b0310503000402c65920014170710342100810104240308040040400e442c0110900500d80c1020318100140106512130181c540e04500b09508070203016401007903d0b40c03400000a142c264050700386802d69104006200100781154507070180e1040381300560048030842c400031580004d00c488180f83d0300c403201c8a40451102c1e0341c4c01076401900c07a40c04448981a2010b1240129030a41c49520041005040c42c0c83d00e05000300003440e0301c0f5002c2d00c1550070a681d2100b0903410152a42401c5408051603400c01040540008581e0b002c1c10084c6407041d1f50304161743c0301c010040c1d9a8210342006413100c41d04060780610034030854041e03a803078043c0384407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 911599541 1250 911598291 911598313
    0xe190b040b1606020304392d031511040815040f0b0403030504170a05090d020103140403020304030204291203160c030605010914040809030c0a0b030f0702060702100b03070503 77
    0x9905e14403441040e90100076504941070f000ca04203482d040c1ca034651f400000c0c40361a00c40940704c00440c10041c480300069441540040c006034160850017940200e00c3d45803d018607005800c210745030348901017141e05040c80140035222000030100000d0505000c00a0640c07102d003801c0c100c400039030000500c80810700040004265050300114001c034455220508076401c41d400c94009400f0305042c400c00104c050140c04250b240001061005d90b0040c100004d201c0c4d107c814029840c00104c806030090381c8006003c20031410517200c0c030005810004020300b428094414646003441e028100ba9101e40c4001e2903ca0f0800c000340100c402c103070302404a103001e0b241c036450130040c61801c41c170054800310320b4200000703038240490151980305032003400f400720b46036140e0381c800c00190840c1d1010354040c0b02c0c00c0303460383ca26116030045501420030015210345074034200e1200340c1244001001d001c110f400a00902c40708680001e1024090345407507001007039049082002c01c0c40c006a84e407041c1c1e0715103d0051a50 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 911600791 1250 911599541 911599553
    0x2030901020a030c02370c1d01080c01090b0310170a02010311130b03040507030c060c050c030d05030a0e03070213050402011e08042307060e190b040b1606020304 71
    0x84900b01c4640c0302030180d036102400680c0c0b40c0d6040032030503084e44000d02c080e10650107040707001d0121900305c00c04030103040e1890b1070316690300c4d0081e0040041a9010040350600b04001c803000303070060181d58000c01c100010740c00000c246410358803903000051070100c0402c0d0300550507076080001c2c3c0001700409580c414a02c000a540d14615802070740424603015070b04421b4080304046030020380258000b640e00f6403403c42d15107203a0b40001c0081c1c41d00d002d46000840028034801140c0e004006a58414002e01b18a04019013428007480c0268801d60000310741c180590f40240c20b60307500104100000500c501c0034a035040c110300c2250002940181007031078286401c4015070105000314000e0faa11882c80010010b110700318600c5d00c071108003107030341c1000046c002180c240509450011804100300c21000d4810445d140140da50804400b1030b01d1800710403100d042c8289400e02c11a0090301c01c04078649881e0384141c50340f01c0c0b4003600c3d80d501400503210030b44d2004060380d0142103501c444110740d2440e203030034a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 911602041 1250 911600791 911600797
    0x4090b010f050409122303070207030b070201050426091f090b04030819090e090c0907030b01140703030204210b01051f08070201240e0601050304031407150203090102 73
    0x640150407080106503410140b0400080b282d11840303804021800c044156203010f00d150400700d40c00400d81c031040021030580d015500450f442d400801c00c650451400c00c00c450402000c0d5000c5a05d8074081001007082d041030ba9441550840303040058404d6004e814510b031144110300341d005845d04058000d01d0600c10200c03240304c42603945074040369860f801c1072011881345102c090034620f014000d0702d0341c1d00065944071500241508100c082e02c2d40d90801011601c00440b00c8100540144800d40b62509040f14042d5200041d0315041004822000004c1c0442c6400080e15200501c00329540c81054080d0f81102e0103043c28030004004110588003078842c16116080440341030300d0b0140009103034149180e440c01074071844004895003000503202141c2d543c0009052008543d00c42940840070420900356120f1640000d41e460501e40c00c0603143e40b0f141b03c2c080e00a03070400508100300004694805503021185034100c0710706d99a08202e08011010008000016815a200106000d4010415802 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 911603291 1250 911602041 911602049
    0x60606030506330d0c17090703150506010507020406030506060312041508103804030206160606170a05070509010303091503110f1c0c1b0f0f03090e10121101020a0204090b01 76
    0x1b40142607a949801603220151448010080c44076804c1400280200d03030061a84881e042c9046428480c2d50340010b0144c070140d60040d070319a04003006200c064181402004500c079149003c061034240b42070348407010b40621211705c90400c800c240116800680d040d00344001810100303890003a40042d025075040e003552908090301c858079208034032003281050609940403290000c3c04603042001c0419514042040060212401940e6401c0440c40c07078182d80c3c484c041c1d903c2c607000030b0120301c130580f415500d00180340c0c0045105a400d18010800294880c201c501580c03a00e09064480060040703041e4054a02078440262140012901d40040383d02400548100900000d0500040c142070040b6001c075182450702e0400a1001c08405501d003850600744440e1600c120f210ae902e41d42503864a000c40c00040008030005004450304102c5407200300e040c1c5401c080c504051003c03017031401c144441500000400100710400c0034580c01101c1c2e000307000e44800190050300c180060700203481d101030f0710442405 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 911604541 1250 911603291 911603327
    0xd0f030e1815101e0302032403060c07020d0506130c0e1b09010212040f0305070518130f1208010305011d0c130612060606030506330d0c 60
    0xc504240151403080c003070441d61440208801c00b5400307100708140303003850200c14082c444107102c021404140c04298110100c0e58010b03100d00300451050207042d1140309078520315820545201080c1d602203486500608107124680d0b481a003403000c55484414101c1c0a45140141001c100080020552400d245885507000d14100350720307203001007440031301580d00c801030040c000c99481c0078807100c100038907078460140100c8402400c50560b1030165803089e003041c1071035a4054020420014204001c1e40902805c0b1000c40384840c29407401018020010510b000e00c503e80080781c0d00b03010610421700090390700216244048000c607103000d00700d00301c00c1c44110707210b42c6002c14858021f201c41d01c8042c01c030f04004000e044021601020044403050f44039602c40c0441d9101c000045010b14010200e4000d403040e00c0c040344c298500035018007100d80041c40c1d1b5000c1d50f452807840d4011184914583d001105140340c11115103141501c615803401f0382c41506440c00e00d050050380b41d80c0e03005181141201d0200c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 911605791 1250 911604541 911604559
    0x40603050a0c020a0f0c1a090406060302040308071104110d1407021227030105070f020607020307020a030803090703020918060105030c0105070312020720040f0b0303030a09020d0f030e 81
    0x4048608a8420b11810b03801600b04009500000b03a400c0021054140a614207207802c0e9201c251030000110f0b000b2558844020000f0303a081c03542028040c810042c00703941001c6090071302e152541c0035288503014000b0b0212221040c90b0103070341e9072a071000f44c08403050480e443e105c500d0454200000d20510700050000c0c0d80d03001c001903034107100240d50400102100540c50038550a040304c24020001450794101c5080c862201c203880b074a092140c0d611616080d521510308150003103000e800e04101500404c01c54100f00000400743c0ca5508a120850303500164059407584d0320201300c0e051120f03d4100a51100c00103092000b50034400ca4008138500d101c8041d41c900740d90360002c05548134502644a404a0024032400012070f010740c0ca003000048200c140989408229664a61070000c900c904000c0b40e40000c40422035800c09109418401d0188442003000f0104c440020381d89000051504007016100c921450440d203405150722090342d40031040108883d280d00d0043e241e000002183c0340104191 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 911607041 1250 911605791 911605801
    0x21050a020a1d060910230319060e0610050c0a03080610090812070326190923070e040b061005030408041517090105061203070b0628060504060305 64
    0x20b03081500d10a500109602d00d04002c001c280151060302c0b80b4800c0a0115110b454006801085c200001030503001e10900e547e80b408001c42030b0101d444d0301e00302c0c401a20f054001c1c82400b038224049504804115008800621f05420840305481440b0200102e0b004610240041581108045d8010481140c46141810508408448009040c170462165030f10a920319071491035503c00401030341d40a0310b0012038031040350344480da06060004c011070034884014100050141e10307403d00c404100c81c2d0b10052004a829440381d044010031440c0d11001d60200c0b915110688104001c090000c04c8182d507e090b841c98903040c10107010354104c0300309000d84040c080074a00c10f0310840444c2c0c45554040a60f0707051906054001007a900600d1402d4180410300f192813a00d20070000b81203108030304000010030503103401340610000d103c10030700b078218960090004000080c0803014441d480345050784c0200508a580344803d0004000c000350566811030b0340c00c040780117a805030007042a00d5003a10300307002d99103078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 911608291 1250 911607041 911607077
    0x3030908030f03060d0c0f0e04150606051228021b1615051b0c03070e160e040b180f07090f090902130c02070e0c04030503040621050a020a 61
    0xa02d941c80b0b81d90903082001410615003010044119801a0311400c807590300d8561780100402d06030044150910107070200003c0020030300e120035a101c03661405014213440d0282c044c00c0c600884100c00f0808020000140308400c40051130039000200000310f940c1d640a00c0e000c1c40081d80100100c180114030301b01e546001000020b20380c43c510032601d805864040c60444105481260007a004c002c01c44200004e24150b001002c0360310380792103480c02901d2070040001c101490007001d544912070400800040002c231040d401480303030311803805d811300c0d00703a420071400004e00030911032071002d0b80902454214624040f148480c42d00c0f9010b41e1000c0052500c4d021000d6a07581741e1403041d0210030030b80300b0042c000c500c207542021071050700c041c2c074410710024010b000030180d6440600690040c0d000315402c1282e8070400f85100d80160034061414078060851700c034143c0782c2c410344c004e0b8018000250240f80c000792600d4000c5d02d107141340400c00c11050414001c002c0182d849003c4803400900061007240307038085 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 911609541 1250 911608291 911608297
    0x51017010522110312180109030809010e04090b0423060408040302121501090c020d0c0b0a0510120302011b03020c0606130f1e0c0203192d0201060303090803 69
    0x350b80190300550020030340c581040d8200b011012a80d0f03200301d000e100c4036601c0410203180400680c5080c00d840742e600006084404e0030b41c200941c100101c07000100003040f405022240085020b291003090046407074080f41c00740801c0c600041003d080c0c8010032082c010000944400c00c201c00c00d903001c3c0d0412410240381c0e503120503100a060504200070800c010300d0541e0100d80401c00841c02c3c2c404a507a800c003c9401c09100f41d03c03a501c03107a160b11107081c0382eaa0605c071500903800c1d00c0c2406900c560072a100d030002c0500080102c0820b96640d00070400754040e20303c07210001c154819903071324004002d00c4d008ac0a0724265400389031407030b584003410008a00a00a07220285660340c005d00007691a0402c0041c00641e01e8407000c0c035287c0e02c8422000781402c03409502d10407511080c412164004810041d400c941404ca010341c1150402c2c031480e10f04815645a4040c203101d5446c01c0c3c07070007029590664954601c58001c01a00360611501201981d4047d00301c04200d9000b91591105036540d1000c042d2284 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 911610791 1250 911609541 911609551
    0x1170103030f03091509050c09010609060503012907050f060105010c03230903070b0c07060519051e07050f152707052d0316030809130510170105 64
    0xa8600000c01c1d00b03041c03103070340320312038890042541816101c1d2603c111012268170120684540e0446008100c5504140114900403c079528021040300d141100040060006018484510300181e0841c2041e407100300c8440301140c044038401d683d5845600e40f860b51100e403900b2625035409120700001e2070b50301032104171441ca83c058842c2d169040c03440036032001c0ca410003d0381e1018400203100b00412910204289800781504c4120360b03542300c0c11641d480d440d004203684204100502008040c10040034800c000c540b4262500304140c91300c102800e03038401301503c01880b10f52540042101d2051220000e001c100340c10808040d96101c10407444da06130720010481e08600690f0340c0220034005034440c8201203e036850828103407100f00303442e44000741200c410041947c40c4240c1d440f044550700011000b82c0c1c6d04a00d001c400034000c0b0300503410304035107444c0688005001080040780010345601d5001c0a22814524100c0400a40c0350018001300081b84601800c100601d1884000500000c140304407030041d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 911612041 1250 911610791 911610797
    0x3280f0c060504051c0207031103010903020706050c12030c07060c0c110f0a080610060807020c010206010504050a0b04060b0d0b0a0f050d08040906081c02010c0c2312090117010303 79
    0x203400320741c452102a000151045480c0d2040d46109004c10548594000d0580290b0b0b01070144546141041c3c880d4028003040b0922030b0b450b0103140000a6000295a0201c41b03803814400d40314038011000d282440c0103c44c00c40310b030780c00000400064602c014020040b06100315001c00c03d191440d48120b950380700501d0010400c8026210701401440e000001054021004101d03140e11905c408035141080d005807801e10003081c1202d814003040b81c200840c168842624402000e800c040300d00001d60319503040c0f06090040b580e03480800e01c40441170300840c180352405001408415900c034410030840d0710543c882e1280d50b18004910320140f90001041c02118001a0300204c031500307080c00c021100002c92011145e8440800001a0803c03036401030600401070038001e8120400d100300d0100c1c200342802000800c40e4585501050100d030000c01d01000c1a4000c1e09494645c201400742800c4520782c001c111405105070390100110390071601c001c04101d41c00380e855040c0781d490b8055004030f60034207001c02404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 911613291 1250 911612041 911612057
    0x10b0a080a02030a0e010f0c110a24020706180201140403020d1106120115090b030c1e1b030315030c0a06080a0605270f06100c080c03280f 61
    0x82616142c000c0c41e0003070500c12001401c003103001031003804c681c0400d0351980115111603440980941100070304281c04030701809495007410981e151011800351001c565056600c501417141c0248650781a07a01141d485402041502809602c20303240105442c4224005000d404200201c0000d40050303e007101c0d80904403205228499560100562100c0344050700141c0500044855880340c0c000d00b070003000804283d03100d0036240e4030000c00359103080c0c0103140035003000c00601901d26040b0088030010382e428898025205041e90b50342c0010312565006003012218613001088082002c030046008a40d010290800d8485180605480e0310001d18a107600040c100300400c01140a954099400f8000300c00c0091003c0c4c4400000380c42500740c00c00c07202d80d080c05000440108021141158000d0007216841d00700f8940440013441d10b0b0f110800c000b041141ca4100041040301d04d009882840e11240103594882c038002200d07600c081181c400601d02803142c0c0c481c0c0d413181070080018001c116040c1d42c50200d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 911614541 1250 911613291 911613301
    0x42303040b0702030a1a180312010509060a091e050105040c02060f0c0f0a030209011106010521031209010e0d180302061b0109031116050a0521010221010b0a08 70
    0x2000e0b0002041607800d40540c1c90700030001039614030304a5440007485110207003400e200440c11010703142100d0f6000030307600420003001c0e820000031010b4111398040365450450f9403484003040c1203013200d1340840c07034a500b0030603400511598070741c071158894540107082140303a0740e0b0310400c000d84680c04d08500240c0c10079408907101014203012140e01407000c1941d1880c28690558959003130303010075207680010f80d01040c410581d69210500b0f8046880401c003c0c4100d50610303002540030a0f0000d00c100d243c400c0c13081d01c18181c0341c00f801a2000440481c0360003815141600300300f4068600c0d03490f06000f07406003003010140e050040440e4549071420081600ca0701d0b085500b4800954030980d40c0000c0301002e54240c04071503c00340030704180c0c24802d41d03031070301c01c0031200219510341001c0340b0002c540cac090b16080c144521f4840da03407802c040b12412030346800110f41d1141040d81c2203810f0640d09900c0d500024040748401d0f40c036652003a18070008540818503131303a9400302d000ea074020610303003000103138010011403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 911615791 1250 911614541 911614559
    0xf0f0d020d0c1707030f12050f13030b0a1e0506040e030d06081e0303060f060408011b09052e030e0f160e070c03110c03010c030618050c0d02031b1204230304 69
    0x10007c4062400e0a51070300007040d20320320003134101c0d2030310543d1815000703002d10420082d80805070f001102e8100034030401d6034070141012410b50020880c40300036980c80010b0345c2230361260003040c120241502960f5481c1c5412106201501c40d0b030181c40510301c1810f480c003164145c481852992803407881c02940c110b89400080028140059001a92040c1d06100104d0741d401d0038802c0c0c1c828880d8404040105551021015142e81c550f58030052154035003005c3ca02c003001140d001500e1082c0600032020700c17070010480c15802440e9259540f0400d202d8140e05181c7c1e03800025010340100ca00c00e80d00900160380c0c1d0200d0300307000d200315001c40004d440d407108440020b009413101511100c903a4152801361030789102203401c48081408500009840d168108215010111401c4507484014030a11462615008041c558441d00c242c01c2140c079800000215100034172400e2050410314a44010795a240110454941c3c2600395800d5980003c0c001c0c0540064802c05018002e48002c94007850230036140a101d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 911617041 1250 911615791 911615813
    0x708040b0603120a0e09091204090b0d050f0d030b03010203160f0c0b070c02012c190b031509150907270803040608070e0f0f0d020d0c1707030f 63
    0x10a0b0503225142030071500424140260104041590300c1302592070701c0c0820440d07000e0340a880b0a60641095141004440102044406541c01070502142d490001c8001c034890000c501e00c0944180102104040050400b00358052140c0305942c00740183c030b101d035017014200c0c402038400c400c1c150080072120708818000c0600102d510542c8c208689401c525450700311848504650000000f42c043e08003104540e00034408000414803041c54203008010f003016419603100303081040d1704c140c0152040c07445c0d84002180580180a0340c81110b0b031a42014140c40e4200300981c1481803151041c000081e00301508041ca083d50114010030045007a16604415501c10301d4014640076840d03140d1480e007480144044041000b401d0107802540e407540b81110040c440e02d0080c00210030410414004030041d40c2e841e241103600e0600701c2c2c411450031502c00000d001d120142400a4100790040520000d0041595259080300d082c070000ca10500e0030015519121021404000c018440f41000702003c02c1d02170040c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 911618291 1250 911617041 911617051
    0x90405010912230408060f04020604120c030611120703020f0d1a0111030a02060a0c030f05041b060908190204150b0304050c06091c060612140607080708040b 69
    0x14100d5081d1036401042c8002d0380e50342c020521440c0750388a026115454441100d80c80c414040c142810030341e10715180d54010740380d80b910340c00e03800c081000d5603101411500145200b083c011140c0c1610701e01181c0c5156103200030764100313140050f0116158429011219081a02ca550f240103503541c2d0b000390025000741d41445100c01040c48041c14254161188840401646a0705200001142c0004000184409004145070020b0150311070990700060556041b0213201800b140041d02c88904a005000505003101e02c6800c0c40c003440180100140c20250782c55407228220030703460b00e5071400d903200c17603803071150b42c419501a100c08954603021450b1080c94030300c0207002094100300000d00c0c071303005c1d1400d030072074000c40748000309020402404001207400414140d904905045009000980904c0142c000010214017611410b08001180d800740c0042d1000c0e4103500340d402001d0034000800000052703102c04a02c1500041000d95010700c1c20684a10120380d12280b059590381d591001e201d0001e00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 911619541 1250 911618291 911618293
    0x501170a06050d03030e0c06040f030308091005071e1806030504140624041b0f020c1f09051905100318030c0b100e0c0a021e01060e24090405 62
    0xc000c90190b0790788014040383d602950b000703d00400f10702c00e002c1c01c151200d04050300c1603408020800c8030292503412a01180e801d03040c0450b460307031000012030038011031031844800c8620745402c0191440c2c120b0501c01c42d448620642d040035500143c019a0444481101e035401c450341c41b00c08003c00307407003600300580c040d04c0b503411a2507036000650083c2c54031106a50302d004200a045c403000b0404000b0456001202c001c6500b8860002100f00520100d164048400c040002c40780002420a0081000c40c03001040903042221014801980c90103610f0405d1000c0001045003000180710b1511054400400d00221015030100340f0b45401c1250491041900c24249034807250300701424601001003030003890103910303495540c02d981d180c40c0903281e90041041d869612a141d05210f55204000315981c0b00048014440e510f244915003a442d2110420003002500d0090a9440254006411078412514600680c0c0c0c225115645007200521482e4602075450a02030480d00e50781c41c00c042c48581190242d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 911620791 1250 911619541 911619551
    0x203040f1112032b021305010815010801032d1b0806010f050d290615031603020309010e06100f0602120d0b01050d0510060905030312011a2b060504060501170a 70
    0x100038030286e0300300d58488107080030151410030132540c10007012030b0b1240b8000b003908170648007000068641314041c08098441d0f81d800298000ea1001511407030542c9240c0601c2b000c02d040346141495491481d6800394003e5101e0b0140040c2401c80000d90301d060310180038041020f541000b003801140400d80005403010190002e2400e0b100300c40088030a890040d0381c40c24401440c040381403241c50500c0244050803035030100708000080845070901c1c0807106003460096544c1e01c421054a0251280151300c00445c0a20028004591009914041290320b40031340f050308596507040680c0c0300d01a1480500d0038030000c1010300500201c1d82d10001c42c00d4814100311341884900310f2080e0461b0000c603000c600318402da00d401d0051507082054200140750440c01145001d01c1e420f00c01101c4071042c0b00d4440840c1100b00d41c1d114480116041e82c0c011801c030240034900f49074515242c40b0f00300c000340c3c2c60000703a4500ba6011030340b030406d4007842e026070304103031110a1711a0356005a9000008014600034100d40d41d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 911622041 1250 911620791 911620867
    0x91f1b21021c050d14040f110a261504050d1404210203010f051302040e0c061909151d0103061a0c1b0d030c080c010203040f111203 58
    0x1c55000a45803030590740c2d058032001340540c0e90045030204d403110703003000440000704000a40340c0c3d0311020350300341e001414003400d403044808584c1030707205130b08440c044040c2502e05904c00350002c1491807100c10400112340f212405001c3c907020b0b4401c1550007500c036801040a00c2c1d145405090006030400100c4881c528242c1da41d42040c40e181e6110511001c0a5156184201940b40c00d0090030740e84000140204554184490030f4584610701720307030081c0034588840c500703800034030184440c205800c0060a40c55a981d00704a41c0c8004941710b81000700842c881c1c00300414581900304d20404003281c40d40340c4c19146421100100420704001030702e54101a12818042420b00c490404400141c0c0100c04d4030380c42c1c0c4c0c00e05002500b41004500c0c3d42c1c440a2680f1600107003650340560300000c01c5c0e0507003400076560000e03040504840c8540c150a0000350f0001046c0700810500703402240b00280604d2402e20008040010400c640020610600c4203600601c540031410280280e2801c0301141d5511480f460680 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 911623291 1250 911622041 911622073
    0xa030c27060f08011a0f1309080703090312020304120609260a0e0f1806010504031e02010e030f100b010c020d060518031c0c05091f1b2102 61
    0x200d0703005441c0c502480c20b02000025400d00405840200090507000511251004240500a60302c480c07407007119400a071210501065101103681600056825507940032400d0242c1401400d20044031030045281110540c0c0d4808400e84050303640b40185a200c0d5801500c5040203000c00400c1560780c02d115001c030650301c1d22003140c4201d070890717440110b41d00e030300012101400c40d1100b0052035001ea002405007000c0c035527441d04200540174500c0340d8013620f0f89039140126214040c0f80c10041145400003180c440c08050503440c032002c14070036600c4030312410210301455260405da01d101c880320b03801000300038000c0c2c0490300028040001850000d5820301e054000803240006c54900b6030340e8560300c005019104020420681c070b0005540011440c0021a0540014511a04441c41440741e6284211040c69110310300b2211910401051010352101d144d0440c1c0702500020404000b1521524040084000340b40181c0b41168104513455200701c050f1005e00c50005d007010b2039604600420070140c0035000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 911624541 1250 911623291 911623301
    0x10603032003030a1a0d061413031407030509030619060902040b1813111201050d0305030406020a050d0f15060306210510140108060606030c0f09010210290a030c27 72
    0x7c01080c002c1155040d41c84071004202002d4580c010855008102d4030100750019204062501c14841e0955198403134181115940a01040903030305000d0b05040c80070082805501c0d6090100305241001501c0d03640400408a03c100d100d00c1101c8501030118412540e104d000d040c454400c0070300010030b0341c00034241c41c10440300150b05c9008242d03404030b0b1041195240b07004040c090329003510400e04010461720090b10b503000c02400101000c0d00000c511130300034428426504090341d49541070021504100100001d4149128103003440a52020b0025401e80b00303000b00001c44040240c1c1c203a2031420198080c100090014003a15a80305501020755590001d00c44d4510b0b42c803045101e49040c0d418200100e080540140400c0e12a440a200f03000394500e282c821948000020000b8954803480240184d0518118402c60729940385003c81100355804440c95a0a802d0540c003440c520640810003013100880941c04082c0c094031070b406050190b00160320001d8003203620b2146e2034002003490480130050303031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 911625791 1250 911624541 911624543
    0x5010b04060611010b121906090f0c0603150f14060f0c0606010807020313090911030105040308190603080405091f14010e03010b030606060313080309010603032003030a1a0d 76
    0x44070440191004242032041455905c0115074210a403080101d0702a924a80703c070341c4020580340001600100121070740502c01981e0f01c660b0005c072038060b0b0705003010902ca491017800c0129041a1010248400c44d0810310180c41148503010031203410f10301034003508500c1c1c5040c9a04264208409e1002d054840b02510900d01c211000300740910b05880014500f12016000405643c01480030407100c405074240501030301c40281d40022240110301300300c0e00344e03e1002c00c2c01ea0554600710602c403d059005502134410301184094510000c0040f41d007808403010b0f0701c805082c40100384401e01c12481c080c60b546070040319600480340c0b221020399a11108090540c89a040c584980c425405d8658000c159a0540c2100324020400070072140c000c41e07120f64004103410301c5141c0010000f031482c40d400c001045000d4000100316104c0c501040428003c12043c041076000c501d6090410000f01c51001d80b038080c1007400d101641c1152a42081c0a000c3c0041840003040c3c00b100d140e0114094a403180082030035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 911627041 1250 911625791 911625797
    0x31e1209120f0503070509130b06130603110403080d0e0a17030a0c050301140d0204021b010b0a0905090706030b0103230604050f091b0f0316081002031504020705010b040606 76
    0x8407034002400740080404010711014802c040c8200103c0580000036501445402c1c1d9001c0c989003855504000101314400c2c0749944104040b508948002c1503000d10001d8031015141001a0800740d005a101d2340150320000348510000c01100354089010b800c01c0d0907080c10181101e00119495581c0f0300ba00d01d071a02441e041c600007200304003003030041c0d01410309260000d08121385194107051910408a10400249002d004034207040070864960358102c840030324103400350300308256551565601805c0d016546c2842010380d80000324458000344141c07030003040c6010040154510b40030056024010000c4180d0525a40d140094407000ca00d0540c7c0c04035510013406450386103014801c001c00c44601a100d0000c8081d048204140d00c030000510314210704002c80d40e000e0716030260001500c2a50504241e540600619508010880c22000d016066854000644401c0c0e40041c0b0714108901041361055484207600d442c8c400c103418a41d0080281c1e0b0b0091001146000441000c6819261a58414400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 911628291 1250 911627041 911627063
    0x506152b0e0f2a060724020d0e0618030a0f1b03030f0f0903020c010c0219080c09070305042d0b0907080c030309060901050310030c03081b0a031e1209 66
    0xf00c80f50030004454074000d440c0720001481440b102003041d600402200800c089055030701101e45890858640c001b1200421041d5a42d04070b00c2c02c5400502510468402d0a10a000c045501c01d0300010490122920081c000c50418001800840d0f139200c1440441d81440500810090741e86080d03502c141c030303083c040d072030100d10b034502020340310201c80a59001422851411920310b002a5010407012452039091a1070600d075607440c00000c00740070034034442528101d034040b0300140e80407010820003044082252550030981c1e5054090b002c0e51011200100b50101241d40311009480c6031002420492000f081410320b10b44170381d0350080014059480c1c01c1c466004140800688204015546c4840b001b07a029506101c20003003c11400c0c015560028180f08010000840b1807801048000085820503601d00e1403d0b03884c2050902640114159095840c0c0c01c03c030500c0c91480002c0340d040f40c55040d9a08006a59012280016680707507105032010008881120000c1c40580d00075006003078025070141d98 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 911629541 1250 911628291 911628313
    0x20a080402120f0a060506190e010608010f0e070807031d0105040c080d1409030a0c06031401090203070518131505031e0a03032a030506152b0e0f 64
    0x1110305290490381c40d41d100454104010f103012a410050f207900c1840802c141d100c160000341a003507039280a070070383e070905100001d6003c040f0b440e81781200e40e02d88a0001c1a40c0764601c140c0c031841103000d41c81c1e54211075400705240c54410104507034403036092320b0006200c180c0305c81c00070304600ca03034a141c05440c1e4603281488280001c620000d80104890030040c03005800c4004098905184040b490501c404041861400343d24140406440c10764003036040c02080d0b403550005001003908002000303195000400124801820707208880c0520403d403a002e04103400707480301614025401034429040550000d200b0b817501918000c40003030004440c011841c180c1440203152400014048002c156840981c2182e100303400071070385e04d0085406150210341036002c2401c014004500c4645a040b12000760b2881600d02e034580e2080b409904101c0f80000c0300030b0841c0804041e4024900054040b4401c01c420001034281c1c84801d00500c09000d00105003c80a42000c80c00c0c1040c89006d606181c01c4010140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 911630791 1250 911629541 911629549
    0x160f020d0b0609060916080405070b0304081b150112170408030d2a230d02075003030106050c060127020705011d070906090b06030424020a080402 64
    0x9134080b0082e1407291140ca0840c213a41043d1451440c603600b489003140124042c44000d21a60300504003218105a680c1018a4400c04a50100d004c400c141c44158240c008020004921154104d0040c1d83c1c000c8240d00341590503044500080c0e00f15100010001042420b40c149000b500013400501c01642d1509102144072068807000500500030704188107100d407403005100401c20509100d03241c00c2810b958241020302c10309007010b03502d01003d0f1340403401800100041c0c0040039103d01c1100501d500c0e00c0c0344102c80344003503944541595140304001c0c0040081e031074003c0c1143c1c000b0000b01108210102000d005c0d0941d0320a81107070380040e20010b0140001c200c200445401001482000903011482070686043c528026160b40325840e000a154403d00909401802011092451822074100001d60265a910862091000b11408d24400244d8071005100d40c003840d81c800b809451039541c1e80e6840411a112141070b880921010311210500c41c0070354405081e5407a00c0f521014124100744c0100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 911632041 1250 911630791 911630809
    0x1e0d02130f140a050603040602161406010510020109051c09050a08010510150903110a031208061905150d060803121e09030d0b120307061506090803160f020d0b06 71
    0xb050054a80d81d4080145498141c110ba078420f820020050301e07542c05805500c80d490a212010f0005100012688180c18001c545281200d070100d885e1041c810000d00f069090303a0035003101400035001001455030b192000c0d49042d1003038426181c0302c0307400c0d0b440d4400a2001c80c1e4075004201541e6540c000c003c1010700d0741404d200a0b120030501c920f044c40180e14000d0201034140002881035044011b40281c0b5102c0c61100710203507920400c030016050845400801601c0100c0f40c0500c2025480f40d003c3e080354407000450180e801c054180c0c0c02c0e00c03003008003042403a400f01c148200c0300c0e0f40d0340400107804078040c0090203600c40580740b03605250400013800c09042e20f0f50113030010010540c00130310501400000444d10005040c07240443c01e064110000740100100001c0e1a07001d0100240c0d03c000c0240c50b610a810001400c400c800d5134985625044032410118007032910280d20410654400d0303090794018118480c031a1000c00208422a400f003008004954400c4603034062840501440340b40c48514 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 911633291 1250 911632041 911632079
    0x30b06040e030721030605150901030f05060a03080304052103011a090d020906030a02061b1501030b060904050c0d0807120c030806150921121e0d02130f 67
    0x650502c0c8441e1034000c8030750a40c8140301c0503a144900b0503038016001b03400031802454010180d4900b4038103401d200055038455440719000034541301c0b1260703a40340140300d820b0007944040d0a042c02107040d95960310307655101274000c0c1c51074483c1c0c07403035100080c400302c0c031625040e444007402c2616545040d010b070006c510000e040d0b41003800f0500090000b07403510b08108804640444410788961110000300f400c11900040c00b0350800f400048204815560309041e25810360060300f11920f0080120507001c0e400d50a020052603607401402159041c90690800c0d50418090307000d031140b00d0080c81c0040c54075024103204644d440c00104a040a110740740b070501800c0d0f4410301f42800c44c0d1400b030780d0043c400c1400611041c40b40c0d01c9514140d880003040300c2a036800716806011b6101c4c41c440b201914000c481111101ca6440c0700d844000525800c003002500c0c504188105175035419106030031441c41503000700b400119419400d12140c24101c1040c00490020070403040705030312032820720850b15610410b40d51 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 911634541 1250 911633291 911633293
    0x20a140609060c0d020c01151d090c040221101a03090601360905010b03030406052d13030302061513090204060b0d1e0c0507031116030b06040e 63
    0x2080001c070408101c00d030b40401c800860540d9a030350520108020700424005580070f41c40d21400c240050410701005050320b004420000c0010130b0200d24104440d41142c071a00700da04000c50f80d4285040640180c000718480390401c20301401c480c030807000f00f914100c0b0300c0303156903201d000c080240c10301c0c410f500c807102d05d40c0304055842c0d40b038680c01a641e200700c107204088040e42030300c0e983e2418150304200203402080c141018482c144107140150b0180403030210030380711b80d46444a80251841e002040b1401c0b6000c3d9203071a1b00703000510310149401e0954031603034070300b07a03ca0107001d050b031a940500403e241c0e50380303e0030204828294180240740503c0240443c40c2c10802410411513070b920041c10003417001350800081801c005910102c1c2c041c088a5101c04282c02000c00c2c3ca0340d405440e60001032a100c080f0715042c1c400100703c1050000d07148001ca02e080402c004004403004244030388405403001c041d090840d00d5052a00d241c00619032882e034002e40e0441008000e0210524050180100c1088100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 911635791 1250 911634541 911634553
    0x303050c030f07180b040e0103021513030809030a08041d180c04021315050403060c050702090606031005030d0e0414090618010615080f1f050f01030207080a020a14 72
    0x46440c030711141c0035101800380140820004e01440019035100003070080828566251a034505003100c0018080c04128490842e2103040c4040d0b0194401b566a4203114000b15003007549192181003190340403903049501400380c400803002080710a4020b100502d05441201130122825040900b64400540b01300800d605000e031402c0590400140c500e1241307000c880060741d41e200282c506d080000b007903100003088214806246c2c00c1c10741103000742c0200e80c0603072000d024400b6480d00403100307441034142c02503208085002040341410103502841e401101401164841500e840000f403034258280382400010f4181c00e11003055040c82d01840d081c14400c210f4030251400d280c80c17841e40316403004141281415039640034802c2c140094208100070700c2100410901a00204002001c0003c101c50300494001d00d080806e9041016400003d503480c42103000803101c40c20b050401007005c0c03680c400c0307504168003880410085200c290060100030f161340c0060031695407501d002110300d07840004100494102d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 911637041 1250 911635791 911635801
    0x90e13060e210c0a0212071505090d2301050408041409040f060b0102120705100507020a02030d1b02130501050f030a1a06010c051b010e03010608120f040312020102070303050c03 78
    0x503049a02c2e030344500ea01580c5454200201924180303c0341000303948440085c45020014002003150800d840c0800c1210194180c000815100c80c4a600040c0340c01c52540140000841c00b40030003010709201d01e025600345164403245c0e00c1d0955100365000c5d2040500040d003000200780c0090a0560b0342c000343d6080b041403a042d103614201c89801e581c09801903444280085803a0b2007030042103860b0749c080c5c0c1ca0549480040c24036a035650844104c040850345410049501b041c0009107424420f54004c000b80310407203081e481115203c504000c8954a0b000c0c00c8103c01c016035610709010169004a03200003199890042003114030204909914002c0d00002081d2001c01e03003194008800c80084441c805481d159240100c880074180ca402418500a5500352080f20000c1c1010004150090f030742c0c260180030340c4081500301e0b80140314210f8a80d0208600f4554201090050090020700050290505a03240c135144070407020002c00c032005135800680d00c000c143d0544a503070342120304081d1a904510701 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 911638291 1250 911637041 911637073
    0x3090b0c010b100221091f0e04060603060e0a110c071e1202150a090b0c010203041a092104050411130e0c0a11100e0a03020c1519090e13060e 62
    0x171034146501e00b010006400e4040b91901c2c000c44014141c2c426038241902c48a100c01070031000712183c030b1031085040c0030000840511900600043e1555152824500e031940b821010040441048881d5404020b00180c0d601724401d01454006208c0c01e00d004003044140341114985041d80d030802c042079402940e5000242c1c4400748228450301c8034001c01960f070901001c090b159143c1d00d910040c1d0302c0600040c2c800c01814190091400b45104050944400070844801c900810701141c4c400043d5006600051031400c586441e1404070b0945044985080c1c0c480000c103041da940e44074080700303e440002e103026040071003e001c8402042c1d01040e41105050a02c0701540e203110304500b65080204203c203800f0035050038000003042821010007005801c0c540c03642c2c10b40b107000c5008140e01600070310110750341a0a08a186200544000d8402c52914070b4803c000b1100c8001c00b0030107001c00011001c003140d20041541c04074000e21541c1d80d12180480d0a1601c0c40a0358200003501c1941d410007801c250000030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 911639541 1250 911638291 911638333
    0x120c02071e2d03020a1412070602030306130b0a0825120b0a15090614120601050415080d030b09060d02010e040c120228110c0d03090b0c010b1002 64
    0xa144440150008444800c02e148040c2500065405410628000f9a024480c004121000025180c6c50300107000103a0303107030b100d1480c1d10481d405130b0070400024000d468510b220125821700c1850000d941125a0082030b4054000d410000036548005000520320142c0da9400183d482c5070030078468942c0c18800c54120036141890010054040c3c000030a00210160b00080007031000c1c103800c002c8603652001c07000041e116600c141090406405440405401d08117644405803540d840285016441c04050000500103c10322a070180c642c10000b003281941031005420701121954040740820900e820080d010304090a80f81c4681d41064040c00182d800c14441c6001c0982102c0000d4580d0050506659440c012000002220310000f0901c070b10310b4144000721981c14110054003400d99400300140d41c0068000d601c04426484012003074040d140400c1044580b51003850401c0906a8410b0b202050b50410328074070b002d0365194140e424241c04d000100d0b09001000e0b10081c1200006440c0c18030b040340c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 911640791 1250 911639541 911639579
    0x9061e010507060b030d0207060e0102031201120204091b0306050115020a17191107091107061109060301142d040e0a02090702150609010b04060e01120c02071e 70
    0x140218081d000e000b244c0d888064840e80140907208404407044000751180ca803800790201241c21950038029951001003608d417600c0244400e210281d00702520f00300a6650620201e034800d0701c0d001503c00141c6415070200c4101c803400b040220369070540c0703005819150141c114400da15944202040d806e6400100d190364a50801032402d800041031f07810490f1481400c1c0013503a48075640f801252119408415003280b54003e01c1510b040c551290715100550b54003141451442e0790501568001c0b400f03c1c0c2c440560030981040d0140b40543c1c03000440e04a41090b4403801e00d124050040d80c0650400507007480d03e20842c400000645080b104801420070036081c10107003d5a9078800701000b0a070700f000003001c1e00b03800a000c0c040603e02800003c4d036500181054401c0e10502074003040b0703241410740b042c0d81a146076400840c01c06042c05002c5480c41410000141040300c00124214609003e218000503000710b030340500001401c00643c490003604090381e410b8802d13101c40c001c10204804c440c02c18512 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 911642041 1250 911640791 911640797
    0x20609061b3c0a1707030815010203040522051305010c020c1c0309081203071e12050424020306150c25030b09010221040b0f0c070b1509061e01 63
    0x610b0205038054074022002c2001424504002008902105000098086184a5554420070340d40f100c8070240740c0f40701c035040c5030b01603401400140881c2c50820803140c21080c082c8803515a03003412a00f0300040d683e0640d102e049400091111100b030010078000d8100a8100e400141034404602010a2000f600d00c080760807103612000d1175804042c0301b40b141c80c004064500c02c481e2910032000c0d4890482c0d0060b101c0b40041a40b14288903500500c0412114121141c1d4032643d031030b1040d0011020281100601c115a90f40100681403240016443c00009426691300010b84034945141400110740d0049603894402201303000800038400d0008912035201c03480001d26040c0711101042440a400903000100400d40c08010080c3c0d4030015409090005410154417a800c140044000b94040054401410501010002500c44a451001250040b40491a8a10307080450311070044650301994030440c5188803c803161081d14201d2603c0740c02c40e1003210402108040c0602c21000c40000000b82814 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 911643291 1250 911642041 911642143
    0xa200102032a0403050f010c0e0307030f08032d0619121e0206030f06010f0507081209070f0b1308150115021914061005030712020609061b 61
    0x1070b101078006850045503c0000c03100c40d01400030406010340030701c0307400400192400740f40701c03c180f43c00240b03201102d0300310075000188012a00c81c000103500041804201d4038040000107500e1414078070801002882d020501c030a41001420407002c1d08503103014800c1104514414030150300041e101c06510350b44018000603514225526406110302031101030340c018008004c200e6409080d01032240310701c50990761000c110030074a9083e03c0a008020f8054200202400603003003601c004005241c204030190110341c101991000195403600803a000084221401308800100341d25450040c030242c0200300140180c40300042144890640500c40c080754407248080840d400c500a102043c58401e5424143d9004149800c062100708500030108803d48940320000300c2d2007402d109241c0507205c009010340685490076910707034501400c107a81a0f074892400c00080e101651a08014003e840029810782d5403031280d5800c481c1413141564042e51584041d244000b61203030800c42403200000c0150b11104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 911644541 1250 911643291 911643361
    0x15020d090c0b1207022a0301090b1626011211060f04140a0e040b07090503060f071704110f01050409240b07030903030c150f0f0b01020a050a02091b0a20010203 70
    0x30140603108800b42c80c01c030441c0180500c0d441012106840b2075142e0300c0701e000c4cc200030400c0800e07a0424402488608460314018440342c0f402410810010740114100c4105441180010b070700c0764800711064411440c0014100444030032945902181c1703030304460342c0d91042c0c600300001300340c01d400600042c42111081c00003101c0c24050402140508400344c01c80d052482c2821542c81100000e450800200b065a03031880c500e00c1e03d90b507415124952003441008100e0050007481031915842e0713801410b00400b440041040c010611500c1d80c540351080d41c08041601c91765040740d07051850303000007510780b404007c041c021a030010340c107100b220742c140360149003c4a02d0400b98805500260700c0f101e002c4c141400304c645440d6680000f03c010f1728042003082010135480040e680c8400d002e100034103941010f038442e001740c81c1810403d07030b01113021200d0580200c40100c0ac2f448035484400d2610200c0d0303207070004c0100c0c000303040640b9401c060110021460760500c103a03020b10042003160198800d2180e0341c200e607 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 911645791 1250 911644541 911644543
    0x30304030e0319050105062d0f0f1c0201110d0905060d0204050603040b010501110c010207090e0106080717060705040e04020d03110307060b120303010315020d090c0b1207022a03 78
    0x60f00d084042503031248903e81c2850600d018020030350f0014820b000c0d0058112140d01c03050194501e98416410048488801909200e2003410010a1355804030505c0095440c43e04c13107880010380c0308400d04a6090440162002504844c0500c0030300d45144d004107107071034515801c0b484000545900b10b03501d507100c150303101c88c4070061b1040c1c0d041150480004000c0c0803c00c09594091410b884090301c0b50344001c0805003101341e1b10440d094105006034400c010400010000740d020852110302c80001007421a100c005d50340c6000f81a91100c40300950751102c45000078802e0001c00d800545500e442407919142c50080205403401820203842854200c00308420103004484d0700740c441aa800582e5124030803410008010080403444034010a050500880e02c04408011130707041c1c0c0c0d4414140204c0540a031285002508072584141c2e005559010b5800401c0d03c034030581005020410203075580b42d50000540320b100202400c84000d5602000440758413203107c89a020042111100c1710480075802c600103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 911647041 1250 911645791 911645803
    0x703081b070c060201020309011a0d02041503080703020708100203044b063605010b2e09181113030807030807020c0612090c120c19030203030304030e03 67
    0x421103241c05100103002c035011b4024510034003401008100d40d2183e90700c9100650001c0f42581c1d80201c81c5102c03100103285c43d43c04044284005076081e1407840d00ea40d1940d4995100003c280c0c0580d0181e80104841401088110244070711b00001b54198145540c1300d28520b07000300c2d4102c032000314020340b42c0384030151740c155542c4d070b401984498151120450003448010250b40020344003c0e0421504980380744c40600e07000359648240c40981100b44402c845218050b5040c201222155200d03422560306a4035071a44045103240020900790504a4281142568452943d294103012010800300281800d04031081000748030600085040080e05003000f1461240581c5840c60081c80c1c0c03400f00034010000c01501821f44280ca4102e2503480d40c6206981d100c1c128070180c0c1c5e1101041201145042900c0b14091308a40c0c040c044800c0c0694600c005569170468541da890303550b1102240504a19003480141c0300c108046008940321410b64021980320700c0003c00c0582442000c03582c440c40e6440400403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 911648291 1250 911647041 911647043
    0x20103180209100f06030203010b1605030d0c03060e01170a020f04020405121c051e071e03030506030d0309020f210303280507050a0c06020d0e1e030703081b07 70
    0x2a02c0307a030b4542801d1000a91600c1c1c06a10000150f2000208119000b48201ca05039005004e1160600900541e0504600c2182c6012240313804144652001e40610740140b20329544c80783c90200d0b40c2404c00780300394003c04c0168480100ca0079900710741c030301c02d0720049550003d994054800f44105402e881c0401d020744602d502240e00078a00414150340c0c1c4401040a21550900d1301307903042e8007c00c080044415001d440900c8441d07140c004e000803421400040101049445074009980710030700350440030300d5a400c0c140706401180e221010042d0502d81445602c02c0b041c00340c20100000242c5401003800b2100c0c9150300e43c0038240404100643c02c42c420910b0343c820b2401c1c0b084031b603a840c080403074009090120310003500540022000b6000100780f070091a104040700d07078600b03041c042254404c6603400100c00c1c0030340c0c00c2e41d401c011501d900340d900c5c000c6940610b2400000e0610381e6111072407600c0b000003901c6602068005110030300010b0303400f000c0e0343c2d080881200ca07a00d40d40d220403020a824811024 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 911649541 1250 911648291 911648299
    0x1031b0c030504051e100305091e01090804090b01030f0e12030402031c050d2003240316030302150106080c0309030d290307260c042a0c0f0201031802 66
    0x7030141e2496245c025122400005580020f416020950180c081c1c44050303440030a180c0090000c00040584002c41600701c4407028008a404a05616842c445a100b50040e101c9152240c01c0300c449944c2600552501c0d03101250300700405240158502e0700d4040b81d20a480e981100000850159a0b08010780a403600d13101040c5c6a4081e81180042c116902c0091035003181c03070030031140e40e200d940382008030101e454000c1d20280c036681d102ca50410441e500f017640c10741840300016405600b03480411103401e1501204011141e4542542006898012035814809212500c2001402540c1e40309401c00c2e00150f292030600c3e100c1d1909501c4070300f10300aa0651000c01454000000c41d16280d01d103c030b02c1300414101401d82e00c070300b0080516440c0d264a020301c4c16442c003c1501c40191000c1c2d03920380e0140301d41713400a80b00400f01910008003a500080a200b2044680c40c010f503641c40d40e01c1c0c11207040c2607010306001c800c0300f0301035807450f03040030150001030706056880902e10080707101c040d42e001d10994028 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 911650791 1250 911649541 911649559
    0x20712020f1017010e09070b0901020a0b010b0306010306080313030204020f0c0d09050406050301050906040201050a0903050a0602120c0319180b18010b04090f1202070f03051b01031b0c03050405 85
    0x42d00184000000380c0800c00105201000081c000341d082e441d03500607507070740d8081c0c041e1a0500e0540102584204102811440344800b00d2001c282008541c03806000c501d00e03110b5482c1486800181664015001419507410411444940400300208001203d80c1983c000da15410101d2541c02c060281304440c8015000c1e0b003c030f030445581c1c081c040e03006490046400b04030711900c502c1810b00b25041150158000c1c0e00c480081005076014101506c00d00c5240d140c01d042c401e403261358043c2030140c0b03080304861054010603c1902c4030025030440c2c0d440080c0154890071403070681b288143c0700032081803090b40030742c4e100c0f80e036022540301ea011400da45400801514050034100d910f1411b1a00002c4440010351800d0802c105a25050281c01215a0003002ca60303940759240e1a42e0152924001c102c2d010f6106200c000105026240c41030001140182c001c0d20b042152030710b4002c1590031411081d410140351018107aa4844800d483c1003038408980f921300d0143d1600c0c901a40c161180d600025842070200b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 911652041 1250 911650791 911650819
    0xc08010519060b09010e0a050a0b0c0d320915070606080601290415020a03030528020a02010905031309230601050c1903030504030e0a06020712020f 65
    0x5410280c01880c10116210200c400c1e41c8001045034200e0003110701c00c05081040502d6584940c070762459806000700340341c0303200d69030300001251488240d20070b41c4d06a0021030070b411001c0c0140070035000c02802e801d1001c01400b5a403401c1500d1050809203c4035138040120303410840d208182a0341028001810000c0c030741d00b5001d1910f003582c001d0b01d02140c07114242840801d40c40b501250250403101e0003817041400140303801d10300c80b9000200218030f4641e0010300c00041c4590303c030b408005950700242c001e800700e850b15080c002d0944c0c60040805182000403010554000451802006e0400c0100c2c001600d4a401030400c80c054418014064114030011403440d40680144901000301c5489403000c06c20110607650f240c80d04105500c41003000c0c18440005400c65010b80300070103681281070251815a801150300d05480c002001e42600080c0d03541040004050f002081d13000c09400460b441525140383c500000c0d03588c101070048440365541101c84404544a8061610704040d00170410800c00c0d8078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 911653291 1250 911652041 911652043
    0x306060b0306090702010c0504090e0c10260c070201030b0409050f0115120c030809150705031918090b060d020301180b010f23040506030403020c010f0e1c020109030c08 74
    0x402d8452034803c44004000c0b901090051088020f110500d0300c2d1681018509a4008000e05150514140e01d000e0101c0c8000e8594440c11090392900064451081d990380360005038450514000d50418400760040030308c5824200078041d0b0303002a81c24a000310310b40c569140400c01501c980940280240301e5811001c51025041d000f102c500d14000754684601952600310350000d0041540c0035040480a0704c040c00851803071380003058100300140c00142b110301c01c0802001298004001900c040d040420107404d0120029442a07100c8454602b01c05401c4003000d000741041414400d4942195407821212126203515003902d0300304250409c01c5407a0740c0c1d203504000e9a042594099080c0901c0d0144041040d8000d000020000c0440c3e84ea0229501400881801c145c0d2500b0003544089d206002c0042c0e0b079510312000714801c920a0303005d01101e0000d540058500b00f2809030590500544115044d016150544140c6000d074129141280d0602c0a000686008490b80c00280020000714404280104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 911654541 1250 911653291 911653297
    0xc0c0503160804080118110d0f0f0c050d03030b0f0a14211b04060f0e010e070212040305010915020319021b0715120c0e010e0a0e0106030603021207080c060d060306060b 74
    0x1015107d290300801100c0100804580c01e45002440c0d412500c41d01e10104800c0c4298002c242c1c400c2d81c01c0329140d912600090503203002c802044000035298038655032142011260010034107010348500032110305000c080411400d91a01340c038068105a05580024031440000c1402141c02006072082c1001003404038039502c201840c220300072414554002124034107000ca003403c44580d80302aa610380d081c449041101c005c00b400c0c2c401144102000f02d2404004c103c010002948075200022394003515103011415044100c60380c009031481401000101a220080351003001030203803005075a401d05038000e00034507400240103e001c4c85071040c042106601c0c4c1c011200b42c01d086443e141450760000403040141c40000355150009490380c10030507160350144d5905132031044010140800c490701d0f0b00c658045200c0980c00742000039103803c4200158107086003110800c407080006001d110303003820b50340c541d03800950702200d008210000fa0415200c0060744140c1c05940d10250520450761b03110342d600c00d660 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 911655791 1250 911654541 911654543
    0x210705010b061b0c030a03020c01050d06180203150a06090b0a03060f0906030b0c070807140a150c1b0209010e04170301081e0309010f1101111209010c0c0503160804080118 75
    0x1102d203080c0c015045c41c0020320403130420392603030050820100040c01101e8a801007880c0c540c00c0f589a120124003403c83d4a010034035820707403220050312840d15074980d0180f003d9264800340590101a800c0c0085644881e4003401e4078481c42f085540d4800322031044005080e070307521074140c0640403100441d04100c6a013045040742c0c064002400c4580365040811824415614020417415040040741d00040c5500e2686000010403029a0130070005904c0d007120000e0051800b000030b659540d00011825007020103019811021501ca000500386079010074040b100600454a030780426100043c02c020300e0350b9078034054524070f0300e425440707507035850526036200c441d44200d005c60f0380450b02459000400109880710789505039950b202c075103601c0c0419200300100200c0d10810f5501d85228468402c0b4a0008029001c40300341705020a2601042c0c081c2103c00d9814810100441c584480d40400d0700002922000c01d410b0f0350281042c42d40380341400341c91045901255580d42881c00140454509884082e0a2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 911657041 1250 911655791 911655793
    0x1180e041202011b050319180b010807120512090406050303040603090b010504020c0d0c02041104061e020d020717011803020303060f03010605280305061f08210705010b061b 76
    0x600280c5003400310100f40c00c4204d00014805000003583e2034075034945074140103e89000001e403241580ea00f98280c02000701d054400300000c0c001001490700400c15900284040030000d034020b0803681d00d55440c3c030481d031180c25502c9004038001400b6903c907409040100001804c403a80d0310755a45025024108241007074502c817004000010f110700702402201c03505070900c80079200d000c8074642d0036240c0034036041040e03812541e2410584896190580100003414064640413108004040008088244d4040010464014000400d051900012040b050b128410700058518800c28007031401020740074940e51560160f8800d0205042d00400114010072058803d811070500c4207007810b09071815403080300d41052444c0001620303104a0702c45614410500c03009920016626141d0701e25290091311400030a405070b04189005064207540701004010010142501658008050410041102c4410004074002841000f0024294000c0200c808000e102903100d03544440300a51180ba8101d0300410303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 911658291 1250 911657041 911657051
    0x607020105070e0f04180204050c0705100e0319051e04080f07051f1202191b110f1908070501031103040506060105070203190818010c0b0601180e04120201 68
    0x800b902c03459080003200000b42002807050020428000140220034401c16840390030820308005035640c0c080c107405680e1210354035440740c0c1c490810b00e04080c0f0040584892924105550b14a40c10110680700703030846551001c6440c20344541c00380e440e4400d9403000d582000107222222684146070000e8403e072141c400407100114511a0826542e4000c1c3c0540ca60001c0454001248200c090009505907541071030014100004450001c0603a00031000d482e0510f02c07a0b590041016500034010700d0714600f01d80000324200d0700da80310040300c0e00d1494182da000301000070900b5590740740c10921282450f0341600000d03480d036841009580360726090168038002401c14011107142545401070324006c6130000054001754803000010345d5290b201070402c98040c09056080c15002000c46912100d150060408aa6483e245001f018040c0c99a00509041c04040204640401c2d00c0f4040654001c000b800d10805249452001a1040006601c2402d6180111007040100070040d10107480021158000f840 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 911659541 1250 911658291 911658301
    0x103060c0216090e0109060905060405010b01210b0105090d1209150207050607170d050a0b0a18050403020f010c11070603060b0a0f030603121e0504050607060b030c03030c0607020105 80
    0x40c64040040c800401258a0302d030600929103260302c204070366550500001803030442a81c8a4054a201007410f403910742281c0108001c0c08000e01550400641c01d1810007120501142403410814019060981c0103640c0c0b8100c50069003d8001c80b000a02c0c0108012075090003468031000a420f042d19140c0082d4851800152002c0d40341880c1301c204580703402400c2d8007810f02007070040c039411905069501c200076072207124003e40040c0041c0030240900102041c20725101b0100000d550311141120b0184007808020410450078889051203800c44030320106e1540c555003412880c140300d20080c000c0719442d0000c00c0d24003a402c90384440880704200140c60200c0d50729402542200c41a00c59170300c02c801d0400843c2a207074400c00704078014624034180003440c0e61f12501c0c2e451880d1649220407010505c000382003402c1080c15041c03644891302900c1c0042c0b900d42400042a04d60040307680092060b61250300c00a40342d6000e208210302c150000c2c1c11280c540c0c0d04808400d90b1030f4802d0b2440009940f0b0070f40811 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 911660791 1250 911659541 911659543
    0x603080304030e0f060a110c04050702030406111212190c090e0f060d0f0501021e0403050c0406080309040e0703050f013e07030320090307080105010320270103060c02 73
    0x102e04c52100800c0b560600340070f820b0a0f141d0000002850b18503002d0020500e0741650383e0300ca481d01841c1c95600440c0c9560500d80e0180c4100d04002c841c1e10150700c413134030f200c0d48a40180100d401326000c5603c805680d40300c440c0740014103c0b00c20000c0c00e0a07400c2400d1304040c55444a1000c04686174032214808540750702031849480102512120707040129141040040380601088900c107602c14070005161400703140c0081c5458042d01940358005000050070401c1c4801007000c5807214a0854040003880d01d06a074540e582c1c8079140c1030703601a98543d0580170b8456820b01569000f1174100c0d050354103da003200b0f034550080181d0110507001c0013001c1340e00ca40340700199050225807041c031a010359400081c031001402503005100201c00b0141c4420700c06208054207a138110704d080c1d41d4821207403559410f4081600b0806641c1000704240c0c5840010408902c103600784a202c508000205010805601c022888061070345490304c2514040041900380340805500366030480380200700400c0004c010070812 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 911662041 1250 911660791 911660809
    0x1e050c1506060f0304050a0c0608061810182406110303040c0e060a05041406040e0f060412030902180910020f0318011e14090303070903080f0d0603080304030e 70
    0x150489010310403400300c83c3d00c140046400a01440403908004410368030307510071507156000b050025988000f4040182441421000a000000d9101030145440d5a100c1403090280c8503810f034094506000c80c12030849035214407030161183c61078007110004a120b118130810503206420010381103221040c5100b4000c8152401141c0c400c5d424003510f4070b401849400d50030050400307a0700c6501750300000707841c2c2d03100d204107100440c3c0e03814044410314050341000215407903420914495000050702c12621400865000c1e0320603484540f4090300c561403402100100700300c00740290090210300c50107102e03144822206114400d40400c561031204204086002d9010b22485410908000d20203c1d18982c48840015100d0280800005140b80b41610384007c41620f074034544c480c155900440080700010001269120700a80000c0d859402d0946008005100c01c1c4400b0f0800760f408a1408540110704e412625244400d800c01d1025907128244449194410b94003100410301d03001015160381009105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 911663291 1250 911662041 911662051
    0x303040602060a053402010e030a02070608040611032e2312120901080f0115050c12040b180301060501120c03020d0f0e2407050a1e050c15 61
    0x5890542c445203580c1000c0d1001516103844400401c16016a480c003114501c414503441c14014044808001006400c58000d01703a524940c8d0002c10ac460b252039000074840c01150b2103454400119542e600b0440014410580e01210305007000003400745228569211100281352030907000140c40c00d0f08580120031940344160f0480030000c142c0402101c1140711324401412010300350f921210072070085541001500020881e403010041f40c1d464035968440543c5512000d178500480d50780d4180703407001b14071100000c480b070100040010f0205809c90705001c100227503203e01c0901070722079881e0162200c541d00407928107010b0844240036511513180500420302100c4060310f9035507a10b1401c040d04000f81440d11008801c0c540c0030401300546d01114070604020700b8a00c00c000445c4020a87c1c0281031120341595680c8030704108400040f441c0d0702d04080e54200701c031402c03c282d59554082c0b05440d0900f1480111351126000c2d40b15030f8101790400000c1544a0004040d901051280c4103881452141924 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 911664541 1250 911663291 911663293
    0x302060105040e21041a03010e040813030b1e280f1e0516091d04030c0b040b1b040311060a031e020d050114010e012106030614060303040602 62
    0x8010012410035500c204031448a030004d988200002001204005000440d00801004009010402101140f4168003840e2400c20031030b1031545083c41110320700002400140c50703810300148188000d0b65440040f0001d69000755007031f1580c900b68a9075071082c000d2000102c251002a80042e403d0b0a00c042008180e0216032560901e00720313056110001040e0144820000660b15030500405818000d09418140b1010f000401d1a1520005008041a02c00061014400091010320000c00300c07520358034031700c082d00350700800e00d0351141021540c44640e42070103054442020148400e029100c0c1c403261140358406d0100b100c1203481206c40e0920b02ca9071102400d500c1d41200304101e6403810600030146900700f0b1901044401081c05031070711100810302e60515031035000425810440c00e50240b10700505029035103a489042c6580040c16040d00440d8481c100b009252654005003843c2100707568401036010208a0300347c0380c2c0340c0707940108510303042d0350211300c1c600000904514002046606441e101e43c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 911665791 1250 911664541 911664553
    0x120a05061f02013911031621022a060d051801290609061902010e1009020102060c070c0b0a03020f070c140f060928030f0c060c0302 58
    0x1c07403280c00c1241c0840c1031045548603613401c6a072019101d08014030030801c61441e0b203002509510000c4520204034540d003805022210a2902e070313170100c1500c01c0b07000990903842a000307691810001000c4c0d21004084078052600c3c40d140e40e56800142c007580b0640780f444590f94001c421400c0c40d010603021020940c007113001c002c01070703000d0840c2d0003040e002009920180e411410440c449420744600c01c29910309640350b0b0304450707620151003840f4440044107071406480d1174402e501095182c803e0300080c0c20000c15000050240502c00d510941c0450003c109441c404510914080d003e01841c00c001e0340184070341c4000c40d44410700c00085400d4164481c11600c0d2240c81c1402845803500526007203802d25509002c01c200344801d84000740301140c4680103108410742802003403a0420503e05070503004030350f801000302c62510380104a8040001c102ca02c007000840d08071314805805240d40c408172803030144c0b000000802c50028a0040c0542c4507405031a004c64490100f200d480070b200d140039006038804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 911667041 1250 911665791 911665819
    0x61b050601060c030905030601031110050a0c121b030e2106070c140a2904020d02090a1518050606120621030a09060e0a0513050c0705060c120a0506 65
    0xf007896408452013410030b10141d40d555000203040c040c09130b00076600b00d1100803240300c8501e01081600d100141c00c3c00c00310300f0b02c004860010301c29041c5540c0181903405000c60700c3c540e41c2c016080512a158412011401c003820b41c5001801c8208000078140580b0100101580000314240d00d581e801100e98014820303943d40d82001c886200414000707440401c0032020060b504402031180d0786e0750a02444082c03000e0080403010550020f840030103030500d01090003c0c00f0060350707030703220b00240c40d901103902286c02e0300c50558080042507507800101c100c0c803c0e85000611b0b405041e8102d84050f007031b82400c0100703540f0001401032a115123450700d807803405901d00261491524594402c44681154009260b00041c80181840e650012841c080400c100e03000c2002500da0095221400351000d031402c4405600d010701084142e80360071a0b04920989500005a4440d281e4081d290f10035040070403641c05040183d00c40b030305640000c05a4820710280b50019a03c1c80081c081c0da80140c00c00b81001c20600d200b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 911668291 1250 911667041 911667047
    0x806060708090a03050a050c0a03120309050c030115090c0f140c0705100e1009080a08030604020c070e0f070c080403260c1f05090c090a1b0504061b05060106 69
    0xc0c0c10201d8549400b80000301680d101d980441c000b6600c01c4c0c000381815032032030502500c0c1104d9090b0301403094000301c0c03040c0005549011503000a80560402251120043c9400f504000a442c1b10070741540c0780c02c140720a0300c08a0803040302242d0344180204804441c03440b040310212008030507500800c03002c101c2c01c5c005c0c10340c2c4401011821621010759401a0300d5000007030441c0214031015000942d103509088080c0780924602186100d90b081000c0418584020b0b0740e15800f65440141090901200107201612150121003043c104401a110119200c0da44d0b10070f007040030b40d15040d800d42000b00040682d40128548906142c01c01c1907181418a959aa400981c10f40e007500f41110501c812144060483c0d10040c04500841c64080e140031006d4a03118200344105804030040c5e5406c2c101030114454001c6410102030030f081d9601c02040d0303034500e1070501819110580d428250714030007981c948d05501c070303026200740c4130a540c4a0b18101001400c01c201c0903607180015012750071001c0100080d40c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 911669541 1250 911668291 911668297
    0x2803121401031b05150d0e0a2406050a080312011418130f05010f0f050c090405090a05100b10031e021b0303040809040c020601080d080a02121024080606 67
    0x640035081c405100c0c0c1351408680042c0c40c0c003a64810302080401c070a2058807140c002d808007040c60300014503484003e03440b01c08407201109100d400c8074030400c00640b048449500004003525000e410448e0304d0385d5030688c0030b030b80754407802001d200d2403400c2d0300104806c164003660008002008005101c090035104d409854074501a14524041064000810014010030b40302c000e01801a400014112400c04089083e074a007810442c0da8903282c4010440c00c41600002c0d80c1540c8029140055195a0031242a2030312016a0001c0d10910520b00d40f01c60345080ba40007148910342c1600d00034010540400240e003600e804041034205184e202c40100146040c50b409007410100c120421220549030700303640350a66006480030303a02c0344800070320441a403e05000b04030440e070103407000701180d6240c41600f0361520082c04040c002c00511a01051440030603070107990841c100100c1c54041428140084a5000d80c24030411045030a0540e40b884000b000c101006020390150702c0304416a907800302042110f80c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 911670791 1250 911669541 911669573
    0x1206040b0a0b030d02010c08070507211b0b0709050105030c0d0f0f0603140c0a21030519110c030d0518180c0d05010801090305160302280312140103 65
    0x682d480c005210103a5082028990400240c1c00010f00305034011002030070494001c2070b00052080400000c00003a038485040c01c0292192050350414010116048a0300701840720181d180c00e40441c4c80805001c0340b44059401400300703483c2e06060316912401907130240000c460000d25188180506c0000034601d400003525001600700020301489030311045421a9003e4200b91600812611304c541e280740c0402601c1d11115044484254541c58050161401000d030402c1c0c00484205058040801d030080003540d1319600c8144850383c80b081040401052114021303015901803082c00e003030006900740841c00406d4205035950711443d285031044030342c2c04041c2e000c0086802005034250303290382d03800c2500380c01c1c02410351100c0203945040c0c2c0c40340d443c1a40c030180c0082045034502104240007036003040442d0103100d20741200200140d003e08040c2c1c01d001048144588400c072210324144014020803108402500c2502d0300b070101c0085260000031201e00700884074030803c2480050010510680d4005011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 911672041 1250 911670791 911670811
    0x91b040f091209030b221b12060b010806010f0f0e0303041805091b03070911070221010f090209011a0d0e060412020607020a031101060e01180b1206040b 67
    0x1076265076030100e021100c00d80c0100094400c150900400440007020b82d00414102d2001d01020402c0e031840050b10701440c0c0c001d100760340c1e00350b0941c11b0016011940e001010106592000031600d13040c4a00a0810350b48501c0c0003803800d500103200d07503014003d42203050317080ea51910003c101c20030f130550300206020708440e410301c000e02001031184031244c4c0084200b40c2030080130030103081c6169000e18001e24100b02e01d03c02c0d201003041103a1134400190403022a120f05402003009100030005081d184034a410103500441040104025548404c041041c5508500001c0000c0035100118108465010400960182c1c16900401c141ca1402b490010101078007000785c1d151070740d48a5040f08503240301600c0c00d0950010420002440412649002221241e00250001e8640040c00a454007400f020003070522410080e6500015000d60001c409041a801450802d50b11100065000340c41c4110341905541001600c0140d4200712201810920315040180031039140d694a900090000900d402c1003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 911673291 1250 911672041 911672051
    0xa0b061302071704030308010b07050d0f03020d0e0105040b0c070b0a0506061218072c04050f0318041d0304030b04060f06030b160203040501020309060f0c07031505091b040f 76
    0x200d034543c0c070345502a92003809020b64035403840c40c000d8110728050340b004046a03000c0c0b05600c081140860312038205507144c0303031120146400c0d4000782e00a024944140d0b001c2e03846c2000705c01014030154030041c01980120ba080b4015a1200c0c411502441030060041134500c2034404034540c0003036904141d40052008203d1402e040c4007888030f0309a000c0c103e40204142041c02d0080c203681d6014805000a041e080700a5400a04455080c2002500030b54145480c010034500041c148002484404110400e40307099a6582c00503420010f02c41d0a0240e1a9105a18161000c2c0840402400320400030000740d0156017014078540390354544000c01401900c50039103076400740810031388c10300c5104059485081444a24208800482c00d01104141d0000655108000500c00341ea0000705981141d0412640503030b8038521880d0400307a0b0b004104054800740b10340407020041180010269105071020700d4204007907590512140d03610000f4898a01d8030701c01d01c640110703a40c205074000c20003242c00b102c0003040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 911674541 1250 911673291 911673293
    0x50703051c050907030b060603100302100908010c0207050102010e07060c0b071209061d071a070819020307170f0a14130608090708011a010c031b06060302040c020a0b06130207 77
    0x140c450403120103d854018001c02d01c20000900003054103c03206032000d50075841d1419001c52803840c50302010b80305030103413521000558414261407001d440d0f020f0007031000410960703002e50f41712030500815004d5400d0070030640741c1c99000185401224110303600c09403a407590b41c8455100d030101a010408205070910003160203080d41c01340c0601c0501c41c41001840c0302503074401d00480d007008881c040198012260820030b00303800c80c40d43d808101803d4100340d500c40b40c038a0710000e40d1082d2845c501030348c1031500004070274680210103030458a00416507400c2c0c1c1e401c0e141c900895403181c800e503c6c416400c1841079060103440303045083d00c29850041202c3c50405030a0102e00446900d03030140700051620001c018507a90280009801840640000e015180c0c440c1d2441300340018010741141003113113628040050610900d4214001c00b4040c4404e01500d40320700b081c2002c3d103160b0005030f024a0410035080038880c80012040c0d1526000000c208840d02c820040101c280c2d90407021064040c0c0900c5450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 911675791 1250 911674541 911674597
    0x61b0913020c06060127050609033301270f09050a050a02041803021908040510020a12050c1b040209060a0507020f04020c0303040312110f0a0206060406050105070305 73
    0x54803951107001054280f071310200041406000911502c1c1080c00030055044440c90304422500fa5042200c41644615242c000300e440e100400c408600c182c11031204e22801d0307401040101c0944041080d56500c82e070380300c0f030318203000c06054000140003603201c0407020150100359116802d01c91303a4650214501d0410345400745003001d044401e450f0354010303400346030441c9402d101c1d11140d0448501d881010480c0c07500c0103512001100c04112046d40da4014070002c2000c802c040f203028010023001c8122011101100030360310400d0034000c9076040e844d5800303015010b010740c0c151044450404001c2903010341d4041400c11b462810f1034800d8215400384084007495503510082c3c80441042e0380d600361680e0f40342c010010844902d10000740191300c100101080d09402000701ca5026406042c000c1d10061012581401400e1910700031000704004500c030100302d0050700c0180700001495080b100d46413141c0040000b01c0340e50348a101d000c50020060000024003c0c07000e40b8042d290705601c01001000d540e80b076 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 911677041 1250 911675791 911675797
    0x403090306090b16030605010e04111b1f020720040905120702210c0d2f0405070809071502031201080a03090b0f040909151e0e061b091302 61
    0x48800a03c1c01e000c21002040c080b441000441642c5414040c3c11318083c0080c207078607803050b5928000c82d216030b1000305034050041141c0c0300e8045942c01c01314000880c1c40c81912101a000b0490070b00024800000d4050700600a6800d0a900f00005800b0704108a58002203241101d0741e0b180c2064440021101240d420704c030320111081c2401100b507072090240b040203880f048001100f18005070602a10080c8600029a80342c072613010b03150400131203840d091864100b40c454002c03460b845c544014941002007149420160902705980c00d010a13224404280c482c00c00071242c0a4942e841781c50200541c00c104051626240c00900542c2e00d0f2500c40c00c8211020402600715100c1580300c10180010550300803072407001030003001c8003d401c0c410851492020341c4101d1041c0300715940c0351120b86060000d000401405060700050400803020300030886405000c254102d140b46504d00701d000102c40d0b10204902c2c4c41042c0c001c402c1542e2016540b80c2c6800780d04941d44d00c03030300f0234041809061101c5c40e1b8801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 911678291 1250 911677041 911677043
    0xd05010c200609100c021002160b1302031c0c020315010e010f140d060b0d0b0a051503100203041b08060109361704030f02100c02011205040309030609 66
    0x744207110000a440c4496000c0303024000001640032000300481c82c40c0101d0068640e50f0060808034290182800407450a462190507900b40780c40010f15045ca030441010308813980c3e01c41e081d549199900d9006201d2071440c0220007940540007801c0c0145400540f00f501c94030103c55040825008540350040391600880c440a5114080240010b00c1808880c00b4503a00520000308100201d41c14400d0904030b086001c081c0d50301841c680d89042d4100200c58004c02d03e00346000c1d088248015150030b143c4804441034880310040791602c0003103041d003041c81c440c0f00381c1401d014008185a244015084e4000c3d072000304107542c010000340d48044034401e44240c2c04010103070780e4000d01c6e81d541455102c0b0100d8214400c8546007007a40070305a4031130f241d0040c90076204600c02e05c4290100d00542050b1411006c0c404241008080020b004810419400c483c00712517402552911885007107264140c0390b601c60114040d0204900c00603a45584040b9004240d0041c420b14000c911595659581c0044d03410340c01d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 911679541 1250 911678291 911678297
    0x20d0204091d0c030d05130e07080402100206060f0d05010216050307030201051312120e07090608070801050c030402091905191401180b03070b070503031b040e01090b0d05010c 77
    0x60031100607000200000480d410102404550f003104001a44d0342203001049028014042030303141c03149007a002c980000703042c00c01006600d4078296400505400c41110100d204210415480d0300092002410603c6880054000081807500c4070030049920390a542c100d8042d07408004450180d40070036034544609200790700468072115203180c003070b0a40302c0092483c02d038503100754094000301d62400b0003a81034558a003008030403241d031514081301504900c1c60140c01c0340714103400018500b140e0b41c004d008491569058426881d21584054241d500c20b480c00d100c00c00c8144003140143c03801080c1c0380e4002044965400e1200c00d0a1124410f0b2041200c03c4030950400380080e681301030440c001c80c0041c0c500810038100540c100300e46182000d141d00c5180440c03690b11800455140c40401c6282d0140c401c10410716104c078124a02250b4a501c125031460001600c14204100c040c040c00a03141564402e5001031a56803c08030404000c0c041c0f8500745030300000d5940d0300808900c0c01c1c4240d2880107100d035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 911680791 1250 911679541 911679551
    0x10b040207051f0207020f010c0501021b0d0f08090a030e06070b01060305010914160f02010605060706050106090501050f09040f09081b0706141207020a0c08060f181b0103020d020409 80
    0x22420b00085100e03c0c0040b580500400540d801071752038403821a245142400d00392940e88190400a009003c0c040c02c50348503000404a20458102c00500d20503101e01503500e0f900d6041040504892304070f01900c00316420f82c8854041780010380183c82858040380060710380d074200346690b1604031aa150a07404a070109030707500018404107144c0e00900d98062508002130000f42040c03d0200c01440d101280c01d41000b00712041100113501c03e4100000a000042c102500c486950800b9401017901780b01e480e0200e080c000000035254042d0003950340360050004001c1c1442d40e03403000d01024080c0103c3d00354201d0350303944840e000118a00040e02e0350a000c0c80c01c106485840445051500d0003d130000420302500381d40c00f55001070310341d0403165035820b024030414a035140d00c2810f13072070100c00e51030061041815000208081c400002d001d0701c41d0920b850b80701d556031100f102c6a100c5140342045030485401c40c40c14039495001e2501e44d6600e100040c54018a440c1c0d0260702103080741c00c0b54010451094a503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 911682041 1250 911680791 911680813
    0x130905010618030201080f06060408070b03090c0a0e040609030e12030d060b03100b0912031b1917090d140c1302280c0213050414060709050103020c010b04020705 71
    0x111410108980b650080b03224040c1c1150006003202d0401001e94241c1c05c80391001441688482068030002c24110f03048a034906d0300c40084250035001203901c81442d10a003400d5a00034034000241600f12202c6264106058940d902c0c0d500c09032541c03031403d40500c018240313054220b40710542e1000311101a030b0041e540b03036041040d01d1015501c20740e0040f40354990610601c600444594001c208680000c41d030550341d03144840c04a240001030500c0e520300c0d0701002c40d4100422001c07900c04a1a00700c0c3c83e055540b80d8422140118403411210800ba280070b040c821b42d0102c600c150401030510300d0000f000e072804140e1958903107850030000d5006441c541c0000000d2142420000c0031406295504602541024981c00d0402d480c01c408121980c0c1c1802c8100c079200700c460040901c41180e0740c001e88500084207921103c000603250984086662441d0b5900c4c00811040204030361380184920b580f400c1c0e9542c139000046000e90000781d0511a15540c80580144654907880240011441003003e0207109600d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 911683291 1250 911682041 911682047
    0x16061404031a0123090109020705010f0603081315050d05150907020d110f0d0509131a0a121110111e01060803040b0304061e0e15060301020a090e06061309050106 71
    0x1140740c1620345803d206100e840155a0352815605580380d40e5001609d81950342005805004a0514511040c7ca004804000c0c040140c0c02001c3d00f607003404005a07150369550320541d041610200020000348184404a005183c0350851600601d01c8411144843c1d0604000b440c01502966140c0c0581c2c003100750703e40c090b50400c00c3d41a00b00b0f84840508849044407803583d444110802c0031008000000400b4010340d6070303c4403502118541000200041c207000305010181c3c00d50814124410389040f0400110307032041c0106250240d6004000004090200c0140250100400103e20500c4071303038010303c034120000700141159540ba000110f81161020444503007102d125800c00581a0000c010078840000300c002280c0e0015402500000d00000d500b001c5040203e8100494030a0360400403511030f40c4000007004800d0078449d180e400303001d4440800300341c201d1003030000b0000402c0b2100405c000020814110540c007410240c043c3d031801c520504005503480b41f030341140354555a2540140002a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 911684541 1250 911683291 911683319
    0x10617102103030c0f091223031c09110d061e090b060a0509040809031e16060e0d030c050c04020a0c03020601050a140f01020f0718050916061404031a01 67
    0x1d81c506140301e84c1000620b00031b2140c1b1407801000b5100c01081015810081981000f042c02c1c90416035155072400583c1010b40c49604c5800b18002100320400c6080c0341481c2441150090b80d0f014400006088180c1d0074080303490400d42054805507518852014140c0c030441074107600c400e81101c0022400d045181120500801420482c01185c0010050080c0c1c0c444130b12854200390050f45040d15041c2d000002440d0000e61304440f103402044d40c200050804000812130b242032070710808666543d07100c5204a6079298103031510f507400342e03250000c3d5010078014102c4c44001c6d4003500070f8403003009a2101040a076070201302184005045024444141541840310f1805001c0461f40341e50014030740440f00c0d40c0740302d4136200303140700d1203201c07240030b800740c0c020010743c4c40160854042e980042d5480381201e00030903850031078052007400d000008034042030210b4030a1454030b08040264801d814600c0c101c42402c4c1c5400c000c03c0c030340020840400420b91008008048110303ca0442d040c82d81000c0d541c01480b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 911685791 1250 911684541 911684561
    0x70e4506090105040201080601111c0c030806040b130f14010807150c0b06011b0203010f0f0f0e0714060409090b16030b010c0b1306050123030601061710210303 70
    0x1900d803d0901c40141c0c0c0c045401c0d03400102c2441c010041000c1e00403190b044c0546282c40500c5155100e55004525410440d0808114000c0e251780c0410399400c01403006079040d024140764090314201c090506d100030790707021911130801c41000042211108200607581c8000ba002051a68826101004820100d030752081c400402443c1441c6002c03048e644103d03c0f40380c042c100b1410700803e00104a00a02c004510207070786a0000d000340030800c0caa894540c0217244280181207403900b07151a540300c40031940600315108207014020820301e0310b0000780c01c200b00e0b40006040e074070441c1044001140c0c0e51500902c60014001c03104600c05041c01c80071001003004c4000448241400d281a4000981e04070300611182703070b08020011016a2403210904448509031801000d1500d00f4001003000714100780a032000507c80175050b0100149542015503421091007030340c0c0003408511884c40c4041000919039000f90069500744c0f4015101c1a0512180c00700740b020428594502100f5030030f055040c0141801c1c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 911687041 1250 911685791 911685793
    0x3030c12011d0c0f07050613022404152705040c03090f061e09110307050d0b13020d020a09020d1505010c030c140a0c17070e450609 58
    0x21000850306900b40000b4811060843d01140710610080300307808039410030342e00200340c50316131030301c4240402070404011080e402041c8040f10325084808032658820100106001c0c039042603e4021004001c102840c518001c1000781300000401c040740d400c408400480624040f82114281b9041c0402c84d4003d94004040605003800d500229808500004501d6000880402c0302c9100407014554415802c000020b4207103014141c4050100d600300c55241c565003202a80c103110354490800c1b6088043c0503015086084150100b1480e2002110030909507201800c03600c0c41c2c0440d600040d04100d4103501485075035400091b00d0b04010594421616201078030341845c0ca825003884002003016035241c4000b0309100456129200b4040e241c003002d10b84540d004219101d860071440e0002d45400700d4440d124016170a020251038040700400c07840d09840c0242c1c02c0000550350004102c00081810340c0d40b081c1303102d540f400c0304404440c0186901045503031203084044044824007083c58190014584031003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 911688291 1250 911687041 911687069
    0x9240b27100203180f0607080703230a021b0a0608070e030607050c1c0f030902040204050d050a1b060e0105160510061403030c0714060d0212150102010e0a02040509070803030c1201 79
    0x5c2c5a4802c4141c1e09401d4103d03112540f500501c2c90256018070340c44480700c8103140e880d400304c0e203041c0e80000288000980c541c00e07140301e401c491260440f0492041d600d40c2c0d106a4802050104900c90000300d54030540901d069100040302c0c80100b420818141d441a00240c0c0015030155103550402080c040d03c0c8481c00540786a01420170014a04052010a8810150ac80e0908015940c403078040d04c02900004260702d056502501e4401d54510b071118045400c0e10100c0010849460402c0e000000c50f80c1c2c41e16218004e0301c03108011210350340001c0e036803175200b54800140c0011410030441c0300d0b03800f4020350002400d541481503000807240220181c510a9004100c480310130080818034004803189180c80e4421010700c80009a01400341c7d9440c0c03401184042a06d40181125034401c5d8050400165400a44050040120300ba54a02c40003010070754441c0c2500303c010305042d88031550007c0610103807807205486604641c1140d01c20b0303954601100000c078500070005490f40669004040119aa8079 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 911689541 1250 911688291 911688319
    0x305012402060a110d0f090219030506070c062a081803090411040e0702011e060e0f090102130f0810200f0906030109240b2710020318 59
    0x5600c101c02400070803203613250550448241c41d034506035040405450002d00c0340c044a444000020004500141e00c80c8280343c50151480e552801884207594008003d085c543c4e8600100307940352032207000300711105503131802c50a2901c402203500361845042e502c0c40d52000030f10824000e040c11800f40c8001c450444405507403040c0c20000049a004010540e00811f0300510384821119038000c03a0300416070b1a40b0501000039469065100410b14461030719421114907152815408803072540c021180424000b80103d0017981c1d00381412030f844242c0400141c90554545000c0079a00200e03400340001006290050208102c1400030b041002d044a82c01c00040102d9410300d00c8911400039002900032000801480500381a01100d1a008018050301e0b6256035a2901d00010000f2240000c1040000107104407507a44c1100214103d405000c1c21078102240e9041c40c04c2696086114000c00441c2c00305900382980340d0b0368118181e060b141e0095603d41d03514021140b60506224903903481502d041210341 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 911690647 1106 911689541 911689543
    0x13081c060b091302030a090c061706030303041e080f0a0807020c01090807051201020c0601060804120906020d030e03120103061a06040b04090b010516030305012402 72
    0x4902907a550940301d19000e80c030a116404000300c80c1808a5000c80d401954024011100000c0d125400b99a00483e0107101c0d031110010070483e1011840c40c0d01010445580620141c0156145140c190b0f1744154a02c0c56280c058a82c138404200d00c81400000703825a5041c41c8981c0216568202101024150890483d0b400006104030071010b6510b522900b0944100c601000040c40498140001c00110451480f17400b9695035003400308176910b450070400740e0300900d1241c807641c0307550410f0706105d03c582c1d804140d440144078081108115207a03001400c00800c03a054a4000b441c036080402042c1584207d65442e050350781c4840020050010035401944583c241d03018411034026100207000c9107005520400c02e051905010411a0304800e40044248000501d0401d141124602c0514003410a44000380c00117603484c001403040c0400780d070341d4400e039003801e192124554006e81402 = true := by decide +kernel

theorem cover : BRFrame.Cov 911510791 911690647 := by
  have h0 := BRFrame.cov_init 911510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 911510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 911510791 ≤ n) (h2 : n < 911690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
