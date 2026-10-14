-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:48:29.773125+00:00
-- url     : https://prove2.me/submissions/801d452c-1825-405e-8c5c-7772b2484333

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 566187050 ≤ n < 566366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 566188300 1250 566187050 566187077
    0x201110619180b06090c0d090c05130b031c05040b0a0903050706020705010203030c030403020c0a060306081002070203030910020304182012061c0b01030b0f1003050303060603130b0906070f 83
    0x2c0f1000c040c0c052032040588a010501c43d68400701600d0040702529000c2000040c00d26120141c40303100c1c800d040c015590040c02c0c012001d40c501c1190500003000e005000b041c1c1c3c181c5400c1d11003801e9041c2d91002e0010500001c941c00e0303e0350014000c03280260300c41480300b90440c200a8030b0001281d000c481190300020040c48680d81c0407050360341001a0004883d02e03920340389016414518203009c0c4035004003001c0400140180e2540000c02201d0710001550002a1541d807890168070840602030341690041100500a040040b15510000c92030701c10350741000d80380c01080007003110340c3c040145101e44407908034883d0084480701a81c01e10a2500311490810302c184800c1100a00404e800d10a1070b6024013038034400109500d0300034565202c1100006580c4904e00202002d005941119400c1442000036a03807010322030450003980e801400031825540d0701c2c0d0411443e80d1005100140711800c0004000000e94450000d900541c1c0701d001420451401c031070003e0994560055002c10000c90b480f000a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 566189550 1250 566188300 566188313
    0x30d0b090717060607050604050109210915090816050306060a031a070201020d022106030c0102060109050a0f0906020307030b0a1a070215070b1b071e020111061918 72
    0x3602c0c000c00300d400c0c1c0641c1e0b6603c00011410300809101400b02c3c001c0408000401ca810f5114100c01c81c46114680003140e8201100745400d00b810524501180c00090107004844840f10800075a81c114a072401c1019110340384c4c2418210a403503010150710300140144407600d028040c1035070200c4c0546500700301c5d81c6903071a0504d0004007000103154601800b40800c0c04036202390115055146292030540da82ca414400e15050095829000a400c60041c40481c5c1340e40782c041a1000c5440059008010f541d080c403403801c00602021f004007011980e1910711080030080c2c0d0094101e494080c9800680301e190001015080d07440c1c000d6594456807040c8018001100c0e203c070000113480c00070f084a0b803070740142e101088850703401403948501b032000840d55500300300c42881c8040c4030301d4680380c00c0d003825900010112418050304400030510720307052418601404600d101c81c440c071401450103814140000580c1401c100003555403501003601880c2d01030b180300e8140101e824400d290141125414819100e11307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 566190800 1250 566189550 566189567
    0x60e06060d0914060c0c16050136060c0506060301091e050309040203010e011809050604062d0c0329010c020a1a070b0603010e0d050d0603080309030d0b0907 69
    0x28141c665151080d0043c00703000b80f5403140d01c4000d00111005402c003801c0d081d50f160001807500b0340511804400104114040324008126801a103c0c0e10003c000d485d01c030054090704041018540caa00d4581d4540b07d0890700c440b00060101d503e40101407041814480c0c280302c002050103003c0e0781408040000540800005000500072092144113001e00d8540b55046204030170050358003a001200215017500c03035440c1503040750a0490402114482c0d02c8404065603001074001e0035a07041000003c0204011390000118141c0018907a50351007078071109204da9005842c1c05001c6240c0c1d40c00820700454241c03145e103104142c0554450520122070558040b03885510701035604012204c40440700b15250b40030043c001d0205c0c545007a40c1c0200e031030b0300042160030150045da1740528240100709181810f00c034001d0350105500c06051494132102c800e89050303010590307408449a96041c00400b15131407002031405041e802001c2c0d07030340d410681a00e209841503600120b00c03c01403942800805038100004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 566192050 1250 566190800 566190817
    0x406080114040b09101506081b1e16030c020a050303120c13080f03030403020c011b020d230a1b080304060804020f1201050a0f0614011b06140703060e0606 68
    0xd11820341d0764071142c0c0d061601840c4014031139403c0c01440900d030001c601e000c1e02580c0d07d503512000580d8500300300481d500542c0c1101208100c2c100039800c06a4001ca1a0b0049500e103400d00c1840c044065000400c80a460038017900000c4203000c00d2011460b00405800060034110019410400d030020004c0c000709014000380c084400c0054403c007010350100030b200c010501d03582604c040800c0185c10b56240d074401c5904400500403440814203560050107090402c00e24044500c4440c01c440d4244020342c0c02021040c2d640802c0300c00701c021401c0d500b003800741000c00360201403d0010070a1074841548511190700110015151005210002c4000140c5d01125410319085d50103840314000300e1248034441d0340c1190440075410800c2c0f04240150802030080c4407985081091805a560076000c4555500032000716040a8140c030b82150f10031920110048800c03100701c01c2d80700c41955100c084030301c0c0c40c1280b04007242250401542e140c240c0b08000003006115899065131074504000b4089201c0c1694 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 566193300 1250 566192050 566192063
    0xc03082a010e0c010305090f030304150516090e07092103110c0102031e0f0a081801060510030b040605030f0120030103020d0305030903220512210304080c0714040608011404 76
    0x1f8468080802c00448809421003d485e40d07070800703090620f80c90000001000105041402040420700400c41e829448200c9944044c8107038101507002c0e08881c0080c244404111a080740451038129070440c18610200a6244412030f01d4103180140800800300c03d0000c0640006a4213003440c3d80110488003048182e00021140d0f9168007482e904a00440310004010385010455041c17031a000313107600b0b02407910f022020050f4940c02c0c0fa414280d400c3c82c0551600400b85401c0e40030107600076001601c0c03001005101083d42d54540001c0707840c2001d000c940c8241a919082c040403159001c00200000d03207042d41c00240345604507008140d00c031300d6042c001000c2040000014020080c248180d0314804224241c080c0500c007200d0381440e105c1c01d1405104d00ca012194003060203180001544188009602001604480400d81d2880c03ea0401413043d00c004c0c00c204105060303078106100030800750145071030f40240b401c20b020622003114840e402c0142540e140c00c00721080341d585000c0c1c29a020340d0091 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 566194550 1250 566193300 566193311
    0xb0708120613020706140603030304150b04020d0e010606030b1f050a0522030519110d0201050f0c03030a0501090905100f0b210105070206070c0f0c03082a010e0c0103 73
    0x4002c0342d00040700b01603006100c0c1c07010410b4400c20441e9084503100d2a050008200d031603c0310803c0640381e11045d1002004002082d080c0114204150803a500040d0014401402d14040041c10015207458804000190350340f902d0030700441d9050b214454224800ba100d82d000300100038408c04881c00810010000c0c0500401c1c2050302e14807400031160000742a4121203440f000501c0c4120b11400540407c807454001c10000c04100035041440c911416013200034406959003140501005640c8a20306a0400004000001010030080024106685840c00a55881c60300012901c00c81d2010703007103603024500742201480800d800240c0c400c0c400c265910006002070708502c01000409403254496001101400518900000c441000e494403800034006d110740c1d5500c1c1000c0b03845d43d00440702a40450112024172003c0390503100072420140c49264400d00f1981c480d00d80c13a010f41c000ca2240c02a5145600c2c00c01c0300d034540b54605020340c0c803406001f8490840c84051164a900004240a04155452 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 566195800 1250 566194550 566194561
    0x1051003060b0f15030901050f0c090f030309090103141002400b0c16050a03080f2205010e010309030206012c07020309030d140313080913020408070b070812 69
    0x80012105a9000401400c04c042c02050b0314482504201d44100c081c0d403134500082d220351101e2803540e20900201d2180c91074941c00a080003007850344080d0640c0c1502c8207100010711f60300c1d1400aa40a54001d94a03c00880303048000b1919040010400c21403450060000e10141500d80c0d910a11079200d094110020741c8284400c6d0500d0401c511102d03113420a0b440c1c0000d02c0703801c000b005200e0450482e00f03072a60003644003058040d0209a00c92103410000c120020408900001c0140009501c00c107045803602c403800881950512405a8108060240450401c01982c10401e41d00b015102805d0a01145046480c00f03525441d05110701030b4204141c160364130505460a0055081c0380306843c030440b403030815810084d56500031511003802442080c254554584c001e84142440760f080080451850341c48000c060b1004c001088111400d40080c441c1214035500c078240b0070345000d003520380161a1072034910001d20700407542c0e1240705941d0080040328045041ca500f00c5022265000070001e8a4680 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 566197050 1250 566195800 566195809
    0x5060f0601050d0c2a0f02210607030b0a06030e0d0807020717010603290a15121401200405060f040515041505030601121d161701051003060b 62
    0x41e0b0103a00300c01c84c0340c0741e816820707582c12018041c2d1142c0544480c85601a4070a09103403a220b684c01c0140c0f0b5405606c00000051401d040c0d501107400168011098200c10601414908201a50043c1c0841c1d1580003220700c90074100c4281c001080300d460b040c0000e2500540280d158080b8018031802c12000f000003c684a0080000320014100ca050b003100b000d0344403242038024091800101c4d2816034805c60050544546886101405150070300c0030525143d03008650024841502d110300d01000304900003905403060142e0000690140c60780000842c50280003500f1590b0b440c0e10011640301160810f4040c9a01901359800c2e200151083d5580f14024295075000d4003455022560100349108000c007000305034805401190000c82c03c1e140e01d00c04c1442c1c19030311400b044031014005007110b12032401620064201c1c0082041c100396000750002980340701c42c02d0050a5548a0689254090400c41ca14100102400310320344000204058180402417584002d003d200c083c2449480346d0000c1580e41d074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 566198300 1250 566197050 566197057
    0x4050702030f07060203100f0f0b181002030a0206060103290a090213090b0d0312091703012c090c0d03050d090c1d042a0305060f041b0305060f060105 66
    0x5410800da5103a48092074928040d46c022920f001e204c1140540000d44403603c81084001d84841100004519082800c01212500312a6456040c503031016880305481d02c0360340a0013810456507000e190381d003104c040d0107494002d0141615040528041c00e000340d0300011120b8241810041d41c07011403400c11000010324002468104449091000494008901e400326003c402c603000f800d028820071611004004050b1541076000d400315410050340b6242c440c6130f41c451480c0b24481d00ea0201035481c002050f000c2600240c10007211a00000b038100c00c5450803c420342816602c4541044140c0703802400e49803115a40084280107008260003401050700440640d986014440d0040200071568108071103000b0b81440341004541340c40c0740301c20080300c072200352911070354001195146481180c100a518264034030010030000c0401000400061024401d850040b5581c071201c2c00c0c0e80c102400e00b0304542030010008440300301e103420100001800842c40c254881c1c10701100001e980d0f1041c0c01600e141c070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 566199550 1250 566198300 566198317
    0x8100e070e040f020d0903090b070b13081903021c1503020d0507033302132d03140607210c0c0b0f090f0c0a030f0f080403050309030613020f0405070203 67
    0x24001700c0d00d2a0590010383c04489414081d5a035034048d10b0740c403122040a403092003400750004421000040c68004072010401c0140d10411050b440c00003d408184190810b20b1100e20000e0b400244041100c02c10940c100c1c000b4003907100c200003668800390049001c44017844000c3c01403403440f9540c030502200b0702c0b01c0b800550b000003241c80444000e55071404603c6290020100555200c540203406003142d01c245c0d1105040542c20081d89420400e100038503070140c02801c0d0003489400c4141e203054824510031001544501c5483d408121f04c000c0e401d00748103008100804212103140700c66103a504a590800b0409031500d40018108000e5400700e07000002040090070140c7d882081c0702c07502d00ca5850440c465054082a80c10303c103d56401c00b500c410019008552107a840b2030284041400c00031101e440c103105005440803519503543e0504141c0080e8001c0e0741d0383c0c202044254107400c05100050740a04640b0762035085c0c00040d8001050883c00781c0d644c7e8040e50f641c1300001d00c0b0783c2c001c20841d5005e8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 566200800 1250 566199550 566199581
    0x406080a1d0d0c05100c0c140717100f0b060711031c0c0c0503010e070306111b0706030c020a0b04110409080d0903020c09010503030f0a0e0604090204030308100e070e04 74
    0x40074800c028140b209060401c80d41ca01ca6178542e2404142c0f54482c0d100c40540aa880e120039001d60b0b159011001300941c51301005000d4042c001410070340c540010200540880045c003d01c01c44d078100c2d0000c455012813244819810144002e02594542c7c00302c580d11544004003903070120b02d1201091408650b8295890341c08240040851030a0b003000c0c101d15038a02c114828580d0780c0e111000e03d82030360038041400800c2e44c0302d844184006000e50b00603210b41246180d40c0750410348000c0c44940c02c902820121101600302e00b0040c011103906000303101d403c04450000b00f0540c0c085549029501c03100501c0500b100070002c001c5a40380d555070308100e04054004085544401030041039600428200400b00c0261207a8407031111b803402d0210019040f9540207001c1c50900b151494400450360080c1807601c20840c1040d28042541c2e81c00d000761003d403560f0100103868500398a0041d100704000b030f0000080f09070b112020031425a23a9942154400f80074500b07446170750100800301d4040c11a807808088030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 566202050 1250 566200800 566200813
    0x170a15050108150d0804031b051f020a0203060f16080601020606010c021c08090f041a060702150409020403060e011e020d09020a080d03140705031f030203060f070f050406080a1d 78
    0x85c05051030203803003500d000300350860712540342c200b040c42006035610840d5004954624140400f0408104440c0003400c1401a94086e03011580000e0500c00200e032024004d150203414088003006000421a0410752030230a01c04d1401c0840010707581e24401015241008404006c15045448045844440c00c43d0400d04400c1c080d924a00040c85401c6000400e001e0075000740d5501e142d142c10701525044200100d11800b66201001c203000c1240d00402059801c1030b0607000d81e03107170b482e445070082009006407140140c6071030442c5002c030f054540c0941594031981c10b0500c0002c014000800605252200c100c0059032160b81d02840c0c1301810f07800a01960041c0e1030310001a8010000c02c0c05035038030300b440d41c0030092140192290f00749034000f43c5014000800920010309141c03800540922038000b00030300324411560340ea000926100e0100c0385154914607007818007045171340281042c00540e10b81d0030303c01c0c00d160812a0051035a100203042c09851b0391500002d180080080c4101202d001c59441503508 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 566203300 1250 566202050 566202053
    0x361f0f0c0207150f080f0c0c0703050d0924111614040501060305010308070611041223190809040204030206071a010f0b0307030507021c170a15050108150d 68
    0x4070340806100701002c4103c6210600071040c4103100103803e00026485400c000d8030b0300c850b08002c05c0d800820b1840081c10400901c140036200700008401035100300300510450300305030b000505202c82503015030302040041c1c604140f00b150f01484444035401c10300d0869040a181c022561420412900201c1d8883e06d0a0010031300e8203004000c0c004504007a038051142c2c0c0d903244003c80440310244805011300138140410800140240c020380400751030204460706280d19858090440c11942904a034110a40840c008600031520148208054131101a00c280700850920944044407008010000d0707400103842c0d0341341d944072340c1510055600600410b13210402d500d00030140c00c0c11960041c1d00300480000010b54400c841004005490043d03c50310705540342c107501034024190180c02a03043d0301541c0d90504800d20380040360401441c0c0d0b44ea85401d0f10b609200100c80c8404050001e0245a090078484018156030b64a09400c503442032804203d5565503103071100c011850030b190558015081e040040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 566204550 1250 566203300 566203303
    0xf01050304061d030706150501020a02060a0215070c0b060409200d23060903130e0910050a020d0608060f0115210b0103061d07050a09080303361f0f0c02 67
    0x70b0030f40c1c1b04100800c60745561900710720202d0340074890580141c0c400301d4103500509040d0081c005c080e00c580100c451045856410b011070403003c0700c03aa400a000000796405002e00500316a410210a0701c0c100300307111281d12044482160101d0261490748817140510994403040030701c00e0b200b0f4100005441e0a2500342d04030035054090091000640f05541c0416520f43c0e011040303034891450456a80600c5140610031044c0c1d40d0b00602d64280d90041501d103c00320030050050301d118a4450000580c1c0301c051140720382c201d807126005550700d07a025100b0071240420344070701c0c41e055480303215140c280400703281c004a400e21031140403258028404005049540d14580005900800989092102c0780e101c050321122070500010030704030035540d0030205c0c0d241ca003d040100f002a000b0325042201644504249103554020b450700b8030004000400d0743c50456021240038006800c2100d074521607505081c520b07540d00c00c44804141180580e040941d8a0b81c49030388040011041014144041d8001c4240039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 566205800 1250 566204550 566204557
    0x305070b1305030d0f080406062601110f03040b04210302030f13200a0503030a0e030105060a05060708030a150306150602070807180209060c03030103060b09060f01050304061d03 78
    0x1007020020181c001c40da030b2030040f8109228241541e20700000000c4a601196502e5000d03209642080e6196808070301c000740c1e20f0058020090840446524003034103c0d8403400c4441c030b080e288034928020f004280c00070800a040341d411540050604181c0d880340d0070980c800c8940510340082113014a160300510759010b030040c41c418500b0038003c040c999203610118200980d2010024000b0540104030203100c01d5100d0080e00ca51400f800902840d5120310100745141d112041140102d550f210700c2d910745150034010b041d0b00040c02d4a03c940150715140c049055801040c1004241c00c0d0003000061940c00c455210040d880d661680f06102d0b40d81c1d0b414002d00a20001040c600a0840c0c2c06001c11071500010360034088440d2711000305800c52810401440c08512010b0311005290204000d0169648200140040d0448180619070f01d514500e00001152a09a80316006000700020080d40340da800c1c4007680506000c2c05d096642e036650749010030007442e2070000300c60340c010369030304410b201f06000024 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 566207050 1250 566205800 566205817
    0x131403090a181a0f090403110d0c170403020a0308030406141503060a05070e1509030d0504060909060b04050d02060c010903020606130b0a0501050c0a14060712090c0902130305070b 79
    0x800c03501d1849004042010f0441c91030070b403c071980c4040c00707100c5d003002140c04e03600078040d140030700803101d2000c1d2081c1821780a1010200286040f0040000e0003d84081010046517910555290515550108100000300e220140c202040400002c080c842e040d00041d07049a00ca40d24101c03103242c05602d1144601c800f1800a000f4030507840007031000c41c0c1900c00c013400bc03c01501c0303140e5140c10070010404004c00400c0f41e03c0c030941043c0001103082d2010401d200003640c41d62192a00e55050000c01002154940e0009103518101f03c410002d5060f140115410f80d942900c145013800c3c40d600203d6614494144101000e6103090b0303504080c16400300d06140036000850310410700f980280d01c868152045207184075401184200c0c208880c0d8061001803480000400c1900c1c03144085440c0e000103400710702c0ca1020a60003100400180c80d41c41075203241c1203074450004101600d2283c4451035140c2141c010301c0060b907400164401281c000071054402154003100f12201a91101031081403034001c100d4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 566208300 1250 566207050 566207099
    0x608030409050c070b04080c0f030d020d050f040c0303050d0b1804060605010c0510051b070c0e010e0906161e05040e0108011103070804030e120c0a0b03131403090a 72
    0x3003010b482a00084a4120307130003800350b00345c075200d40e01d038a20350b80d01074070306100d103882400318020384140281301070b03c0c6124543c01d00507202c0017241091000c0c1d078001050040380b25072250070000000c182da02102c0980c1c0c2c040c46d11a46902014072210700502c80101c0c0f145d4828660fa04081000038041180303442a071058206100d0155100c00542c1c24062900000300b458000101400c10440550b04c10360340241221802160700026038461541640810001d94080701502000d0007540503a54541d4010507001047c03095526002071b400f074641e80d0141040d4141c050141800310038038881c1707029050101c51280c0d51094468101809446540140b003500200300814000160300030301841a480080150400035245694041c01101d04040043c011010b001400d4000c90031510b401040340d184c0805100146501c000f800304101190030591311035100f0fa10100100b110340d25290b000d030000f10303a22542d007854420b03120315594110300420745055042181c0340700004030020203064107002982c9040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 566209550 1250 566208300 566208311
    0x308030403030f1503080306030a060e0a0c12080702040b010e12011a040614010c060f02040b03180d09060e0a0b0a02030318070605030c0304060b1503100e041505190608030409 77
    0x44603101500d400318a24082e1804d038507000c201003030080d03000b5580820002c05442500380155510b408807040340c00521050741c05903030968100140c04404002a141004800710074031140d903a00c110300c0c07059040007030044d80c0328039104006900511205000da04020311002d1805003141c0e01c14000c198803041c0c0654405060341906c80ea052522808050302c81c014141d19180300e02e07030015540140610012100e450b510301d140c860b01240d51010f403000c0d00c00c10b8562603a9080c1103c1c4021486883c2000707486d203130080d080100480750003c8101d4100c425500707280c01e8465224001911a44559000d40c03162000010400081c55002c4015031007035a4101400308400c03c3c02c030380c181c1d96031064000c85010881c1080030550707003001403010315445485a0804030f242da0b000d002150340d00e62003244a0121110200c140621142c50b513241c90041e108103502d0b010185070680368007003202d480c095100c036040d42e1507010036091140c4020b500c3c4411902c0d00c0501016a036036a840eaa2039001d48100411240b400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 566210800 1250 566209550 566209571
    0x605091e040e0a113c010909090b01031101030510030212031c06060801060203120118090530070b010b0307110d02030a1403091b0307150c0203010e07030201142101030803040303 78
    0x5071620b14800032210b03a801d6602801540d1105d00d0040c41c0d0194180002c001002130410050b01808002c984980741140e255407451410101f08065400e416051508003020040300e9000182c0c50030450b501100d030742c3d000c07007080e0702d0442c01d61184800c00d0895503031181c00c06805040d180c1011003110440e40d03c60515a0380c1b548100d8a0f40078200c650045507960600402c120062003004946003418000c0000e039502c030075030340c0900d002140d44484582c1c010040341c01d022120f000100c0910b00180d00d000c14a840300b103540300c400f540300500070f600c1034203408004114198410426642420610011074140843d005006981c0740c11440341c14000800c0381d00c01c2d800044084040e01d01518140c8020200c2c6a00b4040150102c05101f4156826100b004d5001401141d0301448072203248064582d1607a124550040c182501d00128000c05e950340300c2d000070030040c0d83c8072000490b00c00181050035240c0e000e6000c46001d0001e80305481500e8407005001200740086000250f0069129031000c004c80b07402c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 566212050 1250 566210800 566210839
    0x605100602010915270b090d090602030d0213030203060c0315030d0e0136060201180f170c060a020a110c0a090e0f01110a02070605091e040e0a11 64
    0x28000200400713200e403640b01150510b500580d500f0b4004071202c005100e4001d8640c52040640c1c003083d1401d1200c1c0c021320000d064180488a035541d42840c0c101015410803101075640c0c41903051181a41c0d500140001c808113100e0b944002442d80141a51000d040081d50300c60f25400c241d4861054150b1156074a9441c030b07001a08104075402601c807014540d04000c0155072a009130f04400c04044030394482d0303c0c0001e2940c40d003104490313440440e5100040c14001300a0071200700c2c04811001e4155203900001080c1c003d4000340c2c0c916444280c1000780484510360702c6860107051024030640c8940414090702101e19000380c4132400f03c5a46005401e0b0b41d62000580d141c0c2500e81c0d464000c000304005002e01806030300107180c125481e90484e401880798503665802c6031022011f841c01c0143c045070342c0d0101c0c0d03418480f0000a216034640542800d94110000d03880002c0d800080a080303a401d8885001526a43c110b440316802440682c2c60900761403d0018151b243c0250440c810383d84071301ca001c0207004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 566213300 1250 566212050 566212061
    0x120606050405100516031b0c0608011404020c1c050d090803040b25030b0f0901030b09070608010602030919050303131503020703080c0a03060b0403050a060b0a031a0a02090d060510060201 82
    0x2a00440304581c9211501c096440c03104410f030078a00807d50070290f40118040d00343e22002003140b50b50b02e10440d850304c1040c00c5040c0701e588007944a82d00400141300c580c900043c10810204825480364240308644000740c07010302c2100340c1c80c4845c03820204108103010012014501c206e0240d02160406d903100c1e900001690000c40303000c0105000083c00074101c074070aa018500b2914040e2461040d6549140081d181d928241e00890703003100b0f80400c100f8820760a005a00013031119043c00c14407541412000303034036809800c202c203020798110280901500d0001d40100000c000240c10750b81c2d1040880b41181000e000c602601180300868010119014400c1c400c07254019010342d01c0100079215110000244e521202070141050f44031800840c90b112000d0041004511403c014500880203150a80595605030070391841404143e00c204007007404110946501d0f10030207903550a555500c034840e8002c0c094072181070340041b00301609004104c0158000c9010b810b03044804441180d46040072401d948 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 566214550 1250 566213300 566213317
    0x150a0605010203070f080f070c08010f0c080f0a02071509060b09011401050c0f1c080702061902070302010f020d090204361104020f0d0b090903191206060504051005 72
    0x1c3c82041540049122003003005002880b81a2003450701c044504a1101c64114085c141c0b152021402c08006440c000d01c00c2e41410308031504140042440f070007000d001c80d8002810281807011050000c3c8010919030304842c15a0742c82492107025442d05400c0030000c0c94521800c031401850008008402c0c03401080060480d0340c204901c1c0351b10703207142c801103030031b40c1052004600c18802d00e455107900c444c081c800c0e103189680c00011554003d25403000103144040142c070300710664010703c0920200226660441d000502c0401025030364030300c1443c2c105c0c010302c040c2080c0042144003040c07204ca00342c099008500f0040c001c4500b48803001202c1c0a800704102c1c8128101d81c035242c52210502102ea10030a10b41440b40503890110020030710101040a0368486426012800c800040111909030700c2d04c00e400310f00ca4140c4001d40b00380741c4050398540e00c1c49829405600b08045030514603419109100005c1d070314003007200038054540d441c0701c040d07d13541103400b82501c103d200c2145404040d214105403944003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 566215800 1250 566214550 566214553
    0x71403072a1a1303020604080303061c1104021b010912030c14030402010e13050c0304140d140d091a0709060c03021b210d2a060b06070f05150a06050102 67
    0x10510040ba400240c0e001c18095038404000010000160342c400025100a0000e100616030340d01c1e0110810103070506401070b2103802c1010041020115100c08a0b00c15243d0094a0050380d4110380300ca90340e4188a010910009503081601040400100c112103004403540c0d03407024041e0007044a0203440513001880a511245810b000260141d84121525806e05001038a504002c0069003404420748008480b2041c150340004184810040b14640c80e40c040b050000c0948501c0300030060040800418864042e032424000c035003c00040e407075911980500341c0c0031441d00900507054801003413810041780e960001c50106e00000842e140500340d10381f81e250f49035016180406604105290000c6c9140945801c400c010040400355048020a42d200220f0203004040001c0b41d600010013100c07440e91448680900054a0304401781d01814001c110703a4045008100540000040340c180c0c000c054020707200d4402d0202c06806e11001003040c09503004c10041101d51591440342d4131040d41c100c0c1c854940103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 566217050 1250 566215800 566215829
    0x7020102181c0510020414060403020612091006060e03070f080616031d0c10030b0a03080c030c01290a05010816020106030204020c030d050a090c0605071403072a 71
    0x40e40b8000e2007188110041c8400a6102002c0d51501440d106801c00c0c00e08485600050502104640840325040383c0c10842d5a946021300715170108003a07010702c0000651800d200c0000c81d05004080c410740020b00c400303080030001c0958134a0024150705840500c20f00030300130b41d07001050074081c01c0075100c261000c00004283c9034136081481200d140b500d5510f0b004241d615082c244107002c501145420f00c00c064401410925134070b80402070703003080b80760019050600e88107401c60261030380281c0b001142d030007098594554141444e0325065114100000d5841d501c0c1205070003e100c1c0486040f40400e10350107045442044210511808031340c14001d95011641810001e18482601c00040c814500c1a100102d100c6a403135001c681071341c01141040c50f1680000c41d1384501200d10f48201d543c80b003a403400c207009410207615131900e0035140c0d0107041704100300024070780300380708400d4980498841040201d0359150007605100d210909000c0520300c072030f4059a05650403c100d40000402d5800104107143c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 566218300 1250 566217050 566217097
    0xa0509121f1e18020d03031515080a0b100507050312041a010905040b040204020702030a050d03020d1503150923030a030501080f0714190f1a041d0a020c0a03110607020102 75
    0x442545d00c28080341010717207032046803800032100c030b102a00a04526407440082150240b010300740c20001072051850901e049009841641d80d030460f4038220707040e800d00a66422150400138114861081410407461007081440304010003081a65011442d000100880d641c03a554100151403081d50090b0000189030042400351800303500030b102c064801003c88186001d40d68074541400141185000480d5020556a4520485005000581c481ca010441025007141d40348014000254400c200859039038201c207003000780b540c20344142c45000c0c0c8442c014030030b901e030320403560ba622200e41480020304160000801e04070000b2010503045054016083d40c0781442140c1441d80d5000040c2603000c0c40419011641c410104c800701e0103041c0118160580609043c60200c95040c40444110100d00030041003050985403800f82c426482851864407031925140c010001900030b42c8004c854500454094004241e0012042c03260101d01405130f43e071079a1001d405a080740125071000c000e1080d40c541c00340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 566219550 1250 566218300 566218309
    0x40c050f0f0904030e0112090f0b07210c020d030624090909050f01060b0a200106090e0615042016120206010612020a0509121f1e1802 59
    0x942000a44400036030a18900020301080003620141e02003040000e040142e0359000340c03446103002c04c24070284008d807219900e01441d10030510b170190901d40745ca000314503210700c00c1c101021281f02e052108007201586101c01c1d4000c0c202c94400c003000d0721810480d001e155001e802000c044408400140010012100308650000c8806d00f8080812400b0030010910581500c01c01024078001d200510029203a06289801c503207035034000106801e02480905080760740180380f103488040b0302c41681c2e60300e08d9000d2201d001d0921a0842d0f4041c034240071000c1c1d4140000218240714607202d40d004224450b50900340000c681c81092400214503140032140c22400042c801008200c400c460110039040040c1c5a22000b41100ba159200607040200100107943e4044032208403200042d4086160104000f03015255100c4c0c400400c2c05550b01a80070001e016080c00b905490892140c00c484115007552180b030001d018030342088103112418400f00d0b2110700c4501c11101040003548074000185115000c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 566220800 1250 566219550 566219569
    0x1d01050d050a05330112030c0c050d0f060b04110414060f040803130603020c0309040b0126072a0209190c050414190e100b030108060604060e040c05 65
    0x54a8510031000110001081007100c2e0780c0700c105030712600000e131410705201d0201d504d400d50409401e01c6107400600140114264413a84154942010a0f0011151901070403900080d840168004145442d920900404168400d503481c820841040050504010441150341220041c0132881007440240884410501c0f403000c00e110041c04142000382c0c0600340d10075a80700da00008450b402c00b1503001206a4001e510502400c101d08040d42055034a204959803800303454a090305c61900c0b44200c0e002030340140103a2810b00008030415046414501c80b4959542050315188000703034030b144046840d40c4525010b190000ca800c810400504c000f038007005043c020240030152600d05101000c0094074551040c20ba40343c000c0d0300d40c80d84072490800c100b00c049020b0801540161451020344d00903145001613101610b00841507111103440b40c1122240c2203815410400b070102d03000001042481c070000f085841000d0803a001e20615481f00a00c540304001500d004020101c008024412031800c003950 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 566222050 1250 566220800 566220803
    0x403120c0201020408060a020a02060c250c030209090c0f0f09040b150d0318090504050d120b06070b090609031c0f0b0607030e01030b1c030c060b12070f1d01050d 71
    0x503013803d03100ca52250801000750394440060b640060300c1104560184059030780680c8420340e4a09084004024400d11a900401901ca0000c841200e00800100981c8000a160054020ba22900d4803c00e00c0b82d45100e0404210320400c0002e442410510302108513120550015001d181280c445540e2a1006040642421080b040100528080d41c41c3c584500303282d039000e82c0e601d004501c41360b10240b00189841e00f2007012039050800304070201d2000120880262075a1038854044807100d40642c3c01481c0e00c01082c2c0c0d202c1c400144c0441408003118200703002c0d00800d010740d1220744408683c195130f4800d240c2c0501c550030b034980340c80c07400400f60b0b4442d8105040114010409011200000d0040e60003588102d001c110030010802042d41e051040d4205441c0c25030310703c90481c09018045c110f010b00d05070000e0400c10040005803c00915400c44010f00c0c0c00541900100440030540544455441c082c0c00c5002a9000d40012011811368082500d840440c00c0030025074240414070040d200500c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 566223300 1250 566222050 566222053
    0x2802070c080a120f14090603070201060b19020609030c2107020907030c0e010e09130f0506090604120906140304051f02040510020a0809010c02190b1903050403120c02 73
    0x80015841018081d90420521581840700342c808407801c080c10b80001d84182c1e50030041e005e103441c0480a003040890300c000b003048904607143d40e40c14001302e0142c840d9400401301d000c0c011440c0d080404005c1c60310355203044240c0903154240d942500d0320782d890040c51030785c006503440081c4545410305028030f070641d000c0003451494503049503074010500d910020358078040041da5440350041110303481a100c110001c000d20f001300b016000c01001400a10340549078101c04603600100004104007014140c43e42c139404019141d491601d052074903203c40c030446007035408191814107540c44e1445803000e01c0c281c0c1e903240c54030700d507111460903041400d4000501c21152031180c1c0e0000003003815584210102c1c842454000b41c3d50701d052600340821540380c0764a0300c0640d030040020800060b4500c007650482d00b02843c146149845900020382c026041b40d4402c0c1ca1107600c0180810180051001040c80e0400c1c1840840140c0040b10100d0407a01c00f1500500010240160004000050307040400b02d20301610 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 566224550 1250 566223300 566223323
    0x204020714010905060114091303180317040e0c0705061b070f050d0f05040303120e010207080a031a0d02060d0c050d0e030309061b0f1c020a0e09280207 67
    0x409030840f8490341098609900c541c00400c1000441c2410b20428101910460981e0510903407500100007111801028405400e02d215101486546640011a0424501050400700c12245141a030080c01200214030004001410141502c0201d07041694004000c042c580e85003410143c2e60410703081081c200d6502005601e000c5820b22480c1c2880600070340103409468400c5a005d400c2e10b04181d070030028804213010070004260410480c180482d0004008142c5508402c11180244181c160040202c40040740702c075001503040c0c2c0300400c1880062400220820300c141000b1950030580070003907014030f00300903400d800352480c0c000441004040c102036042000c1410a04107680c0380c42002c03a03081d44040304010940104020702074211510003900d400c159010f079000a198860010b40301d0f4031010000300400316842081000703041c04150901151290349000000f84000c01c02618684a803075034101041032040345110600420380e10030095108800c1d00e900c0100a034009c0c81e01070300c0140028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 566225800 1250 566224550 566224583
    0x50106111209030c04050a1a100c032a030504151803080a09091a1801050102150c040b120702010f0b1c060b0d031e02460c090b01170402040207 63
    0x1801824080c601c8880085003690b100240e4045090031160342380e01c180041851508000d800c100b2070a550340d0149400149811001785884010002180c12660841e00f000160305141c3e201020b882070b03071603498400154000c080c904a0780f008100041100c0300341c038158208000381c44500203000345061030a0000042c0c0e500c0fa01c1c40f00302c902d401e060888107a080d84010340b4500e00750800010724101c0d28090351095050800003540c0d85859042507002c854100089565008208140c2d401001080e20090769940f500b40c038000b44001c00c3d07882c24090340c24811002034038942030055a03007000024103900c198000341041580c085036500c4007039400540da030814103074944a00f114010380d103009071205009040852100c5101200c190106004c6400007000701c031040301d05070f40040700005207070024510bc5084000c0d0241c41c1c0d0041c004854a00300281e1403100700581403a159003101d034440d4007003200000f942c00545190810300c1c0c3c1e4201071044000098014546607000e4021180200310200c10719859 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 566227050 1250 566225800 566225809
    0xb07081302040f06050f04060f090506030f0f0d0801120b0f15040203150a0b0703050405150c010c02100c030b1c0f0209070507020a05010908031c0b030a0605010306050106111209030c 80
    0x160703c140320300c0b030b4031480c00344264201191015041c2606643c1000043e19000000383c2d0b0754028092b142d0000d0b114000f1600c19681040803540030349000003076500c540003400d42150755082c1c505c80800851003003000003c0162100e00104201a00204000c545599090995078410b2009088a80d112400001c01c1e4003500e81d840035501c9815a880207040c504200d804200c01c0e007207281d001c0401500e00b005041c0000354480141c0d011500143c400009c4a03d241301804000c0c020a418800d0341c0d80b0b080d1100555650001d21a800048103c0040100c42c010010072415540140403441c1c103d442280810b0080320700810350745102d0b0050201c25212156035000410609003030f0ac403000001d80216007002540b1380b41074100000c01090900c802d0684c41e00f0f0b9031544a001c1d00c16011503540410301c600c40f984030b40c3c2e00007449019000b01a50700900075858580b0042000b8001a60305900d80400840c0c95802401c0d07403603422240c003004006031005007203030f010907600040c0160340500804001003241c0e00d0703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 566228300 1250 566227050 566227061
    0xb2508250806030708031e09010519080f0901061d180111031902190507051c020a05010b090f04080d060f03060f1803050306060f04080a0b04031b0b0708130204 70
    0xa8559038a0070504020040520f4602d85800c00c0301d20360020082e0700744400b45282c00340e03000007111900513100c1092000507651801b61810000c20010072a801404031503106182a20403a81800b0180d40c68807501e4015080791b40c2402401401c10b0303445040cbc0e4a0200044400781d201003640000c410204180c41b1050940e1000498200d20b000c01005000b030488512040090b8244242030442c10b2802c1001c80c40c0c44a150240d05000307119001a21000384503051004100200707844c0513003c21b02080c441e009664250040c4103172520b503e0030f6070005c040c1c60310f04038150203841d845100301c00c00c1c1c0391500c5410250b480019840c900c00d9880b20000b0b40c101390120803000860141c4800580c8400b0b4401400581e480001d00c4101508203550b2980060780100940c0c2d00320700160740740d44c0c96004050240603030f4451034020352224841d238262807040003940da4034584294485d03131b500790704a5a4605545200c659204c001807224540c90000394a00c0d00c1a01d8141d8072203e107011190980d0643d070007103800c0341d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 566229550 1250 566228300 566228371
    0x90d021810080312060d06020d0c090f0902030c07060c02070905070c0201110309100f0c0611040807080706020a0f060603120315051c080c071a04030b2508 68
    0x4045000c10441c001546982030040c1452005035142c00030303402c0e151030310050085c60a44548600c2100d18103201d0a5816180c0a290351001004240740c1d1040103400c4030004d20500748007841411004c40e81c144c4e14001d8900400504c187d141c107101a6039180c002800c1201c0003001144102e24002903002e03c18007449010300c400761102c8102441c81c0c0001880d0300da6162541101c0d500400c00d00b2200e440e2507880d03040c01021440d01000004021008881c20842000d01408541c1026400d147c0480480c000788100c4806d0ba0858071390980c0c0707590385030301ca42c03481c4991405a00104000400f2506c907102c0d5018080c89008001001a220342c0c540305019504001c0c000080d903a0022a01c1d84031211000308d021703040490303502e01c805d0b45c80001004000340d030801c01009640c010800f800040420440c0c03034050641c8100d0300ba42100346200d10329403500320b440207860807c49140420741e00f941d469a00c806e480e004010b49400241c00000944018601910000407046080d51007855004074801151044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 566230800 1250 566229550 566229589
    0x109050703140f041109040b04020909010e03040e2202090f0a060f060e0a09060b04290a0f03150506090402070c0b030a0f0e150106110309100e0102010f050603060705090d02 76
    0x506003400e0840e8803010b001503176070141d01c00c0000c2c040403540f00c2e0216a805503040f1240759050340d610000c00c1c054050400c0e007000b10b220204000c109942c04541051051101203803440c44c2d811280080d4030701030540c4a02a4200f024071000c0f40c03046244440d150340c84010640c012414903540c03c0d4121500c0f4003507120300d0014807040c01c0c0c40c7c01454203104150040408460501c40c0074203044007903915106a1045242003043d80551442c5403042080300683d09908150141d1900400000901381d294080e0344070000a141c00d64a07600700510840c0a4281c42c805001c0c90b082c880702ca42030000a40c428036041c1c86450f0f076141e0006001c0301001c000c5101d0f00c0700500100d04198075808200903a02c0c82a2412003c0e04030700d29074919052100b00560450320603160a04030014180c6e0454110701c203406040785c12003030f0144a80501500500c0d182d141d65000e034000c121042103c049103007282c0c01981c4203039060704600040740903544614007402c403035000103000c41450785d02c690004280c070072480b80d6040345 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 566232050 1250 566230800 566230831
    0xb03070902031f03030e0d0501150e0103020909030c0d0c03020a0b040c0810090209070e19030605071215050105090609090405060702060c120f041104020d050f09010209010206010905070314 83
    0xf00401d10f4030040d105a60f403c1c003901c5203081d0740c3c02a0543e00c0d21152540500710141c07554003400003d42104400c0c191000902000c15103c40300c4080522090005901680014012074240c130000030403644d03040651005880e52480f284411162120a0b20044d402c40c840c000b03008020030024800346020350f00c140fa02314283c5107481051810002c8401d200c81c071840c600702a1101503182c0b64401c4d03034031210514000400c580c0c20302c00076000004400c0740034414443c02d14088200120740d030088d40900102d80703500e592000000c02c3c01065604118044450a510040402184d4000d034003030311038840020510380c1804030540100c1e8081c00110380507500e503400002071040042d0180710554114140303910f0030345000807800390001801c10140c940c00700440d90b000001d0900468141c03001d03502000034000d5640b4080d0b0500d800103800242d0f00b50306407034454400324040040501c201c80c0031038410780103400d940e8601080e060003000f004200394185529218401d0112819030110b911035401d0f424603010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 566233300 1250 566232050 566232061
    0x1206090c1206050103410103050a11100e300102070b01120b040f0201050d02270a08100b0a0909080a020106140d0f060908130e0603030703050f0c010b0307090203 71
    0x944a41d0781c02241031504d480c0c00461b81c2c12030103181c2c000503003000c001c4100003441c80d81d5100d5440c00b04481d0105d4109020004020000c012804407001401074010b500c14490700000c108005d0030000039500424543e004445042c107003981c042d20011010001300741450864000140441c0451303070b2019099500084000402000a030b0741d83c0908010701410300c444e2426980c048855002078805090070408d01c421404683c85601218407182010000759210342807c0020100308a155949483d00320100020fa903984c10102c0c00d80c011295040020030f4116040c814250042c1a415407584d00040c0044001c903501c1200e005841885114854480d03031001c0c1c040000303007144d490703402a40e400d401c0c0844284503542d0300b2006ea01c24540005c0303214510f20756864038000a03d50310000404400e00810003000545e040034044080329141030f05c41046949901c00c05481e44034003200140032401c2842180d0400d41d11030050000da800704000060404001000a07240004942c00181c509800000700f14 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 566234550 1250 566233300 566233337
    0x10b10050406080c040605030118090602070c05090a050403020d0309030c29010603020702030705060a18030c05010909020f1206030703080f0a0f0e0d080d09140f0c09090606011206090c 81
    0x903402056071300280e09140c00d0282c020304a01c01881000310b41d6000d05c100450852083d401030800c41c0e0302030300440d074403043c0b0303d0554101d0005200b01d40c401c40c200c0d0001001e10001d8000d81c4c1c0f00b59070641c00b81c005000104020340041c440128103404002c40e403821031001600058844120406201d02c00009038861601a54a5134058102004141c0140311050068800182440c141c80d812184680c40d03c800d000b040343d0180c0b99140e15080340c0e01c1400004140042c00344084183c5001b0390b21113420b00d031076040c008180d1040343c1caa82c1854004020b5a0140c4020040782900520010141c8d003c0503900d4035440200d400c1001c0c810031079200000c2504586030004490b044c90602414403240740c40000c4002044043c000c031014100c010001242801040542c3c0300d00361055100a8a60b8580c6006010320303a07400b80342600b05903e01c1241c4060360146000611548101e540c2d03801400107964640044030158003d1f101c41a20725200c2c440411118802d001e05411480250303591000c0211001944 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 566235800 1250 566234550 566234567
    0x712020f030f0601091e0203070e030f030403030e040b0102031608030717190f0216080301091505061b010b04022701110304051e0a2c01050d02040e010b10050406 71
    0x118840c1e444615060b0041c20b0204010b4110380c400035002031010305010200ea1036002e480b000d000518800010010400d4000a81c3c1c90150000c9c1c08807024412081c1d0381c01d66034480e80c003014010410800080001d07180c16040300380701e454103205030b07030410202210184088280e580708407038107880401000300080e88112460018002c0700320400160401c980001030b8181941e0b80e25955503115803035440301c0ca000e078040b01c1c1d1101c81001100c0e26042c6038101450f894000303016110074141410441c60300c03400c051508000b503550041001e440c0c03c40c0004042d50001240380c81541e55502e4401604c543c1e65a807018098000d142e9070320102c41c200d28400550240903d0401d141802054205c0c41ca1810b000004d8070f00380e42003a521511280c10800008600000c1c071a0080d6000181241c003048000c4d5192000c94003418a64a4450203064210010500343d824000d940d003000003402c040e000b603d010740000b2200d015030400001d000340c6210104604170302c00e220b0000403990014003007282c1035005903103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 566237050 1250 566235800 566235829
    0xd0908010f0c0f0507030905060a051305030a020121140f151516020d020907050a0221030f07050c0d0503070e04091e02221e0b030d11030408071202 65
    0x20000b58003007050280c039144003606008104003000c1050020140036a10b05805404014581030b240c01d10310000400b141d1100400340f0b40102d84001c0040d0070b0a00080f40d01181d0350513120a4600c6492620078100c1e0007428070380b40000350300d51290940510002042c00d004021b51004c33120545417045030342680c440f00c044000d000f81e581910b03109046010100340c4641c1c041d43d200c00c0740342c84d240c1c3c000100c003001d1500d406903128007194103100890303802c08010a13100c138098080e126a0616548800c084103040d403842820118100b000800c0e031f0809026469000e1040c0c10b0150519400e000350700d103002044080040400e500100780600150405108a18540308603018806040c1503518403002031903903100d8045081d46c64850408540c0c41d00c07000518040884076440d0f10340246c51038a4040c103540640b40081110b100c940030488442030003860b90019001d80100b080c030135644401c0b206480b04c0c458000e910700003401b01080d241c41c00c0c4800802400348503070307900041403035004200104c90842d01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 566238300 1250 566237050 566237081
    0x60501030c080601120e03120a0609062106021e0a0c0510060317030a090203102f0306090c040906030b01181808180d15050c03061e040b030d090801 65
    0x20042542c0e80700414404200711700f4000b05140c0a079100040c994040c41e03507101c004500d40c00c100400050b03e68440000c548940c1800d100190fa2a0700403104208042c00c00d01c60011446110f4012480030703001041924129400700c847e550134428112074a4001d507010200140841040c4070034400100600322140420500c1005007a01e15901d154a40d5091200e00f80c0c0d00c4800310026440442540c000003101b40c0103801c0d2001d034080040c64000802c1c080c4024510030382ca4041c1d245920140b00d80c042001c1d501c10007510320319200c2400300907641c0d034028600c100031201000082607551090091100843c0300303207048807465042088420310180314100c01c1c11039514145450100910700c030001d112a81e0003001c41030b60b0b204828a420340c0b081045035400d4000d41465102d80410042c41a00009088034190410007501c40c501c5a050b0b0344020b40341e1075030100004107104455912408001172150006100064580340c50011908100d0f40644000c04034400e20710070400c140d4203025a4030010503500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 566239550 1250 566238300 566238317
    0x206010f05031009060212090604060f020a0e040515030115050a081b0907090e0103080702120a02011e050d1407120209010c0602180a15020d02070812031f09060501030c 74
    0x4283c0d00c404200c0d180d445a0345607191001401010741c101c1300c651010b403540c00114603000c10202d0790340c4010b030f40898403a490280b075200c4021481c407d1b83d4800070956180001d20118408102c0500005412a004202e000180682994007403007604844202c01448491180c40c202c1000203d190a5014101c0b9800142c003002890450001e4613840c0802154210020740f58190111020a5240c004c0032450403c04000f1040c810076201412082c3d100300e07441c007400d038503101c1c51315100c40303002c10b000740440c03120501f03805840c500405d03522010890780b8041e410090000c0c007850640d0305500000310800203850078400299030080b400701c800c04200e0800d600e416400c80000380b0000c0742035005004294040b40700000c0214020500744050340061203a00c1e4152980720000590240d65490701c090310842c00151041d0340041400343c200e410410242c0007000741c01100f003806a1009100c0e041c0404281000748603290400c800c140985000f420014216080c603001400f2a0340f030300348000138040c2d0807 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 566240800 1250 566239550 566239559
    0x1e0a1505010e060d150819020a1e050909010b04230105011e0309020a080105040b07031b020c12010608070b1207051c0f0f0906021e070f0803060d08190206010f 70
    0x400449180c200e05401c009071714844065901e00316150b80e00411424064010354404000484030005403c6000321484e00c0d00ba59100c2e816560f041c5a0003002c00055024001080640f0784089216801060103002140000300f4400040c2105e0701c0e90018840e2003010010440f10301e00300100240502820b081c03480090381c3c510171b410b02000c8880580d10405444808003030464591207000b1004040c44402848030703003001e140a0010b04001c681c0b0600091905800a446200d182840c40c48075000360090040b800a51090107071a00c641006280325648448000900c010304100a41c0100219105952a40030407c6a4106510080c02c14001c0241c24042500300300503101c520180e050164070005150040014a0000707000c0890303c00004c01c1c5041c0c001024082d4980082800d0083e401c0104074195600244115a0240b07101c040c045002126280e00000d600c00010b603048030000704003080044007980d03001c042e540541004a0410681d6020182d07050701003110070701510030a00c0e04041103061 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 566242050 1250 566240800 566240809
    0x71101050a27170d02010b0f0a120206070b0112060c0e1503100e071d032103100909032106140118090c11060f0709030b1e0a1505010e 59
    0x20314401d078841c28240700300c80c101d02d210101944002e000d9a00c0c2c1d039030350745441d076902c6444036035216600d07002d0750801c01a03100368900004044a107030801400450300070300b44188905000c0c44060102e800c03180c200100808074503450380d510300910766500c0003540b1107180d103061300c15600243c42c5d44061000c011507400c0c172a580d030114100e0102550780c0300c684039a01c1d910709082e0340c3c0041d8070941c072142c2c1480074844901c0e070100c03614690540d40f0881401140048003890342d40e5014038204002440c0c100c04840140182d580119080603803a0f80240d0700c2074540000100300e411403074040307000ca5124941110000a070101a07440f85c086540d013040620303c0e05480000b00c070b044241e8541040b490012101200700e4840003a405010007031010000c50500c11409443e424038401204101e211340c20000e154680e51568091040d07140f907548000c428503550f110740e01c043e17000d07000301094640d0f010300800040034008803910030280100c0108082c0080c034400001d044168000c5410040701000c04c8409446 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 566243300 1250 566242050 566242067
    0xc010e21040b07030513030507080d020303010f0e0c120a0f06081609050c04090501180509190206070204021204111905030a020915090c0a09050f18040203120f071101050a 75
    0xa02c82605580c90308245400c4810b0300c6228805d001c0440610b4010050003000100e100030703551840215285400c40010590fa280400d108a9404d0084508140200303051800d016401682410a0303c0c01c104e20542400025881240c0641010f5a25001550011070501400000b045000098400250720783d024810305900e42c05420711a540f62400b00c0c11460004d0704a5001702035484040020b0f50b15075803042402580407568001c514140f1002c114105000b240380e00d0203034003e9146c5030448200350700780401900a15411303039100e03500740b088408003840030302c0703080c41703284900000a600708001080000b0b5501010200c0440c02c03480109001e162000a0031040d110340445070040556103c0500c1090b4510300a030890300034080d002404551842e960140002300c20380d882d60b122960710b80c8180214540c040d4847c5038009079103110f0341d4202c20011031494020b070014040e01d040300011040300d0300e0340d80310b40303032030701c0f0664002564000303108000201303c90041007443c0a030326190441100800a10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 566244550 1250 566243300 566243309
    0x1061a0a080414010f050411100206040f0204020706110c010c03020c03120c0702060c030c0f010506090f04030e061909050406030201140c1507031d0708030409150b0c010e2104 77
    0x6501c10228050006040d002030300c00c4140e03c0284510413400c070b5400c002e0300068404841030039001520030b03a145402d801d5107100159503401440c0795a5603403210a01e14845003000d0f03030002d80c00c010100c00b240e02030282c04185401c42030120b50b41c0c10b10300f5140e802c4541c1e031005003080520602030300c00d40c0c2c800881102d01c2480011005001c43d11002103a00161190140080d0302030b00018070007a9840001c0080c28006012100740c0300d81d44001e001450070388608071100d5520107039100000707400d9a246600c80781c109010f460080350110b030400100d4a180d1040344074901007050b0780402e229480d8448488000350074280c500f0301802d4035550000c2c00d1004000b609080c100400310350080313000e80400a10700c80d5050161000c205081c0341c10058000c00d40000449030603460803c034283c044071f0004401040321081d10046240520f843c03003035001824800d440c0213143d540100300080710701240f405009400c000200002d818412a10424540700e20504035840090351900950b075140710020585e070444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 566245800 1250 566244550 566244557
    0x15090b0a0b12030c0c01081602030d0e0307020a080304053c15070308250e1c0803100e07091202040507050d02030a0510060e2107030c0e060301061a0a 66
    0x81ea4000041c42d801e0116100c1410748400305118100c02e10029803065014400c2c0c0362110700ea262040c041007074641214180015900400000f0413411792644404114500442943d040489650005021440590003d4940e52000c502032006142c0714240307040440340700400c006120791003040c20000d0240108608641c01c03009442c01c4e4203031030307001c0c0303081c1540030040c080c6a588101c4d1601138248141652503018000c00101042040d0b540c00c06c120405040030348400201c10010307030411600c220b6001c82e08030564041241c6800103543d03c1c0c050741c01010000042d001075410401000020071004000300d0401070b07001d200b04000e40d0300321703c6803000700c0d015140426075035205401030b11305119860704010f4403440042000810b50300f56200728024020038544000703203565590f04407814144c0c15849548005149500240880c07001c0781c42501400750410768145940d01c2d22110764040442d80402920034515041205500d002e00c1288060103c817504203a170354013120050f610314021000980c062 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 566247050 1250 566245800 566245811
    0x20a0e060103020417060a11120a09020f0a0801020903060a06210602090a030f0201020705091918050d110d050a0903150b0a06020a02040b120c01050a031b0c15090b0a 73
    0x980d21a404440141085030b84401c0c865614034251541c0300d40c00c4401034052850310560200700700750b0b40100c502c0707404101c05095275503d03820000c400030060f120041740c3c09114041d030750300c140c0c886092178001818254001a110021a0141420310700300034084094a45096000e0141044807886007101040b004041e002051031480d08400900c141009103600c100d00d000c00100b0020444140041315101380e0030f40703c11320743e14801c1c8090118181d455030414181074100800420301d80c1d120b0480c8408040c03900b4410030b030a845090900032094140300004444800d031605045081040903d0391310903140031440c060140c100104030304203602000b0290542c0310514851185207811941034920000c115540a50b500d0303001a50720003902c2c5c802ca0140c0d00b480d0080381c4900c2c1c60041c00c001c804100c0c01904d280c0d40c2034001151141d0020459400b4035550351142c580750500300c00e0310ba00b2a4610388504030002c60900700540d0240f28040103c00c090f052400440008400b03240d050707008108640302144 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 566248300 1250 566247050 566247061
    0x1033030213120222470609221d0d0203030609041e050d09060e0303030108100e07120c0f14010c1209170309150c07031101051b01060905090703020a0e 66
    0x6010341c80c00941013480b54410411903da840801700c00d109603c40e1840700b145820104628206841800159000d0818807070611036080901e00c081c2115140c0950650a4520542203403c0300d010000c40410710a41000540740b074070040103c401c850445000850640c40c00000040080078020030061002e59560709201e041d0103141000350610354010700783c0b0810464210000c2c0701500c3c41c841d07100050484004000b5034200031044034165820340b80038222f5004c8a40d03421000d0881e10200740500c0c07254007000580c400440700c002e00b10038822000e20020f0b624004200c1d0094100760007006002010b05000d02480c1c0e007000662496070380c841e2160020344699034055800f40000ea112038038401c05462002e0072560040300500780c524040322015171f44800c0c841c448019004040301c040d0746501c44041440419040e00448143d60381c149052413800c8041c194035800301004143d100c0079a91a4642030141e8005809007591101d042e0008022007851500001c20f11002441000646488a0301241 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 566249550 1250 566248300 566248369
    0x301090c1706010e06190e030712081608040f1706010f12020906120f0109050123040602090a0f060f02010b190e250f021510330302131202 61
    0x11110701403c0c2d10351288811b280710180c030000c04a03180c0d520038040c0d01c5000c22421005c1250981060700100c001d0b0030001030303005502d9030f9880104140c40342d0710305010001d441c3c11101564005400e804c98150900d04855090074500241a00700c5000d60380800e00a0020750749601d43e00d006c0a4044442840d40d441b0b03100414201c014140501c2402c0c00352440040c2c1c1e1000c150030424040f84910000c00c21076496072003404a00007050400d102c1000003101140119000380c000d0808018000c10030090155038004a4100d51181d50203200820101c20b25092403940a1107514004901960803061a4144802c04a1110958028042b0364402203010170480a03031564244200c0e214071090307130a050700722400035200356100e50502005200b22010601ca81c0720881d02c02e40039907200d0200c00030742410f107400055208404001042d0180040000c241501491a00b01c0340c07150309a100160349406c03140442e0a51615074104980d2510b41081320b81c0140c881303102e5541032031403ca0345180c103401540da108 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 566250800 1250 566249550 566249557
    0xc09010e151e0304020907121e1a030c060901111e0312090f06040f0311071e050409050d030518060c04090e010b100f050d110301090c1706010e06 64
    0x1034000c1030021198900100007401002101200300000030780c01c0306406035010030710084500940110035000841e07012030150700303002d0198981010109040d41c0c41d2a101c41186030310702122107aa62600c44202da0098410451860342c1c805a0180611080060214500c0d100e020121410044c120703004621405041c401e621200c0c454012500f0404094103416550b42c00c03aa02a000c540801008620441c070001245110882c07500064141d60b501c5071560512074031205010707402d0005401e5028210681800140064004607043c3c12040b029a540704020100940002c2d0060746028001d0300441d4001800110b01c0c0c140e49404625030b540e4041c1c8602e9800070807003505040c42034005025252100c0b4001e003017070382c00c412000c0010702e465514640c00d842c0040f44060700b001078840a515043d00c14054581006c01c10f0a00754a0444101c50040844540440d140d64140010005116180300d5020304014003100303242442c3c410064030200f40d075001000c2e00003410301140d0040046a616142d095 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 566252050 1250 566250800 566250827
    0x6040209090705060408030d11030709090b0f030616030c090b181215091203010e04020f012a1101080403091512090f0c090c0e040b06250303050703060e0c0901 70
    0x6071715035544c1c0101c99a80d42003194036030120b50130301810a8a031840d64050b05d01c182929552144002d1030324040400400d10240d909800c1980c442407505551020170450380a00c6140244000c00140c1038001030444d150000b14204100300168100840c044a9041d161103000c1d1062111004500740d00140030705a21195203144c07406072250f44403001d24003800c040d04c60242ea40c159080c0325503417014146584000d0140024000440c000300e4054207014010b041c40c404103040c006c00040714540900c004035600101228ce034801c000d400e804102515442c82c0081d003080c00d0081013401c19a5015190716100e00803007140c012220352901c8024450600c104660b00a1401006001300604003010366056102098401c004000703000a156911071264081c43c400503500e020a50001208000191044070f0741c640d4082d0003840035580d1168a03950060500f1240348140d00b41600500d400303000d07503200400d034205061500d581049103901c50f80c00789502c51000f4a4981c0d5541e10000183c0307191800815 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 566253300 1250 566252050 566252059
    0x11030c07080c010b101106100515030601031d0109020f0904030f0c1b1508070c030f0c080c0607080402012007050d050a35070c091e0c05191106040209090705 69
    0xa048401e95000000c6c10002455101511142c0e44c90309103214140c1034501c212600400340003c201c40070358540c00996003000c0c0514020503c41e500084140c44d0f5850800040b805035551b002000031450402d40310418010140c0d4403140501d0540c034090810b0300c040801405100020340070004000da445e9502c250791f4003010682c2000340d00c0d619186420003103620f0040c086130455020500c89402841d032a00466410341e01d0001118128808030740c0e405034504115540c140074407a00c541c0010070301080384174090b2583e504181749031500004000121001c00c0c070241689070007980601441c00b00c0c0708d80c2607820681c0c0150460800e0701d0a0b130b1400c2289070f006015803e09020307030f051411440e071140030034641c0c295004503a01ca03c411116060b205008000f0218500d2060802541e4000e03000350081200a0310304070304640000100b04150390440a16a0000b44005001100f204052250410714405458940d0b07144034502c120603690003002e48060b204401010018141030707010058040540000b40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 566254550 1250 566253300 566253319
    0x210063006090b0f0105061204240f09030923010e1302030405010b190b030a091e080d23043206040203011b0516020301110f0d11030c07080c010b 64
    0x70120f1011406540c1100052040400085ca9107060002c0c0c1e00302d90094a00d40b070032502c0340e0355150b0010145100da1541960050754840303130030f210362007003201c0c1240301140881c5107107142c9001426214140c100ca50b50000d00091176521100b54208140742c80e03c00e00704104404500000107210040b080c03446100140000704000c10003c040d001412840f0040c1e0389143d10000c2d148200550542d54040d081000c1c1c014000182c4100e4940c110f030364210b015040000c45031140c01c503208200043c4401c03d482c12440000e050981d130660348101200d0030f01b0900310f01004d0340704d001e91198104000d480031b0b04042800090341d80b0011664520b41401000c0c04501c0c1c11030944860700c4d6110101114103a100b940380c8140e0340004128440300c0030800c3c016960b050319020300c0d1044c42d0880c10355040b050303070590750f914010b01d00421928024000700f4411000c09881e8110140c00c40d0590f2580f0b07040e421222001c0c028004010303009003c1d21600740e4051440e9803215080189103006094803090942e0092488 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 566255800 1250 566254550 566254553
    0x60608060c132706140307060807050a21020304140c04091203091403030a0f0e0d0f12090b0708040203100908030114060906041401120605010f050703030f0e030a021006300609 77
    0x110000c801c000826415900e1f010341c0c0d800d01780d0344158201c80c0000450000c00603d81c10318800c51003043c400300c10701c01c900c0341c40489006010481c0c00442e402c84812805001c003a084400811a00c1400c540c02c4909008904950707888640380e0070600d242c0310070325803501180b201708414080c0d030000342610201142d459250003d4010042c03e2100090280b003850700c65118008a40400e0419004505440c0c6859420b2148411101918448000e41c0c4840d0740f0540364002517504801580201d6090b61125120705042c0101810306640c101c1c0c0307074a44c0d40380c46170001c0040c00b0310084d241151045c00c0a00044600a4007140c424810741c00c800d5800070300011b01080703107410300e5200b00c880d1800386d0700c400c04406500d400901b1141d0600406000c140c00d20408420144182d006119440c400d00d4041051000c4210240685289244a032050342010a8074a2415410456000b0000740c26005004540c40c6c440c9014205000c6880c2504103031040e0703424481d803600b44105c0c3c2030841d40034030208020800c0303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 566257050 1250 566255800 566255819
    0xe010f051504200705030c03210c0c070b160206030108010504111012090606052707140316020a0b0106081e190902031207060608060c132706 62
    0x3161000d0220240080301c506070305191140f0345a1019040070b06264050990b00e46040380c001050848181c401080700040b00403050028107010500201141703d01c108000b1180c8071024010100e0904e904203211280b6180400144003007161502080d0a540b08051064401d6040c1801da0107074004d800000001065101540210f00c582e005031660030306031015004004908c114005040d0000d100c440c0c3c030344540c0002d80e108200031486035400290f11742c0d4480200341e03150f03c03002c81c026031280d1032442c042c1d04004800d02035a02039102c1ca050903844000056140290001034581c50403002d8030403107007500600070072040740429008043c9420640c0d542c0360042c0401000c550314072841048a00108190000da0101409500303104915aa40c0701d03000101c00007800c0002c0281e91520900c0d4041175001468001000920300070000031036031901b800009440d0410140510719031200070040c4161070550801c00b442503c003110742c041011044080540c40c0318640c02100300b1150700e000700c0091102c12 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 566258300 1250 566257050 566257061
    0x50c060a0908010606030e03030f070e04060b190827070e0907060311090607030305090a0602030a0f060f08031c0f0c090305062a070204110d05091902010906030f0e010f 74
    0x2c8580091000584441c4100c0aa884403c80b24a0961050001c103403052000b01103940e01c5000352a003000c480303e04070001000d46202d58032940041400140c1550028010341034a11500c810b03040821441c03e01d0b8031122031003514030403905080140d01c07611640f610414400707880100320402955030b00b814054041a210040d80c810030001c20318140e61250744841650a4070640c00d4002d01d01030a11485450a401800c4004d00c014140e0082141200024800e4170180d03004040200e0001807046110200c60115000394000389014144500b00f0098014004203e031b04940d10340100c0060585812405005041e50901003034010303040550107000c6650200340384080ba40220304450a03515840804508400c0e20794610340c91000d090b281ca491107420701e004110032480500001421007000c0704804031a0418025502c03031540783ca052144840b82000100803202c0c1544051111408075400a08509010701c07544061549038040d00450b441a0742c044070014518000900660b0507101c446401450b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 566259550 1250 566258300 566258309
    0x1b0b070e03190c092703020c0a1d01260601080c1e0306010611070b030c030108060c04080312060f0d1203060b070f1b21030905060306100309050c060a09 67
    0x841c40010441c04415000d0300d64806400010340740f0003604055210020b4529039040704401e542550034500c10040350103c0d000c0c07041c040d40c064000c000100d0200100c1c1e6110341e00811070807035044089402145080d08282c1100c7d000619410701100c1c810350441c0c0b0821860221210f40a60300001820b46808240c44403c0750b011519120400c0c1100c201d0319580411030032043e00743c2d2011005000840c081c0300c103000690341240807034981c03981d50480c1342c0310341d4002c4582031000b080100042091450400201e50404018000e1904080c00c0542c5c3d00d80d2400b03514080b00540c0080e001143d201e440d5050f0b00064014082c040550710401d1b0b081c1790f6081c040040c2a240040e1170120300044100c070107810b0303070b21a5920a450329040990b0b501c45207586c00300102800d00820001d9800110301c80054440c00903600040500501c1c80d030a42405040201c096004501a0804008105403955200741030400c4a5407170070006405543c03420143d144c0404010070940120000504080300d80e00041a8021074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 566260800 1250 566259550 566259553
    0x3020114090d21020a05040302030f0d051204060f0203040b060f010e010e040e0f06070906080603010203011208130b0d020c01060b0406230c070605040302030c090c04061b0b070e03 79
    0x90120300354010800400c4038900c0c1c154010381410600030344a43c08452141c3e4a02901d0a041040d11100400303d81c80702c121640442d600240c00c00c11820140408203184080d03001500003d1015107002c1c1440c0b04050001281100c080700290070805990700451031908a07000071900c80c0703018507184c00364901c02e44090b48681101001c0400c00d40c03203100e0100300a401a964010001c030000140805040f00b008000614040c2039141d01e100c250811940c6d01c101101c3d5280319003649043c1020300003041c0074151074081c1c0d00400060260781c03000d842e04020745900c201c4003a6108402e4120300d54015658020090008000030800421034498029155818290000f0130019944020120a9106030b00c03d050100e01d1107544065000341110a100c82401201c2456242042e003050503411310459801013000700300f020a0070310035801c04012508002c9001d8442000e281410305440507140a40d1140a0420441d644600d914114243c01c800503950f0068a200d05414550005040014086820380c000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 566262050 1250 566260800 566260811
    0x60c030b010e1e01030f1b170c03160c020105070525080105041502130b0d051801150e151203030103051504080a08070507021002100506190e0a061d04030201 69
    0x10303450802610fa243d08000c000266032010b0480c0150042c21341c5403401c0085ca6950000d0a800f4140342000d01e019880c00d03580c07043e003060b90402c0003088180203850300d44100000d200700006002402141020b0a0450900c00401c148520040303c035880751000051a50041c880302c1c05500e141d071090305070117282d0308810100030358603600007500b201c0d41244d0251040041102203410714103294000d10204c095242403443c2143c6170925040c17158000301504128590b6102000403240540c1460403494954000900c8804100c03401201c4501c01c60141c806030400041c0861195101800120940200039010294107202603038216141e0b0802d1206490300c2c000c45c0048820850454251842507a01041507810880c1e019000c84030200700501d50020b0000810105025a949c541800580c400c582c0c000d10102c0c0e40701c00301d1003d58034050400c0d4000c1c1202c506140103500c410308200281c4980b515600003590f906c480540242181d613200e41071041c0c010119400f5408518251445580a41c009100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 566263300 1250 566262050 566262077
    0x3e010f021504060207060b0901180f0605030a022b060b100201060509011202010918091709060a03050c04030606062703170d0b030607030b010e0303120609070c060c030b01 75
    0x310340d11182610011980d4407070000b0005030f01c82e03016005180c001c800001d10603c10801043c80f0758001c1c0c129801c0b000c895802208a44100e0041440351003400c20207014662400c8042a42c60281040c024812030000d4400080b03c2103080315140401690040c0c400d01540c641411802030460f0880c050141d5114180104200c0c014010030b0100e65014103040ca40d43e18202c10f6901441c010340040f4100400740d02c00041c85511b20b00310002200707010a000072140072500e410050340d01030b2514440d42d91030600583d40b0300e54a9030144c920308005800c000c25590b507040690f050601c0b45400041c04103203800000304016603c040d03450854454815a503240210150901a51500612000f1710f1040b10703880110418502d40083c1c100320344145008209001e5600c0001e0a194045032a140003d41c1c5843c101c00e01d60740555100b04a11098004d90f24104052004842000004208a0180124401150101e0304c0385108005541d081041001450700c12040100600216003840f80000d030b6400d25010f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 566264550 1250 566263300 566263303
    0x4060b030702060c1303020d151404020306070e0411031015030e1b01020c2e0507020f270f06151207140d09062004030b043e010f02 58
    0xa00907800e540090040783c3c0d41c0301008110340d03c0081c0140031001081c0300000162540103800181034460b000a40301e56680810800443c0c5000b5030004641e1065010302004d602c1c042521034100e0107506e0001c0800381c4080219010304402000a0000344d07002041020303068030015003900313907840803c0009510007600421002d031355000d6044580f541154150303541100720f404036a8011304043c010b03114910301030300018404d018603a40464100c003100040c001c4441c1511040c082d62452414442e003400000d8002c9180040018542d9028103009030352041c02c800d0801d0003814103819100304910f0352030300b01805000e040094503014020380700702844911708100340e8144c0310b02000100c458241c0c0d03610320b817040360b0304108040d956030301a00801c0000c0902c00280034864445009150101c2e402e010210300801121180b180d551b03103000280024400510140003244d0400e411803822440d405000d4411900340406100c0300e0310055500c11801c00302681401240300300d8600340c071624100ae4400f80140d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 566265800 1250 566264550 566264557
    0x70f0227010b0c010506091509190c0c030e01020d210615020304210302060f0a150816050a1211271e07050409050c07080c030304060506180703181e0204060b 69
    0x940d4000c024984032116424260269034ac0113406a1300319201d04807034a0508211843d000c03c000c005400c5201c4007090540108034450122001c3c802483c02d126064030003820200c4003221518042100b800c1c0003041716168004ca400b07441043e888004031088414060b507240e120344202800307801034600300e2010410b01e56a4401c855016000391829640e03581c05201f0007640107100700c00480e920041c000310018400440c5000e008508020311003c4a00c5a4138208480180d126500c039030300784a01401280c0303080c40508422944000c01071101010b030b200141c0551660400781c0b040e000340035508641c0e040c0c0c249400740074203001c2d080c42200c0b443c800c3d06142843c2040ba020000301c0e10400003044000210340c416503000240c20392807400c041c2c89644031001075200c090307000349650000c01400148003043c410b0079007080080f40c40010000e150704040e0140032006046005150792240102038446048110949a40d4043c519950400342e00c0b116115008120905034000c910b0540041030034540300d0100c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 566267050 1250 566265800 566265811
    0x81803030c030402010c0302070315391103040909080d180804140604080601030305091f0801050f040207020d0c080c09130b06060f0d0c0311070f0227010b0c01050609 73
    0x101d440d41c0d0703c60b0010740307804040c040c0407030840c850a940000400c07082005035100740303001040401d06a420441d214200f1a1521003101d90000358501100c860b02e1441c0105030000081c1015004800030071441030441c0a56408000710a04200310402040b140340014580ea4500c00710410403028802c0e259564103410720f03001001d052040200f8800005407150900e0010002440075240a46441c0200d0500100382c0c4124045400820645018507128007240d048e2980003a12420400e4510002880d580c010300c10702d4040c5c0030b101c1c3d80711100e8840342c048510450b0013400c02d1034000750500d4814a0502c041c0300d43c80d042d00032a402008249070852615000b4122070341814220f201c280c03078280f80c8030409000c41768009010031443c0d0b4148100c0cc06001550180c45001602c2081c0c218040d05440e56058541c6011504101440020b072540031320000e1590113840700c12200d40841c0d03056411440e070f10081b4000200100002861306a200e0050001090540007404151135050034003a04802c00d481 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 566268300 1250 566267050 566267071
    0x51b0f13090203131e200109050319111c1101030c17010b090103020c0a03030608120309030a08040201020f01020c03030618010501090b0c010b040c0203030a0e0309060d020706060504060608180303 86
    0x7040c00100d119481d003448104900245d0003114003196032040d1480c0812580d50160b0714082d008041c10703680280c120802008164060000403840d074802d0205014030200042540e0308490007900192902161640141e451242a0100401c41c0c101040c803529840304050004c3d06004049000300d114201055281e18808002100e9900302580d80312203801c00d585044c10036509000c0050400c0b02008003074841c9009480009400381030080c2c590821800c0700c0c69200901d010000d014014800004aa075401010301d030141c099211480100d080445003040b0b5181c541c000300d40740000d0079001c00114007400d4200d40300e00f4001d181003000c00c0c0f000350908c111360204402040801003020200f00401c01c1c2000140000b40e48071241c80082c01b121042c2c3c50740c0006a00110800600c24024131507080b802c180800118102040000050014425405080c0d0f615401155900800c02140c02000150400800038010303542c450030014409402113036605814906000001007644000c0102c90040ca040d13032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 566269550 1250 566268300 566268331
    0x9071a0702010c1505010e0a0c0c1a040c08060a020c0c1e1c0203031b010507020708250e010801090309060e030a0204020921060a060602120409051b0f13090203 70
    0x700192104039a4050540d1500101c1654110000c92403164034082d05007a9090411400d1080c0e22004941420300741c82d050060764038138180820000c2403a65200d185803220b0040340d83c0d0701d02d000144100b03158007000c81e40c0301d41d1081c001002159006401070881c1c3ea4111070780040401c003000f01c031415081d241044000d1a04c2d40025505000502c03407c0c0c4500ca00003400303030072880e43c04285540d01c12036800c0303403140c10f550700b83d2031450f42030040c2a041489031000709161802c00c4540c0c1e803030b98072050b480103152100700300c0c00f0045299040da44004010444c0d0b41010356a499105034007800f45201f0880000c1d40031100894100d020b03890794441d180020b80101901c2500c1d9081c00000d5200d6210f00354841d8003a4081d03001d8001c4100303949608943e201c06002a0304100502000313880c22a0019003d40d0840b041a411800f83ea800344d40461340344c00c0c40403449803550441c4413404062034003404031803040001c14022081c00783c00103050001a01d211016859500c0d26084c040b4081624134080c0d1800d8203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 566270800 1250 566269550 566269553
    0xc03060405072c0c0f131d0606030412030c0c062906070b070c060b130609050a060e0a05130c0308040510090e041203021306030605030105010b0c0a1514010e09071a07 73
    0x1a014141050308135200500d4800c04c00800c01013000b803031f4024200d1406070010484051f58000000790042000d039221030a6040030754488900c030000d19211002c041e503407040150440d102c1c41e40040130a800000400c043c01c020800107102180d1210071240c0c08100d40d100d00514109032003241c4810344c20580325010741d100c80c8c4089440c0c100e55441513030996203c8003105890307070f40d0304c144400c80b18580f080050317034070324104a01c410f40c0c100900d880e0380240381050800c5170790114040103034170002e115000245503450003114112141c603100c0241c40c55000380000b1003082015401401035407001c40b21641c025403009400c17070361751819014204981e62210003040c0002d03440190741c52910341606015042114850342900c1801d0b1ba41d202100003515008200942d0500f07100d00d43c003402c09001880c0c603007a10703125126643c1401501c010080c1e4600c42070710b00c2250540c0c0c031403800081c042d680103a1550351002d40c0c0c144003200381c07614503160007282c0c000a00c1850010315130307101489807103030b4900b040282d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 566272050 1250 566270800 566270821
    0xa0302060f10170c0a06020319050304081905070b060402040f4101030614010f110c09010909020907081501050d020409091202070605030103030e040c020c03060405072c 74
    0x9031000e00740b07144240340400c5401d00252403204450b4604000c0000a05440422000318010340c01107040d90020010b0a00041000301200e00001c1503091040c1c0e0707500c6628105584e88030714a01114a900e0321010803030215484070003401c0040c01121200e0440e15036008000480c451b52088500903690403c0401c02c4400500e154621044032100300c0000b12903c2e45c400d485001a642d10100d0001c00b4445200f0541c0c05116181c0a05100780c42c541f521200030f0006030400800640400521220007815180b0650410803441e05000207052000c180d6901c01125000e088540412403050403240c001454452146c401107101d185034015646a402080c1c006580c41e40c409841000c045800304000302d95414603002e1140010f100780424a00c0e450003803402418208690483d1701000010001000841d5000c0100c2943c84400c031000a004001a00d0981c54908802040c5d6094021309040000340700c0c000c2a401c0403100e0082220710141c1c2070500c01d054a21446000000700100b10000c1906401c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 566273300 1250 566272050 566272081
    0xf050f0402070f0302010615020a0c0e06150c060402090c030907051302250314030c04211e0203100e1e0705090c070c050108040302030d0c18120c080a030206 69
    0x10003400c01880e00220752242401060f0b071020580244c0e440e4242002400c1c5a0b2075180034014051000c0c18003261a030f81ca0080740f41440c821500f417120790902080c002d40e1090f448001254515141950395069203002c961114400c44d4141e105030321000005005114010807244030b2114032010b0270b00d25083c6020803080b110919240c5032841c2d401d000005071060b00c1514203080c0b50b0101e2080f000402e13140fa009051040d2120740090420042c01801610f4503c0419201a1204801c4c190040c410804914640c541d9450740130f068011056541c0303031030060791468111414001e505550090f1400c10046040ea0220b505162003a0301140d40280400544600307a015000030718140d5422a40d5000040c00814090b24180c0450400145c88420000400d8403000201700a00700415030f4646524040c0d00e0b030041c10340b40160540c42d8000f0001807803280d0404400940c02200c0c03801c103580c542d401c42a9082c41840112040c1402180c041031400000401e0301c0340d242e05500512280d5280d13122040c5090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 566274550 1250 566273300 566273329
    0x30903050c010c09031e020d110316060f12050c0d110c071508090c01050301060302031e1f1a03041202070e0a140601080f07050a0e060c07031505010f05 67
    0x5080c0800307481018280a044091007280d030f1194992421810300390552101041120091000c01c0369820068a60041c10b07182c250b044a0746c3d1540440c0f1801107814a0b104500d03c40307062401c007001207030f515013007101d20b04030382a03950b00c90241d04400b00618048030700644030045c148000340a498240105500720309250b02d0320600076828156446a150303d0700000b41c000416101d541c0010451680d031004100ba80100030000a214001d412030000c1c0c006e00c01805100700309900040007131120009543c0042001c00c43d02c500c012640341290340ca02c0c2010b904400b0009150150303500280d00715a0030310030750a04001840c110314684460350b40c2c0c54280c0e401d840500c10740c002c03800c000605d4013003580d18501c01c5609010108030781c8140540c0440c03580c001845141840804010300c07908140d400e0740d0952060302070a00d290790303200c007147c140c5403174450901440c0d019500044201001c1004a02c00341101d1041510140e6124210141000d41700d003406140c3d40e4080d8038404010a10b40f44a1409448 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 566275800 1250 566274550 566274557
    0xf1e081f0e010c0807081509070309050312041223180307080706171612020904090503071b0b0307020309010f141204120e030304141c150c05120403030903 68
    0x1e0038520384242590f0141e56404080703003002c002c0260058000c1400d0b944040c001c150360414001840008005120151148081594130071400c2e0400804004035400745c03104845210842c1f030185066021203400c800740705d0000f0068264242c1c0307002c40c2881e6000e40c4180d507242d00e00705010b08040c04002c00c82c448000740e02d07101d44c00000a03003a000f407052602504156580c0031f05801103000f120242c08001c0d100c0107105440100240665a01000d03010801080704409a91507082100003805800f00c80c40c0500380c2e00000139003804000c480ca50710014410035a401c0d490040c0e0b01d241452850004907011800b43e00704016000c0c0710340c85101d5103c10840d0311308103a00e900300d4402c550311080c2c121010b52002454001e05200038429181148c0d803140703c15240c40e00300f168142c0302094a03800744d403003401304600c010071221046590f6001c1c00118100030060090f03480b030302402c1025103200f8544804034040e00c1e08401da06040d10400803500025550001482c06446a580460081100036030030f4082 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 566277050 1250 566275800 566275811
    0x60a020304031a01080c010807020c1e100206160206010e01030b07121a0112050c0403020f12060412170609010e090a060c0c020103060b0403110d080904060f1e081f 72
    0x20309840c0030759014051800c01c83c801e903051401d0145010201e04600d41480b1201e81040400c80d030000d00424500d0040d40c0026105252480d0102c2c203c0013603d840e54004c40c44804503104590000d281442060004608008600c00c19000d81e00e95100b8010041c14000510041c00440c0c03812641c203402540c5480c113041c2605040035440c0466440c2880e02c01900c0903000400c82c503681c000095022000b00342020092410f24111b801c00724420707440001d010364401c0342c03c42010781d01d140064110254000590340146040d00d1325800f5050f040c24814041001c1b040001025040c1180c401d00c540000ba1942c4040d03403c0504140d00c1031001030a103100c0d803080314650f50000f034070750041c841200880d07200c2074071010141c40094152034494010042e0104c0c1400100f0105003000001e1202e204180e414091510203804c041420f40b0031100e146800605011b40081d05600d040200e808907610301c0001e03030a061400c05207500b00002da101e4142c49520202015a00c2040003070480e1240400c440700080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 566278300 1250 566277050 566277053
    0x5010602030f130e0c0901170114040c020115090617010b061c09021306060f050c0a02010810030c080d0f021902090c070f050114010f0303020304030b06120624040614060a02030403 79
    0x20304100444174004810000318810700c407960001900141c6107011781840c1c12940c10841013078441c0c0c0c1c01c4525244515100c80c00650501d000394403000c00d00190160749206181c41340144406044584520100e101c00e40c4020540c005041c8600e14604400030003c518184408084c025800c5440c0c1c1c404280c80d641d1890070380183e07248a0710085507078840d20045081c5280c6a0068842240e1052640a00008204001203c0b0010413240841942400c0c44089621080c40c500c0c6030800700d4000901401c4000e402184484002403400b829101c6070345c0d00d0307504107803402c002c0b80c5403090f07400d040355051100e602e42c00c014038118803216403010310314421906010003900c40342d85981d10042d003914079943d80c0803549101c06800705010701402082050205d0f062840e80d00a6880c45648000361804140d200480c046580300390300c05803034050740822921207051200a00e090100c0740b202c5200f2521074400b2882050a0a004503000c440c1e5a01e0005514071581c000c0c8101ca40c4030050b441c0c21404200700110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 566279550 1250 566278300 566278319
    0x24050a03020f0f0c060612010606050306060d0e0d110105060612132604090e06012603040302040207111021020306040e0d020f12070804140301110301141305010602030f13 75
    0x40c00c113414500810b13590400609000081c6044140090680d040460900c44540c00c2070403242c0100098909030341e54540c202030a030050407000c0b2480c80c9806601107031513105074002d504201c2102c00f0b20080003640c540008000040c82440340c0e01d0000c41d4183d00203511154121081c1d104d40e4043e140b82018001600e164900308052241500c540001c081800d0140031030900c5680346440b80300c40108050350402132403501e2804408420700c4140f03094403070ba008021081c42034800840c6d001d0300554640040d46424805038210f80703421405452410b140c400c42c1c5208030300466aa007680707140098000041c082c2c1b04065840140055006622090030401b14a010804d4101400d00c0d40e024000f0260520002400d04203540d02c0e2540c140c2e0280511008a0418021107044883c0304404070883d18400c000700c0c1c050a0314003900d00050b00088000038666a0926440e40bc0000071608420351a6003200307000c044442c00e0141c0d100507402404002604030041004041d140c0990011003082c0341d4800c200c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 566280800 1250 566279550 566279557
    0x61e0f1107090612140d020c061605030412060b0a050f0621040c08061e01140d14030910210518030a120e0604050d050a0302210124050a03020f0f 64
    0x138440144a4010000c0c450660045e040010b15a0040e240c445000b00000b59600000003c0d03030711400002420b484070004d0103502d00c405950200550340ca45030344e804920f149040f4508d00761050740c2090140321013858104040c405442c40100440505400c61080c0040e0707400c0300d031f1481100e00ca208071030b540910140d15554400c034070800c11442c403241003075025818010081c03d00203541c03081d509454100e500004800d41560b06558000c403140307080c1400142400d00f007100c003908014003a03241040c10781c40070009100c143e40a41d0084402183c0000455580c0b05c48400200710003210150345070500e00c103802040d00102464011500f103005400081d0443c1e020001d06004200700d8510b0003040d81745400f6403d030445600004e04454a441d44829450742c500b141b4210800c000000c3d440c10a034026419034400203240d11215110711301c04c002500e0103500a0203107076404516070108188030440c01d0b8460300501060360f1034905103042201c055000c1d4003c0701c02d0f945c044200b8040080c510103000d015 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 566282050 1250 566280800 566280809
    0xd05040c0f0501020a03121515020d091e140f1e0103050a09020d060b0415090b0f0328030e121005092a0a0e04030207061e0f11070906 59
    0x1698a050300c1c01c5009480752039950b0125040d5003242c00030001180e04a03007002045202c104001c6120001a008841020b029800400340d03180101c00c0c0d041d00a6000030040c644810903100c400c003050300d400040d241104075001c101880001c80c94144000d50106a00d40719561018084a440107100000500349120201402c0c090408690b0004419039141c0140f40d08181012020440902580c000c5840300303560103070180509442e0a0350101c0c0e5100e0343e21004803448001c1c142c0c140304d40c4503080c05001d0120b40b140d9a22411520707816022a1401141e1840140045007502540604400c8000074880303c03441e054040c04003003480c45c0340a8503040d034004620b62504020380f030a500321606000846101410011966000c4042e01003c52850701e0312040d20b1400001ca20484400400000c2c1c900003a034200c904407001c00420711003010b030001680820340b02c240d140c441100c2030b0751003d010901110141e000004000050010704640240140c003c25400d0a00f51941c140e00d8805000555415610 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 566283300 1250 566282050 566282063
    0xf0601060f030b01030504030f08190219030f05070905010c142e060e060d020402300a1505060306031501170c060c060f06030a12030c1b0f0b09030d0504 67
    0x803501d40c0d9458820352260725003d00b010012421b15840c000c1502c040403440e00e080c440a00041004c1010349200d40c4400c45000d40e055640b0340030f40009006a071200300c0c5c00c0004ca41851000b071004650f50044038454901559000c0c00c0034501401181d00381c960840543c0c000c601d031003018407812030a000c2d603000c03403004010b8404406122a1101d00040305c001042030030b0307882c2040c01c1c081500b1141000c1c0e00410308a505901c0840d950002900a100d1a0344030280d020410a40d4003c00301c02d10717140390a80f40c1608202d8001e6840f1751400c1c1c240d80307100c03403240d038003041005040c00716150820180da00700ba07001e01202c804000d0043c6035081184282c01081301c08405c00d24113000c80c10104048400c15100365400c0341000c06882e4410b50f601d202800314a160041e8000150b00c1c0e480410182445030307040304000c0d2070101c1c4e1960160007804425040400034404141510320b900411070540c236110342c00466a0710811058540741d07840a000340c01c1a0050104200041510032a4010709000310300941 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 566284550 1250 566283300 566283317
    0x1c0602032a16080306130f15060c242403020a090e031603051606020901080a0204060c03080a0f06140406090513170f070803061e060a110f060106 64
    0x114089070440002031030a03401d101040540504101c0040c40c41545920400352070700c036116000050825066000d000d64001d1038070040c0f034002c102d9178010030365800c1c08601d2000350f130f526414112400442c035840a0100040e41c0982407030724149918400003204e01150000d030b0045188010a2002d4180d07426a8002c00c01131410320070352a18032000d500500e03207000104071850815100c5a01d83c050102c04c010400d40300d40c00f8005040c051070484d04120b00351104c030041c07e111460708900a40281e60074500003003803000020700d204050b108403019110162503500e2920b11a40d821103c0300c400400841815072901ca000d140340096000d494041c040c0f0a0403c40103142e107101384005c075011648160706031801d09041c0003a48a00700b144140c103e4004022443d002c000c80185141403140c0d8641541c00b41d03001815600744648040510300800045440c400d041c50b0480c00740f48080210f00303001d83d2101081080d220506c2c028400da407010107018081c0c900c4000b0031200030341000004d80c41080850042c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 566285800 1250 566284550 566284591
    0xc070c080f07051e0d050703080f0309010f1e02030402040609020301080c04110a08061002010212070305092505060c010e0d03091b08120f0c0d02100e07030206091c060203 75
    0x34000d0801401007913912180b181040c035011800c2d000702d6040240142da074054007005200050000c03402031600070080725601c2004019803155540101d5880f4030a500c0c2a1000070042168024a0310305d0038150b5201021514019550380290300281040b0382c000c2d5504c0c1c0010710700c030060002d50700034183c0001400c07032020020144000d0301d8580b40d288034440c104010480510f07403c0405545c000340103407160081c100001c0e83c00d84c0240b180b802e00d203054200500070010f407141e040e00060b108400250545555220080b800d01c1c06030030310b1100c4501440c41d04014841c85c20040041e007038800b0244004251640c900743d401303041482c0b440e884000030b0b03280c86d16103041c009060001c0001c41c0442110b440f1180c41e040086484110350f1411240707018000034082445911003060703c4c40740035074005071290a05120f102958400400301035565040c00c2040b003000c2c03030b040451041d0482e0307005800c5510b054050700070003441d0303600c44850080300f00c0038010070700102c0c82c14030140d0702c00c2c014100703c0030100801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 566287050 1250 566285800 566285803
    0xd03020405031e10020703181211061c05191a01081b0306040b04240608090106060207140424030507090605030a0b07031d01020715230c070c080f 64
    0x1c584850543c881240c0004003c142c0001e10b0b000c0c078041c0840040e00c07502245070854aa01611100044981410f9400b01d10200c032140c8410500d8400c0070604403645031941400300b02d004407920a503c03140f02510861001509400599106024410110725a00c01e00b4104c070460304111085c6002000c04003c01c00256082038070260007504803445071590500080d11001030380700040520380155207030480710101d5200c0d50021a41500c0c0c00000c0d00302103060b401843c0a40580e40708070030026501e82d02203040464180304000c1a150a64007800c180360400107403482035285046403907000b035030300c0c205c4807a400e09066100a9040303c0b81d103400ca8203032450502ca0b12702200e03600110045484d0050421a03594009401d081d000c0d440091801a42e0b03580100b50000c0c10070072480d0703601180d00780400c0521101940145095849040b0b91181580b0001e800001c40311003a101d09140e02c20790a14040ca001040380c05588524900352013803902c4025030301c00241204a5004540551090724a02c110860 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 566288300 1250 566287050 566287063
    0x2210903010f0e0d18030b07020d030b040e07290c0d3e010e0102160b01090504030f110f1b0310090b06060c0f0a03020d090803070213020901030e0d0302040503 70
    0x5041c0c400e0110100c40c483c4641c0f00c42407500300509008600744180181801e040d0705e43c0013140c010242c00e00c245441c41003e501d40449030f140d5030000345080c103681c0003840c00b8400d01c43c504403d80d004044403420301a2020040d4240c0400040d00100c2c0d103107203840c60212000400d14500d00348094802184400d501078403240c034010074503c6800145101c0480920036040c20310211000742072000900f0060f0301e50500420f400007802405500000f0079040d40022400c4410013103110326094415aa0307105401d0084079800d48000b400110070703c205030082e0303202e0406541d1312030005003596207515a000c1c0140c81c2100c0d04100000c09151807c007501180b8003400700d1100c6000f80e9005020322079a0b0340d0b0310405080e0040199100c0c4002103401c1b1442041003001c008040d108008a440c52001810003039a40c8a5807088070000440a42c00800e0048002c0709aa2a046d8050080b0404240d20388000002c1e40080c668a41015965079401c02e43d84400c10140c0400e0005072001030781c071030425092506006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 566289550 1250 566288300 566288321
    0x2091609060809030a050d0b0a060305011d09070b0f0c06040c090e0f1e0c090103061a0a06020c010e1503070c05160315020703030603020a09020a020c0108090a11010221090301 77
    0xb0308810070503100008412103181080c0307803806555602d4040c19003001803008200341a0010b40e6407002103a810f40541c0014180d030314001c060140c1520b9242c180e050000105ca485010f82c00c400ca04000c46900b00c03015125030350701c0100450824401d002030f1450504101e43c01c2c0d0740140c07556000c0003d440300d0712400449100c1c1c1400f61001c4501d58810343d0b691950308400d0034000303034418520380390f103007050044240a40700101440015656801c22201402449410b001072402c40f80c0441d0092404140e01d208541e0650050711984e414800107440412a0940340c5030080344200361075400880c1e40d0000c41c4035280c0c940f121001c80315641042443e04801e03101d04040080d8030001407002c54900c5050090003519440090380c1d0b40b62607d400c8014203a40d0780000d4025036880300201ea15802071700502a480b01035405c540801440c440116440401070f1032180c0280c204c0c258203004582c221044048048060040725503400300001c46e61200b03180e8016400c048031006c1410350b450701d401c0c0903104890 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 566290800 1250 566289550 566289557
    0x10c08190e10022104090c200a03081b0d020a08040b010f05010c0b0408041e03060c030c050315150c0d11060403020d1101060515031501030908030a020a0203070209160906 75
    0x40002c9080030359540c2c00200700d25410007030220b4443d04020381104840c0a080d0a510610109012600103806000380340e03400300d068401915000c001000010b02c0d07184203501540c0d0b03500c00340c0301e20003040154508a60000070760141001019801510b0340010440c22049a4a0031250315050402c1c0400c03860603040221a030401400c1000960f0780a000b1044154100300100c42c291580e140c8031166109992205c100c9001030001207221a030380403400e13411280140004d021001c02c08000700c1c00c036071a07404807a01040050000c541c259074000b541407850300c00900856902010840c08950507000b14400c1d901640c0003034210441c60390301074803a070b50088080004240707130304140e43c020791241c86488088040000440006080000942107003004180107072010816681000c00b00ea115401201c01d104880303c1031a00105c00e500c68814003844a0b080354034a401e58a4141008019510000f401d9085100501c19000036a550481c064080c41c200302070074200403001c26018000e408254000720070b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 566292050 1250 566290800 566290819
    0x9060b0d0b0414150a032010110a0f020d15020c0c01030b21150a05041a060a030201050a0302270a120b0103060921020f06240f010c08190e 61
    0x143e490400c0366503000484d914519062011040c0030418040456101034906014000e964001402c0c5a24154070080e0a4412140c0041017140668000264507190720069011444030404607903c4110740c001648010500c1c110366465071128020150b40703240c418009680042ca60500038070411000074044802e0030f0030301244031980005640505240800c404021000c0411411b60700d0a018076030680038120355081c07850a2500200c00146000c031821140030903c0c150a43d00d40401d510010720074640101071002050a5900444064000005080a04bc0c09000304100d14459500c03014040307040100903454010800100a0212016445560926078041540c80071900650b0a581529046000415110900e16100840c000382d0305c7c0850340d24106080301340046901085603002041c1c2075040319501d0711440860941c145400e005045815003a0040d25a00e05200c940c03070069060505003220074080079204c0403600d0b8011161a20050408510b481c0f003030b90014610043c1e00d500703a80b100751 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 566293300 1250 566292050 566292071
    0xd03031e150f0e010311181806100510030c03060b0a020109020405060117010b0f040902160614070f0305150a08031e041a0306030a1b03020a0b0f091003020409060b0d0b04 75
    0xa036060117000c0600440306880440b2603684400c5000622901409800000d03843c204400b10081c080303c030b88a0359140290004a1810b0741610051011b130744000b441203001c1d004070107081d401080c2582c203207010706849001c0098540310f04006450030014980010a18288500c1048112a0020034160500c10501c203e1000102c410082c01c0c15500b11200403980c52414503e0090300f80619407140807030b607000040c2d810310300041d4001d0900b410b101c1c0000740050a2158421503040c841219410009071061000c0c1d441c00307110740c11a0341c101c4048200c070303003200c0580c0d40440c091828641000c4c0d01680001144110340d0701e00314201094a0b800c2590750f0420b400c0c54174010b9408030795422000103543c0440450915076050020120b42c40c0d02c2214140342079100c8c00c0b0a0f24026503881b042e0300c1403201c03000000d200e255090869504072210b031540d80c1740616141c1001078840014011400300369090101107540b0015100318406080c000c100151107022240000003901e000141c1140210300300f410302d44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 566294550 1250 566293300 566293319
    0x6091103011e030501022107080103050613060605100f1805010504050d0809280e041109090a0f05030319090203120904110f0304061d0c0d03031e150f 66
    0x741982c1c851102d50151400001e40c1c0001200c241d00050400d51001920881c54501058250031018240310319405a545a6505651034902440302800030b4100f6400201c3e00c400708100c91541c40c0c0f081d0400500144c6032000324a0421070f603120440411801c442500c0b015800a100b030b2400340a058034520443c3c10000028400d0085100d41030040e04080d155404100c01201a90640d50f00074084c02e000e540000083c00c3c0b5841d20741031500502c00340c02d8010900380b2560080c01d200d05e812076009048008900c047c03204407900101040c0d21030081d0016070713002882840341050154000d00c01552a418541941121044c120107103204062401d0b031700d94010384010400003806080e90350015214868980410058545405c00c0c00500100050883c4000d031403001a60285010f04020003030312154140007400303c242c600c214065540f00c1241c080e40d0345820403030010b80da8807034640482c0c414806111480203401d58044a0141911031000040c180302007101c540080c449030f203110a07075926240303240 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 566295800 1250 566294550 566294557
    0x613030e04050a0605030d0306030606080a08040e0603030403051005010915180b0a0f0605070b060105070506041707080d0506010807080106090504021b0a0b011e0303050f0703020a0c0b0c01060911 86
    0x481c0034545503000940c02000700c0e44000002c15028003620660702d03051a00a004084034041254100e00d000d0b07000c80c00c82d00000700004842d6000c0c2c4101c1c07600703060042c0401d501c280240410340c188401c200100000340c0034400403080d0001118046190b50400e020380064031200100c184038405c81107030030044000a00303010b0342214985940010b04080c13000200b03149039503a801c0100080314090001072000e80c003000600401c1d019403407009968035284011074007482044800b5080d076000c600030030b000c64a803041607040841c0b10900d0624142c466a03a100b0507401089418109903030b20b600b00250f0b0350300b050000340d0000711440d100e190756041c40005808003086000f0b160185901142000a15403009109210604104100c85000e42d02e03180c2400c0100c002d0040051407811341d00c40840060109651000341d03a495100d40b4204240416460300c0c4d40c11068095046100d02032807135000c1030803004080040d0440d190501c0d565810344042509685180d80810302c0103140040d80700101d8652020b4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 566297050 1250 566295800 566295827
    0xc061107110405060307080d021b0319020603070c0c03140c0f060316090b040314120906033c01080d050903070b0a020304080712110f01020a11030a1a0603061303 71
    0x10b0507244c041c0468130b0301e0f070281c0080005100716581d02104a800003030b030518407080000c031602800b99020505456404990b40b0603100820020503a0040c41e000b4061030307004880f80342c22000c4034211b884d422001c030b1a035030041d0f601c0001c8080c00f40c4424000d102148449a042ea90100c6814804010a080d44802008000f00f04181b102202030302c1d100303180500c0140511106661210345a0a249275220350142043d2032610444000300175075100034058a44040d0b008059500b540c2e29400c80e00c1c80052052005200e8001c030540c03080001c1402001c1ca42c0014088401c0151581040c04079460500c078602c104050000610402150369000a180d90aa65511725516201e4204100c144c0c41e600a0390080300031401035650114800030703080c0d8400d200070300400d008080c0082c8401400300d0365601d6542e803401031300301c03504200100c0d60b0420796071003544000e01250000640c40e12030704400441404040320742d0354084240502c5240800103a90021000c54001601e0111640c0113441850480701 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 566298300 1250 566297050 566297059
    0x1611091f03110402070206030a0209090f040c150c082701050702030a020d060908070b090d11030a0c03050c0d02100501150203070b13210305070809030406050c0109120c06110711 78
    0x10b115035880310b03015160940d80c00351540c1c1c0c0303074103000403107c01070740102c1e000901403005a8005400b101c2528010b600481d000407800801600301581810640c990480e0401404034130b000c0000007440c1d60700103140b0240c0030070109440409140300014a03605011001d41003010510400000d079074045040c682d01130781160100c01030b181510704180508110746d40039180c6800030401d4800c0c840c2c004c0c1e120348500c0c41c4400780e41210ba01c081c0243e421a01000f5140c00c258428001180074900804694a9560186c00c0240c1440140c851852a004000f240140180c124508880c071604880c020b090140585c800010080300445d01c0c025524001e651014109440307103004140703c024102001c920064201816105000400c00c80e20741c0201c20300840f00000b850400000c148910400190b4003481080b005580f610f840e007003044400d5000450048071955a0341642c03000114885880c407101c19098441440c0c00205040c040200e07214800c0070070f4801802c00c8000700151180c2d000e66400002261f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 566299550 1250 566298300 566298323
    0x8070503120715180302010501051c060e0f030c011a030f03070222050406060510020d140705100e010603030f090608010611160803091201110703050c031611091f03 72
    0x41500c00000c1e00f0886241c114030b0642140001c000c05105003192a0080d0000d10050346d84c1e00a00000501121a201c03181d41e5250030b850004d00075806c10406485204100e66411126000441c1144e0100608607810f03903407007480c4000c442d9902d00105030210218041c021030042c280e051501e0b4425135100900c01d580690744640c640600783d50b0b800c0a08801d20b02000140f0b02071400c10b0040c00c242c011680304072541000c1070151440000c0c80e00d01111144e603051800309603560107000c0d80c0c20011048846001e100c1c000081603110380708142507031100d60000320745035145050207080c3d04551001541007043c0c0d080c051054617000306002e8111030311071801c1c3e028010440c8000e030500c00f00f50340400c800420303510000b40d030100c00006010b08040488002c03100c15082101a405c80e955040482c0d0040020b10811020900480140c0709000d40c0d08107803031401d0780e180a10b540301d075000e4908682d48a031401d854040303401c2c1a032040d076200300c01088910004002501802e884000d51000801c80c08020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 566300800 1250 566299550 566299553
    0x306021308031620100e030f030c011a011103030601080a060e040309030314120f06040216030c031205060d0212030d0204090608060a0c12020d060e041b080705031207 73
    0x80e80100d0003018000305403030316082050003000360140440400d4807035200740000a07103202000b400e051860400100550b03101c00c2205030a4036040c01070075265616005040c254484e42105000801400358401c1c00003807004600c6a040d0380f481c1c458a01941000181e0741c0b0b00244410010441e500704d802428098201e176504003104003d8040d60704450a520008424041055001210320095034400e032038102e614038444a08a030351380145129140201c10308008584519818500d42c0c0c0c2040020f8409440e1003000011083d91030600101180000c0441403502c080c035511400c0c18501151102040c0b0040c104100000c2c5e0010980030085e20401d001e00410034400000c10840e01d0341c0c02520070a540790355840441500030560f134440d00807680198000a550416284140104290310b51660313a4100350264010009401c0028402c11199440002081e111000d2203800e1141744269007540700e200a083d8420f400ba002d41d4880c00c0d842d84528014001640c011440c0303030304003500c80712883e00c0384c295 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 566302050 1250 566300800 566300827
    0x3060e0a0c08030d0b190e0406112a06010e0402120106030c12140a0302120f0702360c04151205041103060c04031110050903010e25080601030602 64
    0x20440001c0924200c000001030600010015003011000c5000400107071920000348940d044007403c00c105841042041405680d240307500081e00301d0700079000020030052054004050340d01c000c0711001403095081d15024a0802c03503400900d0341c1d8036600030b419107500d02034044580e00d401410007032103240c201c074107405c8200b4254000e1008642280c8040d050554031030702c814a8114000d016200d07054002e4500e180c0042c006890000c003075142d8000c1c48100035940380c00c00700f50042a2b040f545c1020810606c80581d983c4407105210240c622103042030064080c42204584030b090100310b1000b0301130702c204118810000305950465000f141e00d10450b56202600b203400d40c2d101003c0640c107a00d40030520050140e10208101d078024141e04440d09031702c40c041c951900740101c0c4002010300c03200340780c440b90764140300005050f26092030801500f8201d0300300010707094590782d5250386819130004258403624050140704894908041800103106030074400303070a480307013414003020307080a400140c40d00d00c0707104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 566303300 1250 566302050 566302063
    0xa090809100528020c180c030601120c030f0e19060c02010207050a051006060908030307050f04050d0620070b0606070c0308030405010501140109080a06241205060901090c03060e 78
    0x15034500d95103102009080c581c3c010341040c0f444006100d154030041680c108a404008103011560041e14544c0e10355880404a91004100c0d604100154071075001e0350105004004100300c558902041101d0351403484400c81c1e6400001075055405030046403900400f0010040b00d841d000207021034080c4410005901a01c10014000c140b48101c098a5040c800040f4101c920051005004e1189656648046910113030030f00482c101d83e0002c101154150380280000d01800f48100055818281c0d55000601984000348044d01c4068417100c641c8600c205034010350881c08074591285041c00c8241e1a00c800c0850001c265038018800012140c0038044c1c03581c8420001c542c0500951303541d01d050f14005002e0103080c416070108150020384d281d92503000700b0b0b18205403600040182403140603074992501801040542507803160405480319011102840048041d0403110307a06034400d00b01d8546545051801001d05110342d01d4902c0800001d12401355103001c43ea00f015010400c042001c0d090b0f0f04103403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 566304550 1250 566303300 566303317
    0x15061602060c1204090e21090409081b100c200709020a11060924070e033a090e07020102160b16140342090a0908091005 53
    0x401c0180030401000c1d824024000d984d85c122040c0403408405561035035400b4100c803c0c0d0200c1e0003100a801440210742c02074900b0f02401000402c01c980c02da00c502c8680c0d4808420162203038445d003071015000108006c80074031046828801c00c480e0203c03810082070b10421a0043d08100940c0300410a491020403443c005441006800c658400342d80401600040e0000380e0703c005401108005003120801080c01910060400c10170800170303851890104241e040241540d0900405c0700c02070211b030b2030800015128030b6072448100324500d10701d2101b480d400390782c003d000b40d0034a441c03243c204000d6000d28403104468040101400340c0e100c485041e80640140d0300703070b00240c40450189a041c03101c442115802040303010b1085c88080d40810007102c40d003e40c28400722130b4440c1000410480403043d12448900c404080266010310b00c0345c00c47c64581c080f60030202049500c07807a103a8078146040c620068100c030841a0400004c40d1541da007a80500681800324842ca03004081c81031994000c80c00c5440c40d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 566305800 1250 566304550 566304553
    0x1b11041d150619080604030f022a130519150306050a0b1f0c0803090c0a180509030703090b0d06030b1602100b0f120c030313090515061602060c 63
    0xa40c4580c1c4101c40d0a4007100c03030701c0c89000d21032039150765071030401d410100792508440503085654680d1007d0f5803000c2040305450441c42100012545c9140c0c41100c54690258442803068040b1030350201700003011840c04a4440e9482c00e0140f21080d40080c01c6060f0000300d060f0b0105480b080f038442e0090031447c540c00904030a040030108500d0840582c0840b4611b201140c200304003444a006020010107010040b40c08140c1210140c0c003c2544800650352001c801003c4a9880d04031740d0106081c5003032680b120b0002000d09001e04074041450082a0780b00e005000118249299034800a09003030080c8614802d11500084c0080003800503005500a5608200c459001c0d081a035417256520f041d403488a40107002d16080b180c51000c560080ca9000c507001030421000500060402025212141c00da118510131440004505c3c0c070140007404010b08481168a156480c141d42c1905a41006001209400c014050844566030300016203030b014a40041c1c040e001d40340c074800304400703100f08003205005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 566307050 1250 566305800 566305813
    0x612180f1a0f060414060d0212012310060c03021203070e0409050c0f0306010b070b150411041d0c07060506030c3109020a0326070609031b11041d 64
    0x205031102e8a00d070203104255000c114600c00000c2c0490000001c0e6143c55000c1d4041c10160054907100480b14013400080c0c000280e0100000c02d64020340104956034400030820b00100030001241081c12070091003103007072561440a1f00c1c0e070022b40340c044010200210080110126034154070440000c1d4a00d0b10281c4100800500b60508a60380c02100881708d11400c0c2d1f41031003030000e0401003102c90423240c00300001303410008983d0300c5440c1d807500202000f0384d0035038601c0410800d90300ca00a9004003090035400c01c0e981c81c18020190004202040718094220400c410f00000c034000c1000c55401c00d810038800111520341100080c24501010b00c5250321071000180840e00104052203000e1000045034a0002984a070420700162500607001960015101c001040440c94004000c004003141c4a040c604148003103880c01c03150742144406455032541c0701d5045003010340010610b004541070380407108202c40a170740c03441010300140c1c8105000d59201c0381c02600c031040c10030b014080c1c013441c1c1054400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 566308300 1250 566307050 566307061
    0x30307110a0516090c0e1507080f1216020f030708160c090204090f150303030902030709050a02030a0b011106070f09050603011d010b0c0a06020901051b070612180f1a 73
    0x88043e04d000d50000c10345000c05100c9080d0107540c00c203001c4407019080c8503043c91451400040342e0000e07201a500860308104400c845007105005050080d2a030151a0b0141444940342e8004c0282c202400150b6000882038561024000150307184a68012106ca54409005c00a40304412088800504000c1003203c0800c66175203a8011748141c5c1d6000e1420000c92040104030001d07640b16003a14400594403800600c00b10f4804e400000403140082c0031101c0e003d50b01c0e200382046420888028600c0740d1f001c0b00348400c04e0072500030008040002d1801481d004d440340700003601c1d0080a0000c00c20b0110f841d0f1110b1134a4000c9061704020200109400d40300d42c2d54442404404410495107510b9598041c00031622586403029184480324081c004c0c107100081e50340742402903024814590510500340b150000044006451184443c1041d002e807039040e01d44032001d02503a08410b60000e5180c103101880610b0300201c200d00504507040300444403201d80c1c0d82400390901c00408010719058201408200c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 566309550 1250 566308300 566308333
    0xa0206060f030106050609060a051201030302010b01081321090b0708070501051f0306020a1b14010c050903151e041b08160e04021504060e12010e030307110a05 70
    0x521a210a580100d40d50002500b01822107005001d2290f0000c010300240300981020000703401348c0030b2242030182c98002070003020003a02c00264002c50042c0c0d141e0000c0046541d21041c102e40283c03109014400a610300e0b51600c00e07034030601400070701051095021003241c41c0b1410807440185003001e00190f80c0c0b840d40c240324643d6403100c1c40c107540540c24000401c400013080034010101d0303070000d0f141c0f040c054250b688603c00780d80f141074140e0400100c504005d200e0b070780c00000c00d03140e0361042070074441c69102c19045d0b07800d444041100c0d01c1802030621100c0d030340b518082881c0910b000303541800c0700d0558035030034581c1d440504018841c40182c46801008100b1007100300a0000c0015152900341203541d411880d03540325003a0301d0010710a050780c0d20821111041d400e800740c000388000c003628298040340302e41e400f20307810a60040d40021380c500781d22030341414203d045058600c1600024005004070400090b503078070001d8584420000704014450014005100315a00580c2c40760585070b041480c44000c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 566310800 1250 566309550 566309563
    0x2012a0501061d0610110d0314090a020f0f060d020d05010806090c131a030105040c0504060b070b01120f08120103060c080403020703030513080f011a0d08040509040809060a02 77
    0x1111103600c1c0a002283c0e10903284080004004010703914002c43e503584044c0000c6480e50350711001403041c0207140800050060140f685180c510769000682074003980c0b854004c840c0090700803065604000c02081c007580307400000003154241035038000500c04103040441c45903c50300e840342022510106030f0781c508080a801c034034100d0300c10408030b400c21303100d03882d2050f2540040c1d5126607000315403081102d212038041e00030300301e290358156500d8075604010011030f00b52202100c04448202c1180418440c0d45840e11680c009000ca80d241d0b28141951662401075002060003100061642441c002c41000440f0900444042d03000c60155214003007001c403c0300b0540d0a0000700c48280c180a0701c603e40d281300d005070302e00c6990540d0090a115107540c5007691303154400030100c0d0519a0465001c0b82581e000c000c2c0e80f004800203000000c05035203200c000c56140348109100340c4a60058411000402c88941c00d40b01644c40c00c98485546031142d107419285c038414521840e030800c001013900009150041641c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 566312050 1250 566310800 566310803
    0xa050d050c0403020103110406090e0a0204090c180b070b0f1308120103060b0612040f050c03030c0703050715020322120503181f03090204060905010f15020304180902012a 75
    0x144000d0003c40c580101f13a0040780151400541ca000e001c003d06403414200c5034102c88800d01c014500f90310354040030151040501100c0c007040030125401507440c1084a007400510302d885d80581000c1041d03603006005540038084c00c0440000760b000c2004d143c02c0407170781c080b6540c0c030404590741c0b40b80e0703101e200f0380c80341091105503113052914503c01c10604281003166540040350381c24903440d640d0344e5542012505401419590703031181e400039035041c5d10300708014840c1020110007007200c03600e50f246c001c1c54880941c00c505080c0303503103100840b000d5030000b042e2080711842c0c524500500740c2900d003070203411050341e0104c1c400d1031181c010401405801f20040190103454159003220490798130a12902044000910104148400d141d0000c40c0c40b9610982c1b44501c01080460450342c1c0e02004030650b2020780004130000e0804401300581c0c0c1003c0005103111085002560416140500920b005611500301a00c1717144c4030a280b4003160701c2120100400a148006200c0f211a0080c11600c0604007100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 566313300 1250 566312050 566312057
    0xd0b1903031d1f050d060e1906171c260108250b09010302070209070305092b080a0e100b012007030201180e040308040c0522020a050d050c04030201 65
    0xe8035a21400c10000600803c6201c00c1d0001d12009104000c450662082c802c01300c00c10398440c00480c1c1c000795100018050160036203018000c030001007403a0f08403030030340c1d11030301d00400200050400d5030004103510361a1100e03018140703c000307240f060a55680c00380e40700c00d00c0c01c50300a01611000100c4400000d0695500004807080d044644001c050b42c140e0300c0f1001e1160f10ba034090700300100340c1c002000742100d040614001d8284910b81c0e01013486881c05445800120b40c4030020848040800c2280750320460782e40912901030341c0b0700c04120702006190845841004900d00026080d51019046904040b200004680c0900d5024080c40001d19151703003861300054501c0d4900c00010488020100f241c0b0124010344a11481d40d401524140d158007010740c00071059040004081c003e61006038496400380c0c684031002d01d00380c88c3c840c030307210000e8020760302c02d008203840c0c899956000c0c141c420150382d403e60010f0384c9400402e13041d100741c000c80005040960420041210780c401c0c40020788102c9100780c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 566314550 1250 566313300 566313347
    0x504030f09050f0a030b0702070f0329150904020609030316050f0109030e0904140609030301032d0f08161109091c03021620030c04110d0b190303 64
    0x20030004269081c52185500030130b00c82c000d0000c07454507a041500035545004a070207040e914800701a81e40c1c180ea00503220241c1580e0b422190340307003004c00240910100b03841e000b8140b402c101300c0703c030342000c2c800514000d410030703c009003c54035208129825103034014201c94407160b5600081d500c0c00385141e000c4500d030044070400e0741e0340b4905004e48400c442e45503c2d110799507103480c414080d1000f0014425100c601d031028003080400c4e003d10407203004401c9a00a5952981181048001d01803511902c20040101a071005000e44030003c00c84455035000c144852104860b04080149000c2c04c0382140700b00300300c000c40d0300801404200b040310b0404299402450340d55022070080c0c82e4840c000c010010a1502c00703210001a100360700903c45c005a0000f0158001c0b255100c50130740080116449060300c800c120786d50b00c00c0c038081200c100708410484040c006810f06038043c0100e4056100040700b42a19910101c0d4035554401004043e081c20324089060b403560f81c00d0081c0307000c0d100382010300700302042c5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 566315800 1250 566314550 566314559
    0xd0501050907091a09130609082737060509010e1804140f01020409050a380a03080c061807061e0e13060602010605040207200d05010504030f09 63
    0x740a030315031042c4c055044070b00040b101c4040c0315050f0303801445000a04060760081c000a011489403410703650080d4001e548603041c0220000c1e00c200d500c030b00310312508a02c80711805035507a02c0d001c1a15005035078080c40101444451074402c40c0c480c011f4110600c0c4142d030408540f441d44007000c1c0011080c00d81e108030360b05000a00b0b11019000180720140088007040001c1e020480c02c40d0140c00700409901261441c904000341182241c1040c1c2005115640314828094804440d001340c501495081c00384512054403440304401c0182e80350208640d075042640c010710705954005050b401160482d034902d5865042a0a60b038440d0030445859620203544400304d172421500048039000e0b9800390f1246c1045000d0b100707400c104504501e51002c02c0104070035000c00d0540700d1420305015908086000300d06c481c00e012000e0b0039134180342c0040703011385d00c144007210100307100c001441c56592804400850b42c480d42408240900030b2518003078215801d144c180030405600c10728040c00c1140c15136035000015240c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 566317050 1250 566315800 566315819
    0xb03011805100b03100c170603010c120f020915030a0e0a1109220f02120c0310090201271a090603041209080f2103041709010306050d0501050907 64
    0x6071003544035075100844010300d540154042c140040403611119910b9083c00107a074001a0401c00040480500340001020071b8a4141c00a008800034001800c01d500300a000265003a0300b80032085d00c41c2d4241c040050180e044842c40d00019080a810005980284400360702c00e60b000c502051601c24203070f200420109040701c40c0c07944821030b4106541e06404000d90460041c2a5900b44074501202c800d0780c0e070b41200b1074031059209400107201da441d20f00410080500030000c101e504d8005200e0424656800320b90b60b451007a41000c0091804d41a00040780c0c00d940940e4080341c500800c54000d0345d016103504000f02201c044e200c0801c201d01b1031030b0424002d0300800129680040e824804a000206c003e41c103c0481d00291519a10b070350b079190100d918042c2441c5608449400085188010528074040008903030000741c078441c514202652020401605198000d136001d4000c5420195a0312a0f0403a80042c40001e005603075150443c2440f50003003000341e4501916119000d000600305a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 566318300 1250 566317050 566317091
    0x91302040b040e060a090e010b0103240315021b0703120201020a0c06020721030b13060b09090403030e070b09090601092306190504030506090601030818010c060e010b0301 75
    0x7501e02a08091500030b92104500d80508515440889440c0104806d007161154070b10303403108980003003084858180094112803200c000003000301300c40400c42c1c0300059070400f00e404881d400380d000074102c115010144028002d80701108005210b03000c049030441400030f0090203490040c0030480c840c3c0d242a00c1070f801c030311650a4403c041203240c1c00b03c001090320740d0b014110b0140216020706660030110340e04284801c03540c0c03001c00405c1d61482d40b041d05041180c40c1e4400704039044030400541d03050490454180c001d04119a1140d1419000035042500c203401034412070240b03004039410a61a41c0000c100c0740c0140b40c0d528010034041c0b0001c0d0044d1300c41d02da040100c5580c0281c0f0440b1800c082e4181514890116101d904540b0400049442c0510380140803118070700e5a58264895082d450004c1c248032000e407145046500140c0103001041e004000c842c0d11966050060050b1820100180da10041950000d0030407840c0c12070000d60688190800025803008a000700004001d28160100c145d0303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 566319550 1250 566318300 566318309
    0xc030304061407081620060901050709050618040c171303120b0109050112090b041a090d120b150c07030c05102003120a020a020c01140a1d0d060209130204 68
    0x505c071602004540c0c01002500c84100f02c3c80402d0890042d844060b80c5004d10076035443c801695600300700009154015142d0010301412500140743c202e9407048040400d00040003207200d15070f613031064020f890117052041802100700903c1c61191810b0b0081d07400303c80c180041900881d00024005030034a000e846a150380c5039058480e091143e00b40b10045074400e1810301030400150780c1d40040004903c11103286840b55110740b1500c88031045601c01500345500c00f42040b02c0340e44c030050149100681103d990600684114800a58140b9120000c0c0c91400807440c660352125001a1424101c0b00115489081e6400390001070f003d00d9460003400301c10110400745000240e80200c260004007001403210085405500450307040c000c0c03064881038824025220384501c20350004a03040019014890702142000c00d00703003048802d900c008010500c0c450700401c00100300c140592801c0003201c801a40b1600c15000e00520b480200b02c1c07402d44025803041003d44c0c0700f42e2140c150140c54128078000c071400d0380c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 566320800 1250 566319550 566319571
    0x7020a03150b04060e0f06030304080106081e03040e0a02030402030c0405010603020c010b090610230c070320060d1515020a110d05150c0f12060f0f0f010e03030c03030406140708 78
    0x651ba2a0400c4085500160016500d400108000100110b0900508000d044187c024040300c07180b01e01003050080d020801c0baa55038006220401c0442011030ba0141e001e004020050fa0366540c92000a01300b40401210315070192502c2c0c000b00702e0035456400740c50900301340802080408400380c100090b0240488247d41c0c080721010341f40c00700701d1080f04102518800945a02c2d030200805000b03c400790004c079030140440d400940e041060007a80e202d0030307d04100810680c103110400202103a413502c01c20041c6046561143d48021060300c04558000040110b900e00300700041c880540251504060001940c0e1404140c140c031000b4503020a94800e025404001800019001701c80b001c883c02004224520190050100200300e02c5007100510b0064041c00781da450601d4100700b001416008640014002da90a03011100692102c4003008220300e42401d0059590807240000707860352141050b900001d000210601c02007044503048031141c0000d8140912199480b05400c640d464412a00c1d494903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 566322050 1250 566320800 566320829
    0x60608030d0903182301030e0f0a0201180e060d211d060f030f0403090308030a14150f0f03071208030901050714070b040312050f0a0c0203070201021c0507020a03150b0406 75
    0x321750140c0c2a00184040c10302180801c500ca4004c3c6c1440b2440d003d0101a4106203a04401c540e4041e900002c503100140c81c50b0ac455081200c1100c0c0014010100d901a0703c41e043c6000a0040c120f5845905002d440b05e40019222464002400d007062010130b29001030300001c2120b0607103420000d5820001903071204a007035030303200004111900300181c401d400b0720143c80004404240c1d500011403040092040110705140d54a248141c0e220004214401c1d2400b14000130900d617031040c15825003420f044803c0d8030702da20b5100000e4100030007035212403841039404055104101d504405144103025410080100b607468520a80301004100e00050308036008000400000780b205c40d5480d0010b0003843c1103c2d80c8181d0000301d4080f070f541034846907407518400342081028901c40c0503c17000c0c3c1d982da101640c1404d0341130b40042d655100100c95070100b1016a0320041900340300e00140c0d04c080790000d20301c3d80c040303559007801c3c1000320404240c441041d00300241e00f592401c2c04e000d16400c413403a00840124 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 566323300 1250 566322050 566322089
    0x1404020402130f090c090608040f120e04060311130204030314070f0b0415111903020d0b03011409150c0a03020304050f1b01110a080412060608030d090318 68
    0x30741c4801c2070003484180d20000480c400a483c20200d0181c0303401d400001e0420600720000d0a080c455174401810003003400108000a1801d4800740d148640c4000d80101d080d40e12501603410452600c10550424949640001801683c111101000000323481c480110b810440642050b0311031808064045400c1c1e058000d030361004480204025401002c0e800305c448890f0b03482c44c074541d00940d0166070402e00b00210904c540c03001d00c154101043d00c001c8261401e03119111030b6511700c0e40c1415200901d40d02141c0c0c100303113000540041d08040c0008000300069904803103c190090402d4030042c44521032038100e10b0744140301c4c604050040a10088250810a1a00e4220041c0d07100500880709405201c1c9100d081070802c00902c00700c1c0b048401d142c0709501b01c400004054482103000448c0c0b1f5400640c285021500002c203c4045e030740d0608118608858905154003d0b20982e808031016100000b10500981055481540d10a100799503a14015501ca0f1a90140314403e005441c25090303007a91100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 566324550 1250 566323300 566323309
    0x150307060c06020d020f0405130b01140a110a050a031205090a080c031b0705130b13330e0702010b0f0910080102030f150a12080a1e030618140402 64
    0x101c1581c8240c401514080301d00c413940e0300342d82140c20050fa8005000c9428040c903c0d100c1a26841c5001c4a00d081042d1415900000c091a1020549401c481000110345400c217125200b4210742e185110102c51904145290250342c80042c04420750015542c0074004141c03a140c2c0c09064083c0c3c0c144c1c0d000b805124002d48665042e603021419034103051008200b941c59044000c6007c0200c3c0d020f10014194203440d0800b03100c6524101400445160310744580d2540a40c0d58081d000040307044544000746100a001032040183d80c640904580c503041c65041c1801c0000d07140c3c240c0e054928102107004143c858a205038243c2d9a1042034940c030114941e18400542080b40a159100e0f2030403161002a1307507100b0607e03003281c0c800d0b500e246d55050303080200a41c1e0030300f210580044031415502c0f0046545040160000d820308100001c02c03603030b4009051808580b00d103444128403041440f0100311582603a0b0050000d260714032404000048000b02e00314000d03a1840307040b40310546130b0a94032165855500300b1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 566325800 1250 566324550 566324567
    0x1030302120d2c06010b070206041e0302090a060816270609110c060105091303050c01020f0301090905100c0e09060411130311040603030c0f231515030706 68
    0x80c0c11499070341e00c000410300b02011040c0c2802501900f000420407682880d503050001c141c00900c28040c0030044a801602c8039030490703040300d0048500100445070400c004605151551003c0e5111000740c090040d900d0032680480200c2e85401e00715505500d43d8442003500d9500e0740300b1409201c480c1070170403420001865100743c081b400e1210025800e5150f00e20708040b22030761054004c0150001c994500606403c0202c5409031000320344a20080c9818051051140c0c0100801020480081250b8000f0785094055480203540c0300295501c0f90703100d40c007020080c0f01b801401d4513288642d4070b078ae9000703c000d440360003d41d48150780e038035081040f03203803e2110808000c1d1001d60016a5901c0b000894405a1b0241401d481b94501d030002081c55030800e450818400e8480c01e10540c07400208000081e00504019099940a050b110801c5d00c81e082c2107542c0c44110104500b491400e25107000d0a810108140d0b46039400390942c041e25454403640b2120b8040200791171505903005260030b02115000d840b91 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 566327050 1250 566325800 566325817
    0x221090d03110f090a15090f120519060f05150102060a110a11070503060408031906120b0604020c010e0105070210060e06011116140a0602010203070206070305091513020103050f0103030212 83
    0x900b507606a03071b0390307100c150892050307a9000050004241032107000c40c080f4054005100703180d41013004001e47e440c0c060311881c030310303000b2520440000508020012544c22100028029000821841c80c091014050300318196036018018006e5130001003000d101441031000a0111441c45400d1034541c01069459400c0c0040310b080500c11074000060030ba0b400c10400e40f080e441340303c800362030781002290240100220710303901c00003d092880078049150310020060340c041e04100810001e0310356101040091041d400359030f09650030010f40742c00f0004150806030041e280e40d401c80d04101d81081c4a0804c4841074041c101ca0102c80402042c59980301c4c40500f103804540d94241c54034070403030700203008910446600082c20031840d65400216071a0412141c0002d010900082d4914509104000d44500e00100b103401403580d2400070a0098a042081500f0401d641e01c040340c1d18181410500b00380c2500110481c0007070b05103c00034810f0380b1410304850407681e15030010f04182c0b0000045880c3c03500801003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 566328300 1250 566327050 566327059
    0x140316110d0c0809151902240406020a0c050109030c050c0613140f0604091a060711120309040603030804060b030703080f030910091209090608070b0c010221090d03110f09 75
    0x201c4980f50941e90300101940140740070084240c0c1c6c0c00c0000079080036804c81c1321215840c007640045181c418240002c0d82e100d50300080c0180d940716448001d43d01080c004a02a101d90320302090f2104240c0c120100c0340380030b401070044442800e0400c04002d0b01c8e01c100301c8030750a5100103210400c010a10b4600039035010070014001c200c2c0da051800402c0d9540c01640c03010b0704254668210725002e244a00e0343ca480740c1400c0c0e9030384d0316240303075502d440034902d00e0841018090300f040800c082d2001d5050094614a2000034001c1c000c55035a07080090508000b13540540d80e2910384000088146800144e4400702d82c1e00c4050b0b10301b002d400740d42c40b100079000241800ca150003181194081c4103900d01c5503241d01c074402c130030070300a000ca510002868101b030394108154203898281c0034082076034001868000c984001e09501d03600d03100c5610340750190195001281d0700344070130000d2084001030001d451380b060740c3c0a4101d4400d51030390501141940d503d05120462420100100301128000d6002000b40140180c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 566329550 1250 566328300 566328319
    0x90f040b03330702011103070c0c03140d080a020c0c1c0609031205060d0c05100c05070906061805092725120804060f140316110d0c0809 60
    0x269284070605490b2104055100e200c28100d8500401c0c035220750808043c2c4001c01100003203181c1200305100c090100b03002d20000e80c410f04208003000310623a02450380180d50a03030358030180050301e03a612813a036582030100d0130520000d50003840304e2098a00038074a50300103050040711401480342c845042100206509004039030003000c00c81034000d03084058072036990040c0b4410010701040072a04058240741c802c074807214440d004124201e48080c15108100c9660303c584514040a461004039a20001d0244c064420f000540da411548000c04031740803920b4148147c1c0440e002015002c040e4019658002840d00c00b00e0080c0448109000800500208003100c40300c160001a1900aa4528041c100c4030080c07250040701e100103808a0061207503070910400c1d2059a80c8030b007210b014a01414040001d04411001107902c2440c40700200e090000c5103a42d00e040c110840800c140c0c6001490340469080190517500c02000503101e6440ba0301caa860101c1c000250396440015400282d801b640610000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 566330800 1250 566329550 566329573
    0x2090c1b03040803070308010914070806010c0606030f0c061403070302090f030604051609020408030414210d031406060d0f02190c12081e07020a2411090f040b03 71
    0x8000034400783c400503000355150b82441c0790061074404d058008550507405c01c890102c04015508600786c101d80f40e810581d01641e56031004a8100d4184880503201d81e00f0a40000148280c040c03070346c44418000d0880b86c1409071182e800360380103020b003c421101e9000800010750440e210364060010164010070002c904000d000009182c184240d9007950107030803076130203050304d10301781340c4070b4402080c5400381507050900c0d0448460300d030300980c03007a18220f581006030090305941c0d00045890000f50a01914100327510745403299a02c0111500c5100400e113131420a0029a041c074111500c1442c0080505240c8041e00310810040e0001e4404140116020b11031031214070024116074480340a0350761100480c075042d042844010001001c0b8900b808986000d000310030001071242c462005d03d058850741c8580758200b04030b1070064000e0003c0c04042a04450300714038208030020242e103d0240005214101504007401c8a600c90703000c915601c8100c0510390307909170034180c0004554002c002d05986904001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 566332050 1250 566330800 566330803
    0x30a0609020d0c0611010f0b03030414130c050406020606010503040b0112020427030314160c0c080d05090102150708130c050907050406020609060708040204020315101107080a02090c1b 81
    0x80e034114130042442003003848442c2c4000d22948102c1d030303d00c0106000b00803c0d10082900c91040740522008141d000722545515160032001c900e55102c2038004104500400324000c1007078200d4015800140038003804600158030810a0b05e029035004102205564a49a1400a00007504604a81043e02e80d6403481c07103030300040354120810440641070101c119203454002d007102c00450030419618030401c184a1074036121030411028100714200b8020100035030400d200d03034104590201c1e08270704c01c080404451550040161010380c801381c085a00c10a0700388514a0800c0c0201c803528002007404001408219402100403107803070149510f60f14803502c4a0104203100300131030307406020a02c005000c106080d030420005034040010300c0a49014200300700e00405a40e0046c10191241e9004030100305401c006c0d0101411100d0024040c2c0150f0003041c1c009040341c440c3d240031900078040c21000258411021948502e0180d0040c130b0030002c2e5a0302c4200381c1c20745d000f01c210100d01c2010701c0c0c00c03402030610 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 566333300 1250 566332050 566332073
    0x501030302060105100c20011701090b0f0306040201230c01140412020f030a0c110409031e02210705010912021b0f1c110622090506030a0609020d 64
    0x940c040c018541c18241172084c000724500c01c803010000400108804169980103402c2c501d921160210400c08a42004884101c880150080c05001440000600794081e038080303c81c0c0321064400311000706242040546415007190b0103400f1a00130407000600400001442c03002c0100a00c0301130a00103401e1002d42101c1c101e40401016603501c005100c1400039802e00820400c20b64801090080725aa580545a0164981d00707414480654044810004603a04214038420042c20400100043d41002010400d0301c540100a07100740d401c0c200c2d0740343d1000c5080d43d0078502d50302c60380404512224151010354401f40c41034995541e5544401c002070007901a40c640c01950b07a00510420804000c141640983c8140c428880c074203e600003810703510b803040a50302454041000302140302041c00d160300000008080c01e94800300014101d84d0000d2074054002c00701d03c1404a1302d401540382c0f010300e002c07190b003501d1b483d50542c130910400000031020380051070903030b2010f00300c10708849859641441951 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 566334550 1250 566333300 566333303
    0x16020402190305092506120908030c3c1308031b0106050109030308040201080411130c1d0f06030403140304112818060f12021c0203060a0c02010b04050103 68
    0x82c0c8400901074040e404100d513110624414440c2d004142c010175500d240307034019104040c02c0c44011440241082069440300b0000c60300300c0030f0142c0e289403180480c081d42c0c3c0085044402d20b040440502106401c00310341c04a83d86042104043d003200e0729507030a02c0340e000313200d555071140c003881d10100342034009002070f089032400480040c40c808181100142540c40d245c01c40b5041240c140c80400100358425400c3d0740242d02030030404440c0d00c85083c80c01511059200480e00300418100d10718080f2400d501a03040612160b4a59014208007024800f50701042d4500c0b175409143e081c60a10b003031030305038020360300240f290900e9400001c082410002c0c60304103c0c0c0a886074070141c9408401400d003140d4807592800001d440010075484100f0b00c4400c0c00da04d0140c40c0e00300036185609200355010b80c0c000005821403140724480d8507900c81c050388500704098000ca004400e100c40c01c61381803003540584c10b40c2d241d00601030440c964548841c01c004000031070081045640715400228142c64034460140070b107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 566335800 1250 566334550 566334557
    0x6110a02010b2106040b0403030e0706051b030f0d0b060d0501180501152c150d0b0306101404021c0501060201050112030e09060f03060c030601031803051602040219 72
    0x41d0004001281030f040000c2070b10103645644102ca01c40e400b203140c80c0e01c90781c00500007400c0d4a46040440040024401c7c0401500c40c5031130102d00144c01802420100003030241144102e05031600d015100d014160842e15402020303c007182400c00c66030030001c2c080d600501102e00f0507078400c20b8441500e800303134012140c10300d40804100422860713000d00c5002d00703040c6410200c02081614001d0290141c0c83d405030442daa40344c44880d6400002000800d01c43e001094007200b05030600420455034044e0790581032541c0340c41104425410041002e904c9100b10f035030303500625440d00ea44400c2c003403200741c00258020b600b0003540b032601c2d030541c80c00c2c03540c2c0741c103104002040e606281000c2c3c00c50394182c0284110301200322060340020341c08601203c0303d801c207948072241a00d40c0ca0104090072a1010300c2d0f64503000303400401015046c036201440c8208004d90b014005a00b10f0200021400520400680011403c029461000c2518100c0c0320380b1501c094001464802c1144022003d8514034a005000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 566337050 1250 566335800 566335811
    0x30301090209040b040501060f3509010b04111e16081206061e0705030912060a0c05041d0601020c120106081203010b090d05032203030809060702031606110a0201 71
    0x2d070a02d40f08200211005640401455041107809403a1703a20b140001350401140347c0c1c0620024121a6440d810119228010b041030030120b500300c281104120b5484c07960350720f0f110400d000ca01c0c0a010724034800b500c9080c800d20301918800700d07a01200301c0000340c5030240020014099040319030003480350700c207004440c942d031149206003c040c0420f41c09000b151140c2d03c24044d00c80030b40c03100700d0342d09495246035566994404039443c1c0a411809034254955000102354010400c044010409500c180300101023000074030b034040d000352a54000e90055201d5414031440c03044c4142000a1034603040503050044070b45810300080005c040560f10220140203075101c1c40c0411000008120308012070139070190050071507041c071042c0c4403280a03426525100c1c0343c503080c050f001c5c40340074400c0741c40c000703210b41c0d498283c00c414180e000b0003a961848200e00040581000980240001ca0518003400450b8061450001070f0340d200d030380296034068142d0391941e48084030800c190480009002d07000e155000400c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 566338300 1250 566337050 566337067
    0x118031b05090a1505010c0501110f0910020304060e0f0301090b01030c140d0f0f0f0803090601030b0a05040b04020f0111010501082b020c130b040c0809060a02070b22050303010902 79
    0xc208406040f1211076424103041c0c20302640507036452010f80f04286800300310111181006030240011441e07421600c64000f42e5041c1e440800001440540015521a0035018541c84101c2e640d1040e4491480091201d0f54140d0062501305103480d185100100040f45a0400d9152030b402140c01781d10899145136451400c00248107a00e003042584803003125521460412511104034000824100402c90890040d61000300003030150703c2d03283c403500311410070389070314090340181d42e01c2c4807e0100340c40b6040301c1e10000360303d000d190140c940f0480e1b018400404039201c2e6404e211242421103907003414071014414a01d4811310912540d80280291801400d0006240b8002d003064200319814020304031070215050503058000440a5901106644181c84498404201d1006010030030f01d0681c0a420310254050041d8800d0486008000510540780a0f460300e002600c120f03c43ca4400402c8541e88500158900602c481c0e100c1400c810028500d00c880b06654a59043d94026000403003901c0d400301da10701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 566339550 1250 566338300 566338309
    0x120c02010306080c371206061202060d0e0c15030615090102031206040f0204060c05070b04050a09051302120a050f010c0e060a09080d020102090405060a140118031b05 73
    0x10020010407010300040702003140031413005d03840580309218003c00294005000c660017211034803e824203d80b04035200d5280d00d80040450783d0a00141c6581b4140308001c258001c10700462101154014460b503d40f130340000307008000e0701c031f4140507030305500075140118842d440300142c03890340d0781814208513501d1901001708510800b42101c81c2e0480c820900c0b010505980000c00c964040b80d004031810308e1503448400040260800c20400c00610f03002107000a131160b007080c40803803018403940540d814103850b00d50030304c101c4c06503100751680507909030020895000503030700641d002040d401032081c00c0c28260300464019890800381101d540d005001c20014854140a0000b0b06c07401c0300000c4c000205440001048104090300c00c034441d260010b8241d8200c0d0088022100400244081e14803039003084001030f000390030200e9079034059410000010132030b2400c00110021f0760f86405140428007d00c00c011160300d80c03030890a020b14541d00401002080320660110410042a1180d1500754107240900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 566340800 1250 566339550 566339561
    0x5090109140a09050a081602150a020c090601210603060905070314060903070b060f130b13060e0403051e030f1b03040515131a01090b1905040b0607120c020103 70
    0x10390007a10300320f002000a6000310b00d000175181c1001000e51a95441e880d1000d114000d0100258440500c00f6000c1d182d1071190081c2104001e29002d503520b0400d41401d201c0e0425040703440c07900007516114002e1001141e1070090500c000c4260bc0000d0540e2640d6512040b00c8030210305440c1907200c900708100b0001c0d03584c3d01c02003089451000d05000c0c104480c200d59a4040d29400034801d20b0354400050481d00e40021754181c000004146da130008800090880c001c00001400a01515034a0442c050340d034807600a1108803924040c5501e4650f8646e00c080710a6000700341c040342c403820b010100302c401d40700610186010f100d03142c41e9414182043e0300340e02c100c0c6846590f02d50312807000b4010040891400f18011000103189005c1514665030390501072880c0c0320618006155000d070701d100e07140b07610741600b10034141d0f40602401c0041c0e811520800181002c0c80e948070085105c218014441070406400c801072980f0017900d002d04096680e0b903100c3c1e0f19952074082e140041c4051b03004205540e81405035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 566342050 1250 566340800 566340811
    0x5090a0f02070501020c06100e06040504031b030306061404060503040b0c1b070503010c030905030a080c2101051309050d03020a020c04020408010209090c0a0f05131a0d0c080105010f180509010914 86
    0x100c007002c03440d200c07030306c84814001000180301cbc40e41d440000d81494005c144d04070700380e00d521070041000062072078050014003081c0281000110020b045070b00d40501c41e0101d03800d45013030382c903071604650350b40d0b4440441d404000c0c04031380e109000344000302c1c0385400b0091590240300070401a0a071203050400b8942125920360380c0d4010541800c11000c00b080c0040202c8e507404e406403034002c10710f55602092900c41c1c8180000d0101c03d10414064269424072542d0850507107008075211111480e9480014041e02c440b108090959000b0000e80a8981e020794010044c0104500581e007120521500280403078015900445c42c50350002400c941078580180b601d580200a5504e4901342030030003000400075040e84040e5000d011000a803e022008405041c100034111500c3d00d179009031040d0000c1e18103802c8101d41d030b0a0b0303901305065030074000d0280d040c50f4103035941a95400b00c200300e2690200e540320005d00448031201e44d4140c011800d604c90443c120701801d44641301140c1882e0503041084842c0e4010b10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 566343300 1250 566342050 566342071
    0x90708180102090a0303030c140c030414030c100f0c0503040e161d01210906140c0915031f0e0619030b01030602030405120c06060f030d0905090a0f02070501020c06 72
    0x90307080f9656603201441c2c180c0c3e402d8600040c48043c42c0300296151511550913685105d008507001d1000c40000000700f054660302c0c8559600c0d43d40b040705041da0394401d030b244a588940103440c10030b0068420240121400341342e240415840d491500c800b4210341c0140c0241c0d40f0030100c40c041283d8606408110304031624186030542c0c540c00d20704401503e1301c4a0028441c100310100420103401d035844488040000d40001e01003140050038603011000300020440324030180300701c000181c40c1038005029600340c180081c000510000021854411690006004e448903040c18104944444590305403c4090506018414445d04007442006603c05800c2d03485030000140180c14030014044040030390440b82d000740c000d622901c0c0c3d0314080f1b0401c1690035032030b1055100031030340844a030b00001e000da0044d1001c0c1c5019080750313040d4085c15282e44241c885140810b0940c4401c10560030700c044000e91140302018005041d04c1c2d40101c05050f64040c4105035401d81d0040790000c004030b03013840b10a400011145 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 566344550 1250 566343300 566343307
    0xf060807080403230d020a180b04140d0506070f0e040905030d02031003140a0c0515070f08090301060b030105150a0801090c02070b03180105012120090708180102 71
    0x300202100001003004041100031803021201101d01c108409010442200c0142c56100a584900003504070912510000780c5041c0f9822850040b0101c2034161020000400c0c603160810082000d002c80124145402c242860700620114205100c0340307003e40c0765036840d5164160041c2e0020201fa202016440c0b00d01c2c0b41200b424001a4000111244400c0441025072640e42d41407403012245103a90025210790a032401c03c050028020901c030056601ca03450902e00309841d131090007006c52469070b54402440d070070882d038004100c0000881d100301e80301342d10f010310b0328819030042070a4816a03440709013481004001448545404031803100c0c40c044a01c03805013000390f0460000c241140612035400c02e1a40e4028042120f8402d000980c0a08810200580d917400e040c139401e000c0b040401035071031042d4603050000c18401c10500c2e08901c1e2580406807440a070b441c0707031a00791104808014400c280e83c254840000240c40b0407801c1486100d5076240c400e406c2c540019403914940081c0c030307665401d07407042 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 566345800 1250 566344550 566344561
    0x1709041802040b04181b0f0314060a060e220210020703030806120604170d020f0a0f030e0c0609041506020a0b0108010e03040b0a0512091014040804030f020312070506010f0608 77
    0x17a1100c82e50240c004000f2600070722600713181d4a101c03002c0e0704016040b8040000c0442486180040f4800030803000c400c5903180d41c0e9001c0088101c4100c1d004103c1d0421782d40010405440585900e03480c241d0384000c00083c1d100307140e40002e94184030151000003581211804209150704220701039485001558411044103030382007529182c841c014001440c01102943c14005074003100191412040c07401d00843da5002c2c00d50f9800500d802402e000c03130004a2101c00350401511078083c50600d181084000c00b0b09250a404000f5542c00c0016110b4016031f807414280c5840c02503030710010060039560007410f40e0b40d0746030908800740c00301600030f14480c1e81003004214100ba0008100d408403080d81007400e4880d100c040086480d8841c0d030f0602c50b603507400c0d00c0503c44021408220b2101c03c10391030200300018200b00708002c0c06420b040b58044c3c8a460b06000c04c00210300c0c0300020a020034402010b07600301c80e03203901c071045c05130b004840250381c140d10030b900520a454503401c6910103450b0383e0800301c000e8a0300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 566347050 1250 566345800 566345831
    0x9050a14060607030f110d021e0109051011090406140a0807080d0518281e090b0402070b01060c050c0f06220b0406020f0c0901050a031709041802040b04 67
    0xb4010004c1c03c001161191401e500e02caa841c145c21111362030300792504042e0401c4001d60318008014001c8420800c2d0502441e280c205108174201d655000001d801081c40900e0188003d2000b401004c085030070400848131256030794414080a42140c0c01e821003500e00d52804c0c0183c031003880d00b002030261b01c9104207100380b40000855501c810303c14a0f22684c1d038070390700b10350b44250078105151540281040c081001d0b4541c0c2200042c1030002003504401e4a80d0740c450840b06101a03070300010040f025034030807c0c0201c1e0083d420000580901801c09403410341c03070b42e642c504040d009070300103400200002c1c809003c00100380f003465070520303044480b07030001c101398000103ca5205001d084a6200c3d4028082092403076503a0000005205041406884568a60020f034517001c10245035409401880c60246452400b8001e89040e07a4001d04110411400c640d61210300211040d0114604202440030b104c841c1c1e10781c06040d0f2800700c54078010004621764418030003510805803086104030709014151108a20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 566348300 1250 566347050 566347057
    0x1e0c0c32010311030c6408060301110408030c01060e060f04020304020f03010e010e070801270503090619020606010f053c07031403040b04080d0b0a09050a140606 71
    0x100c84501c0da46101d11918044506c030220010f280d51005003485898030140f01450312040209441012a4092805042d034102d80c501d03061101221040089143d0f814403907003500368440c070007a0000813a2a442d1207007011981082e8041082c56000180200300c541083c06010700501c01d021001c801400d00340c000990ba2050f08242c140034640c08400031307095542d101e15169220344050002c00c00d4141c41e403100340c0078049004003232507144242540040c400c6414452225403035400301040c90741c004a000280c600a0307841509841a01c818001c0c8071aa40d00c020080c02c0044a0000030f0003c00000e1710040d0602c44020880c9051103240c20390540c5a0340c014085904007101400c212106220080c21340d943d40c4a80c22503582584807400f45590411320351001420300f0b80c003035111008102d01140b906816440300b224001c000a0909010074001510a80030b031031f078100300040102c0d52055050201e104448654450141d054a07002400b05041183c89260801d0510782412011f0389484000f2501510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 566349550 1250 566348300 566348311
    0x150316030203040201180e1012080714071a03010306061508040821012303030301030f020103050a0902060c0a0b0601030209061c0908040305070806071e0c0c3201031103 74
    0x41c1c0020000f001c40e0710401c0a02c01190080d00c07660210f5451b08a044910041240d49807855603011002040d94840710a010b000d00d03600c110014507101c03d0713a171200d12130a00c2c403088091034812000007040c04040001d540c0d001500f80b0540c03a45961550600d0320950b0420340c08561858400d94003030901560080049a100341c00880030369440c00311099282142d000040220410420b50b0004101d0580b401c1c0d03070000005510503084102951503040540707071301c02844000c00484000c2650030040d402038000990001000c000012011202d07004245d03580c0c441d40602d802c036080514243c040080e840c0c020342c1c01960030700c3d04604260200010505603ca0072045000c001c00c1c0b081c210003078140030382025880a40c04a5019207595403840c04569440a900840d1420302034400011100fa01c01c0c40c01044a2590401040d281a40410203035541301d0a00301c143c9040407240703004611502da144144803c1901d00c86000c1b440c5030700302c0040a0001c2c044644a04040c24100840c068250b4901941d403c003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 566350800 1250 566349550 566349557
    0xb0f010c021302120103050c01030623030717010902010305010e060d060915020c03131505040902030612240f04030906120f090c231c0302190b0402150316 68
    0x1444140000b5a45080384403000c09664000140307503060456116805040300d11a40840b2450800003006405a41c5140103000e04209c9103400801542c07031185190000c0a40901500e0440340c03030f400301456603c0c02c1c3c1c000c03010030ba454170094000c5590500c5010b00601018101c0641750800d100095000401850090140d6407140d108500744031030b1b2075003084128411541103651b405003e00050700c0750015200403020400f600300000d040c1070918454103003074179a6555149402e0404490303074000d40000d440190450301204018142900030809115807800d4003618491020a030380780d060024400404224285c11003506200c0042d4001404400780d03206820002e0000130465413220051101c84d541c040740c14103250011041c0100045c9810560302c100301d05d040203005500d6008034082e1003e44140d003095080c801e9a1200c0e10740d1542985007803207807041c0e071185c84aa98420100d810019425946522900140800c51401030141c407034400003907058a045142c40c0700181c0510240780800d4050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 566352050 1250 566350800 566350817
    0x20729011205071e0509010b0c030706021818310206370306060201020a0c060b060409020f090f0d050c0d0c17061b0c030304260403060c120b0f01 64
    0x4102d014003068014281c800b100701c01c0210101c0384c20940da6010702c9090b000e000c02100105614240404880c2800300150040d86402c00aa0343d082c0258080c6034610402c0444002201c00d0b5602c01c0c0542d041d20028121a028500b00740d9181070600d401c218104c0e40307039000c035031080c4881e858902000c00001e4044800e40d803110000c0b0303000b0248034400e1004103001c41940d8052010341c990101c231502d400c14150f8042206030388480060303080380320f09010305002c1903011200d400000c94a81014003c10000350485062030395442c3c040e401d0360882107044403003090220f00c1d1155424048200040000c00700c90a1003900f0740c41d12055220168002081d000d481c00b10114001d100e407122280c0020030a2002e00b482d1411100b08050b100c0f0815200821900100c01419078050204c0050304d03038400d01700e8040e5155845696a081c001b0035403182482e261245602e250080c040d40c01c000d03100a6000703500100c3c0d0026443e20041480301e0341000b880829240440070103a980b116050f031950b00c242820704044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 566353300 1250 566352050 566352053
    0x109030302190218010b030411010809060f0a0209060d2a0c15091211060907060f03020313020414330d050114010f05032a0121050a0207290112 63
    0x10070021031013600101d40304401c00003c60b8407034500203510641c044c0d01007481840131100110350001c0103035407910041d03014401047c0c0d031280d80f406603900610040c00045c544400708002c035095030402040000c0d1180c1e103001040b03800009100400443d80c00241c0705506010000f40903084181c103444c081c0000039006106401109180d01451030140c000c54180140c20684a00501d10f1650708104401806203d001c01e580380400030703d010540340da0741c0311803404481c2c591040707009400c000e0844c40c03000003601089016032107034403c00032590900b170074022240c41c01183c26151483c1c0a0181d141c0303050500941881c60304172030482c2d14009070482e120f080c41c0d131060910314050000c0000260700707910000000124000000b030000115407003035065407200c908548c2d0500c42c041807402100c20010414058010079031084032030202c910310750b500e000316010310bda1050341100c0007100d5050b452940001d9001c180240114000f0499000d800030180d030020303080c1ba041d1858018480d042c846542c1140540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 566354550 1250 566353300 566353309
    0x50f0f09030714040f0615050703031508030703020f0703030e011d150c0c06090609040c020307080309010204090542061c110309150703020c010c0e0a0501090303021902 74
    0x3000d1200040c00c403621540c540d03602885000e903120b030143c0b00710310f4680358201d080054054a011110040341c41e005c9480c080380c0c29519540001421010150303240c203000c20f0707050640d00365005031a40d88001c546600480ca0042e00d80b88040002900300e41c068407003003000a501c07010304c10118000386450008080081c0814116040070301d05903030320880700107680d03110303044103006010202c0314074085400c5202c8100134070075544503544005410900400400314a82099004090552224030443e450a0f0894899540c075400030350b40109165000a402c005c1c03840540141c54200301214038184001c4500341111003004003039034000c20502e11502c4000b110088210310f400030b840b40680ba90f40c2e41c03200011410068180318139010081c2e0701d0302c80808000036454080c0d81c41103403004010560b1060b1a84070385103d25000b001d007010140c08200c90740090100f80200b0400c81c49945482018450035000c20442d07207121340249041060b048000c1010960006000070364000a54034010100103034000318 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 566355800 1250 566354550 566354557
    0x6040e0f210c030a020c0118120602090a1a030406110301060c060b1909060f0b03222102150a11090d1a0103050d120504020105030a021305041803120606050f0f 70
    0x2003034103010100c4c05024281d008600c00d0441300e4240c0e10032303c10420701c4038080c440b040e1902031004d00308003c0000134001807155004082c10b100007809810711603621a2034000380711018180d100d04201c0481400108071060041c40046901c482615080d0340c10050700900301000080301520450303d03040a200d0b1368035500c5030b011f00141028200b04443d5160303400000a0009441a0081e2003121300c40010300b908910162800f80d20348022051103842e40c14001c0c0707034441101c0403d84007000300c081116884400c60800300c40e100c0841c0c0250560508410680b42810b030300030b002e950030604041d0b0701c0c01b8004041e0101c070a1803c08550b1980094900e003440d03140800d481d010703240100d03180c070004030500c0400900c03607544140b541c0d103004100020903010010340b94107032070080c040345080c000301d88405040d0b000340c1000183c100142080382e56840004081c1c50035440610034420302e2901180c145540072040b40040501e083d81481040e14180000744943300c0c2c4213021a158202140003180341c1409000c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 566357050 1250 566355800 566355817
    0xf1203130e1302011e050f03042d0b13051504051e070f091a030703080405010f17070e120609010516030504050a140a0c030b06040e0f21 60
    0x1180d80340c000006540c00000041e0007444000d200500000e66110700018090742c005506a4400400d24800e900d03c9903c0304840c4081014000c09200c031641c00e000a0025600c01c500030a6031440b0003010300f03140a905010142090b01002e0b00c0d80c0c1d00000b05502600c041c0c1c0229000030351042400f802c3c00c00c80e007404014400e008100000c6c07402d00c03003031040004500621600307030341042c01611141320301c40c1d80e03a035080e200744142043d05001c20421069154803141d120b08000000058401c2c02800090800d0380d290000c5500b040085018800c95900520034045140f50342041c4148030f602040841e68214028000c2003000352160001c40c440d1650703076200b6040103450781150729505101c00458064030048851010f030301840320300c0010071031103409005e0180f0f0304074010300170070405616086190b4055103402c030060f200f5001d0711000200b80004440c001c40c000c02e050101ca0400034100800e5a0318a8003000c4c1950000a0020117500c0100e0050421401c210804c8820700e00d28140342d005000f020034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 566358300 1250 566357050 566357053
    0x30c04091109010906050c060718050301020c07180614040b03030702030d0c03080c121602120a0201060f2705091606050d0f0606020307082107120605011d0f12 70
    0x50000c55031200c603001e4000714100341c070384e0a14030341c40b04001c0f03440f80543c103c540030990228011400e6503000740c18000d000b4606404070495185c0b40d0f00400d09a0380b2207445240b1552107440c040084208000303140e0180b5100e60002e020b07072880c00610426036103031003114074860307a9903404208a56034104200c0c0c00045c0e002e429100b185040000c0500b08060304481940895000c60000d0702c25012981203c060810013000003d0b142c4450300040c2c13210303103806400e000350b01c41c00203000000038400380981310540c0580d00100d034150800e11b0244109006034840408030703100420a0390344042d408134400301c40e070b4040780000301d583d185242c051070f01c80302003140c0301c036110400d0011070a00c1e88070b401003565038980c1c0380500041074101e414a0459085215610058000f4043c020024010034010000e40040c207184041a420304908000180d100761803100110b0700c2144825149601805060000c01003400d00f800720000720f110118100001d01030607403081d52032049240050743c2e41c04600316200207140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 566359550 1250 566358300 566358311
    0x10b091017012703081501090e070210050c0c0c03160b07081201030f05251a0f03100f080d0c020d0204090b04150e12091017070c14010c14030c0409 65
    0x3e8030180040d01d00d00090300003030b1031600084c404080460300d00000c0765069407001e451600e000902c04e0b4245020384100c00f180100218000141d00178040d080c010403c5001d1240d0740c04504040518019810071901d009070850740200b2580191008001d00300c640544d00203a90b01024a8504140c0c03040200300c001404401001105010a84a051003030504c17610407a00840d036906c15551244411840920700a081900d05000d0b04144501c000c5071140581922410009100310010703054004031707a515486410500108101264607004038003d21890019100222040e100186600b50060707002c1d0103a03c01041400440d240d42d4000484190000005034480c1054034040d00203010b5880100b0075a8100205440d88503c085010840d00d581c010000c1e15100a902c18001c06003d0f00180400f402444445100d00c80c0200013810310800c0c8542c0c0b9006400f003a40382a1440c10703440484100168036103407a0242c0680c002c15146120004003124030381300d40e20000c06221604c81d64010203540c41c00c10 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 566360800 1250 566359550 566359601
    0xa080c010b090703090f12030b0a120b010b04150c1103150703060b1809130b0708011a040b03043504180e0a1b0512030309010b09101701 60
    0x40d88807800710703501140ea4001c2d64075102d9048041c0c650b89000909128411183c8a00264049428582c42c0040d4240410b00110000020b00c030310b22981d0200105510400d480c0d42000000c0c81068090040d4a40003402c2504007407803096201d40e100b4041e410710400d01c50b002e090004114007641880c000a0480344100007020300e480d0070841c1a90300001107400e00c0b6010030360b0f011850580388201d10a100c85c00003210a0410030441440c058000049800400e1008001c9040306200c00d20412050300d076400b4551510b094800c803002d00203510060104140420f03c0003001640840790400d81200345808986454804c19a107010709d101800c1c2010803a00b01c510002103041c018004540c0e1207100c0d14882405445c40509a8003010300c20110758000c04c0300c4000144089079903c001082000765100304640790800b140d5030117440c43e5000000da0010041050041007401030500c4490141c0e0000c0080c2090a007840076030b1103e01403e040324009124061448109601042d0a401e10104809214044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 566362050 1250 566360800 566360803
    0x80906150d02100509040b1f030f1b09030b060406030f08070c21150501050f01120209040f020c1006080d1101021c090b01080102071a060301021e09100216170a080c 72
    0x1614401d80600d0503e04490031900e031450003d80c1e105140c0c1e00d1001100382c0c2303801c1200205059818605820364600321405221410100980c00016507117542c029241103003012022940700900c624441c03800e0140070b20000d6000980703e442c0560240030b450700c4180920381508030880c4d40c0c00125000d1040059003040c603140120b05440e4030f010300f80840e940d052000446c030903601e01b401b6040c1c02a1074900c0720242ca500c1028190310b60510310f10018206a0b441000500350352608410b40c042c1a0041012103110100f8400090f14003000344041083e1840c0903401034a400f880300041c0144524208555603c0a00390115000011003440e00c860002c00001c1c104020240080e040e14005000340001c00c28590500c01c4071200c40c0c00c420b848001000720404424003000080c01140c06540070310800c40d10207001d0011f20b0b545514102c1035a212032030441403086003100644503604550144590f0030b0000704440401003030394240340d83c1e0204801c001c4c00d0a0b2521340008002003155800040d807100740da00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 566363300 1250 566362050 566362057
    0x90605071106010b03062701090915020a0903031215030b041407080a0215070b040605011410210e070915060c1a07020c0d11090106080906150d021005 66
    0xa40c807401154201044210341d02c400034020b200750500100049403040c41c082d4000b000390190768040031252081d000c240348000d070003a4004407803107440e0f0a1810422175085500080d81036018011400c01612007001801c1070b02c0b038030001c3e00707001003d40402908903e50700280d207280c4142000d82e2419a481c0b900040180c0106c0302665201000042c2d91040d110210340c3c0c03001c9070b1110008000400041c1c0801c01426450707041007591030000c000407400201071000720b81c403441c050310340080c0c02e6141045040b00085045c040c1713841010b494030b6031500180c10181c0314100103568500c0608030342654488100901c0060302035442c034401c180c800141038010350007000c03080700c2106c55a80e603260358075401c0c1e0f41901d01c08402808603098030050b2016039560b81d440e5600c0782c241d2040700c00c0d181000000c074034a81c406807002c0d281300d1103600c280d5806c2d00b000b06100d8010b0480f0b2614860782d1a141200f030341c80713090140c143c1c4c00402c0d11107001c5190b0394501e00e11852690b001800c19000080002010341980e0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 566364550 1250 566363300 566363311
    0x10e0307030c0815100b0a031407030e0f010b0a0306091e140d0c0c06030e010f0c020d020c0609010912031e0306140a060818030c19020918071215090605 67
    0x21030b103c0d060396201411340a184c02648115042844a400c001d6000f68a80000210b1010907076280c2c0c2d0000180500707000e680c02841a0b4400040002c1040701103170812070889031030425a03040c80c006845030340b92103105600700c0c0e4100f1000158824513240044040007203c8080c801e074446400c8041c1441042d40e0f50043c0d0400d40700884402c0e05d1080c0080c1d540c8144a540505550300d00001007021500030b0f0040b1006014100000070415880342d5848120f03400c4800f1280107910a030800ea5119804205180301c000c4104d641d1824080700740002400c000090089172958000007290404040c05162882c900700d204828041900302a000000d0007040f00388100001d442c88030502c0ca250742001906c00041d1400d65441c0001a075491071603401c040001d2042429600c010000c003112007000340045005c00f02079800c924503c00141c0100244c848000e025a0b0034100100b03a08031180c040003550348112014240650742040240c2012182c1d1214800c1c058161400c0444200c01c0000e140d00161044 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 566365800 1250 566364550 566364553
    0x81b1801060e09010f030f0209150a031b060801140d080c0118061409060a0b0a0b0d02180604210201050906130819050307021905130605010f050c0606010e010e0307030c08 75
    0x26a40c0c0c1030000c605031103d12020b8a2810f1500d0b240001d0308040f5809a405001d00344081c11900c041d4000c1820405198416110440b0010051041c1d50800d800d40004123b0b62514142c00d504050003060704030550148540300c0e44a500d401420088581d05031003000c002c1c20000c2080c00e41300d0f003412010701300d44001102d2080c64640c0403a444e521650026010f0701100c0c0003014a0b64034440d8800040c2000110594049103040c0c0005600c0d68040c000c11500c02d00d0600562605c00500e0002c200202010180384954003d020a0100610000280c00b40301200010010785c034040b800140c80c140300e054131658011500013600c4001d024442007880450b059902110303401c040100341d008010010350001061604200207080142c0b809004648035800300c04480500301d0b50321030000d038021803404002c1100c071351a10400c120707a41e08018001082c15403814510b03d8803070f83c10006500c64000800b52410b000403a83c2507401d903442114100d90f0080003504603001280c0300d0400340d41c400300794442c0003141d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 566366906 1106 566365800 566365819
    0x8030f060a18020c160e0a0221010909121d0906061b06090d0801050108010e070c02030d0e0306130b01030206030408070606091410081b1801060e 64
    0x165020080016513804215000c40d08101d00401c20340d9101c03209020800202d0b01000b80158480700744072005980c0c1e02d0040c1070308070810402200b98005400b00d000414843c05503403040b0500e9004420030703070710030400000850341140032017040400301c40c0d115040059424074040c540d40001005154a0402265048101c6a43d00075141a001503003c0803d001180e401400700c0c01080d4541e02d411007256051100180c40d1344c2c8103119002e4400200800250105d20a200d011b04455004003030f00d451001c003200c000d0a025000240500c00e0003040c0204542c0a8011212044140e000d860032a081c0c1c0313103408000c00b5030002002030700ca4410402a041c00555540718a0010b03280041001035090079540e0b2060720301d01c0c020a24858101d02000a0009510006406001443d81c12080d01c80786440408210300c140040d2602a085075580008a003035a0410074040500f407050f9940043c = true := by decide +kernel

theorem cover : BRFrame.Cov 566187050 566366906 := by
  have h0 := BRFrame.cov_init 566187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 566187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 566187050 ≤ n) (h2 : n < 566366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
