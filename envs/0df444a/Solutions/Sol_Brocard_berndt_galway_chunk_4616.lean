-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4616
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:11:42.840893+00:00
-- url     : https://prove2.me/submissions/10462c3b-27f3-4452-8a39-791d3180f008

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 830035971 ≤ n < 830215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 830037221 1250 830035971 830035979
    0xf0c09030a0c0e090102030106390b0a0b0307050f011b0c0b1b030f0d15032f18061c020406030b0708090f12090a120c0810021608160c 59
    0xb050602d1882442e031084200070000d82c0107072062007124169925911002c00c00c02944626100c01300c108018a990903108c0240f0030180035640d00d907010b01c01c0c80b81c030104605241440180d01039807001c1503182c4c0254030010007801261b0703461858102036403081c070704041005001811244105045480a010090803c0010480c840c142d0003c014818102c500c8405400c503040ca1070b60703a449a10341ca0f400904003400030754030104198004500c403145c85070303040d42c02c5030304c0340c4079622140c0b1411042d11218034903845107001c0c000b418207034034207040c000c0700e46004285800e403010300386403402800148124901074000c0e034404603d00103501080d030064002c01030a0b85030310700f1154860701500c01d440401e4944002541a1000182e441c1c0510882e0300941346a1404110002181d04039840d404d40c01131007021b011440740030281d41101000d01070700000b00d02500e001203c608204151280004090040200f44044940c0c021916211548660007a9458502d90254083c031908050007c140052000e4001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 830038471 1250 830037221 830037233
    0xc0813061119080a050f0912010b12010908181809010f0e06130318030f050304030b01050604030c06080403030f0c170604021e03040c05062d0906030f0c09030a 70
    0x42110032481c400c035110801c9089000210b0030b60050010010b01c01001814503985c46680605000d103e009000390500760260006211014404d400c1c009503175450844203d80c1c035040b2160540c04620f035000304400c21954882d01c286200d101100400c4002e1105840d0482e141c07086281c4080c3d00f46451303c040385c18111070307080c042e0051942c541004c6061040d05110040007141480c000c10300c0d2503003100203810541c0c0c103560099413041d482d00071031054000003000c100703801c00c4003024910034400745503a40e0452800c1800e061068102600441c0140003d000240c5085411300a640250078440c03101da45078075044010b8640c2c0c40e2030f111030300d05080800c02643d03089400c0d050f025019021100055603100c084c0803c0340103100c100789141c00f0703014844a5640603207000b941c1142c0100f840281e480d85038000300301103600003506e000c420081e0148541c800345184c2e401c1d4020345803074244c0b01e15020040c40010760900024200031042c2c80950041044000e111049580e050005000d681c0340d80150708080c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 830039721 1250 830038471 830038487
    0x40623070302070b2212020f0f01021309060609031b171605010509010f200d0915090e0c16140c03061501080103120909060909140703030f0c081306 65
    0x40322610700c2440840c16280f40002c5e508180810030000350004444d075100d454100e00140080c0c804e50140b1004031034100ea050040340c0303c0750f410400160b6240c0c100b050440320701056512019106281c144144030565014903080c046940003000c00c83d00000c41c18155440c0345540d403100d441c480b145d194504d58103c02185506034015220a2255420b07502e00040d10711384984000d41d40000c40c074503401c500142c0202d0702006030b1030300d034038aa68041e400000014907118001c01000007103441030404005000c16038507400741c0010303145406110b0501e00001d05131a044043c1c04110b0000001c92808900072510a98592554000710601c00201070161856200c17008010f41c107019004400c009116400c100341c00c0003010b074041e500d0443c103030300c1d684418075401c0d0383c990b03240d0400c54149000650400c45001e108041c0504110010780b84555141090000140c205940d0241e0000001000400e410606010343e1180a0802c148030004918124102e80b0600b212440c019140b1080420707503a620640c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 830040971 1250 830039721 830039723
    0x30306050103051315020c070e040305220312030e2103011509031203020f0d020c010c0809060f0105060f0904020f03061c050307030f0e1e0103110a0804062307030207 73
    0x410001d40e213038000076121302c20351408050710005410b0001860008983d00a10390302d42a903054600c03842e141c002410441d0f805950513400504041003200340003a01c1c08504a0000c0358084040c141d0f45035031b50340c0504010950b81282499078030302000d050b5038070a0000c20504500c888078200000c100050141c0d40750000e001c0e112545001c003410901050150401e0380540b80c10521441560340c135500110040d51012810100c0c06000703100b42264050795001510540d000c8000205070030005500040c60440000c20810703040e4400c030103116041d1030f118900ea040d140d09849042d621402d00b010340b0428420b0188080c0c100d4400140d06040580d40c07006180601c130100d1f4151059802d0444840c00a954602c0142981d0410800d50300003070b0080d09010114a054180390100c484400002982e00400b20310003a01d016141000148547c5d241c80340e2201c11100c4080b050900c0300c0410020501140100010561070340c0c3c00184542000900c2c001c1c0704980c07a45440740881c545010300901030f40000d94 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 830042221 1250 830040971 830040977
    0x816030c05010e0a0905070302040308120403080c21060a1211090603030c030a030f0f0c02010507080a1a01120e0f07060f0309201203030c0c0c030d1b0318030303060501 74
    0x440410740c1e61168220405840c00240042d000600700008800140030113081700d000d01da07003000700100041c19080603007c4c00e480800003411616060401400502e002003d070702c0000c10801044040341c001c28140b00d07100e116001e003c000360b07a0380d801080501e1001e41001100440c00d0300000e081001e8107200c40e1000e1019940100c8945071681403654902403083c25a42d160024010070f10403610176441318000004405020500b940403900c1d5500b250441c0781e40b400182d440c0c00c10044c886420810f0950815584d0134101320040b0000350b03444c15111031243d0581041040034030314280750119000105c0c00900e60b41a14203a0881214466a900040c070030080403070081000070491f9402442280002a000311460794000c2000300418151401019142d501c0310342d9a6a025a6110801c0914402d803c001b602139520004008268076000703c2e0300459119900c000d0302d445500798000c0101d1580c0800040881c9144102c2c5000d5500c5003840400c0c01005001450000c141030b810303004502218401c1e2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 830043471 1250 830042221 830042243
    0x312020a061b021b061b0c0607030801051009140609060f0301240306030b06040509010912080a06050405040f02060f0408010c081b090d030e01210203061503010e0a15081603 76
    0x20740c1d610410940f40d840d070790b800a000d01c1a0032103010b02880b06606802c1c05000d0f180340391101f42c00a08690400740d02a030004c0c0c0d00e800107110320305040d0390a0095a0240c00c1c420300352842c00c0c0c403c0340b8502c05140103600030300000c50105140d4640708140c03070304049102c0e6499241e40e125400685021800c0038031600c1040383c070f49440ba0030f0703000388640c40c1a01d07000600340125a0300d040c180406000081d007201013566036a11007002007414220610541402c50b550900035007409480d2800f95003040e04414403907450b290038800010b009240e10098294107075162078881210801400d51070003603a000000030f50801e52849100c540c0904c0d1148151181c038101051f00e40d002c2286440c030f00450b1080381d040710320340f022400864020032001d00e21140c14034000c401e106500d120b40c41a89002080281110f0300481400264600351405039125000c1030102c2e4115031414500c000c2003203015001a40d0b682d5500407038121a0510060103001e48a480c04032161000d4508120045c01110701c02920f40040c44 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 830044721 1250 830043471 830043493
    0xc181503050a0c061e03230910050603011a040b18010308070308161b020301150602010e01110c0714041103010608070201050f10090f020c0f1005010e010f0312020a061b02 75
    0x6403899001d5140e241700000030044c03404c1c00507030007401500003650311140300c1e000700c00450154088a074030400d04000502040c03408000058255400074100701d101740d051852444c4001c0b9180d404a03000941180c0100307143e914200850031800c110740404a880d05120000300620403200014126148291713074400c4590303201030004e60700c50350403071030000003400c040c11000c1112a01030b40c1443c0c85000600004407141c0b1a00d5008640c15240d0102026035160071400744280340a22442a040c0a0449850b02d0708800d1041562122214000c480441d42200c000c2c00e075507296984007e800003881c0c0b00301ca40d0ba5841e084051700000045032048019820a400170f912080e81c8501c29000d2003414070459115818020f0f1a000307010021490003000350301b88203c05a0040400003a4103181c0351030701171718051104003107990070341e54160800181c4900c120010042c424514a90701c084903002040303483e001c0c82c0190100d041c00c1e00c2c040068905810424080445424540070725403000094007107905120355 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 830045971 1250 830044721 830044727
    0x19031223070605041a090c130c08010608090a06091a0907180e0c04090819050c0a06090203010e070609090605010305010b0909090f06070201091703040c181503050a0c06 74
    0xe5020100050a06011500000304075800c515002481580c02c1072108540e41c145002d840c01c100d420a00680c80b0f4050074801c0e06181d95a980e190388924400c1c044c401d50303180d007c0c281700010300c01e40040040c010000740c034001c400d00c403001160790302c0352050141180d2401c14201070540800644c0e02140c100000c295800c00c002204c008855542043c8840310440031100c10080208881c602d8150186003860300380359407644260b0000a118162403511100342c1012031803800009100e5009000042085245075800003400000305540604040365a540c1480404d0261202c81c2d04800107100e03c40c00811050303000a40f5a0595408480400c290f540c2c0310011420b9400030f2090a0748040b0802c81e2109504200e005154015014000c03500340c94001d40c00e42e40b038030074120340841c0146d40d920b001c0d500b089040104581c1400c407580d003c500f14105900d90289505a903c070781e0717114840e00c01d602140d80c406034121000c025464076404070b8150390f03400d10031744a1084030760803140500d034035102048040c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 830047221 1250 830045971 830046017
    0x81903050a0c0f03021614030304111206010b13150e01030c0f091712070308040506060f090a0c180605451c0302010b0405250806190312 60
    0xb20355034400d0f101c80c94454040d0029403010440000103091881014080b9042858040500e50a5401950303645054180f442400d0724030340499101c0c503014140302102c0140010100d056450560700a9658103104000410990f01980a41d0806070f0b035a82600002d03401240384200301c40c0a0300c040c0503101e950716003200c0850b60341c003a43c001318089000c280901d180c9502680c0300c0c0424442201c09001c098080c589a60308010700c1140002c1d441d9080000f081401e00003650040001e4407856481c48216002030001000246002c40702c0ea5101540003060780b00341c403000d240c2e14058511650b40f44c1c5035080180076a10a030414034500b9201000000c20005046480e13541003170540500f01e08100840e88144240700d40050b4581c0488004402100c2c040500d041680040c42600001605601d101c20700c0103440d07000f0544840c4a0601580c0302c1ca4026415800c0c10225843ca00404203075a102d0000792440c403142d055100b038000383c0e18040100001d02c1c460301407050440c2c8134681d40d90412501e150750303c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 830048471 1250 830047221 830047241
    0x10506010f0201061d060307090203040818150f07052503230d050f04091401080c150901050706060f03030903051c0f030e031216031a0922081903050a 66
    0x140f90b1245007800c00710f170040382508508003c0c142d440865a07403560b103050b40c2003a00c040d240364a000071281c01d0302119809074043c608003900d400c0f102c14101c81440d0164000d207580c540010600040c4401040750500c0b0261000503c901c1d07aa01d5845015414680c8840b07600044070300002c40d07070310221840001500000d00f12141030041c580e0030700c1250f04a560b070f0064400c45112240900003c04c0c40e01c641d00810045610301009402a5031401c00c18504d002600d1100f9401018501981038a0047d4001211074002c001c0c213055607200320341c0c034001c00200019400480000300140e000b20416903c640a0003c0b280034008860300c44003011241000c1c600e10700d803031101003010b25038440d8400380070ba08183c4003c41e4690030307242417110302c0c40c1150b01094120f0b00010f810400340320619001b50144200c100242000b10340301c0151700e4400126045800140040000c5140d081040070160a011760300e011031030740810103a4a4000d403140f0004030200e0381c01c08001190a140c0050850034561141451340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 830049721 1250 830048471 830048489
    0x3010c02030c1b030a05010c0c110616061a03010504050a052a131b200a0825151a0108070c030f020c121b0a080a11010e0909010506010f020106 63
    0x34000c40f10001c108a440001458240c05135440300004110203214218203102651a102c4100d01c061034415417040c50010240e20801082c0520000b02202c0049001c0340307544071000142102140c00d80c0c4a0351241c0d054002e500d582041c00308001c102c0c01041ca156038500c01c0045036041901c1d1a500c1030711442030600c4581c000300b01201e110041ca00b44428444501e0003441c00160380c2183d80f000300042e00c034640a400411014004160400c1d001817040312841407660281446c0200c503903840303030a44640703014820320300d4074903e811194034184501c0d001465841120030a5100b00743c040c04c4085d10751529800010038420302c10450b0341d4050300000d84142210b03540c903041106555019501e40717919041c058114410b4040c461081e480d0300790075010070400c600c002c0c0403030604100c0c000c80c081d040540341ca001d10000340b010001842c000030707400e5401e540840c071007690441010049590340f00e01da4901d684104400c041c010f4a28040d8082805080c0a990300d0300443c44410050f403e035a401d01c42c5040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 830050971 1250 830049721 830049733
    0xe1903121b0503150604092301080d140c0f15041109010605032a1303050613080910051315020c010309021c02060f13050a21030e0f0405040602040503010c02030c 71
    0x21004984c15460300d04c1900511050400c0d4440c4141c4044600800640030702c821500180c1100504c00081c090040c0140001840c02c003401e620000c0c00d441d84e46121110505020891202e8004240b2540d02c1480c8040308035010001104107440c801c0c1d4040d10180ea08210850b4100700c00e041280d101810381c0d0442c1c95407031568403240060b1009062010310310a045003070130204081304101c50010446250b4000201c00313100d095003403103070420700050b01d604142c0c000e0801c00400207030603005589802208840c9007005510002094403a0f208007060401c20000550000c920540d480380c2e2a24008015030803903c80c0c1d9102c0740150708560711158082c0d400780c0101480301002d4800e00f03560680d43d1020302540d0825102400201c019001400d60b031209200c803000a1003d0300b000b01c0940c00400240c045409601040040d2051020070300030043c0c10060041b12400b050745514080c4096400e010f08104154501070409500942090141c0c6100b0f50030842c5441802d0b10000990309030f406521f003d005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 830052221 1250 830050971 830050981
    0x41a1c060b0304110d02030604080c0706020c0d171207021b03010c0c1101050405030a060c170c03010605180d03110c040b0f09040221070e0106090602100e1903121b0503 74
    0x141580301c1c80816500c08000c2c00d4417001a10180040c0d8000d502c15200c40c1d45a48550f4170003410a01c00c1e4100504540c000308040c1c0081c0d8a00750301c0014030750003c400c446c00910148040200d07104046502440e079480304280319240d40d0000e0110720200d1086107a034080102c5000705820b0301c822118001c00149070740719460225500040c3e002007144141080c6140c1070782c070400300e428105028011b0ba12039941f000020212500074840800c50103840074065014681105810024041070040c001004030200350141c1d10f0030080f14004030000d006001d107071044058500200300d043d14032109856400f501e131440c0000d062501440944000040c501c18042100c2010710282c5c01006000307a03440b4002040b0b89400342646e0564100c541e00c014040c282c3c1c0c0341403801d07100c20458103902c0501000050b4604100d0f0395400b06424003040040c50005c107440444545082c03511520121991002c4907a5055008068000c14040180c1d2403620060040040442190480e440b015201402017401000000c1e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 830053471 1250 830052221 830052233
    0x60603150a05030706050408060907051c0516080109030e040e0c04090f0c03150b0603221103240109020c060705030403030905030f0a0e0d03020c060d02041a1c060b0304 74
    0x9440000301601c06450140d854000074134040c0c280c0c0c003142c0800c80015060090780000d01005a010800c04010b040302032810010900c61140484c0c41c0c50000e4608021004001c000e02c1001a120b68005048203003070b0305c9203c1d2038001e144080040340802c104401c10350540c00c15008108030542100094030300e4006200610001c1c04c182078040750700750100b03028840020070744084003020310300a5807203c03101d410844100c800ca421120314984903103400d2080000704105514404801200650f5444000001c0c0c0b61015200300344262007941402a005e4407640980c94001c522520a14003c10482d50390ba1041600103d1154902d140c0050b0031107400100c0d181c1c0240001c581140c82441c0004803034100380c0300e040c2160040160641c00010021340043c51136804101801c001c3d0f81107482e0708001d04070b62341c040d680d0188002001d000790b201140c20300c3c10070456816640102911002c0d45980d04418002103500c2e1b0281101180745079400c500c0440c02034840c42a0811398400b500c11324596101e5440300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 830054721 1250 830053471 830053501
    0x151f03060b0306070e012c0a1707090207020603010b0a05070f060c17040f060b0105040f0f0302150306090613021c0c140f040522022a011e05090a1202150c03060603 72
    0x544400e200e056a0400c040c0c0311810382100801004071060848905500c44500741881035200199a3340140722045c05a80ca200480c1d0442d60615102a9185012072050360f0704d0003000c3d005000b00e100b51904005210f0581c01c01c5030750410790707a920603c0340e405e4a44400ba024054070054000b641100740311001610581c40540c0410701410203d0400355101c01655042c2d0240d0000600480310400820460400090010b001c40c90010001c1c1140b402c0c1001c150a140e0083c4414031810781042030b090191669030450700b40d14000311440030f49455281330000600f0b145100c0d81c0014241c1394a801030351800c10140c40080ca030201c0ca041c44d1a1601003080031101e9800f12a0f0001d01e44051100c184c00424801440c404150f4214080c050700c403031064850761401411201c07416418503d0600726011143c1c0075910f503680308800019a52110402185072100c6039000502000710180409405600001c54000c003801525461850369a03412142166000941e038a0707030024020f10109901c181ca010b02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 830055971 1250 830054721 830054777
    0x60c1209010c050601080d030c08010302011d15070c150c0c06030506030312010303031a01050903030f070f0b040b09011a0901061b0503130302180405151f03060b0306070e01 76
    0x30b071030b09508644580f4101a0281e100500584c81000300c3c038807680d003500079400d10080d1400c00443ca58503540010f400c0007450795084002a5806514501070f81c2c40c002034880e50724640201517211102450003418410044c01044e6280c0c240796960349449100f0a845840590710840807408146490416000381c00b01514440d03041c0418410021503001d003ca00d280210b00070303500403c0040c005800c0c50700b02180441c031141005001c201c503902d03d450000403990008096416a5552912400e0515103a03c00700c0780180710013084410700040c8840c0c1002d060141c86010020003191328112600c4100340300b091001c42d04042e407000100451030040f4130034903075040c0c00d140e40000d030301150781e0301c6080d0f60110740700d0035000c140910705200b5802c200094140001c50700c81c0d4000a414103480d4940d80d002540700e103003402d40032880012841c10035281c211084080500c0801500d079106c1c038101c005040440c0426000744150360000758005d2140091b1480034006841e41c01c2504203002801c0021508440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 830057221 1250 830055971 830055977
    0x10f05060c070902030c27100f12060b13090501030506072d030c0f02030315060901050c0d0f0e090f06040509160305070e01082e09022d060c120901 65
    0x200241c0100f10703000452003954024082541d5015101d00541c16699440d428062180e00d20811040780c1c40344154014580c91608101020400841040318140104080d03100c40758246a0009044500440034100c030640318030141d2807058370b821034441111402d11014202d03034480000300d0442400742c40c0c4c46c040a0751100d14201149101d81c000c50760705210145010020f0b036508249000f06500402103da4440d562028502d541001f905600200d40d18600b070714130a10300001c00c440140e01a40444000300e045809540c0c0c003a580c1d407000b904000b040d00108010800941c1888034600d85071414900c10f2414104910454546400340001404020a5207882e4410903518501c2038001070804402113208200400e0000d0401c501c0480e03103d0180d001003010b0b40804a81045409000316014141c0192002c00c00106980c4059201600031500042d42002e1055540f00e100d00d217904000b40c00101031a415000c60442c40103104213813040703031180c1141c3e4004094400048410400506402c2da0500d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 830058471 1250 830057221 830057233
    0x90109050d0b01090615081605120106110c100c060f06080106080604021c0b010b0306031e03030603120a20070504051609061b030f12020a0e0117010f05060c 69
    0x60081011141d8851007030300c081d5100c4004020b43c05050043e00d010340380e540081407240551030000342c0900d20207464080e10f0701d18501316242144c4100d00742d852080d58115503c885503034400020340020910000b406450040621110307280c20555082c81d044d111942d2101c400007103545590f8018075900c05607811140d02d4580000b0180c00900440014000400140565082a10401500b030701c1002101085541c440120004a000068428110381707801c0e88480da6503581200090402c054821007a0140858500c4802c4a160000246100350020380482d20310068044011030ba0380500c580140020b80c00703038980d08010000461404a080400040b580c515444000007010780d24229007221000e622101e50100070356104207940004d03c1c403400c2038208000c49085000c12070031000c2000d420301000300b40340303c1100d20950f110a0f00d4411040d0440d22492142c40041038200d440410500088050b90f500c200342240400030b50488000e8051542541d10381014840140c021080b04845070240c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 830059721 1250 830058471 830058479
    0x10e100501052a10062d061202070209100602160e180a1502090114031003020d030507060c0f1101060f031e0f110a061b082b05040308180a08090109 65
    0x30800300c1d51100c81a14003040f05410075541c940c1c3e0010461846408911b40340810b0841124511114152010361500d00790400d20001c00002901c1281c0f0025004908070041080c2ca6143d1078880058030701985c20b03940d50400e6034041801d8600140546106061000045040000041c0d081d0107002e08010a44d0704140c16134850f00b0380c01c0550b07141500990f4001582300c0300c0c0e43e4400c2e10061360b281e06103089425410030a0303080004464500000f40500c42c00c0030808107050003503040d92107040c0d00c86803e124100d001c0b100200b1001c8244012000b042490b0070840c410241809150282c5602410349500b00b4a15221003000040d80b221003103110424803924408a02000101e8080c503000d0000030500917103c00502c0109030156201c01d0420854100e41070000c0840c0d803404070303038035085101203480d550020000725080500880030458a496a4080310001489401040c0308900940360300c00c3c2c039610030081e04000a001d201d60300d6a500044400c3c800034540e038010700a01c1c007061620651035915 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 830060971 1250 830059721 830059723
    0x21c1101060e070f020a080a03090305090d0c080c0105090d020607020613090219030501030201082e0311100809030717040e09010207060f111b030f12010e100501052a 73
    0x8103801c41a1800a601c040050891308000002003c21080c801054040d0741030700d0781c0c3c0042c02150015800c160311a00c1c03d00070702d88520250b0702d0100000b001d0311074451213450007140a07200c40c4100c241c2401207601c1404c1541c0110269a080c0381d01803d448041030440e801c02c69503622254040343c0c030450a2200c3d4840a10068041c0d000c0d02c80c142c001650b900403c113818181e131103584c40300e40415007450010300050364072111064000721010054038540303900800072240c5140c12911104161030310400001441590000ca10400f003040d5a10140302c2c0202408a44d541381c03c070350b0301113903a004001d0040050061014407100c9014814043d040641310100e4200b2000207844459540c1c1d004912041803004e00c2c8074200d0f0b00b15141c2e000b00140d07106260b0341c440900854180c0c0b00c059030318400160b04000240119034040d8030030000c46980d03c01d5140e91b44c07002e002c20f0244110543e4564009401131401007090301c280c540c140c50700303030038070f59002452620f07003040c814403918010b10404d00a422205c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 830062221 1250 830060971 830060981
    0x2a0e221506030f03080c0a0912150203070504051801080601030f051009080a021c080a0b0d0510050405070902040e04020d110a08251526190e03070201021c1101 70
    0x4840c440c0411403c8140c2002000010f001d0b04d2905180d504115a801c4180c2100c2d0540032916694025200900c09040010480c2107600c500c080c058000010403e8099116004005560048800f191113004081403c0460002400340403201d40c0084010300100b88808051a2240c0c4600103c85508007040c241e001130380c028a5040390780325000702e0720404140c1c05000e1800d149440a40c3d807c0042c21140c0300510700c480103020900c409a84000e00151500c9000003003c030075401800300c0e600c080c902d0203494000c00b01200e054880d401810800302d0070b15081d00030bd600301e0740e058001d007440c2d45407602040300558035600100c2d106001d07884804219201c00c03540320700420100c0007500704003080900e40711460151118004078405025824011018441e5100d21403254624001d000801e090510080901d0b045142078520b1902104011440005881d0b0360603510003480c0620018141c600d0040e03903400b075558001e0140c0c201e1402343c02d80224a0703501010514403850304c9074515007100c43c41400c5071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 830063471 1250 830062221 830062223
    0x3090c0801020c0604060b060315091317041a0406142a0f061602030301150201021b070503010f0203010e0f040302010f02070c03060b03030c0304031e2a0e22150603 72
    0x504035100b04400e000c998070802000030030a8a10509d540342070191046c0007114140c100d441460240003103000800c4065a203041103900040d40c982940b56100a901103070070074410100d010140c0025103481511036800e0780c0440d90305407103110404112340e40140060304604e04040c400010b0141c5101070306145d01c0d4089031110041d02400c2a28a1070030540e05140000307044038400c02c02c1981c40403a4030303800001c89045034044410581560f10356078040b8003910404c60000ba01015403089050803050120301041122070890081184410742c10729481a80070034403842c44003801c148001703012040c04000440e449446071000140c400502070005080f82c2100a041d0303001e5455680034801c02103540f0960401007400c800840c203040180c560707a40d4034415404014801c0d000010454042841d003d0200c4000d0b0f80621052100e502180240b106201d103c840d0b20031a180030f480001c0c5104600300828015800c00007070300024081014003100000084804444400300d450036000541031621604001d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 830064721 1250 830063471 830063473
    0x905150a060309060b1f0e030a060c170703060b030c1c1107020a090225060908041706131106130b040305060613050702030d0b2202040f080304051003090c0801020c 72
    0x480700e1070030244120f52481d6170050003004415a049000b480030203003580f44c11440d1138959021660000804d003801c103070f40b100030308190510f02400c03115034002c001013074698080ea9141202d5521450102c040c0d814601c14003030001c00030004508526440002403155641c1c02c5108412500840080c1d0102e45070f400000e213403284040b68610452818082c200000c0c242d181d01542860451440e0004400200d0365090015501c81549000c001c40c13500070041c2d00b50002c1c8035544550351070382c42410074504000403080d24058200001c60089009641c590029040005041000180c009201e0250701c21914101e02881800b0001002c03403d000c002d00245204402500b4141090380900a490912018a01640f401c010400c079600d030f40041519076a10080b84041002d1507030101081e090a0001903001e407000f1088150080c911658005100f100d4440645140d0103544024a80c2c42e4002c500a00707600c2105203e002000510a0b089484c1450180b440c0905543da5060141d08a903c091015026 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 830065971 1250 830064721 830064731
    0x1409060604140903030604051008061512011a060c030412290f2d04030e01020c030c06040b1b030406020a030305010501090e0a0915141501050f03010905150a0603 71
    0x1504060007001240d28204520003010300f00450704645038000107010601a5581d90001081a9052a0480000e00c448020b98255041c000c0d00015004408075146005840701b401e0b180f0000014400c944000391283c6080d07100c541c03202c040200d40d5001c2c0b08141401e220a00c80460361f6040390080d141c80078800d42404c062800c00500d141e0f4191806a110a9120102c2c0708010380226010904c40d030041d0f2202181c000d840d8808601003141002054001d6000c040200700b10030140c0125016460b00070036002c58080e0f99203172007016900c590140c20140c01003800d210800500320703500b0282013105281c81d80d0a000321580300756035146030030aa00c42001a07000700e003c0000e054051188a001d000c0c02e10700943c1050030304400b0061888050b000f00642581c030100b030010f01188201603404024180000d20900481281c00c2415200542c2e24440c0c1414145440e0070560080e030072a014012139040d40c03801c582ca0310086200400340204169200d650400007000d00da9900da080c1d60203407130300d41ca001038 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 830067221 1250 830065971 830065981
    0x90c16111503041b0b0409020c030d1806060b0a05070b0402041112070305092b14030112050c040c020601030b070909050c0d05090c0901050d0c0b0a0917190b0a140906 73
    0x1180850702c3c404d28240f1420054103000410015007124265402c450740035039035000b1456010f00d148a41c500101040e803500c010000702180301038104e0340c214003424083c03006075144c9014070510711034492002d000c00c2c8100001b40c00034900c041c0305980140003c0001507542590454650135501c081d41213020040064204001d803500b51003607913044180c02c4010080c005071510510101b03c0c802004000031005100096000b03485241584401554805c0007510b95070340d40b48555081b040c0748012240c500402000b0351890038603104480013100203034010b1003107034a151601c14003c0c101501400402400c0c12000c2064021806100d002da0000141c00fa564034003000040201d65016002c088a50841c41403034400d942c1e000310031415560115190302c9601e41600d001940020207a01c00d1f17222490120b15062280c4c4c100300100c044444082ca0013601c048030151194a07002c1d48604014100101c400410104010150760b030703444081641c1c0003440e241c0e21074000d215810102c03220310403980070104100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 830068471 1250 830067221 830067233
    0x50705030f06090f0c03031e091e01020f0109080f0c030f0a021501141503090102210103051212070f1209142a09150603091b090c1611150304 62
    0x3500324091200078002240300800041d4403445542000141c08c6560b500d4950f68100400840300000d00040c020100c001000610000700b0282001050140c0200e680b0740c2c81d0030b1410b0043c80200c6034002819890a01103195201440c0c00001030001548030070b03c800c019000681000f004011900d400a2258017001c0030481300c58036050b0040d256030100180c0881c2e2949403d504161490240c014081d1280c3e141c0c10700a0080c0100d00450901d8100c8519139082e20000e8007110b4180c034041c20030b03603007040e413a50304c80c20061284084030100400b81c85c0c0003a40356446a6090401104940360000064151045c01c8081c7c44002d10180c03a9210300b900d50f9a203080c002c104103030f8545a100d000f0b80c0c02c80c064820342d0412070b0380c01d0075241c041c191180c000b03042c042482801401c1d0440c028029908da0501c048282c1d03407086008660f469030b00350041071542c0303880c104520b2032040c6552a001d40c03900d04e00c2060030358200404131040f81c460050f0301c0800601d0ba20201e8069418015850454a900d81303404c000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 830069721 1250 830068471 830068483
    0x30b070905030d0e040e0a030c0506060d080414010216150207152f06091005061824040501090b1c030c170c0d05040303030c08010b0a0c050705030f0609 67
    0x2018000d5016082019880c0882c22800c95412414041d84030300c02c0c0070100e40034007000c1c01c2c284814014480b04008054101c290b200c88240500c040f585243d130b0f09014480b500b0308001000e81803c000b4130080103e0580f40e215624030900601c1a04c2003142c0c48034080c1008540b40d00b16650b510f40011584070002e0341040410000c14000d10403040c1601001d0020706100c2002d882e27101e51500381c1518800040c45400390300744020740172080701d03603078038001240c44d0301d403400c60090342c220a0814010400b80c0c80c0c24140e081202440c0728070401d564030f40103050100d0300b05113048101070420f0240304404980c1d86100b4507000706242d00340032523081e544170200038050b02da600f906401800800980004254048440040380e40e0124007540800e01d8440c3c00f081c940038030241c000c003d2103a11a041c80c00c030f030f0040140080368401d48050101c142000001d03100c43d0001d01480c0c510b01d0040c05940240e62255a0b1314010b54041c4047d0750b202070321580803030300308445211810390170b51110051054841c010044 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 830070971 1250 830069721 830069731
    0xb04230307080a080f0601050301051309080703031508060105030709020a0c020a030c050a062303180609070f15021f0f050a0501211a06040e010e06040c0605160f060b0604030c030b 79
    0xc2e180640c80c6ca100080d0840c041801003a0007234240c2030180e0700b1900c640d403240410316000168280c884200d8a0020058511074940d001c4c1c00703a201200003411540040c0715416039000802415289003420244002900904442410800c000d014070015807611901c40c00a180990076001d101420304c0103000c15680568808410060b00704203d5041d05070080320b02ca00d003c591403080c0e41e00d0700d400091601e40700d010b0440c4c5a0b01c0c001d01003844244800090351a01700c0700c20301c41049103150f941e0145032a203440321985101680000e07540003000700000403518911071080d000040c00c1d50040c6901d0003224401c07103403003009030742e0703800188106400040b01484503070103140303401182d4245503500c0740104401c400030031651000c4800720f90b060365150010400032020000810a42101c802d22642c1ca0f0415201075844002a1300c02081c2640300c0d0040b550b18102141d214049080e041d510202370888500341914100c0d5241061440f594400e070050000b5070040082c407c2003429400d05210000d00170302 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 830072221 1250 830070971 830070991
    0x3020d0605091c091202190b12180c011103160309170106030c060e0d120816020f0c060705030d0216050706030b010909090c05120d0305130b04230307080a08 69
    0x107010454a030b401a00001944c1e10f821090008172840d1000c500d14000c400c002c0d25684200c000c0109013214408098180810a4000b03616242c4418600781c00840740b07400010702c160841c104100a0354007507052200588001c0013181c1c80c150300e801c14200d448100c00c004400240c00928200503807641c0305500b507001030114008110141ca55a00c59040708000d1080c3c6060200c00342d150302403a40d47d00600c0040302d42000010600c1144000001e01d42013040314245000602c18424004482c80025800c1c500b0445100801030f2138080700401040d41c02c04c0404a40324482001410f074201028005421040c000000e0700340303001d80c00c2c5070441c1040d190b174104104052a000c0f400717031660b0b03000b0500800c0f10440390000821000c3c1c0d0610304404036443d040350350452412403c07054403c20000703c0e010003455981d820089a1a2071881400d0072401031700142031080c0d0440031034082551031042d080d110110384450800d0000580916040d5044040190340e60440400c207001d68030340011410760b000112403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 830073471 1250 830072221 830072263
    0x1c0f020405270c0d1202010b0406060309020102240a020c0102070203100e06010602030c0303010e040602090411090f090c221d040c080c03070b1606020f07020f101b0c03020d060509 79
    0x9000c0307100d0010503c0003031704103101d04044801c0d85000390b11944030160040e1051100342e450f41c030003a001e13000d4110101d0051048018012180c0e0354089030310366509200d8030b1240d10740c032406030002c065080107051549656003002840f006940801c000c000411403131001088003400f41803400c2c10107205038440400c0d0340040000340307810540401140c0c15201c50303150584031501c1d51304060000f409075402e80c5030003600c0d00b01492040c00200e030107407c000c1422500c403640712a201081c41082c20f0709031101d010091040c008080741c8104244441140c0320351504407020140c7c0d1304804000000320500c100c0b441459081030205000700300c080000582410001800103113001804241d60344030b240f042c5481750034013103103140250310003c0d00e0080903a00039000359202c3e501e0384c4406090740d1107120224812194600d00038454140720b0f890411190382d42d205c8401c42644001507480d010b1070b002d02221040344102e404001a5a00c00440b4210350195000044e40d240080f2001c0c5000413664129402007003036 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 830074721 1250 830073471 830073493
    0x50304050c01080411101805040c1b080f0f0a0e0f03061b0c030c0303100503060402060a030908040b030901150e0c04060c15061203021603021c0f02040527 68
    0x684007409600030300e42215a41c0d0fa80c10716104820301d09010716800401206035610080d80900907000807602a009000050359400802044480c2c080040010400782403082107009841150400c145d4000d1000b04d00d428900190455140d1205500c0c031040c640124000c0c81e19680142d241000c25400e8801000c0e04102c680020343e00c0600070403040302c009213010a401e0504244090300c02085403d41100d480e2850300c4206070b20ba8000b03c9801d40749a6800e0b6001a061070001111805507402802d07413403500c030b0f1300d9030300310081e140e0440180c4640d08200700c0041d94000c1d0310011486025040c1c000600703068040b003402c03020b030490342c40044070001a4013440310341c5aa200c111401c640c054200249004500c1c41d05107041d4581a01d0101030034902100056002c4070780e03182140d2240300780d0030340d8420307408805082e500c1102404042e41198400000480002c410100702500c64012401440205102e034000f8081c0c800844a05480e41104c2c0c0030204560740c00405e807041d201c003c0307011701b52010354 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 830075971 1250 830074721 830074723
    0x60a02070f020609011107082b0806090702160b030103060506090f010605090f0406080a02010f0215010501050a11161409010b0703050a090b0a081e0709030b0903130306060509010605030405 83
    0x3803900060702c2030000050302001d90780244104986c090700c010036034400a40c0c1c1d419107a102c0500300000b41c05150108980300908814890b2400500c0c2e060711000340d40d4444006110391003d0040c111020b5106881203420009040001007004207540c3c0c44032503813581036103860070030307613030040c10039030240c80d070b800030b01c01c0307440c00b045100341514800e240070340c0c5400a003400980c8259241d92250703005482c22602040400d0701180388080355000ba201d05540310000e0b1402c80e80e400803d41041d0715040c080340140002e41c400c00082c801502c503481e12801002c84100c82c47c2c10f0a41841a03403909090f421010040c082c44a2100426501c2c11190b840d00b961400031075006a00c140d8000404202d00041c02240a038060038002000e40f6401c040d1b281c41c1c182011025080540913141400189000401c101441d03d0440c0540e101b44601e60b02c0281d01459643e61092400020380000141c0c0814080103c807501508000070013180274103008202c8a03d08814400c1103081a0480010010208101700c04104 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 830077221 1250 830075971 830075993
    0x70302040b0d020d1101020d08130b0a0228030f0606120f0e0607030f06170c010f0311160b06040924020f070605043818030f030405060a0207 62
    0x50196404111007400d20700154041084100096129000d054088240140c0a41141856000782c00b1580e00fa10308010035500c00303d0440d85040b55401a9450303400160101e414030341c03c4940078602604000b4000030fa5a42182c404100a0307020700768200540c0d0180c2d16026007001c04450207010422142060310040a54541441c002096900e94032260481c034000d40c0219103120704041a18128101141d0080c0a814441d010900e0207003000303004268900002c11450114807944010314425800c0b0005503440c0036020403443c1403544da42a00911200100e000b040701001e45080c0d0314280c101841c05a14a003009001c003809107240c2051040000c11440b201c04044590340001c080506808022002900c42e40c0c4040001c940041004420046603402ca54000da100381c802c52180782901c030024940c0ca080500411100d205000d201c04407107440000070b5007040d4540c18600045150651803451075200040092020400100b04002d2200900c0119040304e040700c002c7d40740c0a910b841e8041d90350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 830078471 1250 830077221 830077223
    0xf1002100b031e06010e090c0a1e080706050d0e0c0901360615030b01020d0c060b03031201030b0c1c0203060f0d12140304021f0c211e020703 62
    0x16a580300ca030300c12030b50200002805449450324011031046081840758880c0c400b8441c890a065440c400b103010b01c0c0003c40c00c0c074001a4050011000603140c00c00c428290007425480c4580c003001d0190120385c865090080202403c880d489065940c0440707036000044402807515510380e50020300c0585119540d40e8026411103400090020100744440b1060508650344044200d6030003410f011240c0c2e104070340e0030000448290030354240c555180110180c0903039600c05000ea0041e040390100000180c0503426505074180600000904110b4100209143d940030000c0485040e010000400410500541c950f03400300c00310640d10700740400c015000032000088196144c4164012001a03d40d1b00d40902d44921004003d140c0d00f2031410034100103058061304100140040e070510b40364480505e00c501200d01456000d0100503215410801140e4261a666000c03410051002c0c01c44001c100829030080d50001d0500b80030114071480c81d0f004c0d24020004000005041b0041e05a03003079590081580300c222 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 830079721 1250 830078471 830078503
    0x90a0509070210050106030501060908030910051b0102040b0306030127060c170a0c02250306052508010801060515181c060b10030e1b03010f020a030b0f1002 69
    0x1611048070aa0416030f510000c035200a14000000408a0385600407178102c1e811600c88501c4907854120f050386910902d00c115030402d20101e00c0203030484c417410080070001c0b088440c1b044000c0f854000c0c14203a0740030303900c030502c4080701005104c4986000c0c032480200e03842c100210943c00c2443c441c0580407403040032015101a941d200062a868000d48906841d203003107140c00b0041e850000d00b85401458000c0d40740300140b15403c002c5240c0541102000c07113158070071184c030840a14640d100e07005440c2c01000030000d0700008100d40da41008201600c1c1411100391503000496041c403940e14211540c0da404984500c42d9141c004251015800803544003448500100c2c181400311400304a10031100600c4a4100b1540382c0c0e00c1c003d22945501c404586d02c0308641010180494613001c601b41c452040000d91150061034404401308802801142540c6000c1d0011130a80c030f841e0320490481c0c200300180004a511222074841e40c0c50300c006801404c100440c1c0b643c40c50072500000940d00c185d44e01c500062 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 830080971 1250 830079721 830079739
    0x7140607030c11040f110d050705090a051504080a1a0c070210050912060c21010803120a1401031101020607140a18080105070509120705010f0f0e030d0e0312090a05 72
    0x300382c0720390300004401003201780240540d40864030601c925511120a6803a024070340b030042030506100318202c4101c0e02d402400900c1c0c0c5810802000501c5224298002000204200018a4490510000d54000d019002103181030700302c540c4071380e0809001401045000b90406c0f610700181e03188400c4000304000d80c6031440e1a10000c82c00300395005103610201c000c5100d4102000410b080310801080b05040c6005247e00400d0050ba03030840d0803800f07004488031504140561001a01c032065413682c84440f80300d010400900300c103c44803001d202a081a540c00c8121a500045560100119904401103160011029801000610389405841c08820820505038210051410050024805841d03580000c000d181810f40c0c018025500001e4202c0c0034107444030001c0c1070700c480030401c0021500706031542160b03650b0030041129011f9000c840030090280f40c0c02d4024158404200d00131190324030380c6800c0300c400340300000c15103030103d803580d441d2006d1010491b040b03003520707001d4429049070429903107018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 830082221 1250 830080971 830081003
    0x50301050a271d0708160905090a0b19020403110a1203080f1003170c160b0301180905150a06050a03080d0207050a0212070509070c051902040e070807140607030c 71
    0xb9060390400505140d1040f8040800c1001c5c01040424206101e4000c0143d01c0f5611030106c000e68400f01c801c01c05640002e10214042210303c100300d030703014124032803503144d440c0c402d007540080f60010382055030400350108c0c102089051402c41c100c054070080d410360581001e07542d030003420040005e01e0100094884070209455200d400c03081400303141d011903903404000001b0304c2080a40c02c0307240703046402c2c441c1d2700858100c0c560540704207054442c4042c040340b43d603080074120b0449050710380310080510b94603070806011450a104900039400307520145003090414018034000c0d179519400085c801e150840d41000050b03a000216003030f00c0c0e0000e5002d40c44001500740582000c041c17250280d080400c11104842c0f0034000300e8020103440c8211984030540d100c0c445e0440e41c000c811400100240d00c4280071002c86c40340d403403101506e54130081c40460020303c01c5007018140849503106001e0b550000009104a4101c00d6074000520010f486060030300000340c4000b407001d01c010901400103100044540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 830083471 1250 830082221 830082251
    0x211b0210110703110307050f1e180f04260703030f1d070807120827130e0c030102070f0807081314040b01023705010c050301050a27 58
    0x140c5624007040d42c240c1652810050040b8050782502803080c02408000300f26481d08104c1d99500c060080d1207040c1c80400310708215800780c0c1c8840800c1d84885401904510380614400c0079120b01e404540507200d6040c1880d0004900c4c1c0441100c036203144140004051010200c1f041d6020a9011714021400c43d03030381c4481d030005025541000b02a00300109d448030f01180005071000c00c440c10001143d4080c0d550740e00c3d004041d0341080c0c004040e18420070400520000780c200e0b182000e1484d0424110303840000f07000039203501d1664680d1a41540311801040701940074041c420702540140c0c020751908540c0e80c1c0d1120007104090700244081c4001c14007400740040b150686400507035030424044041c0d25442c8603144601143c80192240703040009591295202240744000792600340d402c8001280c3e4003402404080d038004250820381c031325000e0900803885c2400760110300031480d1182981c950401041c802c1411064004000b982400a15000d0a150660904482c400140c00010340c03045011410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 830084721 1250 830083471 830083487
    0x1a0609073603050c0109060203031012021206190b01210e10020c011b17060111150406240b0f0f0f0304050105061c05060f060418211b0210 61
    0x740503201d8446101004000300000c0c06038118500340c036051205640ca032001c03a564030044880200c0a41c056030708001d102003003000082c100d880140313003001c14070004002c0d03460b00008550140b001014002c5144d0b08020511620407081028a13040e20311075844900c030541d01c0b03950a00501e500703030340311081c441100e0103116848007903600c1d550941d41e41e58840e0707060b4041c01d2005039000425202d52500300282d0302440c80720400d8001881c401e03115544010042d04d03200c40d00880d01c8480e010300d580003c3c1a01260202d18401e5110f40000148042010410000c4048e05080078016600e00300041c030200008505542c0f01c414810f43c401e0781c40c038285496001f180100b120b41c484481c401300621041041c10342000b8400e8000307503030001d020f8076240940c0e0f04a8a43c9840540250424004100105041854203070b10450142c0041203a0801c58107034100090342640641e0310014a1200f4283ca400031480c14002c5400e510b005c08203400c4540070094000040314000b84035200e07005500d103c080c052070130 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 830085971 1250 830084721 830084807
    0x3120605181b0901080f1b070c03030210180b1504020c0105010f051219030203130b1b010b0d080918040f3c0c031202030405032505011d0d1a060907 65
    0xca030303202c8201d840c082c2274000715400100c000d03004018500890107040e100303403a001509110900524000c507100c8184402d4041c1803500040d924906044203900c490008080c06803074000006015854080f8141501259820291140308410700f800e02d546000142c03002d600914400d2100e6041a03884c00307a2130351250f00118410b800140e5000103c1421010151109503c0c0511039030308541c42d022158201c500f914181c0b9403045a040b040c1000c83e0041d4003078040d480c00940402c80710002c1c025010000700c030840e0f0440f420700c4100d85100402002041559502400101c607450008020000c11013810f552107449100048100d1005c0c18048103092002c0215080b10729641c52060196001303480380d04c24012a4020701c0b601540ca84007009450510000d400302c00e2040034194182001140e60052a6100c461003d208445c1c0c0d10940e070380c0c18004c0c2002c52141516003044440d141c1d402100c02c1008000034814140641046100c0b03402c03d0000c448901c01642c1003141810005241000d200301002e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 830087221 1250 830085971 830086021
    0x21070b18060c07053a0c06031d161a130b0c1006030c210b0604020f130b03010e010503030a02070b0c15090d02060c040b0703120605181b0901080f 64
    0x81c1c0500c0880d41400170321660040580c10140713925400c0d820301d006412100050010649000c01c00c0582e2280d40844900380604c6104001c200c00200c5007032811a4001d80c800b06898000402c204217221401244410110083c4a0b810700507111085880103010b403040c14a504d41c0040c500440542c00d00c0f484841c0c242901c01001416106e0030b06030481040b80c019818001c03911041a42c818003405001480a035201c4481c400340c3d900d0105200103500301030001c001420090207606c00c0711383c2d0341d00b2010192032141116901c1c1c0d85801c0b514a4902c3c0107034400c50090b0010485034032540c2e40800c504040d40d402042940d901c3c03a00401e43d0386002c1000340d04c4c07440c8650f00005c0c032200300d9011441c9034507280d203942290a02d80310728804240500c01da100d80c00c8012030804c8408006800303184d000d00c24994039840003882c01da6800200352254442d0800c1081d04103880c003000f210035948135282800b00d0301e100719176040c8603400001034501100546020114048000085c90308400b001c04040c4000d0030350 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 830088471 1250 830087221 830087239
    0x40602040e090c010e01021207021c0804080102031f08061b09040608061905011d09031c0c0201150f0b0702030c030715171003081821070b18060c0705 66
    0xc05050b4660080d10307051400100d41d0030b00c005c0c0340c0d840056a800009007080403e85001d555508001c1700f081c0542c101100f5030300301040f00d004035801c08060401016094005030380d0b45045600030880c1512030300c1c00d6218003505031013030040040020f00d07035074031020594490010010071000080680584a0020341c041d0501c040803900c5000801e080d80254410510401c81003207583c0301d001560703824044c290b9010070030503461500c050500c90594110203a5400e8a2030850000ca0300b4035010401d00310a0440e5840302c2c032004440ba824403900c800c0d80c180c1104129102e00385004003860b40704034841c1c4c05800714045850002d542d030510207003034040c00080850300c040f44d645003800c0c0d03101c1540b6110b5004c902c40c40c141307404003a015a103151099900c0c103401540c9608690b5850b1064202c1080084001c2103c410340019884001c08040c020b220561440c40f51a41840c40303600d001560b03004044102e105018188241d4842c1c441000c00000480303080b03888100040c1034510386019a413100c1d91008800b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 830089721 1250 830088471 830088481
    0x60403050406050328020d06140603280606260f1302030102160c03150e0c060c0a050d021029011b1e0605010e0402090606160c0323120a08040602040e 66
    0xc0d40c0106071f507003625a81400410355070000488000f042c00c40c3c00350031940400000e610111005540c066100c1505500c0d500c0c44060071030f44044a200d5003040d004120040c418010011055422555003100c203100035241740740440c8010f007003030405801801c414848004081c111350382901541e02c0c3c0700d0301441c0d140e200d48041c2404990307034040b44001e4030170045070102060310740b00f24000c000c4040380b010001c003901c0c5102011f0007026032140300315102500a4040c0080041d000307100d19000200c503a801440307605c5808968504541c0c8074030040d00410300d04d010042c1108010700c1100d10b070365000d00b03041c1c6900408004840d02d003004840010b00008200d4004003042c8040c42d01e00320518000d801c10411a81c0b0f480e019000d101e4252006940705000034000b4555141502c010b1551090490301c00103186130366079400d0380540d400c1d00222001b00101003030186c02c00d9048460310400c20820001d090b2a41102076020b000d201c0c0d40318035001c00030160002018840d46070100c0d00101030524042942e480d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 830090971 1250 830089721 830089801
    0x5060405103c09202a0d09080127291003120504061d03031309050604050f010e070309260a0e1516020a0306090503030405010e0604030504060503 64
    0xc40d0040c5400030313181460308030a00e08440e581e40ba09002d0220a149450840b0403c0c10b02c40d4805c500800c40d04054040e0440c0d01542031140420480080d00c40c2d60b441c03130411700c4241c00c0d6412110440040380076890f145180401001e001406150130011640100425030541506008a590320300c45581c400b809101d0341100d5030703503008102d80c05900044a8086240c2007118148134a216000002c2e02a450000301003480c0380b0700d00410303a07000b0209e901c0c185440c14003000035012980322880060341d507010020039003804d010b83c80d84600700102d070010a44c104002d500c0d001c0e6024203014109580d030940744c401c21000402080640c00309010140410381144240b400940c0400d07514000507059111060090422465081c82c050141d9903003800c0944018903c92100085981a03034001d64200c4000f0101d10341e446003103030481c0220080e503a030340343c142406030035a0651810f008103a4004420000401d5000b01664181c0c1c0c5913182003544c0782c480c0d20b0f0100400019080e441000024030742107422240c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 830092221 1250 830090971 830091089
    0xf120f09081605100e0a1202190b070818090112020112060b19140f0c0f0c010804030e0d0b070807181a03071b0602040501030506040510 60
    0x56569610400d035072550101a102d907021100c6580024108005004618115200c00c60000c1d0170b1401400e404c0c00080040d003040940c1e441104101f0000c200358003542094001414000f0900c903003c01c007280f80c11f00310403561003404800341211707001041d454440d400c6400c69035000b59005042c032500e56101d40c269595201d140c0012404070300c00c514015101d500b1402150100c0b48485000b40c204808609a18004030320b500100c800c02c01d0707100a01066400d5503002d8191401d10010054464080f40301c190b00e4228401414dc0c0d580e4030181102185aa02440440e4025030510301a4400300a441c0443c242e042104030040c050328800007080001c903071218101d88540709942c0c44004070400ca003001c018507183c900844060a804e402031175600d0015500460304140e0900c1c1869105641084124085603482d81c101c80e4203400043c10041ea6134503009040d00003d0440c1d00704410305018200980c3c1c1d041520801c406404c1240c1a40801d2109540c1d030000e59a010a65440f98a136842d2a001620 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 830093471 1250 830092221 830092247
    0x2090118030b1801090c2106020d0203010503070807080303010b16060507031410050306040b0903090d050102070c0e070c15111209070e092503120e33070f12 69
    0x1c41c092002c004840c0e05021700d02e00d41d034208803c4011305082c0301100c00c2c0300d84405000640620018000e10000301c07244020071030200b00a10060722035042c0010182801e000e5806140c080d030100c0c0c424040480040101c034110f91841c445965290340c0300034580c1d11400410005400e0500d07003010400c00030b8140c0c110100241100e0560740107580d41e0100c0f19141022070080b60340691004000400003400ca0340165008181e050849040a0014000614038400503000711031a03500892144100114116130340c01811058440741030500d8807280c000c00c0d00c1c022000c040c0810540a6181149000c00c0e8801918031035060b1100d6501c140c07404600c8613800050340e100c00c19100ba06000101621003400f6503000700b0110001e40b007540720700c03880c12125011055428800303144080d4004002403174201d00211301c048035205c0c082000b1f045420014441d81090a03d0205040c0569849002c00510100e5400790010305400b0b40310103050070b0024010303d4000005250442444400309000d80124220100d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 830094721 1250 830093471 830093491
    0x370303140a02041203080a1418070e0f04030309110316230d0f031707080403020105061207060c030e0616020901140d12120609050703060b12060402090118030b 70
    0x19120085440200c3c407440c0302d104102c030340f4281a48002481000b506801c0807a40c0400b01e0f500c01c000b41012014801a2a51044101051080d06240c4800e000c1c3c0300c0101000c14903560140f400025a10001800400c001c0c00c05599441e40303c1080040040780d44245000341c2212050001c0302e40108030b9800070700070050700c880d40c06602c03a054515914425403510020303001c00d41c84420740d520302414060400c0e01b1414410f2411840c00c50703c2c06840440d120345a1703a502ca01050401c0d00303020b402c460000e0312050180044601224503014009a40700880d5900d1078040c801182c142030440d16124000d10640e448030b00000c1040001445a43c09100c0d103000312141c00481e603a440d01c01c1c0e0300300200211103412800110340600440c04100c00001c1140040c06d102529158030f405420031a2015044100b580e0ba4407003d010b51583e051003010007501a44801078505140002160f03081000240124861500000c40d80340c40d920407a00b00f58510507408802c2056900d03803030019041001152240c44c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 830095971 1250 830094721 830094761
    0x6210f10060302060904050612010c02100c020d020706050a1107180c05030411060a03060905132307090e0a05101a04020f09010809030f21010611370303 67
    0x80c054051044070700700c0b580200000d144c02c4200d130074400900300041086920000380c4150006490080c01081141e11295010740300311520450100c04441003400d0a600315030000341821a9076400080641c1629000d041c071685441c5079440032200322007840356170140c0d405003000c0051080b10b22400003010342c0e015042400b0800d20320204907100e0100b25400341c03406011848244aa0500c403000b050050070034034000c1a190340302c0d950503081d20300c103648400c420122020103400740101008012640c0030340303030050484040d4000c05995208224022500865661281904000c0003008402ca01c56400403d4800302540445810014000c440e400918000401900909460039208440c0303410241c00040d41405112001101c0300c1c0d40040c00701c1820f2000700300700303d40d00b04120003808203950340ba040071404546510405c20141e2069000c201400071014041e0012440492030381d100d103d40402a100141d0002c0b60030b04412005044094541d0030b0031941014564140c01c44100d03030b40c2030940c540e5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 830097221 1250 830095971 830095993
    0x90803061f08010b07050a06051503010507080c07020f042d060906050d03050a09030b010b090f030a0809090408130b0c010c1103030703180b0a060e0709030506010b0306210f 76
    0x381c24100c4000016202c540107021414000001c0c5c45030310300440c03c0b0b4141c52059039908048540546410680341c0400c1001441842d0902909500950a18000b04281080c1d040c00c0090b010703080300284039508010040110b03480381d6000c2100000c04000c08000b0401d50940c5e60468107914000d01c2109040942c040341641d1240107600460301c010303040490560440d2011140c680200c210201000310002001011030702504920340079100401310301da503403800d003000c01a5546d61100c006019400c542c42443c0410b040c082943c00b0043c0a0341c08540c01d9940785440012849101c0440c003182e00d0202000c107001d210080a4041400d41900800100c0042c5d0f2058030b44103884298042c003588100300144100d8803982026003c14080d4a50f291701c00d94603503821401c0380f402c0721844407041d030f50f090400003c408140c4c2b040d00110b8a0a140420b00c0c103503100c00da1501030500480160000c004040307000394413420040002402036a00c88030307070364080c80d504a49812032400300002d0352044210100c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 830098471 1250 830097221 830097259
    0x150825232e020705100818010509010204230a1707080d020d14360612100b03040804050402180306160e0109061b0201030e0613020103051b1204050102040909080306 72
    0x55500085c10a080c24480c1032044a215000034028100ca0001c26100c200c410001d0042034040e20020001603140c60800341c2034011028814090038641c6c1d416615034a0b151500c101c0403090340d140205504409141161281c42c0588a030f0000c50039110f00d18428250365408519900710840c182d031a48a120085a0900014000c4200d030a100c064100b083c9090341100c40d06040d801e8100e01d58000c0512000750001d20150050800c50f8000b800380010004030745142c440c50380180901105807415424561690007603809140111400b1300c0c0c0c0065442c0c0c90080140c05100190710040441f4854900a80301e400c0700c1e4441c484240100301c90582002d80c0e50f01402d045000c0d50000d986600c2a0010003403010a480200c540990500d5600d80070425400d0f428000300b48104124a9280141b45851000404541004014010840c0900100394110800c04119802c03c00d01402d071310491340f11814550f0092089500c00d0510515041b030141c20004000051071103160125801d030404501f070107c0c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 830099721 1250 830098471 830098483
    0x1e030f05070c0b150a0f0308070c08030c0a0b1f0b07020307090c020d081312051909030b271f050c04030314071401150825232e02 57
    0xf402824940d00184044d1181d00b4103484001004100451107a540c2d040d556107410705800c19101310500065000038001c500282400401549004602d400d08418049484441205004001e60900c0000c2f0307851b6076520000d0000b420955020601d0a0f0f5a001c001c1250707408010204d01030f006444002514000c944905a50410030380c000d41070411282808032115000100340f40c40c0416540d400502048071008012404591a21007660303406103000c40c00d005c1103a0307032050810001303202418400100350003421074100380c450807094136000c103014150700011603074004c8800030b1283c2070110401140c6041190a450110711080156844401c3c03407070b50702e00c210b0202a0108010081c201c085404420003071402600907414a4000406800c010342581c2d0103014552188844c410248030541d401c0c0710041d440d10701c40720041204103081090b030070110010301c1020f00d4400101090003041008103419021a000109042c0050120302e1825a41107010140702c00e01403400740461085900000310 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 830100971 1250 830099721 830099723
    0x204051309020603131514270a060e1e0705190e1503030d0203010801050403090617070f05040f09090c05190506030a180c15030b0d11011e030f05070c 66
    0x1820313145030303940c000511402c0031600013203a25207003491581172454400e1003016100c5a280c10075001509109503100018180a00180b140d10540f03032590807441d400003825500e660344200e0118119000031511414103450000419031641c55521500f0201004100d000965030b04403000c6408152a500204654000c0d0050a4404140101040524062024004040c1c5000341200e1420150340504426030b0001c1c0c0c0801d00783e85d1600700744010590046803039030107080c80b45405034401307101c086410650074002e0601d6050041124081419510840444000e44101041d02030050b50754441032004107650320027544c908488205c04925407924520741400c54407260b8003080b50f68140030400215600140882103c5551031900e070724034046260780405154025200034155601c0c1c8541c4214040c842c051540400d4a80181640e1740d5a48802e60a002e40c0c000340403a10320080100107031035000000c06020482ea4180c03001082060740354128085100303812105001a0b1174042c800e41d440824044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 830102221 1250 830100971 830100979
    0x5010b0a02030d0b0402090607062f2a0a0c0f270f1401080c04050a0b1507080c0618070f0b040e09070b04090c1107030515150303030a020405130902 65
    0x810031440d95613000b204502030024001894019540d001403e140c5c00000200c0740e0f0f0f9115950407441da808801c80310703481022001c0c988412030245421046d54441c12101ca82003901001310002d5241c00c107006610070341d001d01e049036074031039290502207040210340c81444041c0c06039005c0401c0b100c100c1941141052401142c2050101442507a140904800d100074600c00e641c540204151001c1da903a000d000f0301d0082c024140c0d9003044410f20061b900b0081440d0030241c286031040034181c464001d9511000b441260203a243e010354580100300c0c1c4501c580307151082c4260f80074807201d04403c0380f0b020b641200c8102124a03042d600c60740000460b03111301c0741214108041c04200500c240c1080082e5101400d80c0a4400594441034400002d4200e03130040280141d8400004400c950400c0d80ea101502c0c200005041d018910703907402d41c1d03c8054080111803e40710002040031401c840c1c00400750414000c05a0307441e450300d600800003d411074813076540328108480d005031185400348220786c42c60350064 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 830103471 1250 830102221 830102227
    0x405130501050c0901022a0303070c1e0e010b071e032a1509021f02031b03091507150606120f0c0e01030b060d0203010e04060b0109080a060b0114030901060905010b0a0203 75
    0x4a00b8a0080740303911f01d030b040c00030040411280da41c1400240b000d071f1f101c0d940d0490101e01f4040301d80b61511084555600c4411007203030030300010900074012411114850035440c0ea4030315501d0320007039555806000240c0301c081d60319106e04154101d07906040505008599121600707c10f250100030603240140500f00c0c0c04005900303024506903801802000f40090000d5409030054900e03c070301920041118001a003000c580d5240c0c2011b461918051a40c4041c011800c250700c0000150300b096240064281c5290001950f10821141c2154502103034628401009043c1e610703c0050040584e000b040c0321102e15001e01c2401c0e2200c9403080c207450100c1562000c0c9060000310040d802005d038110306660050043c0108003100c00c95000440c042e18246616013403034103051078581e0075078411049660600c9561a42400090f900140112903140c000e640415200a010016548a84c0211400b1031826002040003c0c002c0d0540000301110312181042206030b03a1101c00c01080c0c00f807189202e0050b0020 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 830104721 1250 830103471 830103493
    0x11e170a0c17101211130f0501050a0b040b07020103061a07051c020c0111070915030203100905030717090607050a0c0807050303040302130f02030112110307032406050405130501050c090102 83
    0x9240c1c4c007141441140c4c0000080e2082d40002d01003001c1c6042006059100c0d545141184414020079004080960f0700f202c0090608815090900460007a9450340c00003084000940e886600400c0040036007040c0c1c0141e80941400850760784e448102c040d0346506c1f5010040080030903044480e02e14400030740c09401350541007001140d886107001c8040409118540c40820020391502c150f02c0005a98400001c0c40c42c9140f041c1410301d05190100d960452400034106c01244022084400581c1d0282400d4041c0944168416040c003a2003440c0e5080080401c0c031200f0800b00051058155000b1041950718a41d101e9105a907240c150186071f806400c01e100820050406040319000408070a101140403003000070b200b004c0340c2090f440b48101c0300b06140c0724401e01100c2c41100001400a601600000e400c41d168070680c02081c49001c00b13030b200c003206940083c50040e4031880182400803c2444076041c100c1d9405001d00d07400070151410751034100070514075140036088588002041c0c014001d0a41c032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 830105971 1250 830104721 830104739
    0x60801060503060a180b130e0f03040609060f020703390f0909080705120909011401140708090924010309020f090907031509060e010b011e170a0c1710 66
    0x1080d19080b0000e8603544420180e6844d01501247d000c940080020303410491903000e480c000c154192180307a90800c2009000069100c1100c00c01e031503090070214050b00c5101ba04910f81032aaa002510509204610002d41c0001d04030b28945002580801c0d02c420b11503c42e4484034036260311803030840f820340141c2008015101d42000d00401d000c4c4032214100031203502c98038281509540508905000007803400034514100030340780d01401c800c05130200040fa003880044c1521441540720100313250046404420084483c6c215051003602a0070008141040c1869010f017080000030100c02010b800240302079540b02e80302e18107049130020701c08440c0c100c0b1001031007800c0c40301510300342c070a0003001e001002003008018132001e2a85070640c00508214079007080412a80d41d2007210302540d04040300c10426a80c4411007101c4080219044c424228585a00340c5842c998003540c052480404e408000243c0312940c0400e0309d200d4907407500e00d85070205c40c0b24006042d004440100c103400000c203092080d04e00f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 830107221 1250 830105971 830105999
    0x8060c04181e0b041e0e01271115190f02010b0105040e0901090203030703080601080105180604051909080c07060207051503040503120c1314100302090f150301060801060503060a 78
    0x10040c04c0080d0510f07290f030800d42c80b542c00c101900e41c1c164495484c1241c0c007400b441410010781c22182d281c0c00e41c101048581e0140c1c0051100a0001c59002c401040203688007408180e401001c141041e076150b100a401c0c010b00000c8483d8880425203280c0200d14081c0180109500000141e40704c03458030f401c160301c105125001910010240d0f40e5401c02c200140c034104010a0014013a442d01c9040d40391480004046142c140c100350301504c0715180d214181000b4450b0f0540215003160041036a5980341d551241d003180f06a808195582080b0b0004103000c40c1e00000c1107031011210540d1038150721050140e0341d4002c4d80c440d9070341220800917807240c0382d40f4140c003560f00180301d0800d17a441d14800310400c1c0d0426200780c0d6503015524002070f68405020420310300c01c005141c00622048000c0d8514001907010200da0540302c20b054001410a08540c0c0b148840400741a00030042951084000c2c401a40d075002409094003151008001041d2a0301440c252403241000504650135581040b00ba204070308 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 830108471 1250 830107221 830107241
    0x1d0723032e0e010f120204020304020d06150302041103010b09130219090e090f030906090118030609050f010506030a0602072303180105070203151008060c04181e 71
    0x22800501d80045480c0c0c00e4003030078103004418041c0c1589801c10340706050349103060f84890007640f000c0c02c0130400c1321039101d401401182c04503401038581d926400460594180840000c3c100c0f032520000c42840c840440d40c210541c0e000340c5040021a0310b502103485184001e001300d40b0805800e0048000700d00c0c2c100b00070350711101d00c4080582000c000d00c0b4801c0e81b00b01e100d00c150010910214092180c0003110a40c2d980c05400e040003040030324401d0500544074410903807034500910002490002d42e0740959501c211140d071a11724020420b5490400b1002000300d210300f11800d0203031340c0c1e610b0146034050240501920b801030140c42580c0c000c0d65850000d50000c60110780c084080355550072044002903c9030344020a03000903550300e00054190304050408449102d041c018180b0026002d030b100050180103c0d03410f8000b030202c41d21a000d0300c3c0c840912036440385c103241c41000300300304014100c47d029104a800394110392500c0d898030412402030301d01202003850740c1c030a2010400e0100007c0e4000103211 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 830109721 1250 830108471 830108491
    0xa0803011715220618020f01020d0e040e1e0115060815212d01140f04060612031806090806040308060f060c060f0a02070210110102131d072303 63
    0x1040f5642d1110144c0342d02d80c9200e245041586041e40543c2030512602d640581e09101a0080e58003080002d4030004031040d4983c0207030340d00c60501e150200d042100f060311940c1c510b52072244184090419000e131049803030b16054203124101c00140e41e405000250701a90341c00a4024000e00764205118a00c041c5440215102c00303e8040e5192140d01444039104070141850a03d8101041804c1111480c0304107031401c503140c0c540441c1d103101c0d4080540c155008a8940098003282c1c5031400c11201403c0c240c1c20112801c00c030101c6d07460400d5006001d14944086440718a0301c0c841d521941074801d0701441c851040a500703da0b002600291050841c240e002c00b00810710401c1502180210f582908441c801c030405500200600440a1103080e00b01d40c040e1450a040d40342c80810313800301d80301020f40903580c404c1c085461a00b510085081d01610003100110741d0450880380e94400815500302002c0f0b02d94250241080815507035840303501d10a00e40220f40004400e440030501070006281d0004140d03000c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 830110971 1250 830109721 830109781
    0x2030f03060a09110c0615011b11150301080106120b04020d21050426030a0f0909050f07030f090b2806060e0a0617061c050a0803011715 60
    0x909007036132140003041c4210000c0285c4880c5540641860050050140005062500b00302c201a80c2d05c00e0780d5005050000708030854018007031800c20100b01d480010701d0fa101d1800060380f0302004240000c1c40c101c50341c1000074044c080c0e403940c440e1640081c00002505403100303007001401608005c02d86d21980c42c45041e003540f071150383c0c08d208680c0c581030310f81d0300001400c000350410120650032001d8070380e005801c0345100d42081e0050f42a90700c0c031420100d48140541a82d41340b100c94011189d010007030032021024071682c58031840c8804001022aa0f001c04280f800d0060465090f42e8880c1c813101507845209c81c140c1d6102c2c1101050203500940821600d11355036014407030302c0c403084e000d1100140780d0f940b140b4281c00361305410061031480c990031000070000140d01031003524400003400c80d00014203640072080320308041510b05122000400242c02031041040130001c02401000840c100c1d840c10102d001003c50000c02640c6030802c4e140075405124461021030074600c40e0303400a00e00300c1c4ad01c02280c14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 830112221 1250 830110971 830110979
    0xf0503040521090307061b120210091109010e040c050609030a020d0507050f03060c121902191b260c100b150a051602030106091401090f09020102030f03060a 69
    0x65040003544403603100310b000328020a40b81010170082c0050861810710100c9540c0141807206040603210014100d000750408800000e802800300501d1720790035000500540301c1d2410000003001d80401c01601071315021000064011218407501c0c0615801101241582e29240030000715402901c9019410f001d5080000010380d102005c0219280c810009043c0d4145040300300210340c000c111043e8081c0d04030404110041c4056402c0700e02c00031052185207000d455003102d81c0040240700c0303540e4500520024900000c113074861880c45a09000e07503038010103800801c524251200f0b05000003003509403100c0003242026192200201c8140341c0303c2d0031034108440a801d851402240000c500e6017640d4401010ba40c6052603070b1700e80140342d0500742c3c0700d16103440c0c0200100140308442c08283d00541a5025a04558003900018000c00c002c0c0800d01003007180f84003009243c1d8082c840c01c410300b464902c010714029014060810310702e4058000d5424034084848515559200600c09607004c1a105400f00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 830113471 1250 830112221 830112253
    0x6070f0933030207032a0b132010050d0207021f080121030e030c0303030a0b1e0a0b07030507150605180f0115050c0d0201051608070f05030405 63
    0x3288040709803103108900094016102004244801081c003098010443c2d200031030b0300001100c6908600d80d103c0340060030050725081443c0380d0b03508014882c904030340034010b011a80000c206406400340210415280c034540f610240113100450440d04914000342d29041103002d02c010305030fa000e2001c0050f181000703a600040c2111281014003108002002d41002c50941c0304a4160140c40e0405214200201060740a642059000801004c10070410036611540d102803118001070040501201d0f16400c1040c00c45028040000d00070b4003c2661600004c02d10b40c04440c064681d450207449a910281400b060100e560b108541c260f00b4440100000000680d91a10350880d4032121180041d11504210400c4051040c031121841c2d4442c04070113000d58848548071880c1103500300102090b50b102d8060041c1d846005010607405c042c0078845021110302c0c2c0641245100304c0c401c425842c122203014000750b41102e0305a42881c0021100f02c0300c816040c5c000c00007142c0150241084505d8440002824 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 830114721 1250 830113471 830113499
    0x9041d070b07052112090d0c0209091c090611070e0103140304030c0b030406050a020702100f1b05060603250b130306020304060c0305090705010c1101030e0a050d0207140306070f09 79
    0x103494400c4001781d00c075402e49070b81a03001c0e008800d0b0400341c0f81e0809420001030912a21980280c030889005022400080c020000c030510f4401c0744a5a001e10124480050801c03000c0b40705001c08150344400c0685424804600c07482a5a6005000c0071140d00703540703449095009100c0c1032080e51008220100c046440e00d0350041c0140b502c46491a580d10345403402100b40e510280c9103008150041c070544005a5070b007440d000308030807031346841120aa40154121145400d8400310f03c0d4600794800c1c500244140400c5031840f400c0290201c904c0c6c4000507110006048054401c18003c5801d504148501b5103040d008007441d90080c205280050784a4488608a83c415102111881d6a500f083d0742181d80501445034007061000c090f05000c2e2070300340080c10070580404002d060800d500c02500c80e43c0c0c0641c1c031210341000340c1001c50f080d441852030308640c4c1e081d034040c025015124410000550301c1810b400030f0141c2c00f0290203001c1d581c0780c44006a401c800804211410b1050a410124035484a800740d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 830115971 1250 830114721 830114773
    0x1090f0506090706050a120c02100603210528050f0a0206071e020703030305061801030f030314060f06031b0c213103050703030509041d070b0705 64
    0x54951070a00610082c90303d411540803070140305c020b00c20389181542043d5626440c0c11400801718120802d0717030080342803a5018000840a628003e00401800350403e8684001201c0c42400001d40d81d0085095a1501a41030314448000140780f90b484070f603039080c80304a040c480a0501a01708003400c0e0301020a03800c24026503005911030420401100e6121a0f2035034a00d49404800740821100d100003905e40100b40000703070901d03480340701003440b030384895040f00c0d003146030b9005d11706803940c40e481c0080345114230001c207800080c100313003200c0300c4a030340c511005014480040092606042000911a11360801050a11188a00b060050f50401d000000385a071001c84030280c01d0085000b50103a58840540e10030140803030081c0421a60300800c08541c48080c01103036450351090315140000c094800540d00020590302902d0000800c041d00240139150400d404c98080c019000320b0124030120340702c1c60f00003202c00c0d4003c0c00108203050000000340b20480c01401540c1050387c1a00c43c00040000d4404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 830117221 1250 830115971 830115973
    0x100504170a0e041a010e010903032a060905070501180e0703091b0305160b070510111c060f0b03040b0f06060904180317010b0a12060302040c030605090921070501090f05 74
    0xc800714407586d004400000c40102400d015540c9801e40e1030040500c0310b0003e004000c0c201040c01c8154000014440c14400d95105805004002031441d029031100b1151140a002c10000185581400c00c0c06881c00d041d00c204000d8118250f41e10241117005e42030080007903c2184000c800400d03140310000c00800590302400040c564003c0c4c070801c0fd0b44031038030355001021107081400403d001403008164864201500c0d030340400c4440e0880c80a0341c10740300703441c414404986109011a081103460f0005000c842c2c1c0e0480b4000d64036030f80c031015030342c0b8070046400800c10950040062099095a104240c0010303021300300301d050100c03080100d021903d0070380c5848042004920000d04041d8010034840212801a40d001d441d075151050303040140c003503400050305128002c0710a280c60760082e407000c0d000350b80040082c80703040313080c1001500401950050b18002d440860000c0d02c0f5030000281d0b23480184007005940c2c95208140d84c41991904241c201700c4065484004034804261500300406071503004034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 830118471 1250 830117221 830117261
    0x4030512130524010e040c051003060801060504090b04060c031b030203090c100c0f0201140d05190203100302060d060e090d03150501051209150a0905100504170a0e04 73
    0x41010762030140e0341003c142140303030040c0c002c0d81c0c0c40c0c0b0390300b400e54112051000b40c0102c40c1c590385004540f201058006a03000741031040c0300f2050075031580192080311203410003041314603214401d00c02907030601c80c006840c0200b80400729001581c10380c0050f24040841c980040c0d4144500b099240300c16004007540d00080e00030062101c070380300501200544140403582c042c0a0010510b010300b0303200c102c030005400c40025484000559000d0030540701c101c1000d0b0074441d0342d20090b240950082c1802e9880000340f0143c500d2480044502d442140d0159070092100e41c005460350342044070540c82002c00170040c5480d04000513080c14000e8500d4001c0d0408000f40802e4484980d0043c1100c001c421b038004a0b041100c0c080140340d8004045621808200c1d24a144554031120914a4a20000611282c1c1c0d00003104100e070310710032239111000d41c51084d0192102c680c0ca502c442d40a90300107036006481080c4001d20710300607600300c0004082e5944907042c20700783c500c0c00b44c00082c1240c448140c051892a040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 830119721 1250 830118471 830118473
    0x81b01020c04050603060705071e03030603030e0306091c020a05073f0602030603010e060f061815100c06180b01081911030109081b070605030417030403051213 70
    0x41c0401c0c4491141510200f19a00c0c015000a554001c003038001c50500c1030014400090142c0d01141c43d003030350010321440704045400c0c9001001885207201c180c000880401c00a0820301e400305600303015110841c02007010010000c0100001040c1da8800020751003003a82d4140010003e20031000140f41c0c0941c119103074043c2e0802000040e8030b45116000e042e000c640701c064a1050714818000e666000200140c5a581d8140401d00420708800340c2c3c80c1074458802081440b8001c0d0840e90312524044d1044c40720706a40482e90240d02c4001d50701c40420300020751007030a0a00741084204d03041c0c081450905280c000030780720740d0225814074070010312030219003024000384084900d5050040c00600010480901300e88120031102d03400d00c20041030303540c500360200352503642504030403455504001e04694a00c4003909d924004041d4000c00e0300c040c058450000f440368010350079244075270781240300103c12408403074040c809039000a0080f420f0050a029a40481503058086480794400b6a44078610b4041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 830120971 1250 830119721 830119723
    0xc0904051507110a170d02180103290d0303060e090709140c0319020408011e06050306060102030f0a200312160e0d0606030501021c2a05090307081b0102 67
    0x8001c10312001c3c001c2034a03071615103010029000d4a080c1d000f288031000c003070382c0388403030105481800c5a0001070350004c40e44044001c40b00c1070038601103000742ca080120030030614042042d4a000d000b400160f0030b00403a00c0b045800c0403000115501d2280c94000b0309103841343c414000518041d560b43c88580d01464050044c0069485000ca00340010306802080e440c0405c8400e40a00c801860920110703032280516a43c640305c4e405030f40203054680d001b440302001d0f52640c0c55084603d90200c500d0541041000a92400c6c085902400380d001030303002d1807030140280038200007640403210b600701f00141c1400c28085580c07030482c14418204142c010b9131f9907494480c0b09020912016103ca041c175012b00c442122a07581280580503100029543c503855003804c0d040141c003d01c51750340040c003030b03500008540941b20307000020f442c20148611002c1001c4004290035940110510441422240010078603040481c00344c0c0182c07400b514010100c03495551258109401e002e00415004400555a40049115a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 830122221 1250 830120971 830121013
    0xf09151204110d080306040c17090307060f090b1b090a030f05100b0a05040c03090c090504050d030606080c090f1315061d040b1305010e180610170c090405 68
    0x20044600540c5014180c13185a414070028205d00d01c80da640d8540c140e0303100d0040c079031140002450640b404c090300d40122825144d42c8070082c00c0b10300c0c83c07400703081107400c810394411144455001400c070421136451580f00064104a442d241c42c5414040c440c102499480701c00c803c014500c41d02d01d8602d1010b0625140d4076002e05103604482140c24540d264900d6120130182c2c00444004860106180d82040425070040910b410040c10722000c080c4041491541600f203580264411822281b8852445c901107081301c030070380141c000003080ca00101d00f0030290103001d03003051800100400c1018489000040111401070340b40d0f00b25a8482c0c000c81404282c806102c0c2c020445403c0951003102902c60040303110902000300e40c400d40e61415181159141d800d2260078400000100f0000d0b542c50342e4500d01c1d0784908031030348030440c0c07644580c001000c4008601c5c640213841c46800440858103000340c602c0c442c0c0c070440300014a4440c20201c00b40e030b1b40c0c45021140c0140e008502a2480c00030049400050131 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 830123471 1250 830122221 830122253
    0xb07050c0d05031e010b0408120406080a05060406120b072303160302120403050405040b0d1a0603010f0f02040801060b090102070303050306010203190807030f060b0f09151204 77
    0x2040502a4000050300803030710101c0c101e05803401d070340d8070741c2c9403803001c1400c500c00781d9600030408100d400800c2030502d9000600949201038222000648842e075011014032942c003601c400500c501c404514091850703004070780c01c140001e2020516585a0404071000002d850060314001d03040014000807030740080180c603e9100c01180c2103500c3d00d4480d0030004511016001102c4128500c1c0c049001c14820b50540d10f84040945100a540c2068100104290004d000c1c0c13070b00c540e24042500c4441d20301071504010070b590040d46400c00f01d040c5107040244100c0203180781e406540340d0704c000942c250070744107101050070340703420050b15141455201170131140c0710b070800156102c04014628a9a80005e0341d0802ca903414a800c0e82e403617170350b00b004030305602a802c82c00f00b9000d01000c44940341d40d00081c45510400142d40c08102081c0842d0300e130020741c1c2242c89614041c510801500103000782030402494095400f9000c010328040895000c8442e1340040c418003004003140090100b00402c2c41d000c55085 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 830124721 1250 830123471 830123477
    0x7080a110c0f120106080a0305030702010c0516080a030f02040b0c15071b03090e07090303030b090c090d050a0c090203010e0109020f09040e100f0c120608030301030f230a0b07 77
    0x10400ca40100354882451a0014461690243c906410080c2508000c010b0a40c480565503455491301e80580503404c00d0f00d580e070142d42085803140010f4820300545859200740d101d0140443c615840340040707a4800c01d00701c01010344070f85003004100b8142c001807009058040a80c1d030b0712115400e60310b0400c8503482526600391003070414017450039030044204880141c01030343c05808941c21725065480b40b84507409a046590300e50304020f000f6821a03204421240240c50500c4108150310400042c24011203400800340c006010345465800c0144100b5203071489041204d03920340c6180c541d8041c1103940e91040d40403640000042c0441150040300740e00614104a056060085800452156004025495000742e5850b9410925094204070100b403514034014204000c1c014850300030017818402c039142d4080f40e000f0b07100d003107a10207911030241242d400d800036500f96400c40d604c00b41c40c0704c2c0c1c5000988401000d51240801c2034100c948812410002070020300c0014501c0c030300f80c520444003c1c200814 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 830125971 1250 830124721 830124733
    0x60702010b03060f220606030305030633130806010b04210c0e0a0204030b042604120803060d1502090901050d261b0114060405010b0a030504150207080a11 68
    0x5580d10f4401c0b690f400035417016100104050040d04254003041480f0050030143c1028000810301d50400e00541c0910000d6800c041c0422629050290401e142c00d000295900e10150340f03901542d01390040c1408602000101c544c1c1c45d070302d032107080c40d2010a0b0440c108100000408110001c84840d4074a005001e0801e03406c030018039910355800c0c1e501c2511a603421090100e0005000d050715038112005143c3c400080a440d00305424400300b500002270740740906d0381d0b000c2c021501003102e2400740c03821110b4010041c80c01044907650081249c002601b07035070b00080c00014003000161b020100d518a0b2110744d800503240e20341b15003080104001a4481405000440050004500d410303c060f00004507540d420071a540d00300c880c11b0220700c22040c4808403011003005480b264003064110840c0c1c0610f0301095040d544801c820081111801e1044101060081001000450203a0803140d44a07000305401c8450100499401c2c5c241d90003120100c4503e10b0000d0803050b000d4220081c8802004100300900d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 830127221 1250 830125971 830125981
    0xe0124091406060304060e0c18150105030c07030c050a05030c0d030c0f050d05040318090c2c0913060f051f180b12100b120c010801060c140f060702010b0306 69
    0x242d02c0050001b600c00341d00c5002152000004000344c00110390301500c0c41407507410800300d004520006070346584180700310b460307800b60640c03045c400d03240252201c900b031500d000c880e554142d801d9500403104a4032809055100e42c0402c2c814006010781c049594080d0601211a020042c21030300d061003010305002008810204c0c2662240640d0010b01100d0b400003181d4886040503100248030800c2243c2c1c0c030307003d032001041c0040325801030300c1066101c0d21503d4a4442101191564039102e141001e580320705445d11a200385000c41d1499040403000401340351503c21a100c500603502000800b20b8040d8a034010320807007403600460030003000883d041c000145070034464074070200306924a0400d0640c1d210070032500c3c20340d90f4110b22000ba02003282211240c3d00815444009040c414107000d00c90500c040d001542081d01007104d1904540503514a8456030074003070161461101c2610a4440d56401c0c2042c15506404000d10080b0201d060010102c92910391002030139980091401d0380a40c1003403081c48 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 830128471 1250 830127221 830127229
    0x50a0b0f09031b010f0f020405120a023307050607080f0702060103080d1e1b182105010515150a02030f0f071b0906050d03020604060e0124091406 64
    0x606078585041c260188072034031250084c05420181c4d01c040c140b0f840d20100b00c40c2c08209a0041c01151029240f080890989a90030ba40313641880901039084059441420003139030311548a01828410741d00f032041180d1403541f0030005c54008a400715001d81c003102c140480140c00c0542a035200f80510100f404a2a240000944410040c44000d2540f074010031005c0309040e060300300e86800d0302d00c03c040c0d024083c05000c2d55005490740201a0301041c0150b202d00039410700c81d99281400780c000002d500c10035842c104010084117005005000c0020b2503041c19000500c0a00940b4000d12844980e00e96104aa8041200c40c0032400d05401000d00108a4150525008416110f491016030380c2c8079140c0d180c010310f044052046100080c401072a142401d44600c080000000584402c500c080204948440c14004510a83c0c08090302603884440010b000a5468020544442c210b10000c103008949081c40804644e10701c00796054052000c0c0b05111202c0544240380280900030026141414000080703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 830129721 1250 830128471 830128477
    0xe0d140a17010b0408121812010b1203070b10061b0501020403020406031415070903111f02070608090a03120b040908130503010b030a030c120c122a030e0103180f050a0b0f0903 77
    0x481c003c0c00701088c00c3e402c150003980241404540500100f54440701484099200d610503a01150101d1000c1c0c0807407201061521450151130203901c1d034040d80807011100131500c1d600300d80b08a0302590200f01c00700040c2c0b500e00400000b94883c5441020349684d240929080c00c5140b003255030443c403810100860310382c0c0040080d003101e80000600d1241c1003a80b02041441c00c40742c0452282c0c1151403071000c0d0545c2e00043d010104c1e052030390348260589408404688407810b0300030140000e00108241030040c0000e505c40a4060340c000e000050703103141961307442110b40111440e901e01010007281004541001c0c050180d000f070045000d090100780c0c50f034028208c1007440401501c0101d950303985c0207805000b0002c1c040e40c281c1041a042d00106401c00c01408110103c6840201030f4402c440e03100312a18882c54800b1a5502da25a004c0014120004600030706598040491002550b086440851480030001714001e02400207007400c26003038288400810390180407110706a42d0081007052441c004030030303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 830130971 1250 830129721 830129767
    0x902011b02090a0f0e190c0614070b090c0409030201060602010f02090a0e0712020d0912030203090d080601090b040806060a080d0e06090f0301140603010e0d140a17010b040812 77
    0x11941c459283c4c80340140645542d21280d4810f50701015405e50036128407803011031003110311504e40d035219402150f002e04a81c083d9101a072060080c6400500d01180c520750250280d403c80c5c00351b102120000d030544050560079405070350f50b41c0c41400070075420700801c8040402c552040d0725103013000010910742c14607807240c4c810b002036150105402510841a107101030038641c03001d540321111240c08030020a4590030031100346040c40310445141e4028020359200c1c007c9100034010308000c0d15415104000c000b04464100310b008400403504480c120301900107071064100070020b030700d805c00a101403a0001d4001240341d902c000c410043c0550701042d0881c20100c15103900340c540d40404040368212024004440e415428000428002080c00408a00c103138030882c028054080804042c58681090381e01d41000510449200c411241c3c9500003003030b0444052500f00c00104a0901010780346400703800c23000280c000003038104206c042c00c1000d820340c01068890a440c01c052040b40d00c13182d4501101c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 830132221 1250 830130971 830130991
    0x3061c05100510171e190503030906061c0f0503040b0408030c060703020c1b2e0e2710150203031609060516050c031902010314010608060904050c03030d0902011b0209 73
    0x200c1c013a00405c00c0c040d40c07020040e02641209954042d1800945a0700304980700300c264031522001410343d103415035820001650400901c041e145254840d01702e10031a8075410780780e92100700000507071510a07a008200502c101400f40d0345420302c0146031810a070014040d44c08041c01403000d0702050502007441e40034110080c0789414403002c0d050100e801c044105100100c2482514008200b280c1c42c400551458640c0e5034071440345010800801118201021001000c2031400c994060300500300e04c0d01640200403682c81220f0300e9641e07003046a81100c0d02d020480140c2020042c0514001c451012140501784c80c1896060603040020090443c001c0d1940c140444140c01400e07400e020062150999002025091340c0c2c01c10002140030082c9082030008a00003460328030450080000d100e03096050390b00702c0c0d45949281d121001080240c00d0f024006070f40301c0c0a00300e0410741070b039420401050515400c1002090069547c000580f10b10342007020000a68610b5a10301e005a0321404042e0384156940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 830133471 1250 830132221 830132263
    0xd05030316021b15130906120302010c080f0a0b01020a0209070c0510051b0f1e040f0909050709091a2d06090109020c011e060906050a080303061c0510051017 69
    0xb0820b10001c060354092581b030b5291081c04200c1c81e19109200f45c809000381c00030b01c58004851411144600c08440084a119002010825040740c580113082c55034030510440d0194486c540005920000c20f8030a8030204074442c0042c0308101c170a200411041c0c2c3d414808001d2031a0043c0c6082d80300a054030054030004001921900c10034200007a200c034900c860b00403d0003030071801d120200c0c03070b0301c14050800c8058495000184a215030b010702c0c000144d103c4044d00b1650b00d4580c918000e0411000c08895280c4849468100505028102c2d44034004460300d00321056034141c05404a1030034640c4141c010803204040000b81d03141c1854007411950300308001640d03108411440b5004010310010804404142c1800c0848080b440e044a000c3e00c444c21010000e0319503074400c208071201148121101c41d081880041da461515402c030040ba845201800807140f05555034042c1401841151102c071180c0d10b905020b201d21292401c080a8030383c0c12218410280c0e25030086036607620404200500344a02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 830134721 1250 830133471 830133487
    0x90b09040f0f020d140c040b0303040317090d080d0903080a060518100b0a03150e10330c05010b0102010c1b2a06020f0109030e040203060d05030316021b15 68
    0xc0350700510658105c0007040f00c648041482c00e48481c01e10010341d2207207061040100c41d40c9400b208580031254440200e20885a849504050030b13004420303a203900c824144051004030380d00304020712091a192000041c25820351902a1107144040e1600420501c0d006051103541c9900e503c0c0080e43e03402c21403c120940d0b1703c0000795081691500591001040070070903101a68041e0080c001d01e030843c01c01484d64588031118018007110403240e00c0303640805030004212000c1c0100309080c22124565194034800a610740703000401c00c900ca03002000441c1c40442000344074082c4105040e00c02c0c2403000b4041e8000d142d00040c914951025180c0501e0a188000401c11080c2040c2d025021400c0f083d00c0b84c21007074203021640c21105d40c805d4001500441189503c061018803d9100485e450707200e01103040600400d01c0029000200520340040c1c3c000c0c0ea841c0850001c0029511440000d2640510500c800000a0410300007100301103c0c0f00032000402e000740d0311403410007002000f44918688440760 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 830135971 1250 830134721 830134729
    0xe0108390310020c0f0705040c1e110105010f03060506120309060f040e04030503070f0503060105040312030f05010308090307090b030a0b06150c0d0e01050304051e012301090b09040f0f02 82
    0xc190481200314030000d41304044402c0840c0d03140e00800c0c2d01060300c40d081da4640c103200a640c003c2c803808000694884400c05549104481080d80000a14080a58409800c2c1d65400c644080e0030402800b42108410000c04c20303640106580950142c60900c0e00300c943c0c0c0701c01582c0e802554281b40c4208008108481240014000c1d80d00400f4500d1400b90681040c0c140034207035506c29a000350004004034022504280500c1c1128025001a0750300d41c942440c6440e00c044072901c0d201c04500b09074883c0b5100860718400d016441c040c50145407143d507104160420103240441641c0440d0042c3e0400c02d09105035540810017510b5250840c18401f0140d5801d000100c164070403106c000d94101c008201607124180004081c2c10440042d140c85005845ca8801034401d13000403540109a0391140036449480c0c0c4503104146803d0819500100c0c0600004942c001c034048200034414070141c80000411a500b000d0080200c03141064aa09103a400c1640300c030802b4024800700034016a19240b400750031911 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 830137221 1250 830135971 830135983
    0x21c0506010c0f060b0102120301120f060204180e07060c0f020409061416090e01140d0606081209090c13030f031e03020901030c020f1510030602040e01083903 70
    0x15020780003c104072414075280707008110000c9914010b10400c221080c03524808030482c0d050f540190580c84080d6240d50ba40f001d4400501c0d021140b540d02030000288940c40e0801408014441e140081480c4411f410003030b140800742c0e0302003070420420411030004170384400e64000354281c050710701040c1440c090900c540034000c980680110254001c00308103450f4041d20342001030315444d2340e03000c4030349640d10108140c142c020301a100000c2c1100400510601d460b0381d101038aa44030f84e1003c02c038540d0301d0014500302980c000c40410b140700300040c40c1c0c45a03d040440a03500901b01c0301010304040111040d0717400c11866000041c07040c3c618030362641c00d06003e00c00c1c640b03580f0760034504404c5940004600601035005040313240d0110782055045050f150011460b86021080700000307144c000381d40794040000101c05444012550441480440801c0440c0000d01c05052001210850b80d450007020314035281040d2803861219912590b035103036691600c0b04100c944c1174011240700e04030000d000020f007040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 830138471 1250 830137221 830137223
    0x1c141f141903081204110f2107030c0b120901050112032303010f1d060f040c0905030d020618060c1206130e010b01020c04110d0c050c1b0f0103021c0506010c 69
    0x800f02180b1a00a01c2c820400301d84211b2046003150640f000d61002d0120350a0310b4081564080483d03040100099620303104a101c2030000821514003e6aa460b1301540c0c1905030054094224000303842803090300c16030000c641042280c0020411507241c414410802d0104810080400800301a011000c0200000f0381c410035110314901c541ea03581d180280002d0703a51610031050490900740c0103c000008140901c0e115120250012141840e65401c00005105060019081c016120008541502c1c00c001c6500034003110f80052000d400c00e0141d50725145c011042c04101c0c1d038070620410000310400c00a680d400b296080c035100075030302d40000181944116400030303d0503e203040150781203100150811404600e0a80076140425511800d10040da203594054400743e86040090405551a82c1c0c059046040f4602e0100d040050700024541410306c9c410402d101d00e0264203c0c5542841c0120170b589140c00d090904502e4800c1035405600b4840c40c001d00540302c0795031080019400d1b402030020868103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 830139721 1250 830138471 830138483
    0x10509100e03162405090d0b0c0f120f0105150703050f0d09060609110a170402120a0605011d090a0b0924040b130b04081c141f141903 59
    0x1040d12280042e0312400d00c40b40b01c0c0258800040e03011444c5001c4e00450b5851013029008070303032508241d212042c3e9800003a09040680104100c0b18500d24240b84c0036001010241c2d030140c1280c14115140d403070700641a04154414070f001e0000f58240380c800806c503030000358141401503c030000498410345900840240f50b031901d0407e4090342c1006203d5000c030040c0c07190610204144030b0490620038840c007410f03180c1c8020030f4413000d03441d0014a0383d60185a106100400c0f080c03444803188000ba041c444101e0003280e01c40d455a00500c402c2c1041d00d5807241025072000492917078a440e50480d0b0b5035900d01c16011b426504850301040040300180b04d201d10144800c03d40d040408403018069405080c1110107561a5103c000401d01c100701c3d1400c00d14140d07030040c1c1021010748444e283c825150703000314070700090708840e190400b4070002e0500514542d0b0001003202d104034900000945400c7c100080c41210304c40c0503c005010b15121019820007080e41030b51050400790113880c52101c81d120640016200d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 830140971 1250 830139721 830139763
    0x40b030a2712120b01020309130f02120a050106080c16110613030b13020a06050a0c231c08150310020c010c020d02010c05270924010509100e03 63
    0x2440551080702d00c40807007940e2481c9454035000b032000e00b01c42e1a851403a00580017084440790501c1c201d244060f03460342240001035200030b03660302d0300203c5e40600e807003001c007180280c2008000c44052280a0061205042ca08018a01429046164860003c1c00b590b551025070340d48062240500503103c00078009000503a4909200d0250703507102c0b51500c0100e400ca4820b000040e4030300841c418401803d940505554041810404242e804d600084450010040184040400324210a410046a03a250055454107403403913240d050800094911044061001e15042c41c803da601c40c0302c0719800040501031000000384d00d00082d042c451030b10003d81c90140080350b4881c0501d41948071200361806c0b83c084a00c00c10f000c0205a00340c407a0305940b4004954240044505480c000700c4401610b140f40300189180340c80340000400d05d1304182c50005020300000c000d000310b0441040303186900c0600342003140c14107d1040000b034043c006c2da0b15032020081d00362222601b03900c04120080039100c0c69600000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 830142221 1250 830140971 830140973
    0xb1e0f070c0201110616180602070b0f0d0c020f0f0a111005120c040518040f022205040813061814061b07030b0105060c070504090201030209031903140316030506150a050915040b030a27 81
    0x150714028200107428034091d15020800301c10f03001807028112070b803010800310540ea4820400070030740c1c0c40101340c00500c501000001017445124202c2445000051708107512241400c0034007048601d89038600c40d0071450701e02404041009499488031003503048507114401c48452104041c10410200c901101a04040600041000100c00340c5a24001c444000e20882d03a01c54040318003992980d01c5400c840c0c0b42130418009a84100302c440c22042010745028030340002121030080c091100070301040380c0e8124040520400c100655650300509007100d12506154080c00307010340b580810b204140c441c5035501256400c590081e01a948958001816a1000303052000440c42140032850100e001825102040134843c00c4441a2801144126000f98000700480c005800406010384250303880386100c490850b4508071078004101c2d06180f50754242c2c464405506001c070440524110031040c05080c07200740110b90041e01625405003034110089954070001c07c00004802c0000e0303020140405980b4240 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 830143471 1250 830142221 830142223
    0x70e1005040f170c0a06050a03150e040b04050d050f09040f091a2203050a0309020307090c021f062d0801090b1e0f070c0201110616180602070b0f0d0c02 67
    0x100c084680a01518400c04601d42005a041070a01946c00030510a1000d040340fa88207500208075200400c61584805490740402031074024200c0d011a00c40f1a03040810007048405e0104185c10515414054242510070a44452038081c51440301d0140380e56041d4640541c10f5600031004058102c42d40307402c01404442c48500c0304a040f1901c2540340c104085c003510030b0340611625400c054055444c1070510715006022409450740c0d06050380d051260f520003241c82101c0d0300c030b10b1a4502140c0c00518035003240c0301103203201d40d44124440380020301c1c018007003211030164458003044101c428002080c080c81c40801d4410054981c014640b01c0d0310309042c2c9020401d8580c000c501035051605000c0c0c90751402c803502c61078441c0480741d034605100a000032800c918081c040c6100f0162050425034040c1e0351042a2324944141100c4005181d0096803000d01100d0700901001c0c1c204464041c50707440a8102800030f56520b580b4450300740305070800940c0500400c1c40380c090740c0004641900521135031801d04002 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 830144721 1250 830143471 830143499
    0x503120c0406090b09010801120501021207090f060203070f1205071a010905060d050a1217041b062a030302160606140303040f0b0c3d05070e1005040f 66
    0x400b000c200380318000f007034000042d400d0740c40c0c03018160764420303a9030300b018403485508100e1070381241e0700c0d0740a0048444000c488440d107442500d546c0da91802580c5018410702e90014581c1c41102590001c06c0820045204200403020749600075500703501e14a00010100d421740300c0e6000c050700150300320200d0014840c9501c82c43e0304071081e503a41803003552154010080380240540006010354130010034040091000c0c40307124066401400d14900320000707210803204020342110308550801444078104c1201c00d041141101810003868100400c1c0807d88074122a251518510002c441c0248401c46c10180300713030120f400020b125034046501c05072914001c0042c3c0000e01404030b408100d140010114200007080e03d080b9540c80d0f03084200d261414407000c80a0748000c1900d030260050040c90b6042008010500e814070302250b042008074004290100c035200181c10580b08064180800c0c018210741c815000e00a050301207400d201e040041c0c0030140c6051086500000f0042d840710400038080d2860614 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 830145971 1250 830144721 830144729
    0x409050703060b090d1115070b090f0a1505100f03080c010524091f0b0d0b0102070303140a0c0605010f06021b10080405190807140f190503120c04 64
    0x180101c5840f80000c000c180542a0340c00d4105121503a4030300480e0307102ca09800c2220000d48842e8140b07240200d00295640003034415191402c9107405c0c80700300c0c0810820030392810b424101600c14003d41d03640e04c0035041a800c84982d10350381c6030301c00b244250010010080c018840c503501c80c1e80d03880d501d117012105500250802040c1d54a00800582401515425403403035180c801050004207101104000d480180500109200d5040410030400707006d0440050003c0c20781c501d04d040e225140384025505441c81082c029045400c680c00c1000002e80002c50065104c28081c01251940c6092030308940c2490f00c0000940400e0400d000000c107100302c0200c04003a2007169003500e03426511040c5800b01a16148942604160301e14520051107105000554005210703030181ca90108644103491a4070327900f26015201800000744000401c020301e66418013132000c8101802070700b0f0520604640b6224440c8410118844820b09802080806e008480c040000d420011400b0708001c6000c40a9070060b000b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 830147221 1250 830145971 830145977
    0x5040c0e0f0306010602121c09050a0221120c0a063e041a040b040902130e09070303030f060f1d010e0108030a0e0a030f150f06060804022404090507 65
    0x81c0c000c2c200461454140c5049400410100c03a48000280d00380d4040c1c4e403402010030715920030140c0c00c411802003d0a95000d9401490f144080b401001841781c0c140105c1c1c040d042c00410500d021140c04901512404400c0882a858201ea0441c0c01d082c800440b034010162440c00464108807280310703c00340c4076111640060101c3c02d040c19000411a40c3c06416110843c030300b40020001e07500a428150f00908a81481d40d06003607440010120a4019801410784d007070700032a4030365070300e0038454090004084140e5108600c1c201038824580320f280d00d010280c10944c40e038050300102541904800c0007407003800580708034a9520601c0304150b014110304554103c886000010303406500a2000d816a010340024514004404805692038200700e5107450308840000000004036800584190590f0300802c22401d6024000c0c016200703c0b08500c0c90340300e2032850314205000b000ea028003129031180c2d040d189400d54002c1c01810000200303801090030b152050000380882c1c0b03030351960452030103001192 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 830148471 1250 830147221 830147239
    0x318080c0f1b030616050c030c0705030105160503160e060c0604121106010e06130519060902130314010e06250903020d080d0b0402040b071406100b1305040c0e 70
    0x1e82d40c00441c04004045a03141e407140700403c0303121a01c00180001031006040480c500758845002c9400d54210245900c1035800104042045041c02c0c015590300c407114a0308100c2a5450f103001525a01001e8444070380d2852440848841e03030f0058211301c0760071000610240c3c40e6003010212990b906802c40c1e0480e100a455688111003038018056a455003500c0b0003d40100d0303003881c5402c0c2140030010203c0307501111007600c54601820398440c103802100c20b101544c0e840e503646081c00080e01e001d0f41c89002100e10400601e095904000605002d680d400703084200d10b451b80040050140088619981c40d038010101407210a4080c00c8459003500102d8858070025813242c90240c0e1814014030029400c08500910034001810b0f000082c15030703815400c000075030303a07140c180458203c2c0c0182e0801c80c526940000c040d4240309502086400c2140d11000034031051414210019010840b841348900321040480c0036102642200701c0c0c00d014000c0540200010102100b005040006480b4518000d0900b6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 830149721 1250 830148471 830148493
    0x2070909021507050a0204092a06090909021206070806010908070e060603040503130b031e1302011112161a04031d0102160f0303030c0518010318080c0f 67
    0xd00801461540040018040054030300072020b00364042802212540556160300380140d64910a54880038001c8200031041000d0000400b03121401600700b54020303140b0201000a10f41c0142c03050103a611556003c91098400d201007280c0c1c10035042a080d842c003a0704200704100343d0250200d80303d29402d0361450b480c40e5803034841c10745036140343c05101011904100043c1d00c81c20420700031a041449282103c1c60320707440b480c50100580040e0420703e1514400420700040d01e071b4200c0c421407d0480303040d45c64824140410300510b644841d07000241841041d0007002c8000c502805460040c0002c41035080d0f583c412251100c507071041c17800045440c44041e0589014502d03d01180c241300d65455158882c81004014403c141030264403c2281144210b540e0f840b40d041c00e0303c200000070710f8148100ca00c0a411450302800b681d030200300020070042d060108500c0d180c140c0031640324404082c00e00095405105a000a86880d1404c0107001030788001110510640c1c00291480c4d61240002680d9501c440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 830150971 1250 830149721 830149739
    0x16021e160f0e01030305090a120f290105120f0714010f0c02030a021302210907080d09091e020307050903160b041403030405040504030c0b06061201060f1103190207 72
    0x31805819803420b490030060000900900c014151480000d05814030940d958460005030008400102c3d5076030070b100034078410841c40e0018441a401d103c0b25031020410380600307843e00c0840510455101d580d0320300d0031201e0040b092140320034180310503090314556a01c1c0c19410074140b015646090000e4003241e45c0d01e0302c2c140308846e11000e0381e50080c06000283c44940070041d9009031541030703492042c0c0c200f0280c2d8007920041d00c60514500b8141c170b03007402417a14040c210b0130180d4031340c0120740a8101d19280742c11540d118034100161800f000d00025400e01400f001c41d590b1004014529040f440002401103040d0000040d040766103003281203030601c405004243c2490410f03032045001c1803209001c04d1100d44000e42c0c00c500020000b40c00c40341016910400101514800d1b142540400d000511030014004800c40c075652208080e14014034000d41da6240b505101014402c003c10070400b030003602101482030505440c00403030728003182d48800008414074200c0d031a81c1140070162107540300006007061 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 830152221 1250 830150971 830150999
    0x804051011030601111c0918050103051513051e061f0b0a0c0b07091802030603060f091c0503150126190e030703111516021e16 56
    0x880400741500b1902c4810040d217070154420700883c540c0c003401c141405101e4004444500308001682c2d504500c41c41d21340789a1141c0103100f624811641800b0041c80483c1000504840e200202c24868072140d48820801f01c9441d02400020241d01811810650840021001442080c0c43c0b60954015440740009d10f0111200c451400b86034402030802003110010030009410080094103050496003001c0d40c962940390400c540340c1d0003081c10790b401440f4100000d00e80141c04040740408620790f0500038002603403000c0c01009801041e12240005040040900400d00c1c44080b02c90303442002c1c01103113400780450300304450503400c40781c400070b40305103d620943e00c16a0800071000d140401c1c0c01d20030130101000500506001051041c03600300340c07460500d80f080131420b5600350051622018646030060400c01e6074040001168402c1c04405030f03200200790a160050198601d13120703841d00d481000d9042c10503c12601c0300380c011044005096010104401d10310031700040c00c0741c1c400307912010340002c869 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 830153471 1250 830152221 830152241
    0x306051501020d0f02160e18030403030c0b041505090c030c03010b0f060d021312033c03110c030d060501080118050c040b0403050313141e060f030708040510 69
    0x40e1088a81c480c201c1d028007070410302c4400c5031040d5241180c2010030502d14861640c4142202c140c7d503410008107144071071601c481c95030110055490103155440080c00700d4032510021f05080701d150046020412400b1222084040107a0309102a2600710301c074544440c0e503020f401d4040d0043e188411103603e41841040320341403000344548070450794a81032081070b80103020070342070141d4204140802c0510b19107d030401003428030007802483d48145001030034080c1c1a100000d801c3c03020b4522008180c0e440941c0244083c642c0c8a4100880301c10008a000c1c07c280300c3d9a120380d50000071042101da002000410f0030700280a014084550346a00442e8040d800748200109204418020200d001d503c0d040380c1e402465030f051050602d52140c44010f4940e21a5200711b034258400514600c045a00030490b000030000310340406442d641381c50215030350564030103060b00041885c0d10101d4090781e600c010b0f69281d40541814644a2078482c1c00605402c4054030280c41e548205843c1002d440c00c0ca00075200c01c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 830154721 1250 830153471 830153473
    0x120f06010207120618150e0319180302060a0903020406050616081615140f010605090103020f0f0d0b01111204050405130609060204050a0602010e0a11060c0604050601030605150102 79
    0x483e18200c02c2001e10b11a407a07040324403a440304030620145006407a020080d43c01411040c84c00c0c1d4001680400b115402d90500c0d06540040c041c419001005244030360500d00075061101581c0c414240480c10b07201d681d000258001004075007103030a558058910010f0728030035078040180c1d03a210010001640070386e43c0c0384443e12401c00c0c41c3d840021b40901c05004159100d10070003c00944507a2200e401c4030f26000a44041d560b40c11051180444411020f6040210890078070303565418000d00901078882c84100f14149a000110102c002024108480740f814003455030684901d00070003074801400600c45114000345202c1c1800c441043c0c00319440d841c2c00c03540490b05181038509814800136040003030041e0b00a441440005001c100c0c2e60080e0046141b1030b10005039554102410000d90740d501e40c05c100c085a14004000824074000140c000344107410a0812449003415000070b1603c0c4200d40b40c1000318001c0d07406000c10894002031681c142c0703125500c14070656903400e80b00740301d95805901241c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 830155971 1250 830154721 830154733
    0xa11030301151817031801030c0f18050402030420061201030b04020a030b0a140c09060319060521011a03190510090c0311121203060301061703120f060102 68
    0x2014050703e01002588603091940890542d100715100b0074910078000e01c4140d400010303802c2c645584846141c0802075003400d0403c85945400d800400c0b618140304800d050101c0805c02151600d504c2c100c100c000c017001403040d50303a8a060f2078120100c8982c840e400030b00b421901176042d2103180c49026151454540e00151007540c2c40d41e11803101284000d0410381c1c00c144420408004213044060707044c45030802e00070100307900e0344030040b2400303800000b0100c1016042c10f1088148a6a0300d404980d0011014207000d10700d41d8002c0725900040c00c0d00d40c0165401000c4000014401c81c001c41a04212517900d4000c00c0700030f4a03040701d4241d42d40c0e240c0754294503410287d103460100010510300300500780100100d84054400c0c142701c03004c80352030250548017140c04080c108100111038844203180f030380a441c045420321401c1000340d41c84000819050040c0d4010002480a031000d5001c000100b0440c118600280e4103150700e19200d0b40240d41700640c5c8410000007405e51900550214000e040c10303801008 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 830157221 1250 830155971 830156009
    0x209090c060703030906090b040b1f06051605010b061306020106080d1704053408010e1903050f030103120f0c0b0c0a0306090e03030f0f040519020301200a11030301 72
    0x2000340303045117085501e15035130410100440c900f0020284a107109490070b40050030001015040c0051200c400e9002100036103003400000d41c40002ea90359004c82d84d007003a4000e941440c055002d41910900b45400c8200414044032807809060220100c54042d0002c001994603598040d4070b84100c007100501050218203003541c040d103109002d5502c98001c2003960480f0185d84132124000ca01b2440c5440c6001e10350040340e501e1950386a00200401c0c1d884005c1000700d500039101c40d11807026141d0300c8c2d11505128544814513001d441203070400c42e000282581d03a5a1a17150407060310049481e0040000c20070240000907500a142c0c41c0015504643c8108540e070311441c2c5405184e000300c00300020941c0312180001c03004424016800000d8940740a191070303180100f00da02d038440004101c124200b00031800c0c4000710300d01144a29003d4003104c10a0061044bd001183c003402c040f42454403000300303520312016004c0802c005451504a141e6610820303c0300700c095103586c0c1c0420b006030325440604140c549 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 830158471 1250 830157221 830157227
    0x905030a03021908060a0509150904060b04060501210b031e0d09080604030801170c04060e0403020c010c200111160e07050a0203180d0b040c05040b0402192a050a0209090c060703 78
    0x90384507649005910703404c1c1d4489d011404504050f07070200c035825245d0000c00f155251902881d40a09820b20349064255030b02c0003500c842140c16409845c2c2186e540e0381e11312070381d1420b00c80900d400710300d10210390b4098482440780b550b4100c804004000a4003000c4081135200001c0342860207190180c1d1955116420705018042c0064109840446c03482000003c20840e203840c01800d00409988159581500d0329050184c1813000b01164641000600d482c1c1c040050162402e00181c21003020b06d90f82c844c00101d00507034409286c01b40c4c90314984640412007015500303501b00d20051b1140d110386000107854000303058403680a801d40c000b02580041c08925030660b400b003070307205c0c03501030050204040c5a020f03103500c0c0d14801c095170181d41342e1075211403d10490070280a410740e41d140c2aa002c51a080044c400c0c02c00c0fa8a90000303000401103030f00841e4651120300d0303020380a66800e0000038202452249000e50360740c0403c0004a000e40c0e45840054503a00010035048840038000e000e4601d0302d0051382c3e080f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 830159721 1250 830158471 830158489
    0x80702010e0a1d15090403141804050118140c090d05031b030307090602210d0603050607020a0201120c0c1403041d0105010e220f0905030a03021908060a05 68
    0x1d0b00103140d040000b580c1d07401505503d0204000740e80324140e60514421641d60400d10b03141e0b01780204040c40c14400020361010b9544404611140c2031512030740d0001420002e0311110600b55440f41c1000300110f00320488410b01c100802405408018013450b5005140600c0342c115140c041c1003105010341030070b0382461640b44000c684507405032880c0a1120070b22a80906184400c1d0f45a54800b10400080a40085011000d48201c0c00140ba960a90f00444000c00920a00b80061201d01041100900700300340c1000700a1a4418159a82842c1c0004001c2d0f079040880320031703400902282e0854001e0300091080805950799517a81d4000c80400c1d80b00c0820a40c1400c0122003107100404c000140c0440000140014020081d01400703654507000c001800d050303541901d688280711002030034030043c002e0044420752920201012418be551000300b2001001100341c00380090000081010722158598000c0c03000d00602601c4181e111141c0714103d500341800c032400e9800141004091142d07207820420 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 830160971 1250 830159721 830159747
    0x601081b071a0604063510060e102312010c031a01140d0c02030f13051003052511011406011115150d02100c050717030906070606050307032004060308070201 69
    0x310740c410b00000d8400307180665032501d20040c00e95403142807048270388000d41c05801c0841c21417910446414450ba25520f80806612030070000b040d250721408607100e000c04e0074480300b41c00d0000c010005007040c024014022020300141030b011058140d003c950300440810b81032110160045092020300c03c0e1001c000d0054040e541c0c00d51000b4042c900c00c581a400040000050481c4200e1026280405000700715068183d42014542040108800d4440c04104410050007c5124800200c2c0710502500e031002d198174400143d508000d108a10750f43d010607810b000e41d10070390f1940000d051000341c180d10f4207103c0b9201100041c1d0940840c8050042c0400c4404e88800240303410348010259000401201d10000e660010070350600181c01404800d128803c02420349050b03c0c2c1c03250006142c010340300d00c10042c0d0188034000210783e11b01440f09503403042d405050094200ca5825031641422103d030070880e656022080030428207007981b8240741c06001c00b01e03544000c0541c20702040c0d44c01900c600d150011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 830162221 1250 830160971 830161049
    0x10602060a0e10051b07080d06050906010c03140415080610020a050604030c080d0e342603040f030c0f06090603021c05180f01060303080601081b071a060406 69
    0x8049075000385c0d00006064280c42a0407856680320145107402c10f95036160b1100c4e106140c440c040107280d9030480121030841d941890810026080d412603200c180c05203800c8500c010104140d55074601341c21640340303809158200c84000020840100c12659800000001800c5811140114002a009510b1107141910542d101c0303040c5564072a10f4000c80b82d0b81c00d209030b5541d00030191a40241d54400d80070741380200c1750802030180700d1304c00304464204040b0f100305500242000408526400740485000c2a96003a00a80b65101c0c1e60b9008401078070381a000588201801c0c1c4400114204260b140200311200c1d500c1d070340b02a82c81c20034140c0c000d4010901c400d072500a580d2001804081d1032191621480c0b08407541d0740c0c070001e1032941c9460520003104c008000e070704d41002072021a0b080f54a00750301040918100c1d1035075a0340e80d11841041d048401b03150180b500800c0840420154500148803065031340c4d015892581c40320100300607102e135445000030a8158442c0c04900d06454804d5500f00c00b0303214 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 830163471 1250 830162221 830162251
    0x170a02070302030d170601080c0318010b0a03052d0c04020705010b0415060e0603010b1213141f150902090102010207170409060501020d0206160e06030f010602060a0e1005 75
    0x74000c0303030500015894840c000750a4005c2100014072142c1d20f15007112003841c2484c85485e00c0c0c20078281074400035001080c0040303140d40c0364042c1b02094002c0b0907401c0014004d840750560700e14105640b044504210030000d00618a0390481030a44d035a046903274010400104100400e500c20f104c0207500840c0c084d03074507540b5501c040586071100c0c01181e482c0c81c5050700c490305140c50144028602001858800d2088501b00300402101c03205a050300c0c1401d09070b410499035600d032082e15040151280200030400360917100002a0103002290303444044118840500d442c960a04000048a08403103c5840000110340144405055940500880201800018503150103611801010744172120903c2102000042c14407810306c040c003600c0010718007070004105508988001a40350900200084074909103103048000b0b403440f4085c0d001c080080a400d061383c9042640c0c10340a108000d004400151103948085140600288100c01d50000c504020340b680700580748541010749005410014004403107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 830164721 1250 830163471 830163473
    0xa0311010305180a0b25080709060e090c300708100302030613020a080304080102041e031505040c0e0a0209010306060921050f030c16090b0a21080a020d0e0d170a020703 74
    0xc601c0c010203280c06d500c40703219a1030b1901004022510a4200d0070800c601c0c400100c2c1d03980c4921402c990041c0c4900070781a140e1044102c141d100490402e22644d4240000c03080b140d401c8245103416000300308a0780c64060307a43e1021805540e1b04032a00c002505a804030300003c03500301940c1c68407864184010070703182e8023560320316000740b80d0b41054102c15030f00d07503000408110802c0c0f1014008826140d04502c080e2061542e1510900003a0807031840640b142c03100000303010481c00d40b009c940505070013801c2940c6820711200900c0250045140030780420301e0514081200f900440d001811903134a4038902d0011051100c001c040d01a42440440e04c41c8246d140344111400d092010300240345c4100001c1c50001d42c10001541c200d051640229105854000a81c0c9c00780c5951b0b03000e0b020f4982c2205d180c500c8208400e0400d030128500d06029041040110f120302c016035011802d402e00c80407941e10f240c801d81c08001084428070280704000d00c105144001c0b003001c1404880584480e1074203005546016940e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 830165971 1250 830164721 830164771
    0x1c030e0a0f17060405031c020408030706060303080a1b050f041d09120909390c0114010e070e01020a0503070302070e071b0308060a050a0311010305180a0b 68
    0x940054071840c207600c0041c0210020310600c0741a418982e80149828206a29807545a1040c4040c0c145c052041880c08071456555070102c500602d80401200d5031140103003000d5006000d039010480000e170300007002c9084c03052503028440c0c10340080040d217585042c0f40c28064405a1040722091a9030f070017800002040d501030080240a5080b5801d048150714100c01c03c00e007001c074408c00c40c00c804030050018910640740d0344180c0303a003e080d155410180340710031104568056a0403001500c075400500c02c644058408502425501d0f624600a2014020002036140440000d0040280c1441490006103030544644d54194040e00d041c0180c80d181c0016880d00c0d0b0855020403016005031b48854402c1203020002d202095005600b460700361035145006041c40d400152041f00a800c102c0300101142c11a80c0c0c18108100400c0c0091520401c0c0741d07607241021191440c200c1290100c1d00e00320000341d45445160401d45880544805800c444440b55184610480060021791808040e030300b1207202040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 830167221 1250 830165971 830165989
    0x10203040605090f0610050907090b0a0c02010201110403151d07031101170c2704021b0106120309090911100c02030f03091e0d080403081e03061c030e 66
    0x10094102040310f251219a031450590b10040010302035002008004d00d07185c1d9880082d065a40460343c8800649034402c0031a036154594114030078444e80007805031040c0fa08800c045c500c00b8401e8000b4010003c020038441d03220f0103540b2003d00703000e0060b0554018442582c1c003000e080284a42443c80702c5182502c51807410045410072034a00d83c14910402e403a68215052540c05001e0304841030051070040081c0c10035000d42c024201440c040328004007000c041c849820f84902d04c015108540b10382c0c40482d0114000507c03034602d841c1d9440d04802159011110940c402c4242d015141c404600385012459001400301c0345060b0b40841c5890120035183d0785264142180c01220b80d90b10b100c140b558010581802145070340f142c0e65a00c200b01000b0203895100e0140710300601c161006051406007404140300b8840410001d0850600003000300070011054040d00b0100002101a8252042d030a1041801c2c4401e0b1005548203004011002c080d540410f441c11541d8400e00e0016044151a004110404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 830168471 1250 830167221 830167223
    0x140601060503072d050304050a141006090c0c03050a0306090c090302030610030302190606030b010e091203010302010c020f0117101d040b04110a0e09011b0c0201021203061201020304 80
    0x1440c00010302107204d50220401d600511250300708007041c18180c51084018040d4805101446008400942030150500101048681004c000010780c2c4100310a141c903408440c020305410740c58600049a10321180c89043c04480c4c1c40d4692400c14049a01d0558158206ca04140101038940701c000c00c4508e014001c81004141d5516a84455800c601c101400c001c0c0060062280a500c01d10810100b80e00007020714242c120b90b22030f52002015810140302074880b5400180200c68032a00001d1b407001440788651251494805030b0f11000007160424142d8030003840040d002170040d000031800341c681a100100744c1d181c1410b0a4210300564464140d654804841d481c0e034079081c482c0104101c1107584006c3e501c403036119030b062500d071801d80e440543c6400e01030809023121000032070401064840c56054406411a0720f07a030440d5240480701d06000e011103001c07002d8103040403c1d2a888903409520b42596540e4140c01030103400384041072001c103d0704024a429032240d80580d070250005001e01c0118021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 830169721 1250 830168471 830168477
    0x105090a090e2b0f03180807051b100831030e01030c02030717092202040518060108070e040b0a030807020315042f10030c08010e010f0b030414060106 66
    0x5440c03801444000c00307041c01038400303a4074040f070b000c15115948441c2d8542007040074240060901c002c5080c41040b0b911901c0010074800001400d41c0c24440c3c0001c581c1034000e4608280c5000440503420300c4034083e1000f180f000032030f4521000c5201d0740c1e00300d0308448865140b1220800b0203112a070b013500d00b56180e03d4007500070400e0401c10103602e590501408080032500d0000b03500e803550903035074200d40f400403050b419030700c05c40499211502d0381c410301c0f4212640c200040300003298400651440095201e4880e10f8410300d1004803c202400501c20114481e4805844850507a42c40c001d055034601c0248000e207510507650010b0032103645d90310b8032010207940107065103500d0705410701c14103144c40101001012142d44003810000041c41c0a03d40d480c8490010381c4194030f21000d1000c142103201c0c1100302580c815942090414055415403001c0c130702c81c8003603480004070b0b661140ca80303020100c06c1c0224080f0742c104446c02d2008921020045802034403c00610102504914245003040802e8010b2400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 830170971 1250 830169721 830169733
    0x4080703080c2103060315010807030227181b090a0207050f0d05130f030f02011b080f0d0b040b01122d05100f0506070f140109030503160503090c0105090a090e 70
    0xa581410040c0c5447e00704412020040c1d9410600c0213076940c046884020700c540f103c4000d007082c070341c01190840d450089040070035440c0c0c00c0510f00c1505168400e852481c4510500240d103580d00e0040400a102080c00750154100c2d03203402240f1006540a00002c0d00c06103d64100803002900822444960385e9003550b61a403602103074050744031440599031018240c806c0d96441031002c1490100c0d01080554242407052140100c030701500018040244068031007540481c2000000c0c002c41d004002c40081082c080000920780070412040750340c1d000400d030001d007400108160034046680700b0340344500c0c000c03548505c04040c3c2e0b2030640e0003000960441c8040f52a00d003849900740380104408080e109000640c0851810f101c081410f5004401000e85107144a5006001b40540103589190f0150a00000d001210090501505035841983c48005403d0030880c2ca0131824070900640c0d0003044100040c0c50001c00b11801101c40e44c114107282544946200c1f80010b0442c2d1030320450350112861030280c10 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 830172221 1250 830170971 830170981
    0x3120209130f0e01140a020705250603050618010b0d0204032f031f0f0f1b1b080324030d08010f0b0c1005220b01050a0b04080703080c2103 61
    0x82d98201c100c074003001c0e8105010612442c4654111700d901c2170302c10700c0050b1185020f041507850b001140c85c801200218505501030300070309101c501341c180d60980c1c5003442151161005e1000d5202d00d100142c6691454000500c9030641c54401015100a00720b0094281a16030301c8100f1440340c1a00b0074011044030032205260784000385200302c0880310031030280c02d01d0700700740c805940300350f5082c404149140e544440c41c1d00860780552180741c02e00f80848080107104441c0e0200211800d800b0704200100d403180c0703440b6001003075200c09004042d52001940b411a1111500f80e0210b082c42c11580455491a09404503d41c80810400031040300340e0343e800344603514007500c02c0d05810072900079810703d00040055800b0721f080010150700d051454800051956100034104514001e941c3e8200390200c0101441010703c4103100741181642d808840d400c80082c1c2e00c2d1001409807280e8030401c90b01d13400a54003080810a00340c080c06440400358207980306030171040b40721048040d48454000020b130001c000c3c09 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 830173471 1250 830172221 830172251
    0x70e0411162603130201021903050d050603010615050309280c050103050408040501110a06020a0f1b0507030312020d0c09090b0a080c0d0828022401030312020913 71
    0x1295003200d84141c0c0c680781c0b01010000d40d80b403100504900040c19644002d00459200304000005c20b030460110101034806031600412543c844100040060b040c9400708905180c10b00c11801102c001c8090340d10b04580c00481034502c0e400040a0314018040e106c00d40301400707680c40403014408400140071303020714014685600d80d0b58107900114100f501e4001040001840d200440b8155030b400d090640c0d40d1100410a5841d002001000070902400418049201a0024002d0a0024054503590315140340e021101030b881c032b034114000c0c01c954001d80007000424000d1822a201d6840c25602501e00601499140f060700c0b5001c0703241c00007a403805410000c00c01244145140901c040b00d1201d0b0700c80c6007000c240d9548000c05d10b040d02c1910305c510840300f0840541c1c00c442c51040f180c9600c442c0034200122585000070858000809030080740d010000000101d240085190011078942890380d09644003103440507200940102101d6003000b00c400b069450111a0f414000c6070700c1c011450240e1801d0074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 830174721 1250 830173471 830173493
    0x9100206070e12011b23070b0109050709030804030807061406180c0903010513020a050d080313020604080604150b030a020a092c06040506010b03010608070e041116 72
    0x44215042a400d101c40035501c0340c0c10000b80001200d44040007811400f0303280c01000100c0810f0320b0300418400d030103203e54100c0300d01c800c1084524076800561440d480038003030620940100030b10700c4004500501041c8041d6200c03582001207071030002c4400792a50344d402a940e00c03541054a1010010480038104000c601a0102406a004500300d00703040030400b2512403000d07010404115010100004c08008103041900e600240040090109040c8402048030248443c1c100b82c0c01091401c1c3e01041c4c60400c071f01034a00a03507108090a18640c6c2d0103080d951a460703540000c9a000750100f000046c1c8020030840c55000728080d405462035584911840022240c10011841c0641c01c03480201000da55189041000c840008901254944c02c1c10900da604651b00087c50310308443c0350403960003407034000031940e11403032040003140c1c02640c07101400c04c031501007442981300180401001825040c450030a9072601a0003030008654a040c0c105440c1d110b8200c140c0c8810f0541080044606120f200100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 830175971 1250 830174721 830174749
    0x22020603130b0705180604060c030e010e1809010b03030c032205040f050603010c09060905130204051c0b22020f1207080a2001020705060310120f0b0a11160606120809 73
    0x80d1b01e1030306141c0380010b010020800703809030602c492081d010310540d0284141010582c00101710b40c034100300b41301545480103020750381401e84c1d61030804052a141000000c40f516188220015400c00c116410061b0a81c084514460303091032503601c001038581c03540e00403a11001071181c40801c403440d2460900d270071076004940d0b11007000004582085400e40020b40e410a883d0141c0b01c9003100b030800c01d21031019200e00d9100039001200441d06100c01204d0383c1e810000144542d4406500d80c807450780515034051800001c480c1c0c0b868104d02c21005241c910348400090a02a0803036044202d526480c50500540c2e50090180d80c2124039444100080d00354105805407a6850000960700c0000000b9a0303510b070f0380600340c00b42000102140e2a100f10b081c588001b40842c6000304418072480c2340c1001c108884410480309440ba00e00422050381c07190007404100107100031060300702240800c0c1000070a1040500743d031800d80d200004140b0400081d514030141d40103d146070341d5821b108007403180d6100c030305003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 830177221 1250 830175971 830175979
    0x10507030e0c0f061801091509032f0402160b01030c08071e0e060d05030304030201200c0a020118081606080106090b0a0302070311011802040522020603130b070518 72
    0x20f4280c25543d00c040a4440c5949030f09454504015040d0040c0e4004a10382c022808403403030043d040034201e078444010415a44580000c0d00c80404c081c10799a001044442c0c0f4a091480030071462656061079405010703401503004124403442c8a81d111102040020380003a40c465002c0502403001400420a14006011000588403141c0c3c4001403811040c00d2806801c580003c040041005542c03034075003008940b904902942c0da2400c0c6441d01078002e105241641c89a681d03030800400d4065000c2c411754040c420720b0000f07861000d840d03900440c0c1042c224010580301c1c2c07807418404226000204200301c050305440044c50709841c20b02601501900050744160200f020131341080c0b040c890350800f0746180c048142009130b12500035190907202c8029528124982e50b203001c1c1e07003060741241785000c00980c03402510704000d5a240e41c1d040c0e10301c44644903c00c040464944a13020f0050520b0001940c4c4424007100209240b1601e0755004007041e0251502d400092000c49c0d2900240c45170003034842142002c807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 830178471 1250 830177221 830177239
    0xd02280e090f0601021c05040504110901081501090f03230c0a1e0924080c280f08030a020d0804030804020108090106081009110303040b1b03040305010507030e0c 71
    0x4040701002014114005188008100c5590080254029445030360105456200c48203030010702581041c40b07034600c5903080481c1000740c841e0207812200d4420069491135207541d00e281c3c880200558000b002d81c10440030036000030300d403603c4440182c041e601c184078a85c0c200c948100200940e24943c443d58810360007041c501e081c540d6640428008071104603080711340030907000c0701010420740d4035482401d016041c40030b11590b0b010101c65000350b805880c0070036030003140c0399001159684c0c0e15581031604012810710a081060682c0780c0441c900c90161003e4520f10f444414011082050354010040c40c0d00200e040c11300280c05200308bd01800c140d01d0001c40701e03e013540b401010410094400307418002d51001181c5040e8080d003180303010300004000c8961015801000400030410b4101c10b80b086280c010003048a4a00031044030308840444000504006058a90001c803120094050b5090b2004010000009600b030080d540306111a03100040d240102051807401e0102c0030004612840b1a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 830179721 1250 830178471 830178497
    0xa030605280303120b040203040b011d07050d020702030c0303040b030403080c071a13140319020c030c01050c1908090a050f01020a03030c03060e01030c240e040504080d0228 76
    0x5a5490307070840ea05460800301000030100d0300401003101001c52034115000004110501804104542c100c4404800003120b09510030500055048141c40350000110300300000a4495481d80282095900040540e425898801e00080c55a4040d0780000300e140004010441819040356504e5440b124925500f841c258040c0d8403021403034142c10340c000c001c2a010010400155140708050310003036100d03828001513480390102d10b50300c1d0402118444640b181641201840c5d201040319000d8000150042c00c1040049005480580000c0c03140d0600e4421026003000d4000092045a5103a029040c5540c2e12100c070700c1404202001034204d14014007840c41c01c11107590340002c0e0060400d03014a800101c2038402c0d0300480c040c00742d50340300c030340c0d49886040044140105801024200c0c0c18940c461102e000c80c00b110340b564004814140408600000c0c4420450704080d0070007944144982159880c14000414110413600104403d0388400c980c04400d441614800e0400688140c603800d10300d000c2928 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 830180971 1250 830179721 830179789
    0x601020a05070621020a0309060518070510110d0806010f030b0603040b0405010b030d0203120a05010f0e1f06021506030c0f0f0406120b0403020d08040f0b1b0a030605 73
    0x2c0d51141404014000380c14510764207200c50071140d691035600b019907071811085402009410440010f58555240c50017148860050400b4400484810805816400d20700310800000182e803c110030705004075050851428842400341000358402501c0b616906d04009000410300d00441114405041c90482020003694982003504e80c855072284003049513542d286080760150511000083c2c25105800725107144d0ba4021014003039000040c03035500c0440d034441c01200d040d01c1b020300c01e07002c401c0461030302070007000c10302c03031000d5070051400103c400841c809800310481074005602c904016081100043c0342c0003280030b0a25007109040b001003da4400d410001102c444100c1805c600c6030001c0c0100781c0311503d0300c2e0400001000e12414038504004141840c0c0441034080b5000c0700103028190002808a00032001640074580000350124000e550395100b4003841809841502d43c561110412100301c401c2070020901a56156004140c051a100a208160300c629031a1b1281a01c3c989410042d43c803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 830182221 1250 830180971 830180983
    0xc1401031e200a0512060a0b071502090a1404050708070f210903030902030d0318151d011b1d010302031909051c08241306030501140601020a05 63
    0x80c0e03072680080d122070100100e40d12030408810840d50070b14003089240600c0d81180103850000e1400704650100d613250002c0001007036840c0696641c4003410b10159000c06c1d0198840841b07420401d00052a0284100000d40c400180d80d200b142c05940c0e04811503064106805015001201030030f1804990802070b0003d440b403030710a8880000c1102100310a02c3d00726003503010041c8080c0d90300c42000300d8440d504006010301800c06090340603100f92803207615428440c1c0700d4500e018180c0316860300507100b15650f00a40780f0000400020031910f80e1803400c4c0030041841741c40c1004409a000061050a03150002405032010381c5940902040c2489501501821051902580c03001d180050f50303640d03084001c01e6015054180352600a2a00e9551800c0140002ea01d102480d50104d01106140046508a0b00c002003103c0b12103041035200100001104625004024900004c00d4520b885400b05e9007001114a13585c03041d98280c0d107441c2038030000c04840341099041a800c0c030107050005031981302e00b90b07181 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 830183471 1250 830182221 830182271
    0x130c0e090702031b0105010303030e0a1a04020d080c0a060b2b030306120312140c16050f0f1e0f03030c0c01020417010203160e030d03021c06030c140103 67
    0xa140400607440d18801d008035103404564004441e195240c01c10101d000f00400d000480101c1d1a060384256051400070745850100ea00010528540d8030320701c40f0103c640c4c4043c0040707030800107100d0882d00049090008d8100c02c03040d5001400521034a041803415a1071520001c1c5c0252140991140c1203e07810701440549461038440003040c00d41450120010010366106001c2c0b031203810403581c105540850f905a4a801c001818000400806450010394505484202c000801080050307a407803140c00c800f00c2d00600641c02e80760702c140103040340c0b404c01441c541c01c003100e5044041c110340c2a140396036003c80b003a20a032004144c3c25601c40405a035a22000c1d084903410000880d00c0502610309404480290800d804c5191003004410b203a21302035041503c00f20101807a4000e40c0a1503841000c502284410080081c811010580010f900952050294005614507207552000e03616550244038001c500c10740003c441585040f0200800032180c15402e410036090070420505d07541c6001030413400c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 830184721 1250 830183471 830183479
    0x71a0106020d0305041b0e011503050f0105120a12050c0615210a050d0815030c100c08070204091a0f0c12060315010e06030f030f0703050a09180605130c0e 68
    0x280c45a05000306c03808804000300758003c009a502245030908031368018101c80c03c85900e03a00c1002d0407001030f001e9407000c55242c401c4030b40c1100104021315200a1103c044d07d0b170041038403600d84283d26480c1d12032071000900804124001104c1d002c0100411001e41c0c40307440350402c140d403000540c2c00160422500c540d0112414400004900100e90a102154125030700c441100c0c580e4402c0381c4040d201d01021100c0158400030804402582d09001c5288030791040020b090310604045940241c1d00400044000e81e5581014401000141c4952044403282409100c0e031803001311000c41c8a58681c000141034100c240da289042c08900580d80c4262030048034ac0c42c01061741d65031a0f00202c1d1404294142d490400345480000050411540c1ca8042c0243c00903800c7d240d20101e42440c03566240700b02060100a454200283e10210340b00e070001c2d0846000510300680303034940d80e0300d44a0b6540f158000a401c020356a040401840c0b40501e01c1652001040e034081c41202114031010308400c4081c0412402 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 830185971 1250 830184721 830184731
    0xc030c0604150e1201020c0a0b09010b0d020405100801060311150a050706020703111501061d0612090109021e010306060c0209061e0a060207050a120510020d060b040803071a0106020d03 81
    0x580e07840742401c0d40e2031300381395000315141e8180c20502591804101c01c20b41720040803a0210707444c00018058020220009000506640060340c24070008000040c900304050150074404240640700f809594001c6005500740a800912041000b40c0000010103000fa01c84007044103622041c0c200007a02c08613a000880140c59107210304083d01d8424090005003200e0042c031000703105020a8001c01416503074542e89540a0f0154071101003844100d080559038070540c02e0010200a5142c4503d80740c1c806d418800208000f0a039a001c540318005490103000c074000640d03d001d2540d640751003080010311042c540244241c000e500424042c910260147d80100c01c080d41c502d420040f95048889030400c06001008502c0da60b01009407125018020188203400d08580044d00410720b140340c44603140c214025014460311031000c2402548203d007004000e41d101d0070001042050701014000a01050700a03696030205442c107445107038446c02001420003000310044c03041c1c60740020400230004103400c000503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 830187221 1250 830185971 830185997
    0xf151b0c09050414010609111c0b0d0302060420010e040b04240501080c031e10090c11101a040c050d0501090603030f090312141b0c030c060415 63
    0x294046840c1c00003180c860800042c481004039070000400d020820300d008000740d544802241041e80c25451200c04443d80501207100c044107081040488000c12000000d60000da0300082202c1d01011841580560010000c100502507000030b01020080444a8404240d6800c00041c1900b10154042d9001d90343e03880700801c1c1d54480360701040750350396000c010781180c2000c3e11300e00300321010301d005190010300d101c404a9014110441074a0155103048a903484d904d01c03c003511072403444010160508403103103420000e051520b608c1b5046149043c0d54420350040b60340c131480c5150090b000107124880b031400c401c0d42020320a072861402c1402080300c4c08507410400d610100d1701c900600c140445018500f600014807807a00380e00410469100307846190503040e141c402a601c0c02c1480c40003a05a40310581600401481403204200102842c000b040c10300d8243c486200b624011745580020a500241c030b03051503454204401e8800c60000c40b440c130314003414035122540c60611001018144a00c2d555044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 830188471 1250 830187221 830187233
    0xc080703050c12010b0406030b0406180203060607240b010f0c030f020a02042307110d2f0a0212010e0c060310030206160614010506030414011d06010f151b 68
    0x101c01d01251482c0c6403c550b120391821156501520624010078900f54103000c050929000341e2049500010013070f2020314108213002e0107588028070103540100100a0b401c009007054130b000001c55620111414141c0c00c003041c480403604040500b6052115061180c00c10f25441140144c030305906240000078001210026454242d054000940c05410010a0440c103c0e9001292051054550070090141c9548500f074404034130200c4049040d40102061003801070103591f00c0182070190030107003080050b52041d0307079a0004491a4010303c50b000340041d6400e524152505900e1708521038001c20051008241c1c1070b6584207800c0c6028012480800050741418410000d000296000f8080030b42d520f0841c83e015550300c400c40b00403102a89001c81c00a010038450840c541a5080074100c40c1c91901c40351070b180d8507660351800d1342d1001d41d01d5042c10a44911204462004901080000d01072941003c2c08245500b8054104640c0405541c0542c540c0c0c5074010410040c1d002c524410380803c0101342000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 830189721 1250 830188471 830188477
    0x30f1308030420130219050f07060b010212071a0a110a1409090925140603101e380c07032012070b031909140604150c080703050c 57
    0xd0b9601c003021240c4007110404d6600188420030340c0c03644000c00b0000700042912280261b41c0b200000c800e090000000140c1194456541488140110ba090f180300d000c19541c2940620301c00c03070b80f04d250307108071079121000601000c0d04094408810b002e5810790704810410750140c411860100030207030b618151906021002c840980c1c00103041503100c1c0c98004813407a682c0611001208804440c2001d0111034022800280151102e596072520f00c0c544d08004c00c02c0e1604094507900b5a640c5034100000c080810005e54950502250040d40c4e10500d081c81d100d11114010404000ca0420340c004001803801c3c505c44056564000e52401d515132080c01e80c4140340c000141c00061a001c2c45241c1100401d0054043c400244001c0360031000e02101d91401c96210b038028403840c045480c060010441c000321500c60480b40000b40800001c00c01c8240c1c5034504120020070001c182d40d0400000d0001b405a00b0491031900c81c880d803000c0c0b00031050440000c00380d43e07000300100101595103010072529080c41040f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 830190971 1250 830189721 830189783
    0x5210d021b06040f051905030403410705010903020a0504020a051605011413031e03140f1008030a1b020105071b0e0901060e0408070309050904030302030f13080304 72
    0x446542c0d24052030b0484503080120802d441e01c1c407031030790161500c01d4010002d0039400d5101028509082ca9075130740041d03410300308a44044040d450147c0100a482c1540c03808050560a00d607900a0320807035404038200b81c1603400860400141e01000e00160b1a0344440c4003c130303801a1401603841b0b0207024225100e00072030303002d45140036400202a044c024150000c05180b10881c02032000c940f902e0402e841425040403004022542500d8002c4290f581405030300400c0209080101d04450750712049003041e142100c04040010480040c881e20021075895200542110070046181105000d03019005041090031003840c00c440541c85011644074405980341a41c0c024040ea08000440c85010006074050207144004a0000c00080800005004440c2258121044601c45484540794000107501030345003981071010241f40060f01e5254040c40c40e00c210302035540182c417402e1610080a010a001d01440315040100c1140c002092038402200d0300642d00c1600c62055100200c4114003a44a090b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 830192221 1250 830190971 830190973
    0xb040e0a150b1806040c08090607080c0d09080c0c0a030305191404091d0106050d23070e0103030e0301060506121b0c03070308060922031e0c05210d021b 67
    0x258001c1e0103c034500c02c0d1402136070100e90034054100c0080007201c1d921811a03c0c03030a158808008652401d024070001034200c081841c02c1c1e86070030804c0c1c0350007060300d10358407046610030000502030100c45028002d0300000d15003112519203291454400400138042e1031012050700301b50b840e4070300c0400c2c02000e1200d4801b211104454480e555401d10308000d00c15206802c01a0554404e4025000c0c01842104262940209808480302140d21181016550341c80303c09c060044401444680b403000f0049034000700500300c1c07840d01640c1185002842c6212444a080c02a814900e00348800d071760b104181d51054940c4007044441e950f8101e2282040a9a1b184520084000040742c4400480c003000a15509005e92140ca800c2c0d2900d0040c030607414000c45080e42101030315150010002c07034000d420685540a8900300407a24002202481d01034280c5110340e0100d50141b80c1d00381040340c01c1c0000190140f0b006600494041511410001442070450308052140c0c0000c4440c0c0c1900f01030264001420244 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 830193471 1250 830192221 830192239
    0xc03140a06140f06041509020d0f050a050925050105160b01140a080a17070c091113090213260a06050109110403050d1206051309060b040e0a150b 64
    0x600860a0b00c1654102e074002420000180c1c1402d00e4001c501c66910391800c10610b862405500c50000d401c4400c000500c1615000d04224803946800382c03a00501015034002000e00f405010b0170b10340100440706507a01454407041d00b011290003001c04c0200c0c6c5080c00c0031039943e00300c00199003030001561001801c96503800c0010400313080d0f003582d51580040643d488210281c903405030303030360710b010490307005240768013544903140440a04401391149500c122421202c0300d4460400c0000c1d00c6840036418040300000ca18921801d140e4607081c0001c01c0c1034002140780001c4040034184000507400340081d581c1c084600d00e82c40e0003802144d070b800e80f80c1010655540d280d00b860040041c04007885034010305400e24200403818a901b10864003166032060003491910064001512481300300e45551440c02d55130103000509032200405070fa00b00e03810100000380000c251401c4000c407007810181600031854141c0c013051a01c000a224015030350800d005070b41460029034298003030410a003809800c0000b030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 830194721 1250 830193471 830193491
    0xd1d0a02150d020a17070e03060412090803040e15010305040b060d080f0a090f08030918150d030522060e01111603051b0301050606090603040201030b03030a02070e090a0c03140a06 79
    0x3941d4028060700c1004901c600b61221b40b8200c0311542c140c0300380381d8940c1220010600250606503a8045000d031b0f814051081076860300047d045070042e42c0401030280b041010882c02c801d119401d0f5040f0303a007d0074100414240354498041002c001070503d401361403401c0c2c0a800b445801000d803101170701c0342c0214954620403000000c2444405201b20040816101000f10f03030ba00c1c0100c203403209400003800540c000340c03846030122003040c000380c03c4811240f0081d02140250702d803403410080d401d00039101d80341d40d219a0500f00700003007005203a4417820150168140b000903801091141503000900e0170000034054401c10130b00b00340d141e45042c1480408142c000040000106000c0361100030074009949100349801814280c0700105c41080d44042c04100700866890030300059500a4011715001509045002c0401e01d1984042c9020001d0381c0405000c01042900d0041d0940c01a4950083c1403400039a54421103201c203e400002c02869a110103d41c0828080048421241d0011030903c000100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 830195971 1250 830194721 830194727
    0xf040e010b03060603030c0303190603020d060209120a05070b0c10060312080901050609060d0302010902090a0f06060c020609060714030a0504060e031c0e150304080d1d0a02150d020a 80
    0x141d00e911500030f0256000242840c036000c420b0b601855501409585142d036005a280055800805900c028940d03c40010001d07881d420f0b80485410700c10390006994138000e00401c00c90001580300c200c8141d01020404000a801040e000126080480c01d1515003210b603810505000d02c030f001c3e09a050b4038242000017071003000080020112a5902c40342c0d440d8039985081400d88004a41d0f00fa08104c101e0086800307802c00384c100c40c01503402407000103464000d9600059965070191800d0724229281c9540c00c2c04c202140c8120801881181803e20300ea020303035804603500d40510445a48180c0000c00c4100038030000c80105808170007420256590380c0800700e80a0141e42081c0101c4002680b1400c0010540c10000f55150600210703103920301c6034010b407000c2211488200e000041d0040400340c851070314502d06001441c0200d1140c080b20342c8900d01000101c046503c02c00764803000304140e103400042e0000100b00c85800b2038064a1003030344000c0f070084050a91081c0100d81140e035200203072207c1c189034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 830197221 1250 830195971 830195981
    0xc21060906021806092d03100b120316030c0312050a2a080f04020303041a0d05060a05060319020f0c0703120215011707050907030f0b010e10030203060a030206040e0108210313020f040e01 82
    0x94221a2006241390b103500450341c1780140629103a1303407a98433251001207406074400c000035910916103101c0c034065020a4a00340d460a50744c1d00d4507a40c554030a002408030440d44049088000d081c3c0e40075007018400001d059010240c0901c503001c055070007281c1591000c0c000c46025040340001c2104ca015180f0441c42c4541c80000c100580c5031424001c60024a03120100d001116070040c115400c2d5101c070f04050483d24502504c1406440d400c03c601d40d1030f01d01d802c01412201020f20094640c403031860130110294820180041d0454100e00c00b00f141c0c407011000705030b040d954100300922010140d0240d0a00e00241a000964415002c00c10420030315456084185200001034050251503c000015500e000b80158034176405007044108410f1288a0741c0595070040c001070107500407a0340c80d001701d0340c1548181c2000725141000001404070040070050511056004110240640030140800d24940005400e010f10440c00711800030555403900e605922560008000700041e07500440c00c503000f00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 830198471 1250 830197221 830197241
    0x1030e1f023f0103020d02010f0309050d0e190f1707120c14101d01170c04170d02070506030403051e0c07120c21060906021806092d0310 60
    0x100d15400030580402901490b0341201e5018119098042440d030065585141c080c2e058801c1580d600300080102d0001c003c92054800c41c1d40721080390340444014031151004203e62642031503c420720400114a62240750403c5807503801400714645d00c8482481d003000320703552028001402c2c5040140911440c3d00d0404110350b103039041c070742c1c0c440b101e1400d00040302c8040c04a50042074405084001c41541914905508541490110050706480407024440e00003501e00104542002c50140000d030805001c10180c0205800104002c2d42100d2000755200001d015941c080c02c00440810205030280701a036264515801e801e403010703a166802807120350800411110b851280303020001c0c059481e40c801013812500035150540070340c01d0103e0490b219040b506030700064120392450b01c1c04200c1610030300c10154895140960744083c5908000208100c10900c98801c8004010a10300c5a4540c1807420395865401c800c1211000004180081d516480140540502440e841000c00711126407155080f0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 830199721 1250 830198471 830198557
    0x30702160801060f0623031302090a09230309040906060801091506140a091119020a02030c0924150c1c030b0901030f1704061d01030e1f02 61
    0x3150388510441d00c100310f52000c2c074031800c02001040e1b117044146c0001c540c00403c0161b0012845400e9010880000040f544007007942d542e40b01c00001c100d0504000000052600d0442018203285030613952030f8886c0701005403195603034112260402061780c004400428000f0700810601402d800d064045002c104000b1040c0e5141020100c3d030030b07200c0c1f0704280c60100054206100385d0708003c694801013400c10940b803000c9034107021030000036070110000d2202884540c05000020118418545440c2e00442c64610907440c0000b0400b0180f80907034554020400c00801c100d440c0d080e1700104101c490641c003444141344c800101002c1a600015683c2c54181800540b105104442c01007182115458030096620a80410041011400004082d00d220340031b19810100d443c3e02d041405500d030b000f6405140401d0320003580c4245460060102e201e03c54003070805110740d04005550075250315802c1c0e42a0305002d04610f07001307402c10055040d141c43d00401c0000c0a030303401100700840072900408a01710b040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 830200971 1250 830199721 830199749
    0x3040c08010c050a0c05030708040b0706061d070305040f0c090621020a0b030406060e04060501050915030304091d01050708060907020f0309010f0e0d11031006031703070216080106 79
    0x5800c0c0c0510904000c0340031030341c070fa5003010079015045035084c840000669262000340251004902860002e0009242841c1000d5440c030b46c1e450294190399280d0701510034808440c0005200d001680c102d581c0c0303c41d1a1500089550301c2e440e1901001d00f812401034600000d00700c02107006203040c1e00c04d00503a01e050703900f0741d46441100c900d02065a40610020341000d2003039420001d0b038070454059600540320314408208507448603204900c400c821142038031b0f82d580303400040000c0c0c01c0c050041c9810041204084028100b81004666644503d100c0d6044140d9107150004528540a030801c62040c9003800074011b07820143c2e0010f100304020b8038814411841003000c501805e0001a4140b80042118065800c0014180064660810100a5406025030b00711071071140d41c2c840c00c2130b0600f14441e11071032032034040601c145468905629003107140c1c5860000107002060222044000d40042030003034a03036995451034128144201620402990b01c0f000d40045010030043d00000e003600e103c0e83e90340da0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 830202221 1250 830200971 830200979
    0xd060f0f0609110a0c0312240509040b0105061305090405030a140a0906050d020910080f010b28170f010e0606190c140a030e09010e06090c031906060503040c 69
    0x2c22940d43c1d8000d001407460030070244080d98068042080f9490083c140032040900f6410404207844811081030000c441d0760030f2000c00004003250311805044283d80c4001103280542d00e240c4440b00c1801114415000811001c85800c41c002504020745006081400f003410710349400703503a0340c1040000381c02050060382c50b207503080401710a65805100c6a41c0301075070245000310696032503103c022240411034003046061100e845155a00c0300300000c0703917a21412440d10108080c1c0820041e00300c03101903803003001040b69114007002404045000e003180c284040c0e5049400f681c6003440c00c0711101d008281d603400c0007800350a03410540d041700c0c000110300d0060f03a10b24082100910a580326880441036000d04420011b10404000309014810746031894204080000107141c08000b6000b200025422441ca01c803c1c101141d8031401001d0b181c0d80c841e400c0c100540007500c1c85800a08290005001200160303113542e00c038004101e00170107075034104140c1c2d4842000401030351049400b500e9150090740005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 830203471 1250 830202221 830202239
    0xb09010b0f10050a180e1806090a03080a1d0609070e070c060510080111040602010609060311152b0b030f1e010617010b0a140d08090d060f0f06 63
    0x40888a0018030608103120344900c2903c054000e42080010040d1580f0000703a400c600d6044400a0300300c00e100e650503891705064282102c0401444d00d881038001c041800020300d000903110860740e0740750806608540d610310314180145809400c60a0490034007101c1c8005400108166000d41034050a54460300e071100c5490f0300081d03094840b140040c0b401c11700ca1000c50219800590007030400d041c075402e0f85a507005241d09640c5000280181001c0010341080411340920551004010b0180248596481d50300e41403010710720800c045000d0880c5507503e80f00c1c1d640d04411200c03500c80b80045940715a0b462064400b010758041e0075480d895160601e080018500001d41220000f6940c00600d007552000c46102c0d1000f00c8445c1c054100e40d21080c0108210840004120034070344404000038480104400b003000140103075000b44003080d00021144030030f4803a020100c0203690801d01c140e980c1c02d2807002044400318031201c0a00034501d040701104000055800418202d4101d180601119444010700 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 830204721 1250 830203471 830203489
    0x1030807140a15050a020d1103180a171b030703020c010306050618011407061b080f0c03070503100b030f01030c080d0e0910080703030e1923031002070b09010b 70
    0x1500210020030320f03c014a0181d0070040d8031244070b6070090309001071103002c1c405590784015002986100442000480c000da0400068207485882c000d0039801c1c0c2603202c1790704031114406100c603a040c00180640405080c10580e20600d1150350803a03076183e4007414004c0d00d070803007102442e000174200070700040c2614105050320880e880d14034410301e1900e51480151120200c054907010340c0700040c042540414014420881007041030341120100800b80c41c3c0092038101c00a100c10301c1c6d4440a014030030f80304860303000c0d0395200719641401e0f0341d41d071604084048581740a0340030f1344901d00c0c00020400e41040d502e4510341201e00c20502d448140c2e17183e85145031140621041c9100003030b4041204a020f00d0f043c3c0c9d042d13400440c030307940d010344403600d49030f0542c10701403503800640128104484288103030401c1d40042e14a40f81c407d070700200c12401c0074495141c0c0c00000c3c00141c041c026032040d0301c40c40d0b03400707104000d07101f014001d04542d616180c0c0740035102540c0c00c0356160f442d9481d299903820f1604183c900e03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 830205971 1250 830204721 830204723
    0x3131805010b090f2404150216360b0a0602030405030c060706090c1203110c09070c0516090b0301060b130513112809030c0506071a01030807140a 64
    0x910350400c1c05680074000004007550f2041d03840100d401c2400300c8500e06140c0c030317030818421062066586042c400d6103160039180c01100c1c1e04561040741c40d8840e0001a12844041e12001006c600d82d0340c880c00221407040403280b5085484014901c500c203009401d036800300c0800340e41aa1031a12050f40c40c03a0980c3c5078000c510400f40c00d030b0030080d100340c07503860710300010b041030361007200d00040ea070081e5258500090015000441003c40031082c2030189034010002000c228001e000908071b9040400104003c01800b601250521510140078020448280609a1f0f00e84091001c43c1c411695400c00e10013601c2a606c01e10701039441c1c0b0001040107400e600c00ca030f80505d003850a509246260006000c054841c14102046080c1e03140040e10030a84558020055002440c00390a4485c40040d001e00c100707031702680c0c11801c1c050f54510400c0040c81a10025040f288101c40442e02c03540f00381401203024489820952031418110b002204000403500600340107400303503880e2401d240142c16400d523200100342d0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 830207221 1250 830205971 830205989
    0x150303021e030a050a0c081605070f0807060c020d060c0e13050c0405090709080102041503060504021204020405060a2601060f06140d0e0109150f09210e030313180501 73
    0xb004010f00e9000e10010180c9965618280e0000d002507281c800700350f0042d0904600c000408624038040c884104584000760280684481e01e441c5040072140e42c0d9562803003400c0900c001043c8410955803801c07600c82406404c01001d1021503003042c0000c000f0030070304d111207200311a90840c0450100c4248500703440360301c543c81954a4103080400700040914000c1c07011003000215400402c80300c070203001600c020500060410f80070162184041e0036101260040d60150348103000d02040921205c0d04250801c1d01a40c1c0026181c0310400890004001c980288070392103041041c2c510301c0c000d80c65021404551030002080160344994028401c82c43d0385c8a038a000443c3c5074403440700da0301c5120003004820301d80000012400e0300c400c8064250340075407400380c41c0000d29109413010b04520f4040c1010382c900762007007040b103d4840d60310580061813201c0a90b000d010b141c40340002c098090304e650700c849403004088a032070b069200031851030344002d4018140d0030b41c40000b5200711900f07140615416a24020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 830208471 1250 830207221 830207227
    0x10030210020c13091106070b24330c07090509060f15040624090f0812090307031a190c141e03070314060d0b01051c06150303021e03 58
    0x3d1151001d0b16007010241c0f2135034410722200145a40f000f00038034134144036041f41c541d14036202c04006944100400c50441171443c810000c2080d9807120300c0907195444548000502c0399a075108001807100d001e48180c440707940040c1d030100030000041d0f440111040650280203669900c10465242d07002a1054501800c1d54004038142413202824000c4011014000040361540d0315041d80c12a40905000b02c0c1046070380000845d1141c0c0000c80c00f014120341d0080104107803410125594078101e1a480701e0413004003051200b4160b030103000d070324010b5802110f4105841c0d00307203140d91529501030702c1d1065117031020400d5071243c2c0c140c0c2c0141c0c03918070030a480b40900710761602900c014a600c200040340c02025003106040c032000c03901000e140114036a50700000c40f6040060701c0c0000d0040504018030030b00b036800c000400504610a81170540e1408c1e0f0b002e140d42100501c3e031158519014400030442414010002203035202007046400300d900a500315021a031101141540c404030744240e055140d0010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 830209721 1250 830208471 830208499
    0x1227120a150225060209181f0b180d0507091413030806010309020105070f0b060a1d04030f0216120b07030e060a0513080d09030207081c121410030210020c 68
    0x1c2c1c0c203203e035001e01071403000d85040d00040c0058401c419400c245070b080840402407004038002c500b207911407141d0403400c4920490404018003118041c2c03c10500092102903044442510303440301030342c501a03200007142e805035180c0c41110003a001c08039a41c011a100e0400007140180c41ca0b2100017102d0700754407404201c0d110400110040c155030a001d90521000700122800500407158852180d802800b5021107030806000304200508254400221001c0d02d507000c09682d0554461690040e0307040c2000c440040003928140c0c10480c01c04140c51102c5000840050b0301c011894a00c0140ba100b1a010080c1d84e42d034900660403141099801d4205500840000d4840e010301d034440e0350001d030300314401c0140c0c800c03a54031270342690f00c08805d82c82045d4a43c44010201501008018094100100580090743d100c0706000003140c00300140104126020b1103080c1940308035840000314034459040b404551408800080d4030120500c0704901860318031200e02c107a54800700d10700c0ca940d50010405400243d034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 830210971 1250 830209721 830209777
    0x90411040801154202070e06120615010207080f1605010809060604110904060311090f060102250f0611060703021c02090f0612181227120a1502 63
    0x144402c040070701c55500c1502401d429400500304003203400c4d0350090008a0810288060b50200500503a0180c440f42400c1c2c00342000c08269140e00021180c1c0c0130356a144c240300103d1a10001d5408030000f401240c0e002420210041040d981110080d078007108804e0b650401107841d10801c131141201c5070405008142203141a4002d8100000251303880c50503c020680041c2c01c0318090750089503242e00701c0503a05c0b02424013a0788207521021a01442c00a841d1410010703466207001400800f4a4030514401d1201c0ca0900d03500354003919200010b24405500c840307006c0c00c21060500c09a14500c40c0c4030010706850b03c6030003218125400b61244030030a2014032000c81c00307500140135290740041c0300c8044080b0b54403103c01521292541c60385003261401c08059501754070158105606081e0403600d05400030482400445480d11460380c1d056170641d02c50140302070340c11014080302c1c1d07100c1011890061a000c0000c0c1e48400f035402102c10a00d0350b103c1b04120001c03031040210001c05421004120016041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 830212221 1250 830210971 830211029
    0x115080c0d0b03070b031003020f03010603230102041203080103021f09140d0807111c170d09020d060606020c010c170a090e010e0417070308061509041104080115 71
    0x4002e004c4a41d940c0e21213040080541045510002188901c5d00030815032804118140403501c095008105050841d1150718541d141c1a445040c0b6034466225070718400c409604031001895450030000403c500740c60b00500d021400e220691140107501520102e168404681d403500035010385490908a1404804400c4405071085440e44100e03170002440c081602000100600381c40750088060068506041001d480c1d40391341e01000c50040d4402136000a56410f004890714644c0310b50023a21501860103402c0607044041e0000d40254514002d0340401107070341c200005460454007510203076101c050044401500303100d0064400300c00000202c1c4040c07241001007800c2c08080c902101c0e425150481c502c5690001e91026040800d121300700014070002e00c40ea00c0c00340b101c8804051802083c2d4800418907040a09034500c50000ea54030543e59080003812a001010040d0003030103508039a0322071044c0c58003c0e05c154007041d42000f40c04020700c50384403103100a44910234410151441800c07a600c2c2e00e06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 830213471 1250 830212221 830212241
    0x423090601080c0c0f0c19210602070f0f0201111506040f02250335150d0309080610050607060b010c30050c0a0609080f120115080c0d 59
    0x503800c0040c050380c2c0005000c85c4190b9080c0d407008049241040e000c0c054549100082240c00015142c0c0901140504003002a0401c100c41c2050841c8403460520030000c0c8a203200041c05a41c2542000d001c01480c3e5002e1a0464000d807601060500c0000f000c0d07445241402c0c007040801e1140c40007503400c0c0f52960040034580d418000050400c108403160301407403c0300c2c0d0340c2007441d2111404244101507000ca0042d100380803400f84c0009404601c0340d01e070076040315a884640030000036400600b0b40c3d10050340e04105050003c0014045503c5810042e0441d1090302444045d406000d0000c1d41150284d91035104480300549498940006925480002e218140c03000d4104205101058085007441c40003509085000104000c0b040c030642c503850050050160309414010103000140c0300c488003080c040002d580100e400301c0c40c0720207031418400ca41305a174580300781c0e804013141010b241980c1902c0641a942c4404ea400a10106445c00b5981c03c0c10171a511240300104000048001503985c00140d102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 830214721 1250 830213471 830213491
    0x403080d1404050609012403020f04150b040e090114130f05060c030a051005011e1202180307090203090a030e013006060c0c0509060a1802042309060108 67
    0x10103146507495058070800e480954860340002e081c06400e01080c4201254a61004004040d10603020085580501c83d440068840c0307007011850f02e43d036120703904848c0c0c011400c189a6040c454a5120080c06500240580603425107181c000410040c2d0511030340c0d10915041114420a503645141a08500700300002156612102c180030400a24100803003401442007480458403032610b1040401141c1300100440c200052213142001607036003002101e00e942074049650024501612020390381c02c0b0910400c50011803002400b90f400f4544096200c201c00f800b02e0545200fa0340e1401154142e000c00e0f2280905a08204e0040740003d0040d800007540d8401030400300340b92107940110720744802148104082c82001e40030201c62040b054400d5201800d642d00301640000405d8550b200c14060a0041174051007020000c26901d94918101d40010300d17100344110590080c281d1488041d4025200301d10380022442c4131162841d4002d100e94009200c003510501013030b503410004580c01c01c0b000c0c01e200d02d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 830215827 1106 830214721 830214731
    0x1801030c0318170f180a05090103171b030d05070206070f08040809031905100b0d110904060f0216020a0905190203091911090c090102030403080d 64
    0x401c40c0c016080290b03e100071403d0008a203d0401541402d8a0100e040502c000940c120008114420707198112a1940c0300248040b0640138080103102c00300300c1c4982510310205401600e000f01046071280d01c0719258420590450f402502d041252076141d0f410401259010006aa0030090b549410740511941c2a4028425500a0070080506038002001c604640c0c0400c40920044011121440f00c1c01d8280352040d52500c1e1401d604840b070781000004845403070104d003034021994010040d02201d01c0d43e0410040d80c240c00600032980ba0f50359441e0905030450a00c0607001001d001031064003169084e00410600c8640303030780850680c0381020308024880c4040b48081d284914603407005a12601c0b0b90807018201441510440008920600d86509220303281b259240c80c41b03400e50381c42e915626482c0c01c0008038451050003a001d607004110400019000308001d2880032418400040c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 830035971 830215827 := by
  have h0 := BRFrame.cov_init 830035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 830035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 830035971 ≤ n) (h2 : n < 830215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
