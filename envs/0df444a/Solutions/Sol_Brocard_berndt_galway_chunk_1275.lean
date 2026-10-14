-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1275
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:07:08.721301+00:00
-- url     : https://prove2.me/submissions/e0afafc1-66bc-4de6-97e8-add7444c8b5a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 229136690 ≤ n < 229316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 229137940 1250 229136690 229136701
    0xb0901290f0301050c03010308091c060f14071202030c0d090b011a030903030103150b10020c09010f0e0604021b15071b0213050c27090709050d0f0f020a0e 68
    0x1042014200450283c2d14000502042da0098411241501e0304980c2c0700365218144800300306c000041c040045040c00f14901c03054100061794100e4080002c0c1040d0902c44280700b0300445040c464151000000b02e15824030749412031105402030f55000b848591000d081c010000d08110948075145421220880e4240060018002c4000b80000e0680c3d2107080c3ca0035171500501d4140d031f038071043c04054030084a20b28031040c1122503411404c00d031180646280d0f01c240c981400a9902d8581024603440b56044e0000412040d8210b140442228a010700020503a1240c0c02800020340c4451100b004d406003480d01d80c11070550410400741c0d500c5401609102510f0200c20040c1441079103a0140002d844c1c000c80302c2c1c0503940c0c4203034811000c2281103000540d03403115002c110441c0b0510342c461055020016885000c0c00031a20307040306c2c3d07070401d840c0d0581e1aa0758400454401e0514040c140d4083d02281d150804610b4029141060f070344030ba0410004030849800041407500a0750200000c0f5900404110 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 229139190 1250 229137940 229137949
    0xf040e07020304081b03030904020f09040b031605010c081605030c0c0a0e07032c07080609060f040b100308031005030d02010510062d030504020901061b0b090129 71
    0x1a0300100e00c0c030155042c24180102d154494010200003604001120141c0a05a41c00e00449560000051085549030182407100c2556040780581c0c611480c6064006403a9081c0802c03507000140b0001a80e560302e41c00c190040d588030040402c1030340d96035428001e80859031004030b8480410b5009600070358075552008003152501c542c46545602940c0303241b40c104280b00c0b180307000d107070844503508010a040860344030400c160b801040c1550300c44180c004420504001c0410650184c80c1424203903180ba41d03640140d965a8074080c0e402c142801500740010340407a1101041c0c80e0009504040071820300c0d07580d100d00105030410344e0051036409060b0b10030031080c5800c00c81d00904400b540000e02c1140703801e80300020055514401c00080c0494446089500c65505060f800103074100e01d400ca09099101c0c0004004120485080f4011140c0c2c50000c140c180c022404080d42882844511141040c5565401c050100c058000f60556484404910218071750b80020340b00e40d0301450015034000303102d10412 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 229140440 1250 229139190 229139219
    0x21110d020c071a0a080c0c030904060e01050a091802010c0335011502120d020f0d0c110a0809040c0509031506131404171c0203190b01080403230f04 65
    0x2440e4060100b03c1c0c10899178201e08643e41c0046528404c5441ea0703901c481e40e6046104482ea41540a032900101044120340d2131003241c1691f00664400b00b685480d07140c54001c40d5507455480c0c1c0751850804d145401503108490b1440001e10915010005130181c2e030300c1600c20001c800c1520300f80300d940c629506882000300703203c60040c080581110a0390741114400b9499a01c010035401c1c00c0d04000a02c4c0071030320310742d80440d5240102d00000384d50f514100c0401c0c00c002c1000d81c2c40702c4002145250003c40b014800208004100e8002d20340b00d14203404001004001c1444120b0032043c0001405450b1003641c09110280b1041c40429155982b440d100c1c00308400b440e001c94011a10529098900c04024001150b140d405580100040a2810b54803520b41e0303c2d00404002d00324180c1500c1b88808a420700d500031b90b000d04814030200c2d41d4002044202000e480e03158043c5400900c04500107000300303101d004a01c3d2071403840580300441d500948125042a4090402d2040c0600002001c011131400755110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 229141690 1250 229140440 229140479
    0x30b01052703030c030c21040f0b0306010e060d0203090c0907090314030c0d021c0c0f0206070c030c06031d0c030d050a120903091521110d020c07 64
    0x9514041e581401c1c1e0180d64101e20542160381e4804511840310b44081046520069015041301c5e1a400c82405599840b0a2103a544030481a903108a01501d011002510251002e8440005400e402c060154465030070007440d482c10083c4a0180c00e172a81c441a005055004850402603601d01d009075056180c00700e041c0402d4026080d0508000312284c1c42080501030344d40c0951a000031030400c50b084c92842c011483c108500b4000c0e40146c18540d6000603000088a103046500030344401880004d9030500c121200c09000e003441244c2100051070000003c0c80d11034406c800101c100c1b500da88406000d42a80d42000001c250754903400600a054400075071081c0c10b8038401029180762100c040794440c00c44e0003078581841004a54042c6a5014403901011209420020000c0507800d060080402043c5c0c0302d1541013000341d081c9400d2092088581c0c170854281300c1035001401e00e101d07460200800500c80960745000382032011026445060008000400090008001c2e10f802e00c0030300114810382190303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 229142940 1250 229141690 229141697
    0x20f09040209061203130602010c120207080409090f1202030901090e160810090c02030a0801061704080a020a0804141c030f0e010c0f061e020a0504050d052407030b01 73
    0xc100069445444456203d242070350b2800200712809a503d02d14020b1290a0b0f1891131406008550294158451104112540c2e92078002c01c0e403804030704080307202e01c00c0040c203284030411041c81034110a404c51504144190410200300308251100641a0807a480043c010b800025100006680c05907046010b4544000040e04508000b03482d80d10380c00a0110100904c07240000180b106085030204038000e00310000c0a201650000d80c000751170341d0115010b000420614400410b0f0b20b84a02810003007030030750b5045205140c03525160b00c01181c2020031000f0841c451501e44030000f40420300680024800c28040c2007020007248108840e502d038800000e0030901d041410705011903441000b2a0040c041414030341c140b0b03002038004840f0f81030303000c0010380100107200b0301c0300030840c00b0391185860540783e80201c0c512144901030442684120000364002800500c0b0502c101d00d4607005039404588500221010302d40b50b1401c06168100058006020001103001c11802580502400d41c0303200092a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 229144190 1250 229142940 229142959
    0x6030c020a06090317040302010204031a01031a060402130806091e1513060905030304050105061c060f142e050105160c0306110c0127140102070816020f 67
    0x9900a40d603441c1d01001400498881c0980f00516008000e0000050080c190690b0b8a28150402034040d50191204130307259080d107802130b00d0305042060480d042e00d034401ca45442c54040030b0000240c158000d8019035100340d0800c190380b000c660203210304005110180c0a455185042c00c8010f003010300055400c9070040310b0950214804001280e940d8041c04003101d5100b140d154118018201ca84040005120a19180141c0d00340300001003c1c0d44250b1180c00280115500d8401780520060106201041c900a020024000030100e070860301c0e900520400008240d040201f00344640380003a58091000c03c124400000106142032607558620511081d4503031591404000230882d00ca922914040400c0c420841c50030000010300c810025a04032109002040c01c1654880c0351f0742c0600310380900d03986000d0001c03040a0b500311081c0030151802c40c20031416039140e164440c020184000e61009950308100b11000644040041c094554683e80881260001d500c14442030700c4001c000d40d8030861484 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 229145440 1250 229144190 229144211
    0x190609030c05151204060e03070804031b0312030e030c16032604030204020706180c090f05150f0a0806010f15050316030e0c0402030a0509070b1611060d0f0b0108010603 74
    0x101100c0301301180c4051102c20b6512400c1141c02448965a849554080000e03601c3c288034007000030b40240c1e400746680b89034a0308002c2c440c585826036803200904002c2c50318058014203000390322030304100e400300e000d4a00d448a0ba203569400c4c44004034944a40141c1004280180184501507400d550815a14070801d15030b51040c110340c1d0301603031100030f108030740019119040184580044443c850810798482156843c0d140019024400d0700500e03002c185022426580c030075030b6002e054001e40070145410602e0f01942d040c400d04000800d80346400c825940d034000381c000320400842d8020f004103c50840c03140c2c00c14540c4917001c010038111104000d414014403130032041d000d0440c410220305041c00602c414040c800c4a081c030018010f196407092002c000c0281c01c82c0c3c1c0e074002e03a105104100a0f43e0516807200848540e50040c102a004240f042c01003181c0051400f142d44407000b00c0041c4480e05183e0b00c203450206403400b1440740c54010b61501c0c100c0800356000f02565003d409103050034400003a05 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 229146690 1250 229145440 229145479
    0x190e09030721170907090b03011806090c2403150305030a081504020715050a051905100302120f1507020d050f190c03080601050f0306010c02190609030c05 68
    0x182402946600c9030340c890840107000790310500f01c80c800c00400c8106881c04424090301c0340320500c212041c1c5030900b07182d900186018818a000155010603071444034113142c072980e00401c2e4890f4102c940c1c0d2801c0c640400c840d40030030640d071041c1254042c03d0362841d15024008054460300d42c80201005400c02060000910100036074607401d90525107011141c0c1d4443c0114004550b0000598019100188140c01d104c0c07001114a46404001c00038000303511010084401c4a1040300c030201d12102d515243c00100e0080d80003942c0112202c1c4081c02450b407640c000072252410b071210aa040e501295aa1134200c1c0180060410040d070030744020503901d807564005c0e48503541f00b0f203200208400004e05160706200392080d500200106c40300071040c003840c2c0e0b0002e8081d00318180e00f900468001800902d19602c03d80c2101c10504000c0719890031611020700540311141a01000c9a1100e00e00e640004d0100e1080c0c41c403c000d00550390760036009031545c01d240f52038900356044039000e00110303115022100d41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 229147940 1250 229146690 229146713
    0x4050d0602090103150807030516050604061107091109030606010804171614010c020f0c030d0507260912011104050f18070210061203020705061305190e090307 70
    0x1080540507980b1061000100c3c000d1205001d594000300003e000032800c46030004000c010381e407183c003c9801010f080c02034030404212074071409500510800c010b101c21407103030601c500e142a942c1c040711070300e035100e101c1130040d2403280d908026060300100304540a850100412904100d081c200807569041c11b840305c00f01a802000800c803000400a074141c114810703880706401a64102400d04840d1070340c54007c0380a06140383c1c640c40184550014100d09144c045a40341810303400074024521000e0110050b10950840c54040c2c903001c207000d00c441100701138984800300001400c0c040940c0c1300720b17200c1085820440c0303c80c09000e50f850030141d0551040002c088800707892080f2070060b802c0c000302001a00c070306412088241e0071140300003848550341d0002030403401c4401c01081803000c80d07207840003a16565140070000d801a0300400c1d0803c03060030300c80010310489604c3c1d500521070381d441c0e2011651030341d02ca40b0390301840c2000c2c1d801044070041c8042d00ca90000400005586840d035503441e41c4040c00c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 229149190 1250 229147940 229147943
    0x121012051203130605040b04050105060108150d080409230705070f06090609120305010306060b0702060711121b0312040803030705090609040903020a1203020c070e041104050f0109060b04050d 84
    0x100000801c401d010f03403030303d01045254071840c207000502d4140740c4070703421010a403802c807032540c24000850500c1d03000743d5035644941c4080b4000c030446131010b010043c900e0040c500907140c04208210128091150b405055640c602c0840f005100d002c0c42c145071902400c0c02040c0504108042c4440d0000901c2e0142021034103400841c0490190228100980103000b4040001d050602000b0040025501900081d041300d0080030b01304580c50b41c0e249031400510400c20700a40c4081e041201c2800150142a1407024620141031001c940c4541e90065240004401c3c046080f059600004281858200008040d030031541c0d9209041030301c0d00e903a8584e04e010280222044c0400801d5204560301c0307100139034100b8100140700f48018805030038080c0d184c511000d41a24039443e5000c4000c02a4044d00848010803031541c02440d0403850134068070b501da1009802250303115441407215029586138050b05019072500c040c0780019515150014040726460390140c014013205000801282c0c1e5019926400e55 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 229150440 1250 229149190 229149223
    0x3100e070e010c0602040506030f1b040b03040b04060915090618080702151c0e0c0907020c1c0501050f0702071205070605030c070b01060e03100608060403180b12101205 74
    0x100031928020010340187c0c0c00040c2c105070b0100c10400103d000700c500900441000501c03199401010380c00e44024440c1b8061004c016008101060014030031112007540070b40a4a000904120a13503602040c120a00740c0c01008181c80c1c04481d010700c030052103400350f100c01f180f6078030741a02200d0ba540c4080f8014074034040d11604507a80d00c070281d010101c0840e5007929030003d88020302c941c0c0d402a000109040380181d8428031880b6004002c50422403926801055250000d2242c0c80c4441c04011003045041e8082008001c01000c04001510901525000707495a18611089181c81a002031800c1d079150301c40402c005018500c1c102090001c501002555480c2c90460340d01d0340c43c15103168551140100c02442d02e200c15000148003680a010704088007811015603070301c0d0503901e075414155a11406162610381202000c47c5c0000d0141e51000700e946803000d90300d414280d8800080031641c10403404e9626420004041103240c60300000390b40058080d2910f11403d00e001922850781d14130340a40f040c01503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 229151690 1250 229150440 229150457
    0xb030115032a09060303020313061d19210209090a03080103200d0f1502090a05040c0309020d03080f070306060f0807021207060b0411090310090c031703100e070e01 72
    0x2d040d10318003100d01a10307510300113114040e0340f490001d540741e000c01074900c00e00280c50404505240301d2030340c1200c820b0320040e85041c130115007420888080851010051946000f92001540c03601d4050500390700200300d00100110305c110f0050040c40240144190314035080100100f0000b0f8000c0261815a60020314203600c206540d204002c1207030049610550001000b140101041440300110f50703003d100718020f056a844440941c020f902a41519503440070b80800300348240d003030a42c401003008c0403500c1c011624004a40100d00542d60703418068000074039a004201825103e54002900124a46000c10030030345000001008022102a4070082140c03850104844510800240d8959080401d1442d62010b29107884801424201001400703035040811401c1d024900c1710a0303d10865010300500b4202c410301000310700810b049241296014100389012001c20240b090014003004000c4180361b0381c0c2020380440020010319844003124145400070480c03000c0e030103007502441c0b071001c1c00c00500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 229152940 1250 229151690 229151753
    0x8010c02120901140705011a010305060a0317121e0f040c030f05100213051c020f1315030b0a0f0b0a140103020c19120201021e0c0a050f010b03011503 66
    0x4502403134420380742c030b40030001c1000c030107001040d480503400e1011105040042030414006401b40d8008490b91907010350100c104002003600e11054555460b03403407102501c0c0840001c080005188180c0c0e40240f4009008403860b035103500c00c0202504440d490f00e0008031442d090340c90110211440c0002041c45e54515040c90400c01d08000840d401c808036213065403185c5911143d010300380c2c543e210b00c074801c1c08800050307070780b061418003415010394015119032111040a81881b0301200943c2000b0481d41e501c80b452188250f01040e410702941c824180d411290400d0311540c001ea40300341030001982c0c0c0c90601c5c0710600d03580b42c0c483c0e9400c40d03111001c105d1115200c000107074024001d070100ca520500807114502d030340b081030381c2840300e8041c495100c0c1e11000c0010036040303080703000320192000034060001038042c00b45000f1001d4000c902101084a401a130303192b540e135080402800e00100507a44070700b1496101c3c502030161a0075070070000c8490071402c4c070b0f5031a01c4030211100c000003040c646d00d609040c0c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 229154190 1250 229152940 229152947
    0x121213080705370213020c0a14060105041d0a0b1b070606060809120418020f120a0b0f060405040b010201090f0503070c090e0a022e0c0c08010c02120901 67
    0x1a00c00360010b09494050b09640307010740358010340c4002012615003e088140240e0b5000302042462074020385040320198085c0c400b103000b0351102984410070f00c2010300042c0001c0901003121a0b90f9140b00141165516000910054416061030407940c645100b4650030003210026902d180d0756001a41c9a0190f10380c881c02c0182402c0b00d40300351140202c0010b0640c284001f41c0c00c100308aa059544840c40f40d654402c126813510071070101514080c1c001c1200700320a00305420307004d0041e8621000146081950000c035041a17204018010a424000e0b04011640341203108000000006840d9002141412400201a0b20480c00f44501c40c50380c41d000c800203a4801d50004409a40c0078405003060041e50405a6403a0801d10040b5200d48010602056103035079409000c0c07880e6210002010380d0451ba50030001c04003010341407525007013912078141c0101d988655031010080c3d8151541d407070081e080e040224031a600b0340c00030750346a03041580c446101540000c620940c02042001107840322041d00040b0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 229155440 1250 229154190 229154197
    0x1511010609022115040e010519020c0604110a0e040317060102070f030b1905040803010314010603021020070603020705010b040207080304020d050c0603180610030201021207060b04090f030212121308 87
    0x41d030494900b91014060450541c4003a00a441410250700365003119594080ae901c600c08401d480b0f0b800200100300000c1e607800310003040001c01446101c80e25114400d280019004030340a8001509508542a40c04280308505070041000c0c07000e0507000703080641d40d007800702091000400d87c40e440000190203040742d410100260400300000e006609150034600c6003070b0403e00068070212810300d40c0d800f01c1f09051140d00101c07035020306000d82003960044141c43e40440900001c007040a00005045091310622041c03001c1c1030641c400507161145400e01a007110540ca040031f006a02c1048280c0120300c903c2c041e00e500a50403240030310185c1d19480e003141081e84c2910901c0d044200401840720921040308020441005401106c0f150303501e40300c01c1e0500b03001c01e01c0701a000d608074a00c020001c4900c0f20084c1162802904046a001c0b00340c8049012500c401205517607003035408030f50908055060049185100d591000e06080190510b154100704202400e20011500070b142d1590404c01004140d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 229156690 1250 229155440 229155481
    0xc0c010e0109060b030607080907030f0f0203070602010501084e071101030f05040c05100905030f030903060c0301060e0f01031e0605030111040b0d02090a15110106090221 75
    0x80c8202c2c0c00600e0074001a005441c0000e00c24019480001d02041c89144170520034600c0d5001040c0080c503548400c6080000c400007900c00a100c03503010009071300c04015070350041c0441d500008140d0314214805050451a07403141c2044480400390300c10645104420924041c1c480c02d140103000c031001e141010a032a00304020204203004610782003405204508100040c40030789041c05104030305d2200e80d00304e8001f1a0024081100081c0901090415603140e061103001810020300700c80d19000001d1908280d07812802c820740c4001a00a65424144200c6c0c0d000300d12194868115418048082d26410000076281d0242000991400c49607119800c025890100c2d46d00d0400f2064100004201038031140c0910b90007503090014056418514404032005c031580018128240121000c940029601507040c8680c8143c1080b80810040301c104072440411501c0e46034026076841c1e00f5074007802c1d18100d9204047c454414400002001d1500019409810002a540c21182c3e160700d00c010041019604 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 229157940 1250 229156690 229156693
    0x309190f06020f010c03020a05070609080f070b041110230708030108060402030f030307020a082119050703150b131509030615060504051009120b0621060c0c010e 71
    0x400086080d004681103a0080d0f07000024440f4542480f819000ea02c00c0c803141c0d1001501c00c00690010640d564080841644507000d05032900c2004041004140c022180aa6440b400346d4240020070044100200002c242550300502281071404054440b140000c00074800c024902491180041d00c03d08980d04141e201c1c08450b10381d61030b00d4405645041c1154200d0092154000560b200c6a000041d00e02c1060554000c110090140e40d61040f1500000300140c0003002d481c0e050b400740f0034503014291080401200d400881d00740350b4600e005950001e0001d01c2810f1030095541404081d420415040e03c122851840e50303441001d5190481510f540e00c000e204030314461490190980c811251800c4034082e00e014864862104900116000c1e248203400200d10108003c0080b1f007049013400c0724a40c118145560020780c3d441840c4000251020100c40e00e80d90f8404000551914170200b010301140b080c0220b031803201c2c14032096903c00c805064150340500200e5404800a005d40180310720540c3e890 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 229159190 1250 229157940 229157969
    0x406111009030c032601060e031507020a02091b0a0c051608030307111507030b0109090203070513120f380a0c08090a080901030f14160201020c030919 66
    0x2c0050001030f40340c104800045504410816800b112800c050588100948401d90f50b4a0885e0035213001c040c012607650180207800a00c0c0d4020809421640f080c001600a0100c00f040761040006000c8028620408085c1c92810300d030044a009040d07510410b1141070420041c900d03404d00e2813504000f080c0d040420048480301180f40e080200c00f460140107180c641040c2e01d041341c0310039916403109103201c00003190180c0005a82a22940211201401c10304080404503140c4038507100fa0782c422903103140800d60000e88514150913042c0900010490b07452401550021a9546010903041c5100a0101800c40c21140580880d0150000031000501352034004e01c03001410906d02110129640d0003c41d01d8075010100c894081c0880d0703481100a40060716030603481d5913594296410101c0140e04169880c01003840803034080c41498480c8104050422070392825550344014114900040011640140400c00010f00c3c008191402402c0846015074941c8003101c032000312003601d84c00f416140c825003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 229160440 1250 229159190 229159193
    0xc010603020102300714070b0405010e011b0b04081902010b040608060603070e070e0d0f14010c12050429040308060306040b01152705090109050105060406111009 71
    0x5512020403640700380c003500e00106003201614003030741400703194688691000035681c003060540c03001003081c103208080b443c403150309032039100e8540a0181c00030304500e0350010302840700d980c02132003907400c0040910b8030051118100d843ca4081490042c0001d1800c5500c01c0030600700400c644c140c03490040d5800000c00302401604009000c0c000c1066403501952802002144003100441c0b25485000060005c05960345401c10010441c00020002c20412030842c0d840c0c0607582d5102902100e65004101102c8644160304100d00da0007180c85003110b0340c1c0c1c903040c0303990219030700403030000184100c1000024041d59141403000c001c1c12103580021151686030131103200e48400800260040340650355040e1950398480600d90385000a40e00035117007152942c0100711124200c0d045280003401131401081121051030750041034184601100c142d021032000a0102e410054071007401052160b1090060f5498000442d0261040340116410402600c21980080030100003903d03003520840340800100d07c65 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 229161690 1250 229160440 229160443
    0x2010e030d021e07020603040b040303090203010515030d0306050a05061e07030804150207020102120a0309211701120602070305070804080318100e010e0d0602040e0901050612030a0f0903080c 84
    0x40783c8406103241c030080c0c031a0610026510010760240030a8956221070300d444040c040010001c030100b6032145007070300058500380942070140720550031500d00c0403291800c141c03c103600d0131900410940742c44002c1040e5a01d0030018400c403802a03d0b80b550b030792a49010314804105080c28400380c071400241d003804040e48a20780b14031072405107c580b400002c0110b03000f0241c1c0315800000e40103038048a00002c0301071003240105081c0350641400104585150364000c3d01000c0c6801d02c400550030501101f143e107400c54804450b10410003c041c1d81c941c1000d6007076000d02a06003000c0c0400c2d45c045004410540104121041ca98101c42e03290307186da0f9104520b50741da81c80842c80c00d044102400707084031141062044401e495030b00781c8440d0b00e4114680c004513444c08a24246079805501c0460141c0810241c0c0300a0000e03100303102c0359020300c0c50704168690a50f203015058600421011190019011000c015030300350711503e00d821501210302040441d1509216040980301600008070a20040740 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 229162940 1250 229161690 229161697
    0x910050f190e100e01030308010302211906050105030106080a0602071b0906060f03090308151507050304050307050a0b19020106090609020711090903090418080301081b27060102010e030d02 83
    0x208524411103d901c52001e400d28180c03e04c40200810a000010302c010b15007841c0d80301c803a180300380b2a020201c0301190300c00d103403a4111031080000728080e1121402d00006004450140106900074060f40d0301e4141d00030755900301c1c9c15015010700d9002c20a039082010900000049a4240c4e114001c495114010070004003801e20800c00031030512a62190814064020401841d404ad2102115595080500303a040c0304000117181d801100004000d0042400e180070300803c03400344008649844c104420303d460040f440d0443d0344581018402002000c0b144000c0720104841c00603100484400440242c0c05004190480e42030b56040c02c0f40030600e81140e902401400b8000e45100310000d01c0c0c4414072007c0c180c1a1003028413600200012121810103401000c1e6208112481d03040441c116203c1d004142c0003038011040030742007040000c40b60b00058181418114045a0744141140d0040d402150700c9101090810341620313140000300d103a0f0007075110410540d408819071703a50b14001c4054100030361 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 229164190 1250 229162940 229162951
    0x110418150509010b0a0f02010b010509101101020307090504050108030309030a1b020913152007030c0f110901140d02040c020c040903030501050307060e030307061508010903030f0b0910050f190e 85
    0x400f4540c01d11190f80c0305014003209c1c0d0380706840da207181541c4901400500c140750410071080c004a41c007844ea100c6000d04c0294400c440381c1d0303542000141064100001d817103069000903d241e000740305220321080044100c8440e000c050821100740d0202114011881d100300e8006540f08039404100304403402a022a50b414502c18100d52400e0403c80c41d41104031441c1840c141c08817a03e9010810000d0a13407401800d0580c002d0810b4071810b9027584e60b29100300c6207d9012261042400010705942c180392501c1400b61081e02441801c040400011503414428028081c0c032594440c203d1000140c001d20440e8061600a0000e1188055504010780600400c0c410320b4002d200340080011038500c508503083c000070004018601d81551034940c00c1c06080c5e56420008092070445c000074108000744141e07010544651400303d414501104030408660344422081c1c09824030348100480445a40304404c00c1d19412510701540079004030103c1c24031364001000c074072114859100072500750300d1000c00d03900c0342 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 229165440 1250 229164190 229164197
    0xc0c08060910061e180e0a1a1006080610110a050c0108011d04170903030c01050601021e15071206030c08071a030f070e040501120303110418150509010b0a 68
    0x25544643c140c0c81d0041d807602070100b981140724103020b410044900d9280c100035175140815030844001e049400c1c2078a00204840f50f400007442a103200880c1c0b001c6560105681030400c10301803405601420032100242a144515003402e0500501c50041542c8038424078144225078240700c1c2450030382d669000b5200b020340421512400040c500c07820000d881caa04e02c83d500c1040d4075403a42e0341c4180d00305000d41c4c0015000c00060000000648080010344046101080049600d00f424000a41000702003131100c602c028021360210b2890034009582c0026245400125601307a54410040f103000e9526508403001c68242000081071010b8220442c0c01d840451060b99802e0703548400c1c1040380d03039810413a00d803540002d00000d07000d41740060044c1c3d40200c1a0500301c0c100c018010001701100c1098101a850030703500054103085c580d00d4814440c03580410b40050380740c0b030300b032035909241d140c04500d11100558480d868455a6110250240010000507001d105156103c0101c0c2150703411607076030207000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 229166690 1250 229165440 229165451
    0x50c1f0e010e190303020318030a05031008010506060703080702070302150403020a0b07050a02091305060a0204080c040c090506090d0602070b06090a0603030c0201080705130608090c0d0b070c0c08060910 89
    0x90403000700f011071000c0b0306680312001118055409401075007001748500b40581805000c682004418401003007442e0b00380e603505940703280c44c001c1210f0b0700c6241d030840e440c241c0c900b404100c1c040e10744d01c0c00c640c146030701801d1612280c4d9541c48200c3c07501c1440d4000075005910460280070fa011100080c00c1178a100b00c6000101340d03110784040c00d184c080c409010b0450351008000301c015062040d44940c0144211401c201d88440a031100343c9003038002d64840c11016070004d01081011402c1c8401c150301072044405100c408203e0b0801008200d040c01b07245c0c402c40c8009045251a502e0b81ea15805260b40508155110b0086041003650620206e072000e00844191000030552941841401c007a41e070315494110641003140c00445403600700405070703000c0c0142044180404620064540000e025a0381d4051444c64140311039801c01d8405c0140b18041c01d203081078403000480b00c0c01003540c4144507141026140030542001070a070103003580035600c2401104140802e015002c2641c0150030400d1105110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 229167940 1250 229166690 229166711
    0x20105120a18050102040f1215020f040911030703060506120f0601020309150d11040f060e061b0c03070f0e180a080315010306050d0f0f050f01060f03060e0c10050c1f0e01 75
    0x20303000300c0c0005040315143c0c601270011081d994060403d103948080c0407800c20703803100d110f5400c0360b510101045010f0008020408800d9042c01902c001d40b400f9100681000041e0907803000032030010780300c041d843c0c81d184000f03800360348204203803a4100001000110030107620003075451181c1c85614005803181c1050841000e50b0b03442d42c120b804890380d1601a0070050f03d044011150090005000340c1d101c0c504010265650f07401c0908500462420320284c001105000c08040c54035942d030b8040f0395140c0c6010fa04100c034520204460380c5c001b60414008115840500c8028104076800074000d002250102c240710356282e034800701d40d40b40780003038a0402603192103208004280f1000d684c001c06071301e07030f05600c4d000040203542036400e100d00c18001ca6952060480c106400e580b0a6000458041940c070810814000c07180100d81d04050120081d04240e0185004200c1e948100503030304d001e02030009400c0201c8038007044038620a99000003070030780ca101c403000c041016220b00c1030091300d81c0d070030100d41c541d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 229169190 1250 229167940 229167959
    0x60601110f10050906060d02010507062007110301270204090c0504140109060b13050d0c05060d0c0210090201090e0711030324040506100c080d0515010f0c020105120a18050102040f 79
    0x70a041c8c1c0584070325007031814554482003c0c24000300140c655400b038084094500310f0085c06080300c2446170382801014072115080c03508484081c3e0050300644a50884020381c60214608010b00c2d60301034a02140b050001c4c01c000c0c0d009052688080d800c0744c580603203081e0b00106868031a0607944420014481d8035900d404521107405040c0000070034201000c020483c40c601503040b5000c6500c110710100e4100d03a40c50018560342c100164070b10b4125100e114501c2600c2d8144100c140b41f1001c1182000b00c64103a400080001c200b600400620752560310200781d8042c000c01c0c8020103602504101c0f0354030320308800700203070880001201940c10400c440300402c5134642401458841e6030081c010f00d160152050307044030540c207821700c182c6519004103c8058424001d015252041541e07114402103202118001002c10445400001c108510002c1d40300040c0c2c1c0c00700460f580d001d00d41e1024051a110001014014401c01200118031001d5501301c80c1040010b40152040740c007104d089400903036480c040c0780e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 229170440 1250 229169190 229169209
    0x9060806060f0d150905060a0b040305190f060203040c0509010905190c0e0316060e0a0605070204020f160f06110406020307020d050712030305150a0503060601110f1005090606 77
    0x7a4030000a1000800e08185000606460b541e0716501082101c59100442400811a081004003036218400c104007401d110b5030b100000c02040c0c00f00e85c0342c54a9502e440d500c44103141070111124200c041c0307000a002c114120050000e070402c504664070305182c0f8101c503004190b44a800d0007020b19100020301211184542440b80c0600560400c0c5031841d40700d41801082103106001c2402401041141280c030b0804c800000c810000e2000901d803401e0040203840d501840d48a24070031491030b031091100907032260545c3d9040f507040d41d01580b901184a0100c405010b000c0d00700d03150596116111050118000850200c1c5004000030010fa2980030200041403090f802840c2c050303801040000014100b034044d107041d49004100b40c0b00c407561508500340d44542c88000607000281c48030b06102d440c90307514031403c840745421110302c00194174150100c2e03200c01e4000d084905200718070b00b65004a41c001c0c410300d0410f5aa18051390440358100c1c1032000107200a4801248610600b4001109804d01d180075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 229171690 1250 229170440 229170451
    0xf0d020603062b081b010207020a031e060c031407050a020712020301020705030a051e070c180e0304080a06060807060c0f080c03030112060f151715070503010303090608 74
    0x41d00d190780704401d024610302601c41100903202240d01110102c4615441041e0040c0f0a515480c3d49694048150820303899030722008401e03074030420551005a60300818241202d0348071440b01c00c000030305511718041400451028241c1418080100b50051b856448000b0700c0129840150060b2038600080701c0f03038010102e884000d41d119520a000c2054016807902007103100800152408001d40d85850450b0401c070450f0000c40d00c0410368800c0214030111145034803102c0302c030450603c40b0b507855890150407d40f0512088546a08210804441f0303900842125007200d0203c1e076440c0d542c0d218140e42c5242c104800d4030b80c0c0d8545000801c0c9240c000c600b402c200c480315074a01580b8045500c0d084011001d10504551070711040001810001043c40a580204500090f00f042e0039146d042034401d55035100c8061b410036240108441030b0110015002c41525105000388849811000260b80ba100c8016070300d4248000c4041008240c551200017181a00d10907030320704800036a200000e55000005560 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 229172940 1250 229171690 229171699
    0x4030c270b22090606090b1201090309060c05012d0b06090303030a0e071a03010f080303280e1b12030c060c0d09080d051b180d05160b07020f0d02 64
    0x40c92444100d204240d820342191603400180c010030682d80c010807150780741d1000c0112a210b01c005e2880c8c0c40d16510420810b43c1150003402603d0069500078000c40f443c0c05403000b88004007600c83d05128003503100f90410304020395a055044c002c040c0c210301c0903040c0080e01c2d134040e0130300801c9400e034145941581c2da1340c2c401500850540d26055084030242a89608281c0035110f00b910000d4040c034052025014942c01416140d569410401030f5003803802c644e000a00c60b40e004109000c01043c43e9400c6400e106411900c40b8511043c010018014002d0810401d515100e0390907045843d0840c1c20b03070050480c100b1a01500d1042c60a50304585034001d021071500e840c0c0200000a0040d4034a60041040c048282c000040f002495501c10071307540c10030f4528222080d641c1c030070410a2000f0401501507110115000360a0511140508404803061410b10303002d9214a2441000c219040014a403180c08070b55039680d0340341c0c50b0700d0000e10a4108071426446035182c3d40c01c0580e01d08000d003071030f20055001741 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 229174190 1250 229172940 229172959
    0x1060c050307080a1103040603020d0f062402011508010608010b01020c0901090e0a080309030a270b070c0801180c0f0b030c070201170901020909060a1d0c04030c270b 73
    0x1c43e2180d041d00580344490500c0342d04100040709010a01c004d001929071a200140c940c00c5000b220012070300e030913902c1641c0d280b500205001814442c5641c0320000350800040e001e00005510072405402c1c00b403800c03205810465000304640a043d00b200f410f8035030030b41c0204805110240120b9546180482007901310f64024014030072030450b904112584540841120005886c1c1c7d0344011303440c0e2084841034080d80012a2501c03c080e80001001c891240c0e0a040310f0703001c4820051411800007a20030101a43e0b00050a07000f000780c895401c100601d203100003000f189811b645980d84011032500121a400c0030500c2c04101441c6c1407641c1d60640d02c07054203142c00c1d581c1e01039004040d03600c022010b0b41484140d0098a05540203030341e0b820700c40c82c400e600168a601202050000300e10016002900c102c1c1000020b1000b01400004143c001c16860f542c00c0882d29001c0e111143d42c80742d500040d00c000182000030500d00d041d01c410314410b410103032955160280c004043c2c000c032600e0400141c2d10155a1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 229175440 1250 229174190 229174193
    0x12020703091505040506161e080a0507050f01060308120108070b0405010f030902090c1801020601080303070309030908030f030114090412110c0406080c0a0806072312180601060c050307 81
    0x90b61506a901490912a18043d2214000342c0c85801c80d00d54984000c2c40070b41036038100101c040e99041c80c0084180d40382600c1429036500060750162005160410201190840c1405403c000c1107243d40c0001c8001c0001e42c2d00d9080643d4140d104044550046030490000102c40c88001090812510801d43d100e040500b010011540c400082964508254503a8225000341c1d840403c070f180580c05410f9000e40d40c03101c0003854405d841340440400d055405c648010004108084102c0307600806600c0e00081c1d1141501d0140d0340c0700c1491300038201034403020030500c0c4c0d2141b00d0740007503058911030498009603d20f1202040380c40d40c0102ea00034460861007814a90a5000c0c4807001c1070340c83d040013590301c5240c00c0300c046402caa0070f13580485071541c0004101051070401c025020041c01006025104500e041f12025008180c00ca08055204c040f0781004207a0032003100130340d21501d60040c071000450900300f00e054005104241103004e44c0c0520000042c50901900759400c906030f02c10060b45c14880039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 229176690 1250 229175440 229175459
    0x2030c10181a01092f070213021c15080a0605101203030c0e0d0203030d090302010e0f01060509070e011b0f060c050a08090c180a060506210c07080d050402040b0306161202070309 78
    0x40408076049400040d5500800c9801d0020b000004080300d1400c2a5042285590ac169005003082c47c2c0d000549034010b101c500008110080060780104005c28543c4a04400503500c1c010366106401d911a41c0503d1401c05905130000c51440b216035840c070326406071303040800204180ca81c0009500d6802040020b910710303115040b03e02c040703000740000610210740ca252282403039050801074003280d40d624001d010346c0c5003085070590012040e19140d40314154500010b400044240c54030180501c01080718401c01003070304681e41c40e06510480c144858000860094140c1c3c03c5010f0f0080494800c000103910400d0009140100260040214480811142d20200d890001511025a840c0c40f10130208081d2502401440036446060204000f5650710070580051200640400980c40c4204400400700740c081c4166481c1000a050002c1c0c240c40300e20009000305200b043c03090300340c0034003010400300705040d031480c8010513020340f28400b0000040041c04200c1c468014003c0103e2009182032285000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 229177940 1250 229176690 229176697
    0x9060427020316180e0907051201052e08071206052523031f06021606080604090b04050102030603010605060313060c1b0b07090602030c10181a01092f 66
    0x10300c104c01c4405689692030780340c1d501000c03241540380b40e211250800c524209541d1801610300743c80020040c40c10a01e111490803031200c000c9401c51020380c0740e65000300d54602e80001c01414004d0459282a6803080c0080140c001c122094491515020000d950500d101015074401d0340d03083c8600c0c0008840390810b4821100c1000c1076900310000045010900e80b6030300c021401898400c55002440031040258441030000b034203e0300c1150000c0101c0c07500e10604400b50b13800d0f40c55a04080c0016509c2402160040003210006081e4002c224244001d000c0194004d5005039019002440b2098840c4188092803001b070350410303205580303001c080c0080341880e44041400d140f40d283c500708414540d01509112104000140e8002840340207008032150002c24100041045001440c1492105802d00c1e464040c0c0e1500710180d942c58035101d0300d8116a04d022880341e29840002582d900182140c41c1c09555000d000d4044418030b0703c032410311b41d99080c50600301c0c100100801051044000b0503940c644c3d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 229179190 1250 229177940 229177967
    0x209010302091e13050706090b030a110909150112090b0a09060b03030f0d0507080c1b1f0203040b0f2401021009030e0f01090815090309060427020316 66
    0x8a040040c40b00001603620030f40c019140c25491400300c1545003080b07418000140c0c00740041c0301101204001852001d41980d0f888100103c1c0018030304240b02d100f106500c40e000d003156008001e00c0804c400d00c210a0820003a600007170360361103240106160600f003103c50490002e040c0400d964005004003416410000040d441a900801c03a03070040c2c00447c0ca1078000d039010b000d289030b01140c0d0740701c60341082c400d241c0d120385d051810b80394608000c050b01a861040c070824020004004641010600c800c20902960b80106810f400c2a5028240901c00035082510105c68802c0c0300d0001c50701c03003100c041c0102e01070b00700c1500f901624400c00d2017041900c200705e0001810350180310f294a143c6459446500d101d03d01035121614035a00c050100110181e00d2407100303041c40301ca000103221f8984000340811200e03003603210318025902d40120452030350040500c0726a0020340054003045050f001402101d084400c0051012410184030002013a8001241c0f007a08580c0b0141c90102e000380b00d502c0004454 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 229180440 1250 229179190 229179211
    0x7020313170a0501060609080606150a182d1208120a1118100201050c0a0c1a0406020c0709020a050a031a030105181212010501080403120c080403110a020901030209 72
    0x2c60181c1d80e010b00f541c0721680001d0200b0f41a11040102807014041103034030a20494803505220000b11040045004d8200008100500c400c50f4001d82401244035074050002036071008281d20300d902000b450030362516104110801e0440c80056002200c07800d440c10258004081810001030052184403514010700c840b0240e070301d50205c0c40460408a00030821845103a00c0d83e003805c5580e0041c400b2103940c0541c1c1104580c9406c080080b1a404c10068401681003817800140103000c45c10034005201c4070f20035600092255000f404100700c80340e4010980c07101c481054948865540444104900076542c41c200450b80400140c11000e102c9c0d440241100448050485511060404a4210b510460b000070011006501da9000304208011003140c2c11781ea12030241c500101017914450400041c801da506211791000030900f0117000390203c0e1038200d4034034020412b40d140e900c001004e191065406030042140200f004205001c0424081d82e11074000d0050703059640b81d40e0a02204c1c05c0002c248413000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 229181690 1250 229180440 229180453
    0x1806011d0306070807230d0b0609090a0515210c18222108010f0302060f0c011d0a0b010501080103110f0102033108010b090a0903120617060702031317 66
    0xc5070050010041c8690a9003146e40c0c51706034510060040310200100301d440f500040c080480e00303030340340d40a140d403041100d440401d0710740b280440a24810002e000040d03200000c8045d0111111130031701e172a03510024140444550342405000e015040c4140c15101c4154403031000090074000501c44014409101040e40b0b00b055007075920f0b0907490b00780d240e44184c1c5541d4216001062660302c0748015024100c100c0049012900c1e55002a4071885448502c1c0d400c80c41c040350f441e10b540d9083d401009268415544501c1c0301e240701c0d546d50784500304030204030b65444074400007050951080140c24141c0e940315a24140310b03141501040400b400c002143d50441c07104212a00c0a240c0024030280681c10f100980044200e04044050a901740e81c1c004201c0303603140c5071141070b407980c070203a920f50000207030030300003c107103105007821203e8403100000d40500b00c1c03c240d000070b04284580e0900d43d13200245010744044d515440c0d81207841c1e104001d5007803c2900c04034002d210707070480d501085482460800c1264003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 229182940 1250 229181690 229181717
    0x40f050a080c06100f0602072d0807061101090c05010809070902040803090102010501051c03080a151203110624120706030203180c01120b040b1806011d0306070807 72
    0x40d030b03034000c51a0801e2a00094280071940b0040c00720800940041c1e9202070030036041910095a442c1c0034071440100d205014280c070807040880b51142200c2d8a0040b10064854450030703055994202c0d48509000280c091803a82003481d030612941034007960141007409560314060045610000150810901d0f02911b80006040b6110348020001400d06d01d01a64a4086000c0003a00b1206c050740702c20b010b5400d050300a00c0c00318811403800f00050b81402e25075150b071a000e40d040c0040c0ba0303100d04040d03002c00c000340100c1d02c004410a580c1245105e42d450052038044030503850b40f100030075281c6802d080d00d40c41c0034000e100c18400180307680e400c002d8101c20300c40211120182c6081500e501c4540070036400810700020b03580340110520552020b030300a00141d10405c0009041c0a000e035001c43c0004c0c0d5070044000d540d515078006c1d414501000b44240c00000c8034820fa000244c10555000e0b0206013207a80d8002c01000c80d440491a002004000c1c0c12140d813800b0041c2c55601d0010000e034100b0000c40701295 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 229184190 1250 229182940 229182953
    0xa03080c010e1f0c260c0408010e06010302280e2d0609060105070809040228020607180302011403090325051513020f040209040908130608040308040f050a 68
    0x3140d680022402d90aa4404064000803919000607610410441818481d200590803280c903240702104c0c011740c9001e555101c284001d900451700110419420f1980c145e00721403000030f410341030320700031650159120032a08240d00300c07902e10800e28540460b0784604000403040f254105920035211100c801804120703400c112400604100481d45a1010b1001e00c000707810003c000b180e00c0709080c202285480900d4a40c0c2d0118002c103500903204a800040c1564901211454841082c5034866070060003581458080c1d1180c0d02105d00744c0c00500076030344d4801000008a01601181d40684681094211324180e0040b2980000c0541340548400c00940c0780c200500003440c03042000300072440042c03d404c0e14140b0304000410103195240c807045028446c544610110302400503504840100d00304071000049000390003000c1c607627984a46406000c50603c0a84e01c01850905824008202d54603211030302558903030800c0e28003800140190300003030300048588280c0030806001d44100c0e031114145a5990 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 229185440 1250 229184190 229184203
    0xc010c02011b08040906050405190c0e04020c01020c0c1005250b010314010f0b010e090403020f030a030c09050d030f08100b071a090a2118060e09010806060a03080c010e 74
    0x1203c202c070700020100300d000200e00c00c0801070101240e0500950800c5028442c1c10700280e140084403580d9001c1c0c81c48864010780c0c040342c107244094001d540301c5644100300c034001d4000050020301c42c004c0050190003032a045205a051005035142c0500308140741190100c1211020080502c518140c0e03c9800030900d201603507402140b0454540810381400102c071800d403200715000c035041d20700382141c0891030780e000612043c40305019100f042c010360380c904080b445d05030f00140c40f0800e804001203203103038550716812404103034032540c0302c0c41200c980d10414005c0d9107408003005000a1841c40d95040341d0b41c8a541c0702e5820050761046240c00326240e65011000c0d90007042c08840001c98500d40c0b01d086031201c3e0040c7c0c1e20000020207400c18410365280d05000018440c04880350703c00b1006940c40352400b900e19140f1000000c03540003030342c41c0c4540c03000d49030400107212a48900c550800010308080300045042c070440029180b0084039203940d0311156990400382501c038055407104034040041800f000700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229186690 1250 229185440 229185443
    0xa05070c080c01090609051c020310060e07020d0809030906090604150e010905060c0618010608010501080c0307151409010c0f24060b03060f0102010e0d02160501050c0c010c02011b 79
    0x54905908504005818071480743d1080c42804446c41c81000303281d076107102c2c200c0084010351800d0307021180340c03000074140303032170b1400182d40f0034607040000c02c000c0e2828100341d00c40e880603000c0341c061509419055441ca001210980500c1d1300c00c101034101d90030540081c05120f00013030a154201503c1f0812480c00c40072500d00d0f8000034030b290341d01c1c6205607030024100c1d004290642c3c28a1500e18220516a00c85c0801808150031120070402911405000d501880040190500810140d6100c22301d980d250b180705c41e0762500c40c0c0324403000400c042c7c0d00706520b130310405103d480704034254611668800181c1c000450075818441805203c1d00807400418968242a100340345408003514404110100b0009200c05a90b11610b0100b0074440b103c41582140c0e00000d0485161081902c40c9004034054143d426103400b83e40174058051194a0300014102c02148040f0b94000f00b007611180112aa402071007035041080e2b01018820b1000d50042c070484501c18018900024410702c41001d0754400c1d24030000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 229187940 1250 229186690 229186693
    0x1d060d0206130b0d05130b07030506150412020306061915021c0302031b180409050a0c080a0c080a080904021309060605040807050316031401231f0506030109020a05070c08 75
    0x180c50706050407030f1140c5c81e0320180d1080a12000300a41e00d03400945c80d0300400b10400e041e80d84012a1035540c1b0a40850b00d03052004031206d64958544048903031035907044204a000e07201d9400415080e10b02084641c0551080d00d00f101d24292070900701000341c46003480610258051100b590a102c00354909040d60710440ba1009640da04203d600c1d00b00700c0140151100c20480c0c00d00c04255943e150b0310f00c4c01c3d85140100e0317011502c1d0407182011803c260788200014004040204005030900d030200d01c0300401c2e801008510707092a500c20b0059142c400364240240500810031101e9510701c0c041d03001d003842e40904d05a019040b51501f81801c1211091b400943c0440c4000c5070401ca044006c03c01440a002d0903409403070507400b1000761105422041c040107100e00d40f0b06c04815203040095101c0b00580d040c503e00744007072042c0a24540d04003c810b40e805540720036480c14042001d01a048080210340010b4030752031840e0302e464042c00081d04500060403c100b400c1142c3c5010404600f04540601141d80 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 229189190 1250 229187940 229187947
    0x3031903091a1e07091202010915210e06060402031906080f012307110307050303010f0e010b07210207030c030b0a0513050a030e01030f0f090203071d060d0206130b 72
    0x40941000600c0f8400356408151003810010110b40c08000001200e03400e0400101c04100d610059134105166042012480d003150316515019900c0a0220450a102c3c0c0104801e94661800d81c03045c1c3d200c1c03c1243d51181e020401180c4142010350046034403904604035001c400c210030580380c1c143c072020350201c040ca80c4885030900d40b07440280302d02c4600c600f51441180c0204510f8520044880c001402002481001185a00c0c0302c0c8042c8102c1cae4800b40d1180c01d99941c0d41e10381072450101c1c50240181101d00504200110303140c2610422512031981000088501c112110611448030401d00080c0c000c40c0541d5800100142ca50072417000036612951401c0c44500c0e00a010f41e045450040811440c40313002e24040c40881e8011850418060701454415080800100164042c1c41e186031407510007403911a411142e0b82007035000200182c0f00300c09403a42d00f59503c4801c103001c0b0b981405620b0140c0301e00041407003460414034241002d03202070402410100f02c20101230302035403a584014255103001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 229190440 1250 229189190 229189201
    0x10507110c040e06040b10270c05160b09010b030709090203010b0d0f0b0c04050604080c010f020303010506040e040606030203031c0501060c120e010306090204080703030311030603031903091a 84
    0x10320200c800341400b51410403844103d00d03809030f614130703002d4005001101c0c41c1c0e002c10704103030840d04e5000c05008204000d044400d00d1854065aa600408003016550b25191490701c0482c8242d046415201081e40380142000f0640c070341d40992800034145a140d990798038008800e0342ca05010310b000070300102e000060807490b180185401e403403000801e14810101c0040c10000501c079444021103050f08805a1111551004400f60240c8505d8018541c001c0e000314000825000c0000c2680e2000000c2c0c1c2d07101460740301c2040613650380c00207001c2d282e40010188010701040c41d40f803a040380c0c46402520045622079407600420300f55802080e40c801c140605075090b514420036401003d004110758a0000203064172501c1c0c016280e02c26460780790810464000c1c9200300c0c0e100f900a070010b811040000c40d035075075031004c41c0c0f80d44801d9484218040790425040d0300b44d44e204401039a1080c48040c020b10715000205102c0d42e00895041c004405040d900e10b45880491405400100d02c0304806601900b40e0910 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 229191690 1250 229190440 229190443
    0x140901171e01150801062105190f06260102090a24020d050a0c0221030a020c04022505031b010c0801080313031b080604061d12090609040e01050711 65
    0x5800c040b0303e00c04012031084403e548946028111607903451b100d00d244070b032600009000e403405030341c82e1480741c144410301c104407000b11075100101c5842c0c4070030000ca030f00510150b8140da803680b00741c0303070095003295025044c1d601d100c8214524440300c00c001131400604200040006103a508a043e1002040c074140034080882844007100c05070600082c0402000307580c1c000d020b4419403480c3c40801200310440000c5480325091740c820041042c100060440c0c000360742984d41e400402681e4014450060348841781e007841d100700da0002600d0542070b61031100c4140c5500139060b8201d01180e80b848200b1404800b140091082d2030301a51980010410000480006140c101c040c2c10401c060b03002002455014894404104200e923440009554404008004110170403104e40c0501418020700c0208030800071030354410340707040c2062040c00b0442584030340b10302c1c2d94068541d01038046000c100400c5180386040b8004d810035460050010682400e0000d01074203485081e00d4107400710301030f240a140c904c10b0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 229192940 1250 229191690 229191751
    0x513030c020105031308161e05060c0d0f020a030f06140f151e2706030f0613090c1e0602070b09031e010e010b1203070204020f0c06040c061106010614090117 69
    0x10214000e2350b084030316443d40c3d501c0c0c0e0009017524105210000e103081c646003a941202007403410b00d170000c64852890720b101401a0203142c0c404000c281c0340c0100481d00700700c0d03243e42a4640358041c05100e047d58052091213882c41319000c030001703120300a00c25200c405000c611080031009041c1029074859007103031140da000c2880030f1b01c20500380741c5000c14146580c035900300703980e48986030b02d60b080c01c181c80d104042035012210358002c0a01c2e6080c9400f030703024061080e40310004c450940f52507001c0310740303510f400e001c43c1841c40c001c00c00142c210106c01c0028200101c09805c01030802415a144002448000c100380d5000c080d01c013803165100c10004058020a10402a014030103460b2031013501e036140c3c200c40d107074494080000e00c1035501090540300e91111005481004540c80215846401c10b81003030a040381c0d4621403800083c101d00307030f502070580d4040b071500e04032000e540b125407107000e20f60400c2c222038000503011410080150100b6091a00c1440d0070780c0140350b100001024902c0d01404000c0d100b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 229194190 1250 229192940 229192973
    0x1031e150e101406160510060e101406030a140f16090302012106051201020c070b0f0301030b15040507030209031605060a1b0503030411040513030c02010503130816 72
    0x82c03440401c01c07400910400c1003200c1e0004071102503407000040008013a201c8000000f0303001d0300c15115000700d02440c4c3d5002c3e0064a640b100324103d0f070354031106041e2000c5501d024614904851814001c0c243c204000515080000f034800410103030316040d680c0021034030031200f41e41c00014142c140f0845000e0864032a400d0002031602100d40d0f415500068010f0040a598120013051202c03100103101c1c450348908007602c001015095240070032550341c0c0c00b03034002500c1180305000300c800018104c1a0348048440402d1342c1c040301425070380303542c0f1031000008008100c10580c09040010001603620741c4101803155141d13032170040e16684201d05040c9000b0140000092004c3d0700e100a0000340d4500090781c400302400d2401a51058010a85c001d092101c542e0062280c803011090104100d02c803c0c2d80e20322a01c09940c00c11075036403100081c00d003c2c5c1c9030120207000f046041a035907000d5445070008650040c490403000c0050b82041e91002c10f2036010591191200e040903840c1801c02c500c0148825108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 229195440 1250 229194190 229194211
    0x3120606030b1f050c01020c0a03080f0106080a0f02220306060f03020901090e010207020a0312030c0539160315060308180d0b13060e01060803070201031e150e 70
    0x10b020021400d481c0000404034086510001d0182e4030701e20a20031a0b4503490018000d540741c45d010000282c0d64100050101d0205415100151b011b0100c1c00f0924121101343d690161240c0391854180d0043c0b100e0500320b40b105808101c0c003d002104444010b03880134048003d007441c6840c6080980c1151826000712100c810785035003c00241e60343d005103905642401b1400100c10981c8110b8500a10415400a4002d080d100f0004180301d0000e81d110952841920709120540d80014111200c0c03003881c000a80d4a251041040b0050000c4c0c4281d000154820f1a8480344030442c08401d0303d008200c80b1120242d64141005108001c2108000b03104607404020921006065584032a00cbd4092a4035181d0003041d900d051207035941e00d4044000040fa08281d40c1002418561900514140f0428054a15a0510a4600c2c04480505c80c240813120b00d0b0020314240b604650045007d072001c0e90344440c21000340d454901012180d4411207c0e880030b42c5000c207280078a440000c0706040310040c41030f00c24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 229196690 1250 229195440 229195451
    0x80d0806041103070813170406050c06060a05010c0b2a0301090b0102030301240216091e0203060a03141c0305060f011103040504090204020c030406090312020303071b0503210123180405030706090312060603 90
    0x3503981060700c4071842503000c1004c1203035a49a170061040c4120030000c07180030f0400303c80b10000d04f01c402c1c80214180d4450340c105004680b50035006980e244001e22900310403103590100318403804140c1814a07008181c82c4107884c0c40c0150009141e024110340d0300300842956440e41c0b1030304101000d41c82070000c50b0184600b0340c11840d2800000300b5000b07980c400903140140c103600100280c0d00078459010541c0120354101e07101c12540c000280201f000f00c500c24003c04152400c40b071258092000c058003211840015031030103052000703000191107104e50032a04550240402d0b501000184058800381601d81e6408440350b185040207007460040030700301c0066400800a001e81d86a211f1104000c060480c82810901401403070910310718402c200080079260b061660001031221a030798994100c840c00c0c80078885101112000410510207544426404008800ca060018540040940d071050103801030b00c2c100400ba80702d490651b803450310200c0024407100042d0601c2c2e161441070101601081c13404000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 229197940 1250 229196690 229196699
    0x80f04081b01060503010c140405061b0303070f08060108090706180b04030f06110c06010b070311010e010501150302040f0509060301110a230412020f0406080d0806041103070813170406050c06060a 86
    0x210792040d401074900bd102c00103401c2d0101ca80d40c001d1660301c0e605000450369645810b80c0c009010040071540c6000003100c51000c11419841480f101d070140805802520704d0b180307008002c8e21800001c801102e4040c0310100000fa803100d011b400760005502030141190130710068601001103c5000101c0881d0285c1404404c9045400151003030559401586030761380c07804e04d4201520040d8100e05a08200d601b0010340c1c0e06040c1064118504036044407070f0120810300303550410b90580c05140034400400c04174510400c03162410303501c1550014400340000441d040403240e0048240d0100d0388180100c0c0402c8000303402c4500401c0b540101085003804035051a01780800c0112182800c03401030311658629401c12072a83d40c80d4081e20040099100312004140304090141410307404032545482240760006201d14044200201ea1080703501e552000d00964404030380d03060b66082c0c00c0d030a0300c00d1414081140d40c080014170080018013180c1e114682c81e00081d0445071b14048004091600402c410b440800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 229199190 1250 229197940 229197977
    0x8010509030d02090409080409020d06080f0d0c1a0124050405090c0a110706030b0108130b01050d0c08030a1d0d050d1d090705030708090105010303080f04081b01060503010c 76
    0x2070803644080303009a5101d2042e0005001b80150030300151101900040c000f448680c603500a01140000c200140700c50790b0b0703840c0e455450711680050818503403c07594554040c94482c51030b403141103120307011000c40b882c144419030784c501409030001c0d000c0201c2110020448914000c58944003c0545001c0349042d081401148400030003034241c1640050200d815000240105018881c8203d014222074044d07564a40080203070030300d0f030152800302e400302c00801c010300400d00d9000c15168000004414591034130003805900b0000030810b0301e221413600f01c0032400b44070074801480040c0c9156500450400c11949008458009681c810321440c0119000c000068002c900c4038080c942030305040402d0141400c2013240114100c201a40c495000c40400240035000006140181d007161340d683c4080d0340340ca200701d00700c610138080600424138160014070100201914030307901904c10200c040c2895491443c540300c2d0300e40054003011594413901d080c007242c142403251002c2301440d4a0320740302408070207a605 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 229200440 1250 229199190 229199197
    0x140c041707060f0813021002030a0e0a051c021302030108010507141c0c030605030102040f09060e010f0306150503150105010f090f0504020d06080a140c150d09030306050a08060f010801050903 84
    0xa40920215200089501588585e590015500502202181e17030504600a40f00c0e4401c1c41003201003111942080311504004000394203650002d040c54042c01d080380020000300b0313100c45003280c1c8100c01c903151030b41d0200140082e60081011400100b1141441e03c4060b1601d0060f20b0100b00340d900a001c1da003002d501d5a21514141c8030701400020b00c1d41e4400d2012009400d250704103503019800050b001905030205944542200d1007000c08000da151035030b2021070304420030b01c0b492140105080307003071001c00c08e03543c4407042442c10ba091040507160340c0c0b00424285030840b840c901c04900c0714001003090b541c018541070102d80c1c4a14218041e182406850984a1180e014190080d07a000c038100302c0300800b682c40700002d481701d10120b13985902103282404d0028103255034111a40105051111f0303605009201d00c8104079201442800e2504201c1c0ca00001e24041d04150100340c2c0711040061692905500f001c051b10120003e8000340c50301040700581e140f01a440791140c0c1c1c0c500010001015008400d9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 229201690 1250 229200440 229200467
    0x607080f15011107050a03150c0203090102060106050f1b0a020111010c09031407170f010606050403020a05010309020a03080f0c01061208120a06051509030f060402010819140c04170706 81
    0x1041d0f0f140e0000c81400e20740007103a00800e030000324041c008424841070b070700724030030218842c4814001c0c200d02e8030381240c40b0b00541c801240540d21903001404018003440c040e03d2030700c4011542e5400e2003041080003017403442c2c1540082d42074120201c40d000303650340184a4500b41760000028001407e00c15401002181e2602c0080d180c0d100c6608800041c1006110300d000501d40c001021701000069290292550b00489402096610300b0400140701c5000e0f1080d1011260010310640318546044019009042e4149c0200da01c01c00f40d01e8007100084030754000d0808502840209612408804440c0d401c40323115400420764008001d1034074002030103042c04c840c08540c1c20030204200e911040ca21001811960300420340c0b10800580081c807c0610034043d0600040480c00c4540440414048030385580b01600c0103030004181400003140440079510200e1000c820301c44c00502040344c240250041c000640b0f11507a540e400080c100f00210315070904000300602c602c060485540382440c060000c2000510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 229202940 1250 229201690 229201697
    0x3010f09051e07090b01050c10050708070f0203030c030403020114040c051905030d0509060409061d180c0402220906090b1c02011805060c01061a0c0a020603270607080f1501 76
    0x51700481e0313911600c2907894442d4a14204d500b0101d00f10800c03005007208032a0840003400030030001d05007500c10008034403981400d401444c41e43e03c603200908400d503c010801d506640d00c910f16940310100403400144558041d1412803080c606103803c0060300071400d20b01d9505808212001d00c0036a901088500c61280d1030300780983d0710f0b4191004148a03002ea5800844000c1c07401d00c0010351001c1e0b0703808491800f007031091030b4030856903480d0080d4517484074071103030b40c031a40d0008215400030b0030240c0c010100081260b02d510150044981d045d04000040c0e041911300648070741d81000540c08a016107454200112000000171088030076a07107241c440580d001e410007070346100d50311108002105031005098040e21160f9120b080e25903070340c060035651281c1c841e00309030b4440303201202524a050780c1c102032000c000303450009080e408000e1141c00140ca1186d4005808403aa21013284e11104c0015565070a40030b40360500e000a4080e2110b58002c00c1c0208070503109003001241d11408681450b0541e0908 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 229204190 1250 229202940 229202951
    0x902070c0e0403020c0102010b0621072f150906070e0406030c030807020f010e060405060f090405180f0c0a0306230c07110d020607031d03010f09051e0709 68
    0x30300050600c8294406045214440c0501051681c04210700c60180c1d0203800034441c0700d80000c14052a0710030140751031500b030b03104880002680c8041c001e080e0041c210340f40c100201c017020641444000400d00a0142c921203003100d8503028401030200e2401c0e80300501102901e803500501968460800612620820214010440c0c03259180e07440314010359000700518151684920308501c1c113a00c94001603109105500c0200b6107903120b100d4046d0408000340840381040c0c5001c1c05e00c405508046184c046101d030612000358035885a1068611808514895100031920208000d013450000705503041d903030b000b620064880e42c0710089440d04403a4000c0c4009114940c500c8040c2c041c41f40001d40d131024051f4102071060b0322403200c0140800ba8042ea0300b166a02c10440200981603d00e0607000b50016414812007012900510448103048101382c00b0000c1c1c0700d07100d0300107821500c501e01c01102c20741e50b0720588820701c102000310944e40641c441d082001c41031400c1c0702c07a41d40d485911901d80d00d01e4035036 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 229205440 1250 229204190 229204193
    0x8091009090903031e0c0f03180215070b07181505070b0c040510021b0603061f0203040f06030203130b0a15030b06270708060d0803040302010f0e0115090207 69
    0x500e0300100905044204019032642d928000700078240c9001040b001c070a083c0d04148000030740e0300c00d9004c1b1003c580c07120071106072644001c1d4080c0000940801600e441e004402000d40c50700310284001690000e00c156880c08245403428200030094202410081e04000002d0400c00e52305080c02a104550011000c0c03401c0700c98211f8052003024401404220100184a070000604000d4400d07100100c403e03507070381038050798100d030344050203040e03004140000580c0414901300f450003076400180103000551888640c0c2c400100244d100503400300140d100103400c020f07151050000310050700d11450305500d1410010400d800c4640e07500d01c090040100ea00200e00340164035445040116000c24a010050f0359a0070a02c500bc2401c4520398020000301110031040c1039030000050030711105003108a02a1611003045804240083c40343d500b01e01040d03041d80115145d034000d90b100794030075400460168031091051041d240340a0f0841d17402d0f030404101c1104540e080c00383c00e0075103524810050301d44142e0b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 229206690 1250 229205440 229205447
    0x90f0d08040609140c03010605030c09150a030c06080910110d0e10091b0801330504020c0f12090d03030506030a020a0602060106020115120803060301110a1106090a080910 75
    0x1001e40c001c0600848203c01c0e03112482c0821170304458041240200416503a0740700349a141c402000c0c240c0d6004003c140091008029155412010300c0003401d091959500c95443d031041c54032640003400032406c103004100c0000c404000f041010380803508140081c8aa1a00028090203040342d07110f00300b17440d060f141d4800c5808215001c1c50f102c500c1800d0144240030305200f802d00542d48240d00d04810442004948042c05010781c001c0e5000d44142980349104050040714020850030300d14200180624000582d59114006840b0f90030310b030006089041841032a092030411010701d009052007080c001c01c01345903210440a00c2098040c14003094556800c2d00090511a248100a500c41c4807000003240c0300350b0020302c03581a80d00c181c0080120704084410307455102001c0c420702c00e4070b11032060303840005020007014541200002c1d0011506003050305030310110750042034651000450042080c092300c4403c00c80c05030496000d2002d4021040c090310f4684151090310f20755800384c1709141d4031078100c910 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 229207940 1250 229206690 229206701
    0xe0411090c0901110309030309130605130501092f0a110a05061801090f02010f030f061e0b0c190503070b0a0f0501091401050f04091e0b090f0d080406 66
    0x5005000480c80d28080400440c0354211080c032500003043c0020300001140000215482258010020343c00d100c041d0040204c074051486010f40c0007500c82c1d10004940e00c5a181c405a90745004101194039810320340030908441c01054a52003400b00840e4040740c0c41c0801124018425a444c2c00d140d50340d45007402a55501c050003800070141c403c83c0d1401003480008246c135805503400b10440b0022482459450b0300703803094610040c0440b10841c4202e0300660080b0484140100e150402148025015501c1003c90300d06034811601846494901a00b4107000040040a09094031903241024410141c0d25960f41e0012200596010f14000710018880700304142c0b2101d0703070700466529803854000084409811004c03512000f203428072001086079801c0d030107690003c00070788036211103507032900040040c00c03840200d080d500a961403403c0008a02c0b044d402c5150004070001c03e02c50031849103000104c2c0c00005140000980040f40110b010f0040450518000c2c50b591501121030744403420084000c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 229209190 1250 229207940 229207973
    0x11d0d0803090a020d0b0402010306170613031e0e040c02160332010c0e180403030507030f020f03060f0904050304030311340e090d030e030405091e1f0e04 68
    0x5c240300b030410204085000024481e51007a60244000c907501e125443c0b01c0d170804110b10034903800050015a000411004441080340646030800301d02c0b840c281c80c9100240183c3c460400604080204102820240103440c0c0c045614130080144050340d4009286050013404000c100e407641c041d4282c0840080f0000d141c00c0c4002c6402410b4242048035414000d043d00712440c00070070010307200076036a80f0f481c803000640d1039000030060540340e4550f070b002c030000d2a008100c0c5003070581d90b20899001c0125407000d8002c207035070410352a94a0501750200100801503480091141c020a820000021070210a58086a0781070a00b06522004194003a041070020120f21000c1c1502856046201c02c201228171106184000072110700c0351503001c20200070f135045400f181244d118410f0301c262148a0340c8014804003407074042d20700f00364035880052085d0034203652001d0118880311100344040e80703a80071035400c01030030340c00012180a4030081021072100e0780b207490781101c0c144001400303006842e0000402d40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 229210440 1250 229209190 229209199
    0xa091a04061419080f0129090301060e0c0409060504020316050a05220306050a0902240d0212012112120f0608100c0903050c21010606050702011d0d0803090a02 70
    0x42d103548000401d44c510444400c0b07004040380380005010002800c1c4c0040c0b1301d1202d0326070f00400c0316416980c60b0a510200502d600743d9621140020f40070030108240740502d048400f00d950702c91810360100e051701e0071500500d108038410820700075400b20080c0110300c030004500b011a101c0b000c1d8902525140905403941e00207580f2485400c4881d275403400c440e0142ca1003100c0412040e02c49405000480e510102d00942191040744801e0701c1456005042c041038210b2100a031811381560104002e90b000348400c0d0301c041040c000103004040c4240d00000002c525916101c4255183c0d44444101b1808004d0010074441c0e10582140d1000d19504400000c810300d003014000c0d00d41e50400141d03112640d00134034a0349444c150f051030500d44a00d1012003101d800200500241c0c000c2401c000310405040014400c0386010030014207812170a00500d030050413107403074180d2281d81500000d0711486200c004140d0490421801c40c00c3c960310881c91740035a903000b4004689036603d061600f4680440c2c030074043e500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 229211690 1250 229210440 229210477
    0x70801050408040501091401200a02120102030609010b07030915050408030a09080c04140604020318060103050c03060112120804080c010e071404050c19230a091a040614 74
    0x42c001c4840060044400c03c2c1d80300301502c0c2c2d49600b65141c503440e900145000450525078420030006200400c1c06952801c0c090751140200b40d400940502c06008402200341d4002c0204a0b0034686403d4450051045d205014a40801070b038004000c041c42d40a2155160110603c0241d001d20450646015000020843e43e64003910f000c09085c1500c6440740203041d100b4030b0360500a40c01e240c05030b8001140c100404101c251600820030001e908014004001900e8145654101d04001c204071402180070340040c01165481c4418903080c00c10503003105070782d4140181e21100007005024134401c800722514115100d071320b032458040716074810800710354495801c0c4031a00a8862000c02d02104a401000703500040790000003c0c030003039450480b10f20710030807014444070407550a010403498500304a403906510b050303000f5108501a01c030b110684a601400403071154040c1d41c01455070006000c5c00103041d80b443c801d2842040c0e0a2156005080402250503034480c450320340380d030507500d211554138000e044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 229212940 1250 229211690 229211693
    0xd08210106020a0501110405061206030c04110a0909150603090201020c030616021009120804080906070614090c0a050f12010c020f100b060901080c071a16080c030f0403020708010504 80
    0x41d03e201c42070041c0e40700d51820300c0c00c52400d001da2040f50119400039190a04203600d052403410641402070884d0303007501802071205030302c3e5107a1040c4c109200020381c0b01e5454206800f0003e18001c00e0341c208160580c07806692003408a01090071400700c503403624010400b40710610040307040c42c580300c01940e01480392000317108408404195a2020603a02e0b401c8a01346048510a0f82c1a6843e200014100d030f6641d030480c1415611038102d041d802409071402c203150070100c00200c0e260380d12401007030b54116510308003074810b85190019660040c61480044c640f0511001c000b82007844907200c2c252044da0f0102c031300d9446403036501002101d108150003c1101003050700010351114591000e404d418010300300815100300c201e205010700a40d001c0c0c4110304220b640b0006403883c45015281004480041c440400050701d1501c04040e00d4130780410410290a0407241c0700414420303583c01100f405000c4042064241d022070550381d002c5600c04e088802038031141001d03400c0c04402c1c0c2001c50700c0c0d4204000c110 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 229214190 1250 229212940 229212943
    0x1031407091e0b041712070803010f060c0c0b0306040902060403120e0312181813210813110d0b1603020c0a060903111501030c140d0821010602 63
    0x1080b10030281001802d00311044504055003018010580107041c280018814004416090001103081a048583c02c0710401403c01c49500101003c407041c802c004014011034020a82c1440200160704040e0940394840d59101d1340b1f007600380189c004180c004000034005594641101c403095801030801a512600c2e400c1c61081000303a009003402141482e030024240342400510800403040d4880941c1c1085201c1d0b0703000c1103203207241503010381c8203860400c401c8415040740041030240c00d40180992041025240c034800c0c0301d50201a0b41c2031785400300c40e000e841a40050465902440f650004600001f0030700e084c081c1440020382e955041104030404100308140c845090340240e01c40182011099400c0d00100c0981c416082e9080141d0031840541000800b5500152502482800c002d07500200200f200c40c9081d0f43d90400c07080c15155a001002444100c110541c050052041c0f0701d40e12206030004500d50320403110b002010740f5000151000d490000c612702510a42c00c0d01a020040d582d0740000a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 229215440 1250 229214190 229214207
    0x3112104020405130317060303040504020c0c0102060a0e070b370e09130f23011d0d0206060d0f050a0305030f0601030b030c060c0f06010906060f020c1e01031407 71
    0x8038040d510b0f260100e480a00c0610000d01e403140e0507600c201c0d0580a58044054082e40500841e41520003800041102d640320b001400840604000402841c0301e5000024907090024110842061420312080901b240c0440c10105482c00011441c3d542c02906a12101d0441c00e85002410116201015664101d19401c09000c21246a039503148020051040000364181a504028000380d89252803000540c0d51802c941c0e090700644091480360844100403202581074207002c442d6075920020000b20102040e0451a5424140024048081a202e01940e1544040d108034071072003007001d01200304489010082101a444815501c101d405031801801c550003d40d0041c250401000025410354031034400d0030154140203000702003441c0319805100c426840180448103d0040c80255442d41d0303000c00016000b405404000281d2918203100145101100d1820108640001d0600d003080c1d951440d80e4007170380f40040e1054441d40b0f001c3d001a0f00030101c1098182c40d2030f40702c6040098607030700032052 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 229216690 1250 229215440 229215443
    0x15090f02040e0c0903071202060702030115080709060308030a0513080a0804060609020307021b01020c180106020f03130605090d021c15020c030316090e0c190903021003112104 77
    0x1449416150343e20466003074080c11010607055403104900700304442001c240c00c1040c0d0300140440340340000c1500404d0a5900031510603070158541c0c40d08018032030081154900401e0300d01410030100c0e040d60303500c0015110190498044945072000700320702e0742c80c0061845400741d110404586da644d400801807c9034200322025680706182c41000954114a030003181d114401070f030302070110805007800400c0003010344d031091030461040c0c40743c10050b6260300c3c1030502c125000c0e4001f10340365850484d00a240006a00ca21000c1da04140141a05441c01e003070f5040a507989400e095407100c060034080b40050301d0606001c0d500c0307a14440c0c1710180b07640ca80d804441c0ba5004213415000707010b100d1100400c1e8460b800031004954010800101e001d1418103800c180000705281c0720b4442e980c2c5000881c3c1c80c140940b100d0034181d0340051010b20401202c540c0c651205801d00344103070190700d507400103102004242d50300c8080c10345611214240f87c0b80c3c141260502c44851101d1041034101c11400e01000b141141d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 229217940 1250 229216690 229216709
    0x71101051c1406060703021c11030d0603060b01020f0a0b09030f0a23040f06080c0909010620062205010b19140906091803071e05160303021015090f0204 67
    0x400c3c40360034154219500c203074040e0020321600c000c8460f241196082100c40c042000218940e00a56030f01c140001e08020b05007840101e00181036041c00c0040340c01140e01181951b106508020140b000403d200d00902d402121030503080da0381c4550907085100c1e60703c2900a06200003150901da6412902807400380004000114110580140b9150701c0e1285001d000001030301e82d0740c200507007407059481c0c5a00c00c440558203810003119001140302d10400303803c05800316001c40c3c0c242d440403101c01c4104005108000041495052019401c04420b00000c1002c210040030441e020071b02100f50446007031800c0c09800160388009824072514503040b82c0c060f480c0e03405c0c92198080468038010140da40281001011a24161a40501080c5450380200082464001840b1260100c0c11002108010360290031070241904c201b840c195044c41c20b00a24041582c1202d541400070a41c0083c000075180c000520014503079004880c0d0380300360f000700e030310801049003024902c1e070040d146030700600121103540307c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 229219190 1250 229217940 229217981
    0x9030d0212011d07200703050106060905130209060a0309030c0c0303090f0b0405060301060c031704061d0a1113061701091211030f13050d050705120a0503071101051c 73
    0xc81445032009680d40c90010300070a036401010514000b1701d0f101c00091500700c460466496441343d003500d142c0d82c031010202e508003808200900700504a100700790f40302e0108518190b03c4000150890280d00610340806035246804001c260158580c20192501701070341083c40740c0d0340e140040c408c0b181e90060035490350005000165960a2505a50941d003006046904580c20004211600080c20300164100aa4107046550202c4140c00300c0703020310f0040c42d01245000c3c0c80e001c804526180850507410f11303408a60180c1c007180c02c0b02040705200c00c04451202c07072044030000c0b00c0c0240001d6000b407640350301d4031071088018043c1584941c0920380710302c48d54400b1140034103096404542d0705800f04116003040000039000d10000005001c000401c00c4501d41c020344038004602c080c0e481d407001722903540c0903440900152500c42111841200b070700004048891103659050303128058194000c0001d08008c194082c0390380078038240c4a00d15000c4078008010080b052014029005543c950b19090f030008 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 229220440 1250 229219190 229219229
    0xc110115030821190b090402030a2003010c18120308010b03190e0a06060e1b070203240f06010f20011b12060b120105060309030d021201 60
    0x40c010292401805642940d4080c51521103000c2c0d98800a01a51201d2840c4103040d0283e45500c842c50103401d01141d04207034280c002c90488102e0b202a03240301c2c4204411010440141d0b00003c2d0a04950751140010360f42122145500501c40400300c506039240d420010794403806540542202c0c1071400364600c1440507550762020070100015803c1c080d000441d200010300520b0800c1004541000f00304103400849a00700344d0b00c00848000c41050b8002da0071680d8a1406d00905010701c3c000b500300d0003040043e900f441c04200d00e15010305615104100c4011400b501036550502c01c51000610428200580c860b4101240004400440b503406021001c0c0c40421540d501c03528004011581d0350304c2d9a41800b68030280302c001c52a1600c011401e80d900e500d400039905031240c01460040d1350680310203900c0c8411020140554989400c251590b00040c07024002e24100100c1d00c40c11202d059885030303600d0f00c074080101d003140f1804031005011400024451000d02c45407120340e040321150107041400d05000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 229221690 1250 229220440 229220443
    0xd0810030314030907050a0e070810080d0f020a05010f0203041506051305090a2f0603091203060307090519050a2c03040512010617030c070620100c11 66
    0x9a01010340010030355070a440032a003104000303680210544c400c681c00e859940f0005908000144c000c0c100c010914000d01c000315801c11007160300b019513000348081850034110010740e0760829448007410060384108004000f80213000c121202500f01c03000340240b01c000d0100001a51080e80d0440701403c00c0c810015940209200e400240c40d0b000b0202994000f444008401400300900300342158041d2024000c0015100060306114101f80b42400d01e0b0700100e103a80c0403101d0800315280d0f02401040080054161001c5420400d8a682c01c0e54039489032942400700b40341000c10781158901500d02030034064151101e5200c034500f002885c2080c00143d4405405a0540340d10340000d500061b52550900d1846c01d1103c60b501051440741300322400c00d55036900143c0041c41403001c0180a0355608000d210041c02da4107241600071b00e00f07004502d010610f1800c940c0e5181c203433040604009000c0c0c150301d11900a440b0081106044000300c03094118400c000e000100b100c0300c8c5031004108440c0b40b03440002e10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 229222940 1250 229221690 229221721
    0x60d140916050303040b0901080a14150108010812040306090519030302090307060e061803030c031218060105030a0b100306060305010b010f080c070807170403031806020304030c180b0406080d08 85
    0x40480c800e01f010144030040d15180800350020707031940e031684113002d2075245d002c0c000c03485003044821540300b0302c83c1140058200c80c03040e0003806e01500042880c1c080c107810726088a0072240c0c024400504580e45081c510b003050319220090110700040d400d04410b2543c550041c000f41c000490030f50f00c095584000584035507121000341c9410150510001d8070f07812003400318014810000e000d90f031506903141145821a4400c0702084414110a41407014041d805c440880448038a600100b88a506010000340e5642e4500d500500c0e4007a11000070311010a8408001c00031507000400f408115100d10344139018100d02890a80014100084a08031a200d464004c1c007076100c20880310700c3c4c400192511102070340895410307500c03908018406550078400000500003180240ea032002ca4920b00030a10540d80040d510080c00c55105020600c0400d2050032420100c5000c030144c070000b4025030980e1009080c9490141d94031a00c1c00c01d00203501540490410344520440d5944c540e07650319284103442c55034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 229224190 1250 229222940 229222949
    0x810050a0c080403051308070609030501110a0c020618030a080d0c0e0f040c03110f07050f0a030e040b1f030b010f050708040504051305070f03020918060402060d14091605030304 78
    0x1c2c2c10a0204002c40d000d40000c02003a20803102c11856036449128461610340550300c0207000511600c410401d0080a2107051004c44510740d186d8035001c401040102070800301d90000e4400c0c080002c449a1202550b180e01d4130000c0094141c03440e10701c86051203042074000d08218031810b03041003a8103036524420043e1660070034004201c0c3c01c18058050a1000a042c000700c004180b59440c1f004109000c0710380040c02c0079900b01e0b00050342d1001d0600c0c20500b00760796400d43e1105903201d001d5000c0003030b40009079000918030a4600264604440700020f1102901484800302020510040960590b0607040b4121032042a200c07100750041c9104125280e00c60780c440a41003410034002480319160a8008c40d41000704504410109106a03c1300f40c18244943c3c0074800c0d105c0661410811414030f580c900d981300805402c04031040100c00000c1d510354000600091003080f0025001221680036401000d0000d0010042521450030f0755401ea038608000301c10420002c0c0c403040001341c1e4034000044500741c5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 229225440 1250 229224190 229224197
    0xf020c010c0c05151e0a0e180a050c0c0102130f05060a12051003060509060f10081c141204050c010e0904020d031116081203190209040227011e0f11070e010810050a0c 73
    0x2d40c9e610384840e0051074090004250410308010101c403281003400034110001c114120b01c030085280040c01c1c0c5484c03519510040c042d1070240400600790b9000340c0c10b80e40443d50f201c4040b815949204403451851056040245458a0003052048040700081c0840c42050020b0b6101015110301c03143d5500305c43c1d9441948030341e0f4007007101843c084c1501d90284140c1c4140b0304281050304841c040c58801500202001c1c0644c62941c0c0c1004103100d41001146400d034001c2c03d04252503c944008207000b824000d1010380514844504034081501c91801c0411900800c8143c80682d00c0e02c40080f80106600d00c10010144103d1420400e01c21080086a00900552110ba00e0381462024090043e40200d6409035000740c2c00c1c0404190030800d4101c404040100c10091001c01e5a014005003c00c2240550582c10440a020800340300c0d030040c10140c0901c4c0c240c2840824018440005494034949402055101c5040e200000c0d81c5180000c25101e498941d0009002580c0c03090b5004080300d5030740c130703201000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 229226690 1250 229225440 229225489
    0x209070e030c0103020c0a0210050d0b0d120f02120d0c090806070c0b0411040c0305060405070c0c0b090402040b040305060105120303060a030210020f0106060f020c010c0c05151e0a0e 80
    0x9544c040d45c000c1215085a0080e03612a908980001707104440711910710010a5001440c80500c900c24440d10036641021500010440195200c0d001c8a00d202070300e0300d0520000700614a02940200014517001d03c01c003441550714003121507500c02400d202107038000400d0341c0e0f000119400302d002c100184039001680d0780c0d0700d40301859180d4158040c800351040c1d6600200b0b088617070703550b100c5020b0602c106810f40c41c0824079080c04020302c000c4810013810003040200d000180000a0a441c0c0b698007140c4503034600310b88540101c000100240b085038400d41401c040020000100000450b0080c100e030400c440c007a2540040c1240641c036403204883c202c0c3e100150404c18001460300c00c00340100320245104640207125140012801c42d00d1580046020416140c401e092182d410003042928600c06c1c40c080110389002e03903078102d40002c503000c2d0714441c0f880b10040d030340442518030548240285c500d0301c00f42d00e144901702134507642c0c1c0003010b0200090001002e0348610300704584404401c100c0b4500101c2c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 229227940 1250 229226690 229226713
    0x1140f040b040f1a0711150c0f0c03070f05010b0619140c0a030e100c0312090201020c090c041d0103150e010e010608150714030714090406060503040209070e03 70
    0x40072802030048803040624908180810728000100818011209031403d1030700702044084c0c01e0b454000d070b0b642040d511031046000f000b007a550020360410351562889842d800b8003001080c2c60b001c0d04030840214480803817a282032190802c41e50080c1801030008102c0e49480c0c2091000c94802c3d44024035417180400c0c1414006449a0020260070600c200e241d030401c0c2110811608010b03201c0010380c00a800085900703014a0250101002c80319141014130342d2600c40d40d009402066a00c007030440c5255145c0702001035900a0107603011000006080070440c2c500580c1001254100d4081c42da4a0300410a1000c0030b6650240d0840c162504a0119035100e025001240040d02c01440303090381035500c1d5518114460b40074000d501c05410410040e03c500800a2054002e0b42c4c1e00504141c00c1240d43c400512266100074112a000b41d40c504d04031000340d6401c995440070384108506140c00c5850711200282d400c4d4418003440c0254030880b107035010b50301c1d810b2049070011304000042e03900d500422403012 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 229229190 1250 229227940 229227953
    0x5040e032506051f06080610080c0705120d051b0d0c0932060a08180f1e010c030c050313050c1215090105090307080d0b0409030207060201140f04 64
    0x21030311111565a911118070503941e010580d58140c4030651101d0340100d40000450360350390b10501806451070b010760246007540000d0313800c0d54080321030400d0101c19030100e00c214020100300c403103039a0000c1c100c1e200c1f00050714100300705138811020764070010703d040e01060301481110001c80c041007101d0139107400d092243c00d445008240400c08401407002c024000100d07c943c004403400903a1090220394428068881072151001503282c17203a100d28000c101051400303401c2200d040c0c100c03810089100805c6860201c6074030b8010941d04800d264032500d5500040d1803240e0400095174410100240b0414152941c140c050b01c4001981c84082541800000e0324008818030100b0305a000350101c610601c521000b203541011446d0f02044903800040e5513699514160607159041406c1030000c004034a46450401d4413801010401001c0c00c9001504484007134554000c0000f034100240104140c400525029580c1d2040f40f140d58055401e29585c01150150548100c0c07058908241058441d500d070b65070315 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 229230440 1250 229229190 229229227
    0x5030c0a1a1e0c0c10063308060325060f050703020c0603060307030803010305061015020703240e0c131a0f1f1205100803090f150d09060605040e03 65
    0x3200d1209010182e044c000820441020707410400001030303110708040804460911542007150010004000b9507280540c01c0440d044622061901081c00d8451078000b03401e00b0304030f4010000071050000c02a50b060150b00c815001c0b5041e036283c00c0ca05081120054601d805074100c040c001d030b006010411810308254000b07551144008003034821142d101e940d465410b4000f0303041640d0552003241081940c090314801a000b5141701d0180c1d4000144c0070400a50b10f00e49800014a21841003000c203094a95403007214480004071003040c0403d10380141c0c001c1d03036104a50025442450420803074281440684217441c041194290480815034140040c8840314000000007904541001c21400e11401100f4400d0507010142e680d260703512400601e12016501e0240c900d62040607140030400480c074001044540314042a0380c160b04c1d0102d00c0e000540f46052500080300350620010f0440600d2070305a12025110784181401c0103029140d6041c0f00c122001c40300300c030359507a0040082e68101c0b0340c2c01114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 229231690 1250 229230440 229230451
    0x501061e0e0f030f150c0c030f0a0507120305091b15030613050c1908010605090f0a0b0d0207060509161a1c09111014070501020705030c0a1a1e 63
    0x2420002c581d2000b09180c42440c500340c54503a013100128050740c2088004198100720008541c5080500b42006c0d56100e10507400030300d00c078403400516180c04600900c181d507210341d00a60000d40b86004050003502602d412941980035020f026000b40d035032019442c0001d80618040e2400103496240000c112003644060300c11030b40280070b484099694512401680c1c8250062003803261107070f91100944801c40364815008050010840040c800c180e80101914500481150300d80a82e00109011600001e807580007091301c5080050700450040c1250028441c85114081c00c2040e5690206040c1c1c4510b140600b151a1007840e400400c543e404200c145500c002440312040d14240f20b041400b000c83c48003500d0b0f04542a10743e490701007800300d200100d003c40748090303441d445038450700100145094441a6a48400c0c440440d03890107102c000d41c19551000e40c0f000499a64039003008030300c1c0d65070070802000c899402800307000c9640c06018112041c0524880c2c01c4080401001d43e0b030264030400001c09 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 229232940 1250 229231690 229231699
    0x40c030e03030c07171803060a020a0e06070602091f17010e070302070c0824010605030712020c0a0b0408031005100206060103020915030f040302010e030f0d0f06031506050102010501061e0e 83
    0x807214013041700760040504141510802d0904100403003070508061009000c82c208a105000d03902a094015848000700c500446550360342d401a1728016009010302e5800716005010b80240c074402c4000c84441c40c0c0f40c40c00c03989900344021000d0341040c50315031090280fa2440306081c0041030350740e030080d0013500c000c1f4403030071030170b89466140d82d101807402c1001c848003500710052401001440d103805081034090310003031401515520b0a804090001d0401c803080404607036001521051120040c48448803030303688032a540603503007041e081c43c3d666a007041e41d9907040c2512141d8000346510304440c07c0010250160058001a0f64007001540290441c280c1607402c080f6007405400b15041c0400154070802c1c2940c112600c50504d030030000c0c00c550381c012000c00203a00030050003030792003074450589510303030501100415192001900c15015200c0f41d0b03c02000702c2c407444443d800c2200c2030307080001a42c800782e000b040642c1c0d03500b5003100d02d0070101e24840790115914011502a5110b110380c2c0810345005807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 229234190 1250 229232940 229232963
    0x612021309140105040303180f0201300605130204031a090a061812020d05041e0e1008061003020d02060304030c051006031106040506030c13081b040c030e03030c07 72
    0x12503885000b500111031103016550381d42000105509031280100e1612603d06000d0a4040369444004e02c03031007114040d05000e0b4a0038206801d40c50000b6a00585010703440c01c1d0550301c1c80c0f4200c1c5000d020725024661041d944007034140300004491007510200c90300300500d80204800701908810000000c1c20a40d224010b50341c080004c1541801340e0b0300c00040c80001d00c42c0c90405420f18503020110f80d0549002c6405c6461038512066010b010317a410707101190340140c01c0c4070036016031a955603215404159030b000c1c0c2500300150b00050481388000c5071004415030342d17565109804030361803404600000758406011282840581800b6028590092080c18090721071440e42d199685070554001c691200b4507111001801044034468042c1100703d07040d100103003064107200001d201d60100504000003500c1c00301c4d03860a04400600010001c140c000c1c15a41000f011150801641d062604c886004a00340319290380c03458403038400c407482c0c10218800b65084d41c660010758800d580c0060001c1d0f4080c05045d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 229235440 1250 229234190 229234193
    0x312030f13020d081b010b1f0201060306050108070509090607081909020a030c050a0b0c0616140406031407020d020c060c012a140721111f0f0612021309 67
    0x40f0140d0726454007810b00a82ca5403104000d030ba013107495800300500140d0601c0080b200540314400480c9140108000c880b800219214040340101300e1584041c004600300000040d0300390300441c2d40400d0340c02c162a1058584d40310040507070b8620094618000140740318000403c0c1e81c510011084000c0354a01e07022803107440320b0300050690300003500265058260030170304116a1405100c50780080545001c00c80c200038459042c1501d81d800209821030b0b42a020f00115042486014010410803225840030340b56511900000d00902411011070241c07000c802c042100c45000003004c0b40b5409c5558010300e0702d03188d02c2060160350b822614407100c0c00d64841e106952914040a0440a0405a40035040d03040705401001488080c034401c02582c1d000080060300b0104520141d9400420501652012490718030007084651443c148444259030190342c06948203502c0701c810340451134410351001e01c41010821440400c40b2130901c00e0107100b540e2010500018103005110303200d694019440040d611865 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 229236690 1250 229235440 229235449
    0x12020103021b010e2802090901110f030402040510082d070311030c0604030201093f02030705060f07060f0b0a030506010f0902250609020402041508060312030f1302 72
    0x310301501c60030b035119844c0c1d580ca02001c110401c804030120250311184201d40c6010b4a0142e403036030300a4042c41003000000c2d440b2409410103082d1082030002c03140c0c1c400c84140d440c60641c1059030100c0c8550b080c0000300702101c0140041400752413072440580b00400c010b4071402e9803108100f61030b100500071803640d039283e480c051080074002d500801c0c0036841801100d08043c20010042c880e144204410f200520250340d00c188905d0544060440d045140c140c2568002c0c070b03999054400080e80340b145c00d8405098000d807200603031254402d400700d81e003068440c0e0402190340108a5070010342c08081c00900d002c05d429801c030031060704005800107001d00c20640801ca000c0c207690000d6641d40e01c40001040340001e088104001003019003c11424108885140a1103080100c00c050415a4026821003400001c1d4440e00840340d00400840d07a40b135440c02000340703400d001d01c540030200303560b040060310710304000c1801315040114450541c40c60740c6480404a10140c068140d01c80513402d41810401a01d6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 229237940 1250 229236690 229236727
    0x7060902270109021602060a090506070f050c040504031b03091203030204080d090305030a210e07180e0a03030e070312031a0118030201210504080301050f0a0f1202010302 75
    0x20402190940104441c8501d5403100d0180e00118035180304120164858006103c64003803268121f42150b0f480d4200d000131545040c294100940c00344002038514200241e20302000415881202138500004884c41000102caa0458001e80801c00098601300d2060070b1340c9508400c28824100303030b040151200c100280c00d40850000302e010a6001505014100c0200301d0248042c80390324108007400e0071a60b0741c2d40c607809502401424020303550f021700003164000390400903259410307008101d00d000322401d941d03883c49144901c04d401c0d41c08071944108001180144140500b0700e1008140d0b0b0b04403544c08030001c04030300003103540e02d0080e08000b00000320f654001d43c0e84030304181e03000f280c00380302140d400c070f001030640c0d02090620080c051002c00ca4610186403004032602420680c45022202020f1704003401c180048900f200d24040c208820042464003a5041e518150744812110808500344a0100c142c0c1c09203504103900c00100300070348429405815891032043c500541025004c405030300001e80f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 229239190 1250 229237940 229237969
    0x6030614041406070903060f1d010f0c0903020604030b070509060706060e0f06100807050408030a0c1101030902130509030d050a0903080a0c0e01030504020406050a0803070c1d0105010507060902 85
    0x2854941803205000442548050a07142c4001415141c14081c40142641600740b000400e1252074078104c944100300c6601800c018201c404000d012010505c071800d00a01d111081c1655451030101d46e0701110384202d004000b9258058003480c941800d40e00c50000070000106282c0401c001001241c210b520b4036406011102d11a20010800b01c2c100014031001140051248014500410800c0b00e1942c0301c3da095190940b85060101c0203464a001c219401e01c2550490042484002200d684060f409495907032070a0089110003001070080004409503507124101a5000c001140c21202886207940312541000007401220700d0040312240c500d080d100221080c2c1540c0b40d842c016031091580000515600600150b010022111b40c1c44002c1d08250315900824101a6240c000408540311544980040c190040440030560354a181196481d403101008a0b2110407020740001c5c01d655061015048103e004202c0c012a820300c001116684c004040c15143d654540b181100176071034080d40a80c08130f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 229240440 1250 229239190 229239221
    0x21090609040c170c07200a050a0807060206090601030809011d15030f0f0603060a180204110c070f0302010e01030203041e0b070219020f10111032011701060306 70
    0xb070003400421220800000c040404142c010000d45e0300103500c5480d800e00044c10000200d003c058441c001c03d0704001c040e040366401c2588000d0102d00c1c1d48002031034508a0300d055003104c1a170b075100ea408948504d0280300080118200703005211056008800c0700114040b0450b283c165041140700141406140e11908404c0d40400014000010400601281c0c800320404449070941800c0c008240e541c1300040c01900c2c0310307540750180b07049204011000900d15070010014000612a18840e0090354403034541100759100e03580c030005503004024054011aa0141c4681505141d01170054020350b0005108460010030400e14010180c46594415070090085241f80c1c602d1a00220207880c0190804004e610b21046030407280060703503104400059903c09403030b00000460400360a41d14130a071081c21003d036000c0e03a074030364007041555841940d0f0010741965004610442c4408408810702580111420400bc10010b000c1d483c25400c00400c0c5041c01d50000070025030b42d031a40801c40e0910424131581 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 229241690 1250 229240440 229240457
    0xe121b0102130e060f01120209010c050f15010509010f032d0308150a0b04150c050d08091002070305031305071d0a0608030f07060b030a0f11030f21090609040c 70
    0xf21410f444049501510644410107003aa442d00080d00b07010750004150319054000619500d540d210361210308003658090115800403c80d60f1441c3d407a044410b0f49001c0f1501c913140006954640800b03443d04031140720681115003821a191114040491074243c09080d8140c9490208900f05c007003a00342c41030099440c200355061020303c8901e419481c1c204944100c0c5d466600b0f219004c2040111000c17180e40070a003281c65150b80b2000e84001c0c6001401501c10300400905840c8543c00c210414401c0301902d0544954402c911a900c00300d00490b200600003c1080c0300162142c02014500100316000d102206c81046c0e81d076000c50885102000d1803004922018180311003603131940998005006840007440c1085920308024865011f07448000d0f01440d120700b00d0381c00c1600d09100c6004456008006000080c071982021029803c203485041d019215403480949035007004103071551100714213031400c0c07640b4030510800001c6400c50411258044800c0051a01d079940d640b10300220f901480e210b4082 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 229242940 1250 229241690 229241699
    0x1e0609030f0816030f0f060f031e0807121106100503162103050403020411071101030e0d0c031808010c02151b030a15090203100602010e121b010213 65
    0x494465901c64205104041090140c40c409aa0090303a040743c4034540000c44036030020340a405008200340c0445c2e5a89840c4012540b040d0562401c0c06030b80c05002040f40034255100a01c0c1c09585160020301000c1c0c05101180000704602035005080d0654034040030042c1f13100382080c5c200711054600d10305030040d40d64100864101402207031211001d51150030034191910341e52070046041c00c4c1180ca41a00040d416104050285090310007039a0060410081584210b5503584654484803068412251140000b282d07507200740141c464005440010b410548220380c0203503030b803600707500701101445185040d04038207407002080b00e001040040000f180c1948800c0d8042e080c851020303502c04181040c0410850400f640d01e05514101140300000381d0f0b41c3e625080c4407002000350b041140c120082207c00021101c5880d005980640700c0010410003144e075800c030503400c840e44030f03d00d41e100d41c000030344d80d814031140322002c0c16030307200384a034950b9501c0f01c00b070016402c907400919403003a0020840814030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 229244190 1250 229242940 229242947
    0x11707030209010914031002090a120b040204060e1005041a120715080c0307080a090812040b06060403030905060307051303031806171803090d0c03051212131e060903 73
    0x100204905822500c1c1c0170a024013003038803403903001c120742d00481c0c00003810f00041c0c46441781c9400410303050201c07269001d560b01c0e00c11840c500c152000d80c42607080c0340c00450100c80041d01c0c640186003841001040e140f42409010141c80c01642c15807901080d180c44e09820348038180090b08041210014251445c1440b41c0f80e040798a4003d01901002145400c0252059654003101d400091074200316917035940f10b5641c203020703103a2079900400c0f04401251381d4042020020800c0d00a0340b18500019031942c4502c10f00c40d00d40198070020300001c03054042000707d8284440150742021551415510380190f40d0b0807124103124aa104400140d100b0701e0b0035258008e5411150050030040ca000c00d840700e0300b15405225003001603e41c65601d0796502e11090080c4003001168580b45c4050141400e42d405414000b20301880c82c401a2070728090380911401c455004c0341281c1840042082c19262034861a282e000740c054040c00840c0c4002846041c0c2604141154089000300c1c861000407a80040c6d500d0000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 229245440 1250 229244190 229244207
    0x4050a090231030615120516080d0c0303050a0f020f041d072a170408070509130f0503040315020d2904091505010b0a020f030702010909020901170703020901 69
    0x40000c0b5001d4481070119142d00c1c0c4100103e940040010841c1c07082c005101184500c241c0c04420170b00d12410320b182c1005404600400c0001d004048503600d10303980c20ba6951200c0301c02c0240c0c07000a01e1054020f000134000d03801141c10107100e240009400003815040e4080344e100d04445440210041001c10060110070101c0440c541580d15103941c5041000000d4007101e030070310260004d081d41304050380c054030020f181090501d40110258001c040010440d00c4264418001c02141e0b005214012400d820030304000d41c051410b0080c644690b10315501c1d150705004100314101c41a00007048000040b03000f05180b990380704990302d001030355100b940c0070340c4c41200c13180e150103c0c01e1521803440c1d100000500c0c1d52048182c00c103036404200e000080c50300080c0ca080520902d4200f034600400460242c00301805040d65038081c0c2c0840701c0311081c4060311a0303a80510300b0000e0008040e18400d120136612034014002d038a606060050030040300101c0c038039800c2011206240000d80c0418051415070380100c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 229246690 1250 229245440 229245487
    0x207180207050309061b15150402030f060d0201170106030f140f041205070b13171201031b0308160605060a0b1207170907030b07080c1602010504050a0902 68
    0x1146406803560b07809031280148000c0340d203d040041110202c40440d03030a02c8a0050107134083d2522500c3c00b5480b850a04020780d0346003403500d034050703000055043c04d1007100d0103100136544082e0195910350400803d0902c50703c0881c10000054500c004255010a40c18040d00303050310003194078080941031400b100c013035051100d82e554086090000301604103012503089600b1911040858060400a503130034428041d00038040000c0c181040070400c00311100341e003641d105540c0412025914090b4807403d0180c110240180310041b001000081c11410010041c200e24010b0104200d940e0b4079010307a01d4003c4079170005100300640b100c030200005807141c0d6a01501c02c440c21450380d8144041d400940c02158000f0030007503d0b88000c80c030024040e0002102c80780782d5006400b80f501c0e01c400c44907119100c900c412140d00d031100c0c0100e00601d0181200a2040c00c1c2c80d207240341403a50701d08022240c010031400590602c6030400002c20162501103040004d001d1035003002d42c0e10080009924040e40c0785520 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 229247940 1250 229246690 229246739
    0x305010b03060a0227010302040824330d080309100b010908030904051003380103080f030a0605090c090a0906031e140a060e0c010e013c0207 62
    0x414400c00042c2220380b4107001060b107070b10007917440b03e8005070024803503604210403610031030840d01054070040840403548104006044501d07258203503101c00c201f43d041c40f140c0406010342200800900d6a014801d54a80b00820551035030f40d00e5260602c0c80c0d4402e640e140010b40103106100003000b15400b914554480a2034405841c80c13030198160b469001d0040340d20700c101e07255000310303211034003000070440a0741d084003d003010481080080b0050100103a24000440c01010484524503482c1d80b9903812030780c21200e160714100200d4100c2e030542d80000e240e44400d40c0c1da10000300705070701c565030102d10402c04181860342d6110b0749820040c11011962000022500b062401e00000e221420020700c85e5414015060281000d0724168000401e10007140045120342e10343d00060000d03a0700070303100355500c420540e10381421003001100d5100f0809030150119809100c0061080840900350301c2c00b0740510402d0420081c100c482d00301e03c1030101031030303c0140c2c09500280081101c2c2c2080310001c050203c03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 229249190 1250 229247940 229247947
    0x4020f0102120301120c031a07120209130509010f0e07050a0807080a0f08190e090a021215010201150b040305120a09090b0109170607030b06070503030a0b06040f0305010b03060a02 79
    0x1c8404452105016540480e65007005d04010482c00d100f4017400b5560081c8000c100410104450800d00f50864510380043c1481c3d81e103001c01c444a200f261030035000035150304c0206070361482110151001a0504030159030310500782540c1c68181c1700d055185941c0350098030300c59140a0400034148490b030054505900440c400300455000043e41d0202e15501040705031482500b030400e00010300404130b801c5240c4003001c40030782c0c13036a90008603240390190440c2d42c9140c60b16031005942c102e02801c454002c02c0048070010a41142d00c2c4040d0f5044e9640510003c100c001015070400020031a81d0720044900030003240c01d0080010900050074035058400456041c54203810008180e01054401c0170b00c04c0340d03660b8624544c0c1c0d100345040c8024120300244071140810100f00e85640303e00469000300001d1400075000350f01e00d8a4012208039035040f00045040d0340750740010700c00411070400c04a40c02002004009a051000311a503001940a60000111130750484103060038908000c10720810b5503c1007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 229250440 1250 229249190 229249213
    0x50a0606030210260a02040f0807052407060e0102040f0b0910081015050d021b010c08010b0702091321020d0c0c03030503060d050102190306052e021f0504020f0102 72
    0xf02c010f400303c4c43e50b060202054031205607000081c4180e07000a0440c0382c6000c3c01040d0001e001170080102d600544070110501140182072159450100300b40f03408040400c003080224450350441029900300d080010b2400d592441081c58075a041c0d80940d60361031b0081030b101102e10b02009980c4d01e8039514186804503203840300600394aa103c0380541681d0320320008603039254034031540503078000385020b8508650b5040840003910783e0084113040c491440d03003494400503599100b4007a103070490317030013060041c1451929420882d260364020080c0700d091403034004a1022403400348281556007843c2c4900c4100c0b04c8060700003802d01400040342400c1c82500071300e420000340ca043d1610201ca0305440c0c00b0b600c0c0d4a4200004141ea2803020000d0569070010640070076048481d017001038050300c0e07a1410844d85036544c0c1400740107480e050310203504130a0038980c000282080710140110800318415030b0040722a0314142c601d0051f92445102940c0c5d40c030340c20001182030584410030214024001042004103a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 229251690 1250 229250440 229250477
    0xa03080402010c15060f05040c090503120901030f05010b0c101103070507030c0209040503180d050a290424090f120c050609010f0501060c08071e050a0606030210 71
    0x340c4000d0410201500c204240729402948604c0c0d40402c80c1c0c14088196601a02e143d6007072035015092045181544d552092401040003200700c072809009001e59201501005003aa000010028117042c4c5130780a0b080020903600c2a1800313044912400f0b600c0d2181d034081e5500c2d24818a030b58503c0c0610380920520038401c040181d9901c010107182c650b036103a116240881c1d8030828608020740010f000000d0004000c400700180c94441c4d00a1220000c44604600304a10300c1000f0310080e0558000300c0403c80400c440e1741f03000010007551900080c40c200b54002c680ba00c403c0849003510711012031400b1107256130b80c4141400884100764414000718459442d040b0140c800010010118000b400a6041041c01520035003440c5800100b916941c2c40c208591a018140690606c01080d1400c8008510729004c2c202ca813080b2600701c0c2c1e40790709081480c1d2741c0d081880311104078201800300b0b80e0115000600c0070483c0754601031040c1d10104980340b851041c0442601e40c0c40700c2405000d26054100c502c400d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 229252940 1250 229251690 229251707
    0x604110f0d11121306090803070816020a0206120c0c160e131a07020c0402070303090b060a290d020a030c0216230418050610050613090b1305010f030b090a03 69
    0x100d80c04124a060628080c40108081d400084c0740c83d0000c000c020103075820440c080d20600414401c900c0303462f07107405c0490f210130039424000c0d44044103004031250300680d40b20603580034540050322071510040c49401440d02083c0c421710301c20312103c0d02c0148402007101e01407540201e000480d04020800b02d0780c036000c0480072034251844c1c0f041e4480020700c016100300b05d08062480c018000b1590b8111a08004014020004050301c1c1000041301003603290426025031800c94144110300701c0c010ba402c1400032407080090841c0c1c44c04c1c0300140300010240207e880200031410b900e1301c0c0001c00014603079000c0d04000c0300d6000400c501d42d0200c0d04010030a241c800d803001c00b0441c0340c404804d642103840020000c01c3e00e0040001d0f0118203010400070420002140342c01000b01e0417003815544da03541c04020b03903071080e001000c6080d04001002c0103c000f49803c08000e40000030402c10106030002040c0041300e0007680400d40c0b1647c85c002c01c205000008540700c2d000b00190014040000050b10003401051 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 229254190 1250 229252940 229252951
    0xd0e070e0c0a09050604060e150c0c060705151305060a0b01050f09030a0803040f02011202160609020d060c0519021911060403050a03030207030e0301150e0604110f0d1112 75
    0x44000415000c024481c060940291130020031464440b911654000c00c41c00613480c10728001c81841e01c4060300c2c00040015200e107800310900410710490b00c002031000c644c0000404850510800b9136010b1940c101040e10703482441c0320f51688000700303540d08206203060009031401401c1840c0036503050503070364004203d9200041034420782d5550b4030440b000c00d2070070200c0c1c0c4c0301621690707002c02400304000301c0080c0c562406000340e8aa210f0011081e101004902c6078031426142c0907030301a1900000b512507003000d00d00c0c6000400440341000a502c65000390740e1129081c0300044c40c000b842c50040495110050541d14842c401000400c0240511204107070980102419001c03000111076665038400c0f04480145501009a035985919890302078040e4002d408214042082d04056034080d0a0510452940c840343e420744141780c528000c00890040e0b40a00941c2d042610380d822610f1103006070008180c1c00c00650303c041e0f07441002c0314840c2c04681134800c4031000383c0c01c04c0102a019055441400e1b4012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 229255440 1250 229254190 229254211
    0x9050606040c0e040f02070b091209150f070c17070b0708030603071a0a0801230d021f0801030b01050907020607050d0603140d030e06062d03120d0e070e 67
    0x200c0d82c03000740d407406018212203622a0418020410b0301d00b00382c028040451155030950115254004002c2c0c49061044200340d8011050041001070311701090111480a000b80c0000d10b006001d100c0c4100a511114098540d1a026002080548401c00e068040c20320360b0009441880d0804040719028850184040d0030359001002203182c6070740500c0340708018016803c504d10307980a40c02c010780407a04104103120101d28044000280425004581000c00340000354896440001200304000c401d00c824041e600506940c006402059014031211000e4849885450700341d03140d440c00055144058010a00803a911000c0c024425000103d0702c0d0401c80d241000d681310050030001c0402000c20350703c0900042000c242d80c074a03448001c10300412882036680d00303004186400d0034a030b41c0c41c8026500c01d904074404940640980081c0c0800320704986041c0d5408100f001c07487c0c0080c1c03400940e0340c03030b03100c50707500c002100b0ad0100a58442c80b000c0380d600c600500750040c506000c0442c40391006103106a0b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 229256690 1250 229255440 229255451
    0x82a03070b060a081c121b081b0d0603050709020703090323060403030e010506030c0a060309020f030132070206010510030948030224070f03030f0905060604 69
    0x1942c603038407000d000e40701350000c41742440303030000c501d48000804903030900202d917440694005803d4a400ba074841400070419803450100800070890f207880c0010407800080150210002d10102c0d12801080b080c4820700000c950f413411403c065080640562009031034520411240001a03001300f42032007241c0e0031044450001d00d10000000c421458008156154040c10382080704068241d4801d5103824500fa008001c0e03075548409040d6503840070030a060b802010b440c01048814403940104040c20b1019042a880c940c5000c0442d00751001100c401d80083d48010780c100e0314140d00d00c108055041ca12048203054202408041e454000c1030041502908107040590080c0d03010341c0200310803a07404828014800780d0000b100c03000c0340e460210a5800c0c2d10888403100680b0100001070340c6083c0b004403031042585103908100d051002c0280614080c03503082504c0a484143d10007426049008181c00c04240001d46070040c101c1d01100110f58a062508101c5004100c0008819621130f02c140e800046 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 229257940 1250 229256690 229256701
    0x2251703040c1a03040c060203091e06160c061b0b0c0d14040f0c050a0e0a0906060806040605010303031103150111010b120729070f0204060b0304082a03070b 69
    0x2c00d21070b8202c0b0b140020f00004810705442480001c600c69801502d41449850701c03101d040b0780700c2c4617000506a1200c0c7c280c06001080f000311003081040c1000610062600340b0100c885100b1020003242130711145204401000b0540e00302050380d45c64049282558542c81c4203650303401c1072080103010f03e0100341012901042c85102c03540008012000e05888410a24043c40c0a81201002d1202120034000c10000050b03142403c809a1017a11007030b0700701c0301c3c80d0382d1044852030080c25004829640035484001c002144074003404414000c9000c3c0d900410190705604000e07042e11345c5602d4286a1a0040080140c2462060610300b14100309280402c00f5180c0c2d400c141d0301401c0b4071509282d001d24003025034101104000780e4030301201c44038501104442c01c40a07504900e94211200d86200080401540002400040c07800143e03c0c0f005000250722910303250b8484682d002103404071342c900301c0018040500880e8078510401c000d5031809800a0701c03184041580c4038041c1c1c40f00103180a0000b80490f4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 229259190 1250 229257940 229257953
    0x30316050a0c020a0e060307060f0210110405220b0a0e040201030f0b101205090a050a0314130b07020117010b0412080403050f0325030e0105030c120403030225170304 73
    0x40b80c040e0020800002c20b078841300e880070a0401a50014420b1085100c0003406a000e1805d4008050701900905012032500704c40340050411946004a01c03101000049807a43c1c8001c841b0403921084d4945408503840b00b030b40d0f0803c0b2940041781c580f04259006080081001654455034000e03420f280115000880b01060405015170b40062035009010f41000d144a03036000024004080050800384415140c0b44103090f107038000380d1400b806507000710320811b011030700440c3c0d40d0700940040c0d00b00c2864000610340c4d614483c0000e400541c0700c1d020002e261001d540c0d000817043d110341d840404c00f006da945002c1c45a4458400c2d845054400c200e884500003e1000d1074060320019a04081500c590210080c90300b44c40e80c0c824040810b0200025600403800c0c504140d80340c0038607a1646030701090030880d00065416410080c100c00040204002c030030b02040d021042d641c056442501c01580b25070955483c440d1807414101a2002d601c0703811602404141c1c11603801040790440503c0075600d8443d410803c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 229260440 1250 229259190 229259207
    0x216330309050a060b18010b030c03060619231c0b03030c0f0a0605011a040501050d090516170c0114090111061e0105010c0218070e13091103030316050a 67
    0x94018012101d8400520006410000001400b124030744c6c00d10800c3e44880e0300e40701d402e02038030215050a100003074810600900954020300c0090016003004aa400f58612409449554500040018030982c00c010020f0301109203000c910208103090046c07440030380c1002000003400980c4035480340203410700c03503d05108450711041640c00b42ca08941030000010303035070010480c04032a19458407000103150081d8021040403000174018441c6001e03d4034004482d150049901104c140d07a4600c0c041c400100100f103445600d0003580c10002c02ca034607161030f10903030301c500b01548413103034100c0320200c1c03c103030390000c09099071000482046850f90700900049500aa5070f03078a075402c81c4a0001030011000300b09000088901c2060361000080e07807110011036051070000d100030b400100d400f600c408904800f40b0a19805042d0307181401e0b40202d15030006858030003414402c3c120b1969140349100b441091400d00f4040d840036001117245040c4038a03641c02403e4100e0269081080200e0300800d801d03c64140c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 229261690 1250 229260440 229260443
    0x3120705130905180c2809020408104b02030106020a120201021903090614130203011a0913050f0703080a1805010503010b0a02070b0a0216330309 64
    0x11a200c0030003100401044e10f45000d5600001c1d0024034a040005051843c00d0b40600030b195080e128101409001c000c616400c40f200a040c14080361040b01403010f000100040c00c028485e40f41e85650a0b021500c80280c8055581c01301065201c004059154100303a4445a49a581c5e24085800d0400181200c01d08500440d03800013000045043c0e00041600686000b500c040d1080081c0341800da00f00c0c81200411000ea0006001c2d0b9400d141c020391200700300700e00810020442c0901c000000c16407074002c503003840e007441402424000f0350809104a0089042c000640180405040000303086280018442d4034100e040712160002c10a06209200650030010201c1d907440d612032a050380950464400000015031022400f01d0070080411240308440068450724a140d08086849110b0352014103c0d40941c801e032100060034840410040c4900c0040d0b40c090540d544000440c1c04031409154040030a0f407000404e028081c051a0350021504c4e8034201b403008101034020420740251107090350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 229262940 1250 229261690 229261717
    0xf030304030e0109080d0e010806030109050703030f03181a0702070e280b0a03030e060f030f0402100903050c1014071a010f060e090403020109020a031518020303120705 74
    0x40c40209a000b00618440d02d00036224022042e44032241c459903202486da018001480102c1007943d40d5020380c844daa00068040d0020807030003100d03220245055a1644210300148200d031911411070340c144101100100b00310352596602c003060311355182c0081c1145402c6d800880500120307030040d0080000200500744501e0855162510119080e465884001c0340300e042c0c02440d030603040c03180340da1044d18200d0400512908007541991030031074a042c40850b250760040b208018181800305600f02a501c0740010b101d007034070107103014030505c03400f141402031030020700c0549401800020b4020403580040e01d0309440b070b4184803148460446107100e40142840800d400018000c090024040c1031417030001e40145038030040e036030314009442c003404548105400641c030386e00b07185000d280c103c1947d03401c14004d100100c0c4640716a00021804104c0340e200300d80004209591402c0e001703940c0610b0a44d040240344c8041000c9550700800d4981c454003021241040c40788000604540c090000da6440740100c56 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 229264190 1250 229262940 229262947
    0x121b0f0914160206070e13020c030c0705061303260706150602120714030c0303131101030c1407020a08010f020c120a091e08010f090209070c020307060507050f03 71
    0x180d512004001064819480060203400612a500c1c81410b484002d0450780c0240b00d255106013080328403e0300f0400090340041040c0e09410a24114005095440221000b643e03640b9004400d9520340019540035501407101400f1000104001070b800d5012a0340010700200c0102c2c0080346000d59039607283c20035000c040003041140034031040e03034014040c480c1d8500b00ca084107074541209a0785c42c201042060030840041181c1c4d400108110f20a40c1c0d0742281c8400c40f4103144182120b1030950300120742c4603103001304204204090119401c0c51401d014800e08041050180000c0000c02e1100c20b40c03108072300d8060014285046489000c102c000070160f8000030042c0f6106110564080e500240311000203110b00402c40d20383c4030803803048076400300c051380340c680050746481000411002c00302051814454204400607480000303002d103074040074040c203000070768103064410020003240280c941c40800488912500068800107122800d4030058202140c482c0007918083d442d184030f9601d003c102d4003002c07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 229265440 1250 229264190 229264199
    0x19030e0102040605121e1506090a0e1b03070504060c03021f020306040b01080c030f040c0f0f060f08040203070509090a020409080d0b06031302041a030a110a090204121b0f 75
    0x40050813050001c1c2e000f194140d107440078916686e003600c10b2505403090f100c074081a81c01880d5420354580410140ca81828550300d54001040c58800e94050a15040404104213600361401d1014410415201c0c08504501303050308020280e001d01e0050500307200984005500740350080107070401140d103013110103d0609081c2c200c00040c1d001641d81d00d0243d41845242d00720341d802448010f100e001142a02c9040d13135102d40320112407010151058070818481c0c0c0c0c02142c07440600c1ea1031005403500140c480e060a180072030007000d10440e010100100841101403100695000c1403010440300c04484001980d168030444030700340f8001c1c00c00294414504580541002140b8020704140074003900d00308502915501409a148402c07154910000c4d40e20311014014a42980309400c24554400d0450319103100d100424a8036081c0c910079a0391007003031400d45e5910b1034181c900d02e014101c0100150705041c6000c488c8a03850801c0540240164800044510a50036449a90b402804d003071008081c1182c0c0c1c3e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 229266690 1250 229265440 229265447
    0xb0909071b1719030f1a0d0213090f050c031603020f0103091704090605040c03050705160c0e0a0912050c0307080d0b0d0c03050706090b090108090a0c140f030d0519030e01020406 78
    0x44044410b04170342400c035480e0700500c1d8540c14139000000035101e5510496150308021540014800c0d503040c89558202d42000b046008d242103045c030303219800400201690804261030400c20001040601c45021800c0c070058031340b040c20080441080c00d0208540b04c40e483c00100700405c15030100b001e160003040029004425410141c00c55105850400c6400c1e199101181510000c50380365001c25020000300c4850100c02204100441c0202200c503e02921802c0428004a00b0b591394500395813500104024428203000f800f55a080c5801d01500c1d101140700001d440e8020800c000e4022480800c0c83c05074255a038100c0485690000c01468464080c1d14140c0300d003000d00d00064403103100d41d81010dd016809204041c083d6456014841d040240d0007004541010005090311082c1c0034524040340000e09900c0e44002620050b1102032000842c4014440d50030400d0303400320b1080d48091400207140d030f0001c3c12a00c0041800b40d9105e00b00d4102042034021b0300030480fa901803076100007400900036070f1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 229267940 1250 229266690 229266701
    0x40e07030b0f131e0203010c03050a0507020109150b01090e0a0e0f0c1309050c2d01140403030c05030c06010f0f120c09050a0b0405010b0909071b171903 67
    0x4600c121080540b40e20709640705516088502d001c44480c0c1d038005074007040c681c100b8000c0c10300c2c9003580d0541c140308950110742174640f156480341c0800d45400611450b400d0030301035190f01030b85502c000c1051400c80c1d02d80d038039010b004022541c5203ea80d10340d4140284d1046621030040e05503c041a50941807500050f402001002400000c070f004201c1101805000480e4a03215101c4c0100300c1148540b0380c0010400500c1c0745c01d802c5034603200d50813060580745c550303c407288042c1e010000d03d10004585001c0d4005502e07d0700345ea06041180b440c150b440c104914400350340903a900340c50000d084e400c00d8a041840d40c0f04803100100c4a1180600002e128451111940107940e0407407480c10581341d0f03640c5805210003440340018030303d17600b101040c0001586030340100d5000d0000b40000c01c6500c0c8890105003161300a03041040c1c204c200160048840c18074035001a00408145451019075102c016202c450444201c002021581411038183c041940c41c0160b0b0120641c1421141d15100c005001800604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 229269190 1250 229267940 229267943
    0x60d0f080a2604080d060e07090302100504030812041e1b0e0f16030b0a030506100b090307030f02010509100305040c0503010606090b0f0706020f0715051501050a0e040e0703 76
    0x4030842c280d107054000c60701c001d01101c1c000b0041d000300381d129035484040c41e804c1343d40f900d80d003903588080006622030f19200302801001c0e0b40d1241140c650440c01403180110010a442e8140902000104000b4816804440d54004200303481030480e1158a06074809055110140780050b8000d41c05000388140c40d0040c04c00501c4d6a480d0140503a03550b0030f100d03801001101c136031881601074400070f50441021920507c451800b450700250072403154000417201e9070aa042550141d102d4402c200350744080400800160881100c181d08195000c80045d54414660100500e44104441910210b90040d0155915454002e055032183c10f0b800d800100104000c403419214aa292500000c4509042c852001030341c14031780c1c4841e400c0c0d0408566800c3c5501401400e40f10307803010801c0c2004a449803003d4803805010303015682ea81c14031402e0070f01a10440c0d42c0f1f00c1241a241005000707100365182d050490f030180c207081c090b03207448290009072a1040d003422204e404c00c5c00c01781e5040d0b80100210302d15050302d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 229270440 1250 229269190 229269197
    0x40f060b0f120106080c0d020307210c02070819031409131413080301060c03050c03040b03060a15050706270b0115090e0c0708071b061e09060305060d0f080a 69
    0x2daa0340c031380481e04940180c800c0030f1040c0d8108039080190080341c00941d8050114200000c0408540c80c600c0002000d44010102c000d907034086074421140e0500044004010f1100205481c0705902c845442081c101003004040c488058160300034010740c00c0a035000030000801842d00c01c40c0b5070038024007501c082c200c11450304041c1d0780054101035002080004550308046207600b503030b0911a0a0b80c00f04100d200a03420322030240006144483d08100a0010741a1001c04645904144050002c00c3c6019040940c142c00503035400d616007980b2605840d101c50f0881008514000c1c4001100c0103100e40701c0c2c407000f010140074201c2c400e000601203001d0407103954050751007007049210740448020a07203000b201d00c4404e509012030301c61813049024045a90180354998601103866a9030300303007202d1039101044d400801d003008003c2180c004c0d1079100718004031194001d900f000f04c1c4c00144051058054041803607508d502264441e00c1d00d82c5c104e43c0c0503034400d0482c1c03c4007101d41445ca2030751300041090b0001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 229271690 1250 229270440 229270477
    0x5010605040317070b0c0901090503030c070303030509120a03021305120d020d09050a030f030512090606010210111b0705120709060803090901060c050118120306140609040f060b0f 79
    0x64004a0f04036841c0c0c64002e0500000b81c1c8800c42102a180e1142c0c008904011414901091580d824001041c2d41d440d000300a111441c9946800b80c05d4405c01041c440007034000c00348003018500d06a04488401846150040c1d4038021808903a454062030342140350003000145145045403030006036030316140381c0c907021102d00c18100d8004460319040350150036044402c2020400c00034489964840c0418440d0800601313103510b4003200c4c074400c031381100c1b02d095075440304090202958060007010444201640140318001100071200003512480c41c40081050701c140303428440401c18080700003e0b01005084c003414980c103e0015907201e450f4000e03160703640c4c6010340c0000d458100104a51340c41c0d0024003940c81076840c0c00303030680b548824880e00313883c19500e40e00b52200f419503000c9030580041c4240c1100c5007490903007500504031151508044101c140d2803800c5c1c140703682da480036141e81c150115408030300c003008215148080d25556000e8031007000c020030700220310300c00e00c000341c681c01240e443d0f107602 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 229272940 1250 229271690 229271723
    0x70305010b09060403080d0908120f31020a0f08070f050a03020307030314070503121e041721310305030112020f1302090a090e07060305071101050106050403 69
    0xc0501c214030540364842004c000400020300d4180103480030100c2c0210005050300c4513110358962340c4c0b05000300d00720000001c04005040e10382c0d2000d9900700002c02c210030049101511070101740307012580c04c810107480c0440740c00e04554030030b007a82010700f5400900c060456030300c1d220b181d5641111b02541d001c40284402c0403946061203a09501102c2c0c0003401409090b00c3c0d500c0c1503c1701c500b03075010061140420409480403800400041c01030080e02000640a45482e420b511882c05250366240380d0558140c00744004502c015013070104000c0b50548840d9940d01d5107000074280850a1300f8507440c080e194040028040cac00d032a00034400c2e603c80b501071b1001040700100b4064161000c0c0010041b030010b000601c0023403400303030329525071030f1014248000c19400080081c201c1008007501c06450b540016920181c0c0c2080401c0000512100d00d09104c07030001598607035114103007405034904140e076030f10020b2003e500c241c0c05183c82d0f5011600800595848040044c0540e02c10301068034040ca000b6a80e50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 229274190 1250 229272940 229272959
    0xf19021b09040b041b1d01060e04020c150901021b0105060f030706021b2805010e0a03030905040c020c2e050f0712211b090815060307180507030501 65
    0x2885180d210456600aa035580c3d43c1100401e10790108040050b00340e00d000c107001030b1b11151907201c225240c40c880e21541c903044005000896145186002c1d9005000203a0307038800016046001000c0740382d0780009a600c45001600901403c5401c0612014418102103505019800203004480c19039440208203442e40501d03660307110610074800107900c00103003a99080a480301e0004903d000500d45000314032500c4400359948130495082900401d0124108010b6030400244507010350140d600c0e90f0442c1c80c40d140030b004d0103841d104503401b031a00c1e88081e106440c400c0c00b002040c2e400c010014070701c0424a150100c40405400350500140c081c81409007000c1d4000d1080d1101d608441c07060b00d02c0e103201c076900c59602002000b03e02d024800c010b80c4204049484c4407402d0707101c83c2d1032100020a04d0601c65004050f440081c881e01c103200310064140025400451403581d2010a102c01050310389452011a142c03035030a40c0b244810030030303441c0d01c40240c081d16000140100740e40c0c0c3d418811780c0d881d94007030f2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 229275440 1250 229274190 229274209
    0x80702030f030a20030d110910020d17040204110403050703030813200a030c06020d020712230a05011b0809010e07091104050a03060e161a0f19021b 65
    0x15404540c3c0310107a011380004000b51001d004000c0020740b03003082807603e05e5034140c1f0340b2840e00200e62100496202c0540c10001c15a020b4888944000d001d0741144000162138440d200c3c1b01d0b261681800c400290075500c40f034100c00054240300c915240d07100e5681c2030668840846000441c0052001000b0a0702ca0000030440702e003580c1c000c00205143d0024201503416000c10305011a0442e400c1103001022034035540119009100c0d540240c031101a00d280000e0400c9103a4010442618500146101003242e240018100b85a50804074285600c00c8480034a00441502d0042c819800d10000a50165800c030107140d000c81a40c0303500c249504d030702a06500381d40309004603500d00d07801220100280c48030f61308100d4a5142d0f10580c20700d402d8403500815043d2520307800c15518103071a0f03481c0c9048101d003000f07140e00544411418000b054103082d1004074418110305005d004c00f50105000d250090340500716004046040308007102c01e6012003010b5200d482e21105000e03c0310300b42c4040310780e03400d1081c0754 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 229276690 1250 229275440 229275457
    0x9030c06050a14040503060c1c0c081602030c15090304080106120201080108150a02030c09040e0a0c0e070203191115010504050c0703080f1806070512070f0c020f040209060403080702030f03 83
    0x1800300303540c9100082d000c9402898810327503803240300030288a21303000384d21400214200580d076044451038460080707586036001c001941c0071948100010001c40301c0114041da01820340350641c00c906c0d250102080d01d107004503000000c180d40b0340540050280c1c40c881d880b40d850b07403003030300d403403006a0780d030707900b880e2900703003071030440302c10781301c200c00240c00d0950070340c001e661214081c21040d05261741c080100c0d044030003049046c411517103c520103005101201d48142c0040006e0340c06d184041c684008002d4030303030081e1005000b00e5101c181180c65024015003241c003502c0d81c0c6104542d1016031082c100c9554000c00c2c0f140c0c0c5c2c0103038509008280c4601d00b80303085410b0150141c07204641511490681250604010543204800d035111826880e81441444404d000360342c1640c401d500d400e0380c44100ca400a1003d002c00c42441000140030400b560451503c90382035804803103070340300d400740d800116000c5d103d01d580d038560010001401000300302d17550014040c0d09009030121002014014809a82c0c0e200390000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 229277940 1250 229276690 229276693
    0x8010b0a0518150a12060e010b04051003110109031e11040c02030a0c02040f020301081006140f0607050c0405090717010b0d02060705010b42041509030c06050a14040503 74
    0x612115003450312030030800e000351004d0b854641e00c603810469090707403130700403185103860741180c000b084024000c0205003042200d0400031790800448038548402d903407000400c040259102585240e010380128001181c0241c6c441e0001e00c45407820a0f4101c1c4030003801c41d81c80301d1150708452035003001c3c0f080b40c4c1500c02c80c1d00203500c1c3c00618401992501048441240d00c9520f448055010240707900186000b0040c410003071074030301d01d114044020340d0303a1500016400b010000e18203000381e82e00380000310780388020303102d8998401c0c480c1846810132000e2030349641c002e81050107000102e50005042001c42d11103031500150300244032910f900344c408200c2c807540c0c0005103840c00005403400c6030040500314031840000400c212f01b440410040071074140300d200f95941e0007000091101b41100c800b640c41403050081038980884884114081c0210702480e07080c0c0b9440540014040e0041d00760f11301071a004145c0b1510181d41e5100204a030744824080b1001070940c0400c10305102c07240c000c2c2d80c15248000c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 229279190 1250 229277940 229277989
    0x60f010e01090207140d081008010506030c0111010902100906090605090907030e0a060f0f0608030702010c12020109080c0f01060f08030702010305040f0813050102061506300108010b0a05 82
    0x91082c003a420000003074034025180f1501d50140c45e03080001c481c241004c0d8807016602d00c1c00c041c8034812107805610040099042c1b104010143e500802c180d00300e01802d007010100d0220b4011143d00400240c00000d4000d005800071154964000408a00300e91195030b441003141d4039018200c3c1c141c082c00603a10740004a2602084040f0701070303000000303440c5802e0202c500c0d1036046d49400041e00c1c072420001e0402e5641c2d140702c0341d400d5514003804002e0004440214501072580d400208810140c031070180c00c2810712600818001c2c03003908418000b5400680d40d039111400100000d8070307403441d8803d52545610308440000d481c1d40300310b00c9608503245040034505000054005501522004104503003451100c4047d100041c800400340072003074520341c078440b003103800c207400a841c1c424098003400010b1581684041980c2d5098212004036440c00011004000b50f00300c10303201d010b81e07442c00c1d50428901400200da03246056000c0748002e030046030080c601c140d441090190b1442058004410800d130344 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 229280440 1250 229279190 229279199
    0x1b020601050f01020f1506010e12060f040203030f07150b0409031e02011401030809090106020111090d0f080f030a0516080703051314011410142701030b09060f010e01 73
    0x200d02c900740592041c0140e075404c2c825180401c2c01c0c0382900484000182c0041d051045d507503030002d0001e40e5100282c95225521845100c0b0380d545000040a903000c84c10f1a00015003107407004e1040d10300300818403440d40c1c2c840e00340b440c1084c130009480c0380380c1e030f48075150910004040c80d141c01401101500342d1503250941140c02070500c0008030361001001950740303038103007a21850401501c407802076005450268507a210401041400711040c1c1c01007007160b04004494000400e004111040c2002c11070342c2d0407030031560b850011686030388000090304400c0e0108100c881b01604500940c0f1400711900104425912903102000980c2404002000076071504006400305002e584596044000011018141c96007943e070018420070107000281c82c0c1e515200703e200622140c040c0c4a4014280380d012050711130070a00f0030074107010b80700c141c1d5219601c0051a441411601c0c0040f00c00d0382c44200b6030140d50340c5c5a08000c001080c05881c40051303840350f0000a0805080001c446041e500c08640c000041c0e40790 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 229281690 1250 229280440 229280449
    0xa090b06040b1503130f03091d07021b010903081b060f04150203040516060f0f08090c010e2b0201080717060909030c071805090a08030c0a09050d0303050a1b02060105 73
    0x806861042c0070000ba50001701d0362903201b000045100c0c0e0395074004030303050840682004040c20b07088001040d8010521003030340d8011400382d51590707403545006000040c0d200100c40c0d8003401c2d80040e0058a0018000b01c403c107890741d00030305c1681040c0480b42c1a072181d00080d80d2032281102e010b01045078980e2030710031010a60300195000380c00798044540c100d40400504004552640c0b040010a01c0c1c0c50080940b10b40102c9015400c0e1032a051010807450504500b540381da88106145040202d48205e20003d40e9a0781d046440100c0700c001d10040382000c03640c0340200512201c005070302290b58440026500c612445200808019010384000240c4420062000100300604100103500041c01011504001017141a0040c41e0f10b49a84181150341c80c2040c0c21281d02810a50640d00a1250300b0080b84060045941200850b80d003651b68803070584e01160120096040316600c00914640407003456416001140958400c210070001c41c151003091143c80401005104003580001c0010404c0349031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 229282940 1250 229281690 229281697
    0x309030f0606090f0b01020c04142a0c01020d1503241803020303040c0b19120605061c06170c0f030c0603011d0a06030c0e04030210050a090b06040b15 66
    0x1040e00041480b03500c804901050f19441e441c80601203030f071a24013139855079042000608400007650100030b0100c88840c00c0c9068080140600ca0b444003000164480c1d500c6500c0304400690f416008903107410805e0950f50103036000c614988007090404803140e01003246130540c0300480750300ca101d8070120101c2903500c14500702125041880789698036021903420410180741c240780c6209602441c0d89180c1494070040a2401e50480d07100c801080c02910190340306900c81a201264a0420841c1c03804078185103005420f803604500d800c410082220024000c205c005c01d4601c00b030845040c07150b00d440300c1c4090004c00300300d0044c1165a0143c0007456a50801960044440c0006000e851a0800a82c04107496900a0380209080390310784055082c2d52042e15083c0307400600b98501406014510340303900707595110714024561a21070280206040500800107112540c0a444080c85541345c20404440240000c0303a003a01c20101e0308002030814640b48c812420465002040b254041400b00c0420000c0d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 229284190 1250 229282940 229282943
    0xf060b0414010e040c121b0c1b050a0e01031a1504020d09021203030106021c0906030b0316090605010e03070b040b03042306160509010c080a0903080c160e040309030f 73
    0x2403034415925903204e5004070040004643c0721004040d510005200803202d000030440102c125860145101e10750014130290059041403440c2d900041140c0003100e070540f254002a80b1200c9481c002418402e91000c140c120f078096480080885465014110642400c41d5401c3c003088600303221030040d103419400380c0180610480000740610082e03003c6640080c4150f5503840c00e41c4040010056a541000811742106d04001854800042180064280c01240c007411040c1034807085104400d4070100006021106101031001e0b003982c1d680a4200100b006005050010b1851460b08901e8200000e6034021940a09207951a02d442d241140c0e0181d0000781c411506070b040c0c01541e1400800503100302d2891490742020301081d0500021482484550410304420f120b014080c840290f07801c4404040c0f400d800c00c10540d61540e961078110f40b109050341000708090300c003040f00c00454a001402402d400d40f010704040c06142c0f92510000da8038802c4400600150325198103000113201014a6181d07107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 229285440 1250 229284190 229284197
    0x1a0d0c0612060503010f0906060f0b040506180904120f020312150a08100c09050111030d0e280b09061b0a050d0f050a0b10121a09011203030f060b041401 67
    0x2911000013900b900c446d16403410a440d110892942802850310400c80200f581d81c04440106180c640d610304203010700d1041a202d00ea0118684800702e00c0301e01c0c440a2a0360003024900149820b2610a6000c60460860b40010301c04004001d5014000001c45209001880311111169078000100545071662007840350084a086000600200108006020b4031400f50020407080c02c2848010600110703940598104814100316400350746c408011103112505031b00000c149102d2000360700c3d151a980070380c0503400044483d8104a401400403512041a2107841074145030388070f0340310b0719030745410544092400c40c0f014803c040010409000505202b2514140107050a003c00034007411500c054140b054802c1c4c85070b04000341410903110b00a1801d2048542e03010740101e001c0004e04010400c0c680c5420582d81b0300900301c45200b400c00360754281400401c01c075a0f07588c5070390101106000803141240400e0400c1d50b103131a09403842c05440b00340c8154440d464181894a00d1000000952643d0681030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 229286690 1250 229285440 229285451
    0xf1b0c090c09041d15160305011215090b0114090c031509040f02030d03050a0b01020f060604020a14040303020d110304061b0303020d0e031308120414061c1a0d0c0612 73
    0x1000c4213004446003090071714000300d124500f8110400c146000a98904101407405005214140b40b513040310302003d801054550b902003400740761100038580400050300c2c02d6168000065034062440c41469030320003c0d10103004c039403a0220780150b140800e44000318035070546201d01c04c507801d0000d1041d500a006914058001003a5000300c0e0506041c0d0f02d000700002d44601c100842c4039000d000c0c19001080030300c000c00e4850030403414603440340300c003038005031255400044c2e241185204921b44035503000704100300d0b540c07a9640e10340030795600c2100d56a42c02103601d03000b0708a5168804015101140e03d02d4403844640784900d20000040e82880e0310403400e0560070f01c1065504010740c031038070013004003100040d075035400d00c003480c41041600d41e8000c0700e84d80e0203158503841000d54241603400311070380040e40c12001c02220300025040c0c0652490303450045501c203400c070328444240d0404180c0d440412a0151080d0b018414010104c010001c09071862123800c00c1081030030b1051859241c510352031600040e8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 229287940 1250 229286690 229286741
    0x11040f15140a08010518060a0b03071101060b0306010f1806050f0c0109060e100905100e0c09130c0b270402041203080405060108060708010b07080f1b0c090c0904 71
    0x880b90480c1462200149650005110a0625020b841044040594030b50454604400081c0c0100554040c410001706c0100c0401c50f2140580150314010000034001e1040e151915076213182500202c50150004415040d81040d0724010b250411000c0d0300400c0d40341c076090600300140c40f5507000300303c501070502c0108a40c0c03030240002c0c0300c1d401a0921410008c10400500103c0e81d241c5a03449101d5903907549042110070006e031300000c01c03903250040004041403416840450606000104a00725044013200040040c082d00c80025055013500c50307025011032a4813000f03038240302e00840c01c04010740302d203400303503000c40607007402da52808400020000361400b0385401081c4440b02c001001240440c64403024441040020700c551409000408002c190601d8042c8004080d8079042c454681c80040c009105402c3c0701400c81250b060340e104412065891030f81c00350340385002441100c10700c2030b80140154008075140c000d17807440c002c000c2c0110f414140000c00c010403005080107101003a04a8031501d0b10038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 229289190 1250 229287940 229287977
    0x21e07030c12050705010503151e0405040305040603050a02070206030622020a0e0102060f06030604080c0102040b1215100e040209030a0614090609060103080a0302030414010615020111040f15 84
    0x38111000d2501c0300042c1503e0314503e088565046507061080c2407041007201180700d641200c103580d0484011000c0350004138603048404140c12095002800c010405c0b050541100c005c00803104190360130420be6a6501c1d40781c08070b000c1c0b4500258009801c20101d40030f0320307201e00035221940880c03003100d0328840f180c00110201e91100803460301140803503101c0c110070368050109541c403981b52191081146070a01c00a600c800c030080004059000c081403010701100d007581514003a00b03a1134060782d5900d070400d07a200c0b00b95004455020100c0d60f020400440c5041c040c407209685542500c2e2208400b01d004100320283d00812103031038061003160303d0700c0045500c0e40101e8184a0038035075280c00300d0030a0000f150400c000144800025403140004100240340c0004540140d8024074005849032240d01d0281100c0b07180b441d55000ca5802c0400c08507154102c4105e05524101c07075002007104405500c0d000a4a0140c1d01c14002d00c220401810845040b03082c424082c0d090103480c1030030580f0503c3c05800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 229290440 1250 229289190 229289213
    0xf0718060305090c0402030c0307110f01051005091e0c0904090606031a09030a0c080304020d0203060711070f05060409020c0316150f0e060610021e01150e0403021e0703 74
    0xb0340360018096072080601291001e075105841c15803070b41c50030007180704441c80040c0900080118100e81c4072407000d018465402c41004420090001d42410302481181c0040e901a1500c5540c050012860080d202e008080f03004442c0c03504180580c1e0384203034450654200c8130034642c0040d11052a100020390a114900c0650b10400f141c0108040c01880c01d284c148005056651551042240c0c8170365075081000056036661220400744d0329036840c404034040b681c06c900000e40501c100400d1068803038001c2000d0310500b24040480748256580c020005042605204850304000200400d2204608d95002081407030410310460385401c074a040c040928804980b0191403211000c41e0343c01d2052158062000300d950904070a00c5003000b210300d550303152140604241d00c100c410350f442004403402403140080c2c1542034890005c5514030001c80502925850f4000840c0a48105002ca550805510204d000303d41503070060031407100090707120000e019001070b00c240f140700c0c4210020000ba40355840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 229291690 1250 229290440 229290449
    0x5030d02063c0601030f0219020f0d0e01052206020d020d0c080a0309051e0109020102100501151d0603010906050f0a06080a0b041806061e0305060f0718 67
    0x60509203000b00340310342d1900b4105103190650403400ca80ca8040c15203103902400060480700d4141c01c0392220700059008002c004c00c0d2805007400880c01200c05100180c0c52140d00f86150243c0707850300c1c082039403143c688081c2800203001c03e05410014445500c01c0004e007980d6641c030140c00c0760860200860301c15000b41903102c84016804192806002039050205e1402403150b82451041e80220740e640506a0144c2c5032090105951201c0d1401807140812120900410610500d4213001814440700c1c0a021840c1003a4054442e000c8a580d02c81010702c00d0a04a40c1052416a0724111000b41211000f803c02e5128080c0019424198020b5039401d004600901c0d410a0003d02c0e14681002e0051400568294a10071600c03074804020b0107030010803d6920201e034400010345082c3d001c0000740242445502c0b0700c20740000000117000c100242c0c2c40389066402020410524500c00180080d031585540401411078010401240c4c4990168081c0c2d42c2000441c20041d082c280c0c00c40803c800d54000354407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 229292940 1250 229291690 229291693
    0x41a03151b0705010f2f1216020a0c0e0a0605030c0a03020d0305041e060f030b0d02010302090103060e1014090108151003080a0903030306080a110d0206120a0902100c03020a1b05030d02 81
    0x6c0c1d10310400700d0703030021021210701705055506041446403030403203040c3d0040100c16440135548040b444540b0034490400c81c01c0e030111504007880d48490103910f2641088072485060751402c4c0c03000c159071400003000c0e500a0380041c241e0208030b0941c0c0c20700c03000900f01e5900300c0c240301b42404080341c1c107080000c2000e002d04006070f04000c1c0318a0807074020300c80c501003206a02130502e4244130600e0707601d131864941500381e02800c02580c0c40d044040120700a0100d5070003000164000c00501044540d101c3c03124085a404500051a0008060070810850828860f22a440e405100c0b941e80c8548008001c80d44442c000700003103840c5540740c884071140d5118854030400900b107010300340b04040e094481c503c054003600005003011003c039a540414000010b582d544a0485800d03410210340d00d00c0e0844403050704503422002e146c14019814009081c1d590412441840c0f252940c0d88041d21030f007038160826070036500524060240780c030f80d0074000640c161340c1c0c00320f412071000109841d18200811580707000c8650 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 229294190 1250 229292940 229292981
    0x512160f03050702060f07091a1309060e280f1d060601050901050322050d080a1401090c0905060a0203042301140c01020405041a03151b0705010f 64
    0x94024405140c21032a00c0038186010300784000300ea40010079660003441c00c0403001035602c40071401d039110412540040311000b00084210079001000f0060a100034014034100c04413a02e40c4c901d0030648a150280f800303c44800000141c1303494000c03406103401c0d04030301561301c0100c501d002d580303060701c01e009500d4140544a1041c0b0401d06000002d1204051459025004504100000a01f54820b490030307281001f00101c0800d085802524462400d07094189401d5400d403803134a440e60f15061107064900104c1c860074002089566140602c0185034041000c00c281c2d607007000070980c0100190380c440010400810008211a1207403001000c0012151b0021034a462411840042425200a0714002042c07103c15444059030420060440e4516403054191110039041c0501e0081c010b55105503801fa08102800c00740701159501c908404c1015002e5031540c52281e540c40041a03410303a07513101310103805460f003980b400c29000a440304500c285c0006c52507110390f801e802c09451403490f1447ea0b00b803030751 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 229295440 1250 229294190 229294231
    0x51005120705030d050d020d09030c032d110102130b04050a08030403020d0201030e0f25060507050705012f0c0f0d0803040b040c050d050114060607020a150512 70
    0xc0c005180c026242801085924208030100303403030701005030b040018454003040481103124150152041001b42100410003080c16003070040c40403004141c00e0740481d0f008000c9100c400681c5031181100508000c5842914080700000c0380d0290710000d200165550074040d44246008000b010802895040065501d5504110400c940030103558040780c0c1692081204100507240c4040d0302e2041a02402d0000d80124906003042c20446030707000d8000309006420003001c034005a08103009030700400c070320506902030b206c070800e07181e0b0b11030000c003d445680119002c2056604c200c402c4900a5090150980ca41d80c941652083d034480c02c40490240e0380002055404d0360410f09512038484504683e45c1e6240400c0303071180d20441c03201500140c00c0b0051400002c080c0000c06e03d403a001484041c200742d401c2c1c003160030164000d284e03105132103201e50019404540e403440d05105850065400400e08280585001114030500620381660703414014240512190140115030092051001c40d04200d65000318 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 229296690 1250 229295440 229295449
    0x20307110705101b06060f08010218010813060e01111308100203060d060902220920030d051b010c05070b0c0f04060c02040905071413020705030a05130801051005 71
    0x10340010340209420503900080f42c1c1c1c04030708507201a590f0021411030507901c5c140340e40074111981203420007007100c3c170000804000550080039861014640c82001e03e1003000110340800b003c1d5079030f841d1451580d90322004a1855803010048801e03003000001c0031554060414081c1e00b143e6034840702681c0380c800800102609008220064042080843c035514000380000c0798405171100107000190f480b10f45100710f48960700d07000340c40d000c9d00141c0c100f10002814914040c20060900b182e5920144503803003618816121a00ca2110008001d400400e0410400b151250042d00c140016031403041c40b0010208802e1203982503200300c9603100d1341e1300c00c0d090030001340c2850040c041c036611f070408215164000341e13400c05890903180345240012050b01c1600000b80a01041100a000d6000d04e03030707000601d070043c2200307161074600c1075134500c0141029030081d40484c0034881c07000e801c82d08200704440000d84124010300090703180c0404c0004003620303030b08200e0071124125103540681a00340400e20003480c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 229297940 1250 229296690 229296703
    0x30b070e130e07061b06021206030c030606060a030209030a0209011d0c160f02060d050a1d120a0c0510110912010e0a120c0f08040501030b060307140304030302040902030711 76
    0x21003001030025910908205036034a0781c0780308200170021660307a22500070980811100d080d640181c1c2c29511103110201410700d1410035503103d4824404d02c0c000420340c1c2404104544281c8006104ad401d01d42149e4042d0080e6001b9052680e050003074101a0005950f811007490207072034955040400421402c181c0c04484501801e01c0444110504c661200c505181300061a2607601c003030040c002052620115503a80500850035401030304000410840300c00e26030188107012440d150000c04030951400c9152034941b5240078401c0710b0740c200004600c40e802240341022842c4640c08a0f858200b51840010845040c21504c0b06401000240008a80751020030160042070880c0200320600e41c4200d80c3c0d59420582100130126003001a808110034011b86081c84d1045c2c01a034068000202d62a0400d855032050003000c0c0070a180c00c5199005041071021340344140c0f003c3e01c45c9081107a446440000c0b903003004001b20101602000007081a00f001e00143d4010002da0700c0f649404102010300605000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 229299190 1250 229297940 229297969
    0x100213050913030e180c0a110102070f030210092003030910050705010c081611030904020408150a0204030b040611070f1a060306102607180506030118060f06030b070e 73
    0x65a4017407000c190305040e22203070b400c0100c00014903500d010501050f1066410140110b00d29407001ca000828454903a07070410203e44039900b522120400c240c804d0044034858072002d044e9480b000c42c010300021502100601c0b0001c0101281d041003031440016480402e1095001c0c0020004201c9004004090203090b1014a10741805561031800551540485000b008544100066a2045401c0c80002d00c12980343e480054001c1d0b642e0350300c40d44000e503281c411118415100340083d0008040d13640e01e10036074094075840f0300c0d002c01a0b140c82d1611400b501296003201c8403004100301040000700050441c440d07851044c0c01c1d10010380d0240b00003e0408500400e440d009800803400c1044001180040105641c010002c0c000d044440780d50410b445d01d01034481c803c56214200c0042a640004020750030607503038078102400240d0703400080c10b080c3e910b070014164030000070306060000603082d40c00020110700803400008110f80e403501c40e07001c0090141c45020200e19090910603040c00d00c07022042d00c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 229300440 1250 229299190 229299199
    0x110106080601062a020604060906080903030108150c0f0304060903032306040c02030f0c01020301080d0c0206070b0628170f072607080309100e03100213050913030e 72
    0x20341c5002c3d0041c00581103080f4100d400c0b2188442080d00a01410115980e10b4002d0804c903101c03078807100d003c0e10b080202e00a000c082036034100000d0111000008590685030000d026165101900744540112400542545903040c81030041500003500000030318070580c02400c01045c101c1c29410301034112040300122a840008001042203260001c0c880300340c10207820340c3e0024800200d920121700350300500034082c2c0a54800224040710180c150055410b8840700c2003540d80381000c41800f41c070181c68404d4029004a0140081800b02c1c6908620a500032009040c4c414900d00343e110b44005088420b0042501086010701846010032113074101004c22002c05c000c0490b0b030140d0022640d11500c0e8494440d0400b2a00d890188104244461152041c1c1c0d00b411610000e8650700200c0c0c0f05c0d081814118000d0109480c5590400c1c480c80c0791500802c0098023034403203648007408000c041c0d03100808072040c0d51005800064252110507956104100e94200c9031080d825902d402882c0460850020307118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 229301690 1250 229300440 229300453
    0x1060e0604051302090a1404110f12070915080a050610050a03210507020a030c0510080c16030318062301050105040b091318060c09080a1b0503030a11010608 69
    0x9040043d41e038440c66011208075015584003007004d00903101c1c2100710041c1079990710901080020301500c0d080d0501048a010f40c020003003209120002c40d0020b584015540840400c210049e00c60384104440240300070301c10210f80d04c2e400424a403018562049860750700480800c4005041800000f02814040303819200c0360346140c03941121a029600342c0e8900e00400081014800c0c016421070307d0295016004000940e520300701418956507901c41c242c0204c1c2c01e501c1d5a035443d40b003100514460925440560b042c925801141200b03001c84c44421020f15031b9990b80c1d0f40514991840c0c2d0241c40d4461070700481c0f01d141c0e20248109402044507a805e0002c01c140040c4126a040320507903082d1368409a84546903000f582c009100d8100c210000d99080b460a03451440c50440140003001160095209000c1c1050314002190003e80911070748803150001414100000c01198101013410340011078103050307a403a180080c0c00c43d80900200c902140128480043c00c500170701a9100400b98200549007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 229302940 1250 229301690 229301701
    0x90f1b040314210d0f14010f030c0501020d09030f050f03031611030702010c08030408090a0303090602010c0921080c0607020f070e0115050d0207060e010c110118080307050d0c0201060e060405 84
    0x2c3c076014040300b40286644a038420034500074103038030042104051644241c070350750b0b44442c91110541c2c1d034082607914841101c000f080030750002611043d44030035035030750040480c42d586882c1c8201100d0381d42110304c0e00034030380805103504040010351f02800c00c85901c1c0c0e01c034a40241001d04101c5e40b2610005107500f003400144003503a0000520035146810480103a0789640301e280c58020b074414100000d90000c4652804020f2540c050b0240c0e00380c840b0707a0001c02c2250520038096441200764410f145107960840c0312042c0d00440e007000085036900c20319000b406c0140d40b6030340740d0600908440110050b4000e0300f140b100b40100700700300401424480404449075041c40207019841c00050040b0060201c0090790040c003400a038100d0309030740e420a108100c00098111401c1c042c2604400b888002031400309030341c2d44e111042c820f4000c03411107006a0028040940e40c1e03007a0302e8100a21b07400500400348100d2103804818018102010700541c00010000e0910700f048074002c60107030240f07004c2d83c41e0104100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 229304190 1250 229302940 229303003
    0x1807060c050325060606090914040b06010f020f030c06090613030503070c0201090320040e010e0303060d060e06130501050709150c05011808030411040902090f1b040314 74
    0x145801a900c1c10038050000518080c03024000820b0f00500c664030b001000540d26500500d0441074808030001440100d0305400365104410054902421000c4220007240d1258010a04006a031000d8010340ba040c20503100ea003400c507080100d2040c02c0390802410000c116600b803001c640c0c049106402d20251180c0c41d24000c0507400b000340150f0030b0116150215041d60300900b50780c00215401030256500c016403100b0000180c0290721014042c07420070040014907081030203181000c0c40782100440c1580c1d90340040141c0300441800a4072595511000300142c24014403200d4840c292441c03806010300560700d001403c49000402040400c8114035041c00119050000940703403801c40d1401103031600c55418054014a49080c00024080030012203800b0825402c0141d40b00d0390050004a048600748002d101c10b03907140040c000d5101125100091400d6a940006500281d528803101c2800c0102c145050407540507410544410030b124100c81c0c11002e0030850002c50700703148405401c14206d42003546 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 229305440 1250 229304190 229304197
    0x1e0506010315091a1504090506061303060e010507050405100e150403051e01140705090a080d030c02190201080105090910060e04051902060306040f02090339010804020603070c06051807060c0503 85
    0xc0f5007039265004110a592ba40040d6a013403100c180c099030007550f0302d2400303100400a210301c0c80c07059424200022845030040d0300740e60407a039016207882c0380c6502c00b04040790303590002101c4c00d1740881c030303c0d010056545050000d400518852401403d4001e00c4c500a81555036500b150304441da030621030300120f0292540855600600541400764403200400002281000181c0080b10765109048103985880d81c55088410004070399001d13074540840b0340c84007002c00505a98064040b443c40e40040000e81800c107201e6a0062000c0103940d1401b0701d0f505003809844042e40415a0100144c06002c1846400d202c0e0251650380e40c01c0341840e1711a160301081140c00002c242c28400c580d11504000d0b0705600c2d804a8a16020040c2502c00320350091103c614503c1041400110000341003014111510712410300810500b816103413052565102d500f000b0007584000d049908111030840c0040020340607010720b81c0111300c8151002034600c160140c683c0f500c1c0311035103c07408101542110401043e0040308a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 229306690 1250 229305440 229305449
    0x1215030605070302090d05011d03041a0708070507140111010209030a17120f0109060f0b0d0915140619060e1311040305030c060a1e0506010315091a1504 67
    0x8502569070482c250f0081c080c0c4c0c07066a070000b11143c4488200441944000000c44203400d5070710000110300c940315640e00944c0144154000000380140303121140c00044c00003c0c0c80303000384a11b4021540e07a0181010074660003130441c10b08092040c41190380200b44010044c012030021030401c5a14000a55a00c2003001c5c080e0000a0740c0d140d40b03a40031800400c480440000b0740741d0003828100031004060f201424814168401d01d000c03008518900495141801c5035854110740b4140b29000364607400400020200300c4c2d403001c003415241d4030701c420b80c05511126030007500308914516020b01031000000d010744944090440380002444215040309051a80003425200040c902d00d08551500081200304015031400c1004035002013040000402000390055a80c152100ca0b1903581426007a0740d54120311040034200c0d03040280080c01d044c0d1203a03600c0901490701245121412494009100990304500c4007692280c01c5640c06010000c0c141c4100307030301515800c0c4d980400c02c1d600300700c0340070f035018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 229307940 1250 229306690 229306703
    0x80114061603030e01020418050a0209031c0c0b0903030a0608030301080709110708160309290a031401080d0801050306010e18010603050102030a331707180903121503 73
    0x41034002e141c402d0f0f01401040d41c03154000c6560782d45428a07030480b80c683c102c2c5094254108000542e100216000f902c031b140030098010301c00720468080b03001000c0009482c08003001a50581c14010070081c200040c010000c03c0c0c041c69803818007185400039568550003d122940c01080100898240050220112021b00000242004c02c0010015461003006000b821262001c560800f20740d14404440300d00c50312035181c1108440d600c034000c4041741c0c1500c1d044c280c814481c1e0901d4551003441e4008124156492800040f8004901400102c541d0280c1080003194882e5440c4040c80750040546805004210000c000c80e61402c00b110503104002094265031800c0c05841c0400d8a100750030031800f46a004000f59121f260550703064008010b0142d0045007804d160039204a1094180710041240042c112514100c609095040602d0996901d000b03203103100b0030000150745001e0a00c032001102400801042050407400c00400c11f000b041e280003d40d07841e0100e00c4803030f050118541c0b42225030108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 229309190 1250 229307940 229307977
    0x40e091603030e040e010f0219090f060203070201111914010c110a020f030304091e050627090f070306061508010f0e0c09280b160b060a0315060608011406 68
    0x4000c2d01500501d070a821f4118000700d10410001c17102511000e40001907a0b4200c10184d4518444803481d4540c03082070050b800800c05000035500c12001824096401d40403601c009100508000400c000e000040e255401c0c5030f880306100e10030a00901083d50000d00d4101c1c00340c07440c06641610f600e0000802031141c210b4103c0da11880d213003032094400601c0d0b101d004218041e100c002e402c001c480b501c00014261458076002800c10300e05040703003c038040c40c0e55001e40020b6585100414801e840a0050449441804201002c0700000c1004202440c42180041100c034500300c0c607980c0700e40c0c01b011100140801a80180060a082d0018004440c90008005a251581110034469100b00c86015070000d0356828404403940125511040c10551040441d03507259035048100e5582c00752840101100380040032a40104450500190b04030a0081c05101c44070f54a558841507405c102e505191201e0704c80b80c00708142074111008900403e0016615240e18a645001845510514058600c0000c0c2d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 229310440 1250 229309190 229309211
    0x915030218190e0f090706110c1e031f0b100206160e06071208060603071b0204020c0a15060b0316120b060408071406070b071b020303040e091603030e04 67
    0x1424104001c000070010b43c48181803c41214424001c00c8600c10b125203d40c05001030300070b1007114109880d04842000d800001211801c0044212801c1d0104040403007a11010740d480d83c0501c07003400c62203500100b15032142100700c0d40c41e01340c844d5011214814650100e011000d1600410450b81c01726540f0400c00d089154814143c44240704a1031040d009080442c100081100803071080544075040d4a441c1440d5450000b0000c1602c8129010800641c1e2040740110120a0350503681c1e140d0b1008201608009200504514100380d920050340c00761b68580113291041d00621400000c0c003040e0641c0c81c558a000070849205107006a240d004001c01007071903035039050150b80042c005480061882c1d603102e542c1c08000e503561a070b030300900d103d222414503641070700d103070200446180545c000701c900e13803d03075030031070305541c810f581545541d2008900c00c0417400680c1e00340020400b50104901048240c20102002850401e9030380d00100e2300340c007507081030001c281c200542c0c00325290120303004503120704c0b40e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 229311690 1250 229310440 229310479
    0x201020c01180f0f06081b040501050706090501020d0203041403040806220b0420061c0213030602121006020c01021506030a05010e030405040516050d0b120d0915030218 74
    0x203da100d020303903504061001c16035014500300c44017180d05950342c003007041e12010310649400c06610115010340350100020003582d40144040c00144d4025080041c030700780640c4038113003a0781c8a0444c0c403072900d50000401c01008003c0409215000041000390b05107410b1542a41ea07600001d45019181408141130703038860104075006130320740c0b54002c40700041800c0910307180706116202c50036981d080c0030200300001d0500340300c03007a500a07007003260550070350345424078207100258050150105149480c100100100e12035000410800600100c07401c103a01e403409001007500016006030b000c640000c0441e03845603038005103c050260700303030304008103649880c40020b24010b507000f03008203d9401d12400717203e920808000750003224002e96061080c0d0365805c034034166290f41d0a2481000c500c0511880d400304000358004d11031900007422807090002078003825803a05030200ba8000004010903010702c50007091180442055415040650505458401e107801c0140314590582c00fa84081181041200c41d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 229312940 1250 229311690 229311737
    0x1509060507060e0a14011a010504050405100f06020c09160c0b10081203061534080403080304110103020903070605031b03090708190804050d050c03010204060302040f0e040201020c01 80
    0x5510104d410800540c0740c103031070041498a425141e0b500c1d084800441c100c000c1d80036816641d0507075030360746003c1c142000c00c801408040c1c80c2600c0311010040c041541070503003408402070070060b00100025202e400c1084000f010040440f2010450701051820082d00706004140f03040d8000020076136682d90608050341115994040030b044d10800b2501d0500b10342050041d40100d600341c0341c01c01b007190117610304405841007006001c400700c89100800c44120380f1050107501e0761004860b041c014181c80c0c651001c02c0c1c005820039980510000140000c010007402501c8401c842800c4c1941081d06c2e1000103034030f8000612802c3e0500900200040c00340b00038280404807400710080254407030420103405961030301e940c020b18403140700d085140c41903004004a0141c00550090746686484c3c1420f003440341504035514100c5152255062103405982e00707002410142c1410b980068480e8905080700043d080030341e102104504110f003d10015076408503030012104401c2c01c04600070900c900f5410700641 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 229314190 1250 229312940 229312961
    0x409050105190b030f0a0b04050a0b16020c011107050f01020111030c190302031317160b06011413120305131203030b0f1f03020f03100302030106150906050706 70
    0x1480d05080042c071140c0c00810300300c641001d41c0304026180c600d0003810790b00d04a40341c240d0010351120300488001500b00541d00d602c588154141d83d040c012a0780c800d00070800c1595061144448403410100c0154100302050f44c5039824a0901e1000c4041a21a910707004d003401414018031240c684c86106034005d40104001c044941140c0d540c1f80342280d121141c0d900810300881404e4400c0780e80f031410304d100340240d034000c1401c2e140403484e03101c4503608c0d0349461502c80704400c00302005005a2820619030300c0075441c1d203401142803200a10300308000429040490348001e8004000380700240b0800e1303400814074180c641c0041c1c80b000c00152410240c2d820b0141d6024503003800d88100010405200004591608920035107041c0901d600d81c0c41001a80c4152800043d005120211050126000104441190140e600b0010b00d004a40b080a1207180e00071900f01d5079020090b802041181003d02c1402c0091607512611400300b5940c0c072000342190304070f00c9a01d0802c10017190b034100388603c036401b80c230030729 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 229315440 1250 229314190 229314193
    0xd0c062004090207121404050405040609050d031401151e09081902091305030304150e030406020a21021507121802010e030111070204091a0408031b160204020702040905 74
    0x116501c4103035401039800644c04031100c10180143e00d110320300625a0440c51411914103606260a00c0e00703200c014803005005440d9035441c3c60310758001c81c0b03051111112801d03240e58042405000f0b0342240e80d903503806900c00001d0400000d014101a81e025a5000202ca031100c3c00320652017000200701c1c0c081400d50401e44013402032086c0c5800e00c8418101c92504907100396007520642c0d030ba4006080350181400c001030030039002007000400244042c0c0003481c0d14441081c0c001107118440d0410b6281d90400d401400141c0d200cc2c000d0010b00c013821580c07440c8141800c0407445080343d100340013504c900d4003440143d828560b40000c00c0c0264003902c81c0820804113a01d04101c804401c011401030040c2d5008140e012545c05842080070342018081c0300e40c01e81c500b00c24580f0303052081c1d01b40401821041d40c15190a0400c00042c0960100707800143e0040340929001e548078103004a1305c01c0f02039103c0610f048520070030420703181d1020074801c241c40c40b16011a0300688070007170390010070041d00e02441d000300725 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 229316546 1106 229315440 229315447
    0xe03030d022809690602073302030405030d0f08060307030302031909050a0e09060c04061d041e020a0201180f060b15030906180d0c0620 60
    0x144400d5403032060440c2007044840c41c100c5080881c00785500c18801341008290360410000c0d015110030300364074a140c2c082083c000d01e00c07030002c8000b042c0d003071080c50340e511154000e2043d98000c00014003a114061810400101390f004a49a05404558204085021418000f0742ca00940e03905d81c0042d07140c055640030f03440a42011328801c108100400c140441c06884070780040f00186020082d858582c06e1090482d814480000d00000c3c00301c1003070000708031f8254003000d2400c0515144454400c005858000320b0040c00010001c4880b20120040240043c1c0ca01d900614500185900800150001d041c08007280c03c07000b0401742c030408120000e4400b01b040c0345d10903000c5200083c54025008506409125150011600700d00c4a8105508100c52a00c181c0c45001011110101600096014220180100c0e2f03902c90050990340c0d9a5002c071079030000700389040a2080002044544 = true := by decide +kernel

theorem cover : BRFrame.Cov 229136690 229316546 := by
  have h0 := BRFrame.cov_init 229136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 229136690 ≤ n) (h2 : n < 229316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
