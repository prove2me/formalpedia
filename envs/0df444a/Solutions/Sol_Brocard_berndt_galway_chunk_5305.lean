-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5305
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:25:42.109138+00:00
-- url     : https://prove2.me/submissions/05c76382-cd97-4232-806f-7c86cae5141b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 953956834 ≤ n < 954136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 953958084 1250 953956834 953956841
    0xe07210614034e03010f230f0613141c11061c0207030210050a02090607140c090103030e090c0405010503160306090f0510080a030516020a030f03050c0c060319 70
    0xd51840c038084005500c10300c1482607000f1154aa85100c07a1075695240c0b40d0b884407104202e0f4070141d008803030182000c2491695903140d0012140403280000c103003441e100000e0140c462426410300c2031488010001d015400210905500c41c0211140b0014803010012910802c189881c024507890f000c2c22a00b140789000005048480480003541500c42d81c1d00251108903401590241c0150b4416403a1140d80c00c850300400758072004102c0d0035400c14200d2000305482e4000c0010040c0000000855442e800c032040104514400c401401c0c5a41542d4034200501241c495520984c001c040784070000c0c140e00c00c075004540c03c64106a4a0030b1666032507440c01e003010442d003804c01040685404000410f044180502c01500740071004c0080d590410914202c0c1180540d404121203801c808410800300390000291428840050086241c5aa980c800a420320120750030013800d9081c4000e1000c249503000c40640710340240c3c80c04031948501c0517020400c40b8081111035101122407400c540d480303c8115007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 953959334 1250 953958084 953958163
    0x60503070f1413031b170706030915050106050a080f071d19170f07030c050105031b03130302010f1119030b03070b0a140406090e0721061403 62
    0x5581c1c2d4100400440c0d00d4144920700d0f4130550b0710200301c080c0d05052242c190307070b494010450ba05201003c1031a50000c60f40340c82c6240708e000280b640d03403c40c02040c415280c00c480409404040100115a100c900c0035200c6c1e0010303655030b000104103000086400090115042c002c00b2961100d0302090346081460480d101d8800209130080000441c1c11511480784001e0320242c00c00b10300c070841d8900304065051400201c4c1200070301d43da018000030000300d040c01c1c1441040c1e503000e1030b2259982d80c0300c8041049031415140c00075080c1c2130000c2002140030303427840b8a40d42940b04ea40280045000f900404055034000124001c0c005404c0200c00149480c00d52100302d84044c505000ca10210ba290004c0d0520034941e00609540d5030010b49002500e5015080f1140508251141d80c10207081c400018a0000b40c1e02171554a00400c40210345480d000b4014803103024030400076840b850188000081c05400103109078020b40362109500e5200e854042280070804c480901c241340160440d0909805281205 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 953960584 1250 953959334 953959367
    0x3091d0c09040f090b011e1404110f04080303010501030509030a0818010e151e011809020d0503160b180604110a0e0403031406040b100e210c0406060503070f 69
    0x145014491090039000c1c04403854005c00500c0701d81d600d06036444010645118120221810001051001700071240c6c0c074020401040c1c07000200d90f1000745007100d8622031640c403a400b0703590105000844040000045060b21802c2c0e0f01488079440c0e402409d40c0d02c5c084d0031100c1c00070402e5000024031f176a2900607049002d1643e280040b400800004485007801e001c031041a845403100c10800c1419004d0314180304400d0b031070f0403464040b5850003514084c1d50b4556000d5021841d10b580b030f40419503640340c06030781843e600702e010b480e5a100c0b5000945118124104102c3d1105246400500f00d0665a4140080f04040c0405402140e4842d40e489000c0e090003000b641d801030001c10082444603070000b406100724405e460019000ca031490200c20781a00c005c02d450700ca607040c1034103d02c03141c0f10000c60f0300342102d0318200303c0d5918454000183c032008440e02e031412403001d00140e5a1404a000039100b07182641a101001800d0f119202150544000c442c0440800c3e01703d032008030014821056642802c060 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 953961834 1250 953960584 953960591
    0x80c040510021e031201030f0c0b0d0e0706090501090b0c011d0a0b0a0c0e040f110a020a210516050118061d0c0306070e04060302120a03091d0c0904 65
    0x311800140340088200380200140d00c07005800250640c00d01c0d01c8149850700c40019810580b5035017000d00c56a0301400014002064040260304003c00160004064410304020640321980040003400500000b0321030f07045440f0741ca030002101809034014000341c95040c1d403484c48180c1030007102d807004e600402103550299a10400c158814071710f401d44002c1c40005d5406800d040c042c1e0304004c4140300303004c3c007600c1c10380c2e2415070140e04240e004007842c2002103041d6400324000000038421802090220064041c0c1240010140410341d8081000420148204094040c00d5541d035804101031304102140c8003c82c0b01000f101d81c3c03c2c0c41e030581c072080140c8584004507015821450b815003d44400d04102d4180b6215007180718000403090a501c0401b81c0e05008114101300000026901d00e8050401014882c4503018043e00340c44070703008103001d55002361034610414201c21400e81e80b4030b803200c020341c00100070310004a00c0000c4601008036100c0310761546400317a101d800031a41181e0007040101d0b8010366 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 953963084 1250 953961834 953961839
    0x309080105070f09091e18140c18090d050c030f280206090c0f031216060b0603331207030b39040b0f030a0c140901080c04 54
    0x909008a601c6040e081d0740d0180c0382903544601500e402c0c51500311008560074000c0c4c0c070030001d040314140e8601007181d0300049404d40b800444854100b0b1121009000844d403040042e00780200004c07601d803814025202c0801c4046060f02840d0f00d200300b40c07104101500858241c61403948107101604400c00203005076403401c41c80161181c00c951240301418109400a003000d00700c061841c4a9512648a500140c6400d1810b009000e444409030b0080c58455106e0700707000e402c0c070344081100c41c13981e00101420a69a0304450a14203403071403d040100c480a080c030b40614550304000c41540d006d40480f071141c06051040c101c200c003801c07a843c080c4c00481c40040c01855020394440c0605410081c00c080500796003403c600700b8081c61840207010111855241d01c5020b07e09a02240b88109031810742d0034000d600d280540c511545210341c0e403204a40000104141501c44407160065004291588042020554017103007a110900751484800c0784a81c180140b001550145068580c020f00e8076851030320b001e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 953964334 1250 953963084 953963099
    0x28110a080c070b04080f07050603010305150a0e0d030504060b03150a021c0203161106150618060c0d0e01020a0209010320100c03090f030c21050a1416080d0c0309 71
    0x20415481040d05c3e920907484204d85040a00c60700000e001c080d5030b203502c2d641c119281c0bd6540d0400c0c8903208000740a1a0014070401082da000c140145141170940740103061110004001d44000c1d203007a2025482e1001e03542c0d07107117000154034031410744072014101207946034007000000350000250403400b1803005201d082c6074001c40c03000b9032184003030310341c0e00c00c1807902c0358130082580807182014055031303200c4024440e00402041d00000c0d0b0390000c8444c40c2e40c4006106640070244c2d1208005900700c0030101e01d4500f40040400c48c424284002d54034000d961000200490b55004209006900111103800500c04205801c000f507903c400505040200f00c10040007250a4407190b20303850000841c0880903104055000040c80010710801d010644801d00350340701e68401503072034403502c0c16403804002c3c0161501c00901d0851151034000381541d000400da0b090159400d0b41c171254801c40350082e031030300c1d0440800b2038040405881044000f0031040152003001c1c3c0d02e180741003100f40c041c8a0003510008554 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 953965584 1250 953964334 953964337
    0xe19030f02070f030c0305010c0914060a05070b1305060906040807030e0f131d07141021020306120d0815030f030304080409060b0a0509090c07050328110a080c070b 72
    0x214860b1317120f081c9061460901b1401c4451026104003000102d078410002c81c00e020002d12090a0101c800070b5581c0308181040e82c0324401c19400070700300d1211404005016070f14a400020b66805081038482e01e0f96150300ca240c0f200c0040310024546202400a403010901c50681e00c00a40c0b406007501d002d24080000040c8000e0035464076030b4902e900d4040481c61022820300500101c00d01c0740007410200c2c1403142a6014258420689000d0000c0e00100700d126440b44450646403441c0c88800b0051400021801d23010f5441221150f010301400e1250300030110b40020b0300e40d10481656a1910503445680c02d000060000d040110b03454468810f2264000c2010310007140540d215481982d5560720b032808200a442082d44041680b21051109500c3d050b044003c560060508884c50f82c89030b80da41d02c040c40b0038040c464000e00a0300c4041500c41c000c41d5006119000014140e40c0c80006c0001903104a500d2450501e440f0b60903042101c2a00000e40343c40003625200780c4d01740a4a656a80302d10b000c4145 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 953966834 1250 953965584 953965589
    0x908040b070501051005010e06030a02310816050612060103020c0d1806110a033903020105061905090417120f130b0f0402010c0b0a0f0e19030f02070f 66
    0x2ca964940074014145943c064001c014002802c24043c0d10184000050701030000501c20010280c00094044002c581844a030064070003959a0050022000c0c0d080d00c0e00c1e01e0a4015640705201d404030943c014a10075400400700d610040c100e51901500141442802c24050420380c1417680900030201d01c040140021081002196240d400c1da00c07103040760001c0a0300c0c5502c20700c18409418401180384001003903400d45145c040c148401014240d000003144860b8002d03445120200d007292048a10003014421074015000c1e82c000e02561700c80c0010000e42445810345c0c0d00008100280c10410303401e0444045030311500586c03c8568035070481c1800c0509a000035600c1c0030922a0500300146482020641da410550000000038600607999a8181000d40940422905a00100050116889071210010359540403045035030a09051a001018040c0080c0c1414282d040c00540c4051210001d503100c0059002e1040ca503d425007034600343d81d103681440b00401140104800400d84441d40d40c0301000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 953968084 1250 953966834 953966843
    0x124050f0a091d010612021f0c0503040e040605161e090902030a0501050102070b0901080126010c0504170309060316140c0606040b06070c1802040819110d080703030908040b07 77
    0x10f001c140c1c202c143c212111030b004440300c4c5980e0540c60b0090b0302ca14a911240c40d81624109401c0095008141c2d00f503100b500008240e840000b401089044643d400d86014034420700d018030280d21840c1301d80d04441600c0b001ca00c002400c00903da07040c0604490f4900030200b8a0a0440c4034030348500c1c0e8042a43d20840394901c0c6907071502c0042200c1e590421036030b4028141c0708c4415003000050000204440018882c861401e90303a180e280d070f8803090401012854000c41e5008000f4007481c054090042e402c68440d41c03000100c044080043d00401104840c0700a01c0104860310390758811480d9049100c40352214420080031280c260800300c10b40c0700401030820b2000003040a49014002c10068800c0c0210041c0264018488200001c4061401505455261221011001880c13512800a0045070700034001341c400c045030060300000c40e10400f9065402000904401010310040c0140e82d00705231401042e2060402461f40403c0c4264060ba0080b84200402c03441c240e9220300d42140d41c4c211020988 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 953969334 1250 953968084 953968121
    0x27080d110c0f060c070f0f0c0b0c01051609033c0c0302030d0e09060f040b100305040b0106050703050f0a091203020c0901210209101d090124050f0a09 66
    0x1880c45600f0011290300524030444240780c0680c1d17594500c0d03040780364203000b01070000d8803821004010390000b0b6540940a0b01e500c0070f0301c0d1111441c07403030b001e00340c2522800d00d0b25409104540d01e00340704624010a50341c001c1140700d092058207894140072400300c14006280d80c001440c052204600c090480020b0780190a92041182940100b5013400b40321543d0005100c1500c03014a0300e13071201801c90f0382c01078040310b500300f40c51180c501041c040d00b590286c1545c803550340412805180e070160301c100c1c00703103001d424003810782e80e02c0c0c010590b81449619000741c0420000c0c0403a0848001000040460900c01d1416007221561400c1191a0001807807049000d600101800041401c1c0304000d18010051103250184503680050031013035400c6404400390080600d140021441003034469508001d1269049200407103204010080d072214003a10321107090b500f41205c20b145034411104908440003440c840c92003152810041000e01308482c24211340100c010640010301503864819001815030702004035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 953970584 1250 953969334 953969353
    0x40b190906050105040609030609030324030c050303070503031f050a09240e010b0901090302030f07060206090c01020c0f130510080d03020301210c12030e0427080d110c 74
    0x680a076a2190803190400c041804200882c81d0700500000407640c01070f00018a100f21030408501425200882c0ba82010708a480e020018000c0d0b101d400449000e1007c148030a5241e1040507201d105013031001d0003561007400890441841011100540c0600b2041a44031680d100040f80d40404540e101481e03065503020084680400031010618238240d00b01000c8610b8205074403074203000703018004c00c2900300b000703d0300c8002070740628400d002440d002022035603468214400c1c25541c0f141e03800b40780d0041c0600c60100300001300024220700f017420160003070b08110840f0403d005034615090003c80c3d00c00082c500342525150303d4811903000d00d104c02c919a60b035038180221945805403c0d0456010144104010003903540560000103400c50940040e40107058142000740c060021074001c90070303a0841c0b440402c101030704254011400d0005403000d01071289111254144841e95160400d43ea101701440d5074001810b280090120560b05500022040c1035104103400365000031003000c1c80d907440405003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 953971834 1250 953970584 953970599
    0x30d1103011d0603060103170c0703110117041707060b120607080c0a0914010c1b03031806050a0f050c0f060901061401050703050c03040e13020f0604081902040b19 72
    0x65409042241c00c0b11030b06005012903a100414803001d03040c0c44000c000c2d00040e000c940c040300c1c4110341c1101225030b019140d0600c0c00c80b4000c4030703c440340030840c2500038085203411400900d00c102d070031064650224200700b03007000d2983c0c0800011508150354020501c1143d8400a1201e00f981044004007000e191101002e400d46a001d040c500400d041444030baa0020342c810640010346240e081d003145c14241c003c0c0161205000d40c000204454210380c101803041e5061841070b011280030341d42e0304801070002109520b0b4a2100d02652001400802200b1005030299120704e822039500c3c944140340182d40a034450400c60340d4008076082e0342142d014001d0041e02409088003501002c02000e10701400b4500290092181c0712008041c0800401c008a000c00107105580c0205212019080c1515040c02140312142158000300d00c950083c0d1500344c85420198140e40c140d4074500024a1504243c6a00e80b44132402048100e0384244c0380c00c580d4130162151740d051070341c650741f0306030845409060044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 953973084 1250 953971834 953971859
    0x40e0403030c0e0f1c1a0709050604140105090d021c05010f02190818060c1908090309121608010225111329190f1403030d110301 57
    0x2c0440421048142030707000c5544440c000440c02c681200c4d0760301d28440000e5800c0c5000d00000015066a03110511b0700d01041c2d2002c1d0752441485160fa0712401c55440300c0411595006901034480034090140402e406035024900420307820310014102ca2000000d41c0c00540c9400c0d1a0740750103959614074120008010090180d00d05d034903900c080030340c1019100d5100840045001c117444040142d81400705000110002081261261901c1914864a0045040180c1d036100e21a044e80d0700c580700010307000b01807080050501895a1201175072034041c8610400525940d40400b0300780a00a600c85021050004000c03100204440e400160710b4000e20120034095240840c5400e002c0c502e00708190780000c407061030711360800a08845041900c84509141c40051500d440b4648071403480040b03141c00c080359911520700641c01103c10800504010303610310202c40c40c5118800c1004180c0304103000740301401f03e000e540c2c1c20000d07007100d0800000f032400c4025140d031154500c0c0745120000042c03100400100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 953974334 1250 953973084 953973101
    0x60908130e0606030402010521070c03080901021201050909150a091e120f170709050306100b1b01090c0603140601050306060a0305070e30120a030509030906040e040303 74
    0xc015903031524041000c12490304c00100001c0c10032000041d048800c90300094100e081d080300380c508540710701e0000030160070a2120013054010070403500010b050224140202e40081d000074a84035144c1c1d00e008180300d0301d2140076148030224060450380303625203510070885922521003424081800c05050a1210703008005c0600c884c4000500802807001c100c020f504941d01052914100c031500c4041d50044030158205030411030401c000e001401629a44221000192501101540e01e80d4407040e503c03801c0d031441c07480384201511060061103902c031514020341041000392400852084042d540e143d1944400d0b4016101113a0349011100400c1e140c502c22680c481801c2c06c090385107042c060001291030040c102c05c0000c0549400005680910543c000948824050b02c40c40a1504848950006126000c900c161081401e080d03c42d201c000040c04c0150032201e5040c59107442e4840500303d02808004220390707000d110403c06c002039a190f0000400040c9a480c684403c582810300e8028161030592 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 953975584 1250 953974334 953974349
    0x801090c0e10021903023a050a030b10020102070218090a081b0f060702011503020105030f04020d06110c160302330a0c02030c0306010e220803070c030207171f020706090813 76
    0x2600f49402c110f500c1000300f8051847c9040050b01c500b5943c000b00d02a240310311456401c1495284054540c0703030150054860144200e6003d032409107400c0d50041e03240301c12a42400c1c10ba0186c1000d0000c56141001400c030001d40040d4405810b402d04021494120b90040240203540403000b00000d0603820712030b500e9500d1840c1d16041c2c03141d2a6800091083c000035211200c0500040d0100c0c4c11981d519450312102c03688034005201100301154044440c0c0c004000300101c03405045410068560020b0900064075801480042d40940302c0d50351000d141124003e036010400d0ba0b40b1405c1080701200090650b071165a0354901c00000180305050070401d80c000618025800180140600d110408519a12000101d03400194042c050355105c001d0451120240510600006021586030b10084150b440d5010b5000c80c0c08690340c81420540d419071010150440b60014140c01c0542203090888004011010784050f0a000d800d4850f44100c422090048400d1040010050000850b4500030801070440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 953976834 1250 953975584 953975653
    0x203040b01170f100c020c12030406091d040f02010216031209080c09010b130b0706020909010806070807030b0a1503060603050907030c03080c031201080a030801090c0e1002190302 79
    0x1000000d0741e58401d0070140c0c1360079036200c043e03840b0307000e02c00c2018202d00c1000908001c00103184500041c1c4030f80c414010000050382511000c502e090045070304a0084000d0120200d0640e950f44a140c2d0352600d50070b0890450045c0f500c4038030845c1c0081c0491014501981840003140002c14002e052107410b6031010900350808075264410741e0320454901c0c1122251001c0d0780e56110f03600d01901d22004c6c0c2c0d03000b18903541d02c081000300034000c00307601600d84e0307074000e0310482000d90b240c810040e030b1210112641c100003044a0700069001c2d1281d04100b42c2d1050107003051101948500e0b0501400c0a0700200400003642c50305d00700b004a90501820707400400e0b540150041c40e040d03498104500080d03010141002c07000045d400042d080402c01c55500d441510888001541c452556070707140d94040340d068000a081c0c00c000f040400451103107240b000c00d55240c00003100c000200784106001c003410088190300a4401485c202c0c1288184203180340d00c298003070b002a0040e1001911a8910b0126a5000248 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 953978084 1250 953976834 953976853
    0x7140711190815280501090b04052701020904060e040318120209041416090c031a2202031501020f030f0f0f0705030403060504030818191103010203040b0117 69
    0x10041510443c90400030b031403189a0351000ca04d10b8401c1040034480000d03128400c100c0d07104401c9540618181d803100e500030700032801c6280422054440c00d880a107000161492446900794581190408a221805c0007500700f40003000000c0c2180c0b115400b0444500c8010b04001c00c0507407042203016102403540030b041c0b00501b8401e0064854901da031000f40580014000301c0d0070b0102554010340302c158040c1c1210500790040a001055403014450080075031706002c000c080d058040d02540c100303400c1e84580400004009400c12914500e46150b1900301484c414075642603003212300007188184856090310b4411480c000c00240303088885890003040d03400c1400000c44483c26542100d030310050403020b0680350848412018800c0c0f160000040c21444001000000c010140c4c2241d40300f140203455444995440c4081160f403040c144405c1819500060758800d07510040048030192207004400380e190700810321000c28226801a182a10b12010b40801040044641c0d041030f0381070030681d07015018129 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 953979334 1250 953978084 953978099
    0x9010c0207150306080a050c10030605011d0607050d180b2514061f080f1509012c06090f1b0d1208010501030c0c0c0504050714071119 59
    0xa07480e0142022034031881150a4541d4442c1d0820009412400b081d03951212046c0b4020760b035800c116008a00070f031520380ba41c0d03000e540a4400e0f0000c40704103071112580708103103130726540e402c900c160b83d91f55202105101c0c003004100200300120103007003980c40c0c10012061041c0b05001011040c0d2000c0c0011804100078103030490041e41078a032500c44507884550f0a8001c1c44c042d00080c01c480c80c1c5401e2485a0000c100c405410781c00c011b0f0740269188101c08880752900340e015160012000a004254080090040140d42600800794040030801c0001001c61130a25107014016000d4071442d0011080c00f4103001d03000c0c040c40400d4010b20004003d24400c410084502e40703404e2690310900a00398100805030181d100c54101c80d0300c11fa0300981c54a80388a03400c201420890080c003906000902d440320304881240614460424140c0150900701c0d00c83c5004104070261a0040c038020811401c440d400018141480250841600c20145140200c40000902c15550125074041802050600c8104041c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 953980584 1250 953979334 953979343
    0x90a36020c070e100308030708041505060616110a0303031b051e0a2312090304060c060b0609030a29010e043306030311151906050613050909010c02 65
    0x41e08810002406959080050307034002e8013541c005004540300208000d02142e01600b09817003148144019400007002010540c01c859003142e4498200c03a080080e08a020740c1d4a00d1405800d104100c040501820f850100c1c81ea01040d43c002c41c040ba45419280040c03c095543c900300c0c0e80d11904d09130b07042c8500f05081c041c55950340700310b800e00c9200014035000001e208104001495a4a41540300c6108120220200030ba00a42203584010b0241d004541e000c5000f1003120101e8840c5d41e96200b4004241c9c41d55030081c840301038402d60100003005080019101880541c840a004810001d1201c124fe41c040b04030264550702c00341109144070040c40301d076030740b030491307503081500007142d0b60020820140c81110000c2c0c10b1060f00070b694002141c10180305041e0483da055070320a0707840c508240d20400540b40d5601c0001c00d2080450352a00004a8a040d190044122140365450108400b5a6800413405542c011081240b0b0400101c005124a00700703002c400c0c1e00102183c0007004400300664000792103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 953981834 1250 953980584 953980589
    0x31b12090d0f061103010311090f1603060e010b030f1024030207061b020c030109050303040209042105040f081b01030506010e04060f0824010605090a36020c07 70
    0x1071400038075440a000c1503421005515030b110904000380c00d0403d00c8680150400d2001700e03002c000c0c2643c0c0481504008001900685802170034502d55202e0b003816101103645031b0510403c040c0d0311030000480010045d0464000e2904165050350303070604200d5407210090060034440f9240b12400100500103681d80040803103241210003807104000040120040d10803044007810300c60074104d01c5001c100441030580c4170080c003a0201d1b440c080c40340301494242c9880c0c2c00c0140070b940040c00007401608007485170692003403040541403000c48200c0c1c21050341a495a6002c00020404074040c44019001c0490708080c040c954000c2c0743d0a8185003501445164902141741015161070214141da4050380340d001104000500c180420340d243c1006a0294909116210303003881100c96030544140300006540400c602c2c8803800d0b006030709103841a40c45520038015a07030800340c00d800008a45105440c42c0102c941c81707040d146181c50a0540100d601022242c0c0010b129204101e040c2c05440001340d00002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 953983084 1250 953981834 953981839
    0x2210f070602070e0a1e1505011805151c02041412030703031d010c050d050f040b0f040807201003020c0c0909010905030a120501080601210f14031b1209 67
    0x1481d54035844500040e181e2403603100702241d07902403511280b541b5504000340007041710380b68101d0b240e41ca0004403800c4c038201c4c0b448041019588403c3c03042d030a11082e1400202881d07030f0061300c0c00122001b45140c0c0f03003040c0031901d02d076030307002c10140003882c101c4182c201600d070700b02e03140825480119180c80d10f0707200300000141415920301140d4034481e00c03d20740e181d00c1d80c4084020403203150826400781055002d2681c0030780c45858000020701001c40350702d00c24092070b007040541c0f450f56506e222046030010080c10603114501c0c1800704d640041d072010808070815000400c4619200418000d0260b000c520b42c0c0000c09050042c00007034264800024030031a080401c4420b01c00c81d40b22803120f14010aa2030308054440e0100152000b1199003054041c0301221004004001c143e0b41c54100684403a0b0030702406040940001a500c240d070480f4041c1800a4007410580483d000a0f03982c070281c2e8005000105141d4101045003010003196500c041442c0c0003400151404a8181c081d800f410320400b0102071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 953984334 1250 953983084 953983109
    0xb0d0e030306210a210329060a0207050616030807030e101508030a030501061b020d201807021510120f06020a09050a0b070f0204020c030702210f07060207 68
    0x500343c0104a400da2843d08694202001552518000305a80403850044046405c1003041107281940c3d20a0014401c0799485105004041c034040203a10340c8181d01d24000c40c0714540001c51941d450380020300340d058941a03281c03140011b518016207204402411517091500c0c100c1c1c4050403000c042020b04018a2000c400200700c031150a4000d501d2500d40c10511580c400070841e1071560307405601c442d0683d80701c0c3d01e8004600310b50b071a903002d000d60071400082d0411501e4140000250507050345081a41c0d80e182d0303003041450350b03034013040c82d610343e42154100300603400050060003501800103019402d034110b060102403900038550524076410303114141900f6482000441486074114403603080d03d40c0140155559240b610380148240960f0180710f01c51001214002282180101100c56069100c1012840090541c00304030007500712006910483c0001c202c5000140c0e205000703c1000402e00170101e00300c40b0190801703807070841c40e20185456644003850500c181c40d0001100001c03900b5800e4401c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 953985584 1250 953984334 953984389
    0x150212010e060604090f051f031a07030b041404030305061e0609060906030f040309050a061209080c0f03030109110a081302040b10080403032d020f040b040b0d0e030306 74
    0x24a035100d5079012548886c83e00110741c50000d5a0340006000e070100004104034041210003082d01a0703003920008044a200c030300c844a41160075214142d01240c030381800070340411020701140c02c2d941e0390320866a644e511202040105901840344603000401510b05d08508400d00704001400442c1820480c4208008544810150380e8803007299454140a0201174490034903803505c4c182c5a4060740c045000c144690000710310303030903c000c401d4201c50040d81e41040e4040070b109403200400e0004c4041ea04140d0402c00e41c409444204404488a200000255984e614185040b0100e4450841920f5982d5080228401803a4046040b5030400342c0b0402c2101083d00c00c2c0300140041403280101500002045030004410b500208541c2c422400f9803410710500c03481190021551410f8144034813083d000100c2e4107007490380c0b5805030505022407403a2031f1410703480c1c0b018090b240d040703540501e0b0003160001e40010b00c03481500980300c0d40368004009500b5420900c002880c00f1410368003402c8080c10b542c118 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 953986834 1250 953985584 953985589
    0x20d270b130302180129070303090f080c0708060903040b040323100b09090d1b03170108010e0d030501120f1a01171525021216150212010e06 62
    0x4000541d40100910580040b08106041d54802441508a050011280c3c426040301c60030800b02c1c1c6d80d601c50071692070111256002c0d030013000a1070b02580d040c003c000c0034200107032074000249a2084844020400b651801c4000c52134000010000b41c100d0300700740401c10081008205440540e503205c0070701600c0b03921108100380c0d8840b9007144945140b01d09024880041c4c0c003544211141e010556610400c0e90315181e800780e0b680d52210412000600c4031420450000f00344030701c0300e101403191030111900d180005480d5101107003070b0461025655a0204240c00c2242001410300c000020b013000d001c1507150a1481c0081015908050640f5400410b000104400d02c207440722132190b201a004030a58440141500d00e02481310305054074458041c8100749802c0c000213aa101d801804906802072919405490400e80c001c7e2100017940f0850b07051410b00500b00d8050540c0a240025500c2288120b040c42c200c24840034210402140c410001e20340b65175603900d070550544215900403005925070401 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 953988084 1250 953986834 953986867
    0x92715030307120e0f01080f0a0203070c02090f01080601080a030815061603030603021201090f121b1101020624040b060d15050a0f261606020d270b 65
    0xb002409001d407640202e1810341c0184c41e22000ea0700c140c60902e2410398a0005595a50041d03600e00300500d081700004024400e5500190b610030454900b5108244031640070070210705058800180042803c0c00621030b0740e4040200e035004014100c004d00100c860f079200038103171146c0644200030081b140c401c14491074540d4404c5864801421b0680d850320129070030300038000c01c1d40380070480c4078142e0031109410b28541401403510b400d4004111401800329a9104401d0003200d00c45802405040701192003501c58094984001901455011802d00c0114000909280008050841d402c400743d0604809200e410300c0d08622190940b0002118450800010410302801c2c05841c00a400c0100c0c48010116001050086a9041d00d580010030389035000003500c44405e000e0100c0d104040700c50082c802042c103559007450342c0c142080d907550500300d000d014884400c175000400940d00c0340251281c0294080c82c841441c0c0c0e5420b4409000703401c4c1c0c46c5040020403280c481c00c10420008035401202d55511203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 953989334 1250 953988084 953988097
    0x11d1507140f030c1906060e070c05120a090501081b0a2c06160f210f09060806130204080303010602150a02030c03062110020927150303 60
    0x1009030344446903407411440705104081d9801003070264401c40c002d10030700041910105036014018114280782d0906450110244140030f4410382e031a24800242d8014001c031440c000c54a690315072020318840c3c241149840100103080d21a4241000030004c0b00360f02006400c1a100e09182440b480e03143c41c070160b5200310b01c0c2d0003410144e0700e0014442100710342200d092404003004408601202c0d00c50032200389103180541240f90007120420040c0303040c3c142c0312408800380344500c101031812000d940702c080070b1036600c41041400302420160451850740044102c509040c445c50210b04841c01d200004212140150a03103024000d0060800d800501c41d4040e034000e0090407007148d88960f0745000081d80c82c0181251078001c40700c810082000c041c42802140c0c869000c2009880c039548981041c80b4440302070906500220000d41c024110888061150701c2285406020241e21200c42c0c6003000350040c8811106a0fa4005001d11a00195440c0c0405503010380c010003510304603600b42010906510407103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 953990584 1250 953989334 953989369
    0x240612030d060f050a080708070e130506010b0a0e0d02010e01050f25060c1e0e040608010f050906011d06240c01021305011b020909010b0d05010203160c02011d 70
    0x108003148880114003c0310466400300c035112040c554030380700b0700e407694264010f42545800040c410f2191003205194150400c41342185048018115298581400002e0b00021101980052104015039000301c0d40201c4107000c03100302500e0321715540040d00407070156031140c0c180400400e0007444940c0035801d503500e07190955034401d460115070114036103810810000310355151800f2030068900d40300e400700f4103400c50f2056966110b00d0840f803007078411042960102e0f0740300b51940d034086000c3c1c1080c001c00c0d40c0c006c4502804a514100303402ca0030304205058004440c813404551500a00d44900840c46800030002c0ea9120203400300111903001e50000460b55030455040061a0541c0d900150300914000e40711050290341c0d6034561004403030402c40c0e0747c03041621840b40d01040c1c002d441c0c0241c44a4021016800024040c1050000700d00b0220410b4016038040e540031041000020781805e0042d070039101440c28103001095580040c011403010f084c14030004020710180c020540313402c8017400014002 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 953991834 1250 953990584 953990591
    0x101d0f1b0c010608060f090d1110020f0c010b1002070905061c150e060403051207030e060a020d1802060f0f0c100209040c020703021e01020c0d06020408240612030d 72
    0x814681d00d003c0c1c502489a00041d100d440001846194400c2500f40503600d40c9000c0c140340d04001c442221081c201c142c0780c00581c0984401c403003140b8910b200814181030a940703455296a401d20003d8211035820b058140200008146c01d810315a01050440c15600c25420006075504c8002c04100740700d400f01c001072403192101c01c0380818050603d8000504118804061056001022482d51a410b040d200100400c6050100440c001c241104490380a10b680c9800206081540d410342d25190081e107207510041d0340000c40d40c0808500e8066540f103007001840b061111400303503002c64460712403e5084c408007200411005c580c50310000440e0401032440e0211102c40c3d1502582400a52150100510523840c202d650780d110360010590704112a0000d00c4005910300c0a000184084c248048680c1180143c1403440b00c1075a0b09020491440c0c0a99401600c684c2041c40052401055003507104042018030880c141130501421035590001041c1e134500e01422803a034200345140105040035501904 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 953993084 1250 953991834 953991847
    0xf0f050106170c01020a14012c0106060203030118020714060c03150409050606091b2212110d020f060706050a1116020411040e010b03101d0f1b 63
    0x54000c031094862090300e4106816810480a981d843c2407850240542c1002403030002240c00100452407540c24500041031071f402107140401c480c504042166a03090004092840d2442d091103118040c2038240004c500d1541032910740000e0034010a4440801500010103000b0020329450b1244040d0f411011920141418044100181c10441b404161126901c0143c2d005103864010b1001003504000507102c603840700380c14060b0803070000700210707894481d0014110035034030810001d081d1001019034140c4c0c070a05514003d502c07043e26601500303207041b25030101c2000c5540c01c1d02000f940e01c0c080740d48200c82585403010800f00d01e00015180c0d032105003c9000c009000254002034498102403800f0003441521041d040c4d0ba1303016040c819046c00c98404410320060502e50b0010103100c1c48540d0f49820180e842070719012144098100000d4060080240201c0d008414844000703400050b54118900c100c0506134020400d00503d6981900740140c0803454014108114202d10340d8141501c9a8614 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 953994334 1250 953993084 953993093
    0x80c06010e04020f060f0d1a0d20040e03160317160806011b06020f070204050405030c0f0a0b04150f020a05121003050c311e06210f0f 59
    0x14202c8041e4002c240c042c0400c2d20f103240c807000711185151041d021504290300039807040d0081240002620b400c01408203207541075500c00300e801d080d00380305401c66001e5905c0701010190542c030500c2d0741c500076805c0c803461003009403011041e02c2545034452241c2c07a1072166414100c9001c1d181c902c120405000c1803040c070417402a541005000e5425a483d40c01a0ba1194001120b01030024001c1e020f610b1130f4119440c00059040d0010600000710358040c81c00d00d0b1003a0000b03001c8503c180d0b400c440d25440040c045603000001c1c031810b072848141c08090898540c56407505100d40d1070040c0028802d80c40c00035003002580d0594440c0840070406030b03045440d040e919002610030b5110140c1c88183c8059880000d24038110649190152a4490080c0680c040d0070418003841c2d8140c84c00c481d210000c01010414142c91000d82181002d40c17054010503071604260000500d1140c0d81c12400b95141400002c0c8040e0b1260140c5004484040801c00e203104c4440c02c040081c49100800107001041005110041c007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 953995584 1250 953994334 953994359
    0x4030c0501150e012d0614120c0910050304051507030e16140a18020a0912050109020909030304030903030e0312130608070516080304080c0a030903050c03070608040f080c0601 77
    0xc801e20030544144810848003144c009500717610300c2c621104001010302401d885004428090341c10041514103085450b2188000c15400b207840640b1883c02050f050340918001102515040103410514a58200382e1a0507403188415000061004217000125074094443e50104c000e00200314255804901c8041000540128920842c4402c4d103450101c5125454690580c4003150050711101e4682510980420081c0d081681c816007404500711002601c80c034890142c549440c0b14800014150b505403040080301400501107550513802070040000203a0840d0764079040c1c2e40c142c1031101c4000c9034000080c2c6060885201401c044001181c002682c0c40452651016a0640e84402c2115903d80c0d0003100c05000721114103150306c008044023004225a60002c2d5040b40c000c3c2c03400b0303152840c04a080f500d0a205104110000ac044d200d00b00117010060100c010030460031405007072a00d2505000418016001d440940690500f0124104024401040300d42c95680242603e034075603599038034440d43c1c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 953996834 1250 953995584 953995589
    0xf0706020a03052409130302010b0904030915090e0f0a0f1e051501050304120e150c101505090a1410080c030706050a0e01140d090c090501080604030c0501150e01 71
    0x1580300381c00130442861884c1d24960554640504151116600e10004017104004654103400f95540c034444503030503460701d8101c10710443c0281c451030b040390b241031000c0d2041c140000640080002c40b24040c171010b01c1030f014041d00048003802c98001c0f6103c0107029001000140c034001c05030f6140944a20903078800603203c464031254141c04100c140d885a880f1501035250150340c034001001000000d00103000034a082d000d2040ea440d100c4000320320b420200b03d5400640090014101001c01e944400f00c0042140000c3c1070f0711840c05102c0c01801c0280d1140d440c3c407a0140750b201d454560000750f5004800d50001c00e0600002606e0301041c10a000c070100303041054003840003140500401401d00303042c0003505600311401659450300d40b41d18003034102e881903d214042e40c100040090360036004600c010142c11050b40001c00005d201c0f0b514507248150200d80d82c40000a00d040c2001040340c2c00010800c0d0ba400f5405040460690070f0703070300d40300d4014060402d203644007004070540418190b6801101505 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 953998084 1250 953996834 953996851
    0xa02070506031f2108030718321c0f02130e0d020303070512040305071704080c040b060a031107212604020f0a1701090317090c0103020f0706020a0305 66
    0x340d8545800d104c560a10401c0c03204549420700075075400001d8035503030003150301941c5494602da00348010042510810b04540c0245488001c00300c0f5008801070701480710070309407450400d007030100c410000407070301d8202d03001040014260707007078600000d10030a071220b00e50190303000300a4403e0f429942e110f00010003005403490898814615000030f0300717000004a0340203501030b0f103440e42409010901d021f001d6000034001c0b0200721040c001080065201c2c4031044403806440740d82604c541c14009030f10315103203800403000d114509005903490b054541804440d0001c0c010316010541c5810184001e2251050b820001c00404940100c0c41c04920442003240070b20a030355071025400c1103540504081c9482c00061000504442d05c041401407410300071801800001800380c101c4595520310007a00f56541c0c2d4607204460351115079003410181c0c811402032a91a110b16071a003581001614640d070344000044081c14140d0000340340728000789001c1a0744005501a5040d07649455204000300581429a800c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 953999334 1250 953998084 953998141
    0x12020c031b030703080606070c09021324080f0c070f060209030106050409150f110d090c06050a021209030a0818040501080d0203161104060e0414010516050a0207050603 74
    0x4401c5004001c541d05580c26980b01c1c0c641e91186820130004e03a002c000100ca86027503002000030f00c80e407503002030803503070ba11400b40501641c6040807030250113500c0180000b800480e810302c2c05c100b640000842c1c0e0050100c1903078911a503a0350209003110b10440340080d2114501d004880100040f540040c103082c0070039002030000030ba40300c040c04141d5004840040a40346100881c0b0b8a8844551140b0800e00000c140494604048484d0740059130040000805480d1118640b10500000c00b0703140e4000d015602d005403516502e900025210505850890540300000801400c47e170b804200c030582d56600503811542d10b80001d181c0c1c24140d140300c00140d0299040c0000003404c2c2d0f1003c106402180c945401551410404d52640f02004001c910100e80c0b0200c09000c0b0b0045440705d00c9020301901507141d03c0c0540d81802d00782144c8100d80241240340680c104001c000e007030030884070721381c3e0007412604126448010320350080c0e0420072943c2180390800700c04030400c02811388100400000c1d4428541a5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 954000584 1250 953999334 953999377
    0x71e0503070b1911040608060d140a0203070b090306012d090b0108090703050606060a0306091407110c0d0803041a0f012916080d0204060503060112092112020c03 71
    0x8004d0381c000250311001c03c1010700080024900507000e51758801c10003000c5101c0c149090703030b07602200035010030903036540d41c401030041085040070000036003e0550000c2e26424548036000190796044140150340d03000c106004803091070011805140003410b95802da002c1100d840724680801400788104290004081c200842d140101c00308807501565080406004d2940d5554240541681300b4800301c0100b5070344030800030b2407140324032900301d1000407941100150304004900404003900c40d0988045500001c2115006940d00b910000051740d020030b095451b0398990034110101d50000807050741c84480942006071161010f07044a0681c1e451011004883c2c8801e54803050140b480001d0754126181080264202041000e0700101c2d541b058a2240c43d10403011600002d0340c1150f072045003c43c2c000b1048c40059a0484500582003060000401c80800c0c00d840e07201421044851317880807403c800c00106d101c10b1142a5007424980f4004095590740c1c000b05246907254803043c1c000200b1010907e0700d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 954001834 1250 954000584 954000631
    0x180405010512151b070804050306070513030b060111061f0915140f0a0602010f050a0c05070f03050c0a03090815090604151407120b0105040605071e0503070b 69
    0x288142401e081c4018840100395120b0740107084809002c114451044d2036040c1d000740702250041007a248030f00ca00580325850023044c1440e043e00500346000348402440700c95101003050310304001300ca811010781c6102e91074800058485010400c0620554040c4004010031418070b0b40b17000002240000c4510b06941d80e0304002e9040361050600490100d031400c0080080c40741c0c402c444100c582c030040c00780342d28002c4440054480c1690b5444000540d44070166071241031014481c841e0310855540d000e000d030540100000740700344500ca100070041c2c0420190b00c42031520404c240c444001940d41100c00e14486070034003800480c1e035441990003911a001008034480c01c0951828002c03540c01c03004010300d03141c5a8802c0450b01c42d0701d4005413082e64070b0a2034441c540404029a0044082d600c52031810601041e0341015146800c0405043c401c08000030000c00f82d1100440b00d04980028404c513841c8401075009601c480c403054090304500c40410114207102448014600840c80740080c0e035405a0700303c0a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 954003084 1250 954001834 954001849
    0x1804020f09040905070801061d0a02090109033c051615080901240501030b1f0c050f0a2f030d14090d11120102030c0708070f081804050105 61
    0x144a912840c080c81001001e041c0b82d041030080c584a142038502035600ca0709005c0c2119020340c005504035903011242c980740340c0d699245540050000d4001d520303000340000040c000041500c0000c0071000b140032010603005050501001c0c102c502c082402c15014480044a4512030281051320700340590b10200e08103c0801e6211003c480040f452400400c00891041e11031080003400012030395200d100701182401a12000801622000302c0030001ca820403000404036401d4010240c06030034807240c885c06403119126406803000280c13074018000e4416290082c20074041c100c44055522802c541c00c02001404034801c42c1c168032007031418004000da01c2c800702c00c1192641719260913400158105113854407601c038150407508084a418a08401c074004200400c00715402038441942c00b000722080f51800040c0c00c840f06000d9002541141403d03c1020031030f00c5000c400034113a00e030002c8c1500030042c884803c51081c0d07400035072060b26500e100704502070610810b000140f00f00e103400e00115a41c03a0050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 954004334 1250 954003084 954003097
    0x30c011d0a020f0d0c1d0106030c0207140a1d1b19050901051b060105091501090b070215040608041104050705031303030b0d03050d0c021c051309090503180402 70
    0x24914141680c090107204a4a8040650000d13207461100c8041000d01441d10b000b4401d10801c0c08400301089800c1d284118180c120343c04241c18041c1c0e41c040344c0d42c006645001c0c0c0d907c446900030010f14140009101c144c2c00d40c00341d01e04080411290340c00210105d1010300c2800c01d00b00410300174518406d14105031003074122060148960039032107000188a10050324103c0c00604106142c43e1041c40c3e0222500c1c210b40394080341d540410014440f41c02c0100c68140c0005603298008501811140043c055238184e0107031400d240b0010944000b59a01c1786070340300c1d0701d00e100d0f1040b55485440d61b4004100080c100c0b4103031911503034034021034050300b040d108041c800d500da5601c0d2811500e03100704010450840400a50805440c1e18045483d40d544010a040d0148030352186070782d07030311080c0f02901030351007041451043d50003002c40081e9000c1e0041e02050004a2840d0a55481e800e070403070ba280e4842180c11501c8807916010419040080000081c040e101e01c5545184400101130104000da20030f42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 954005584 1250 954004334 954004391
    0x60f061208040605090411030f06040b120d05030a020f1303210905010e1f0c1a060f0d06060f030303060801200d09030c02090f160f050406140d0e030c01 67
    0x4100420a591003007026240300040100007103510347c079821900015410964944041070011824800907141600c14100c00b0101507602d24554182c17014020784503a8400121030901c40000005203d080300b542c12100d041083c54000c0340c0756210422820700031140f41c00100d03101c0c1c100c600030700e422070a4240d449140c20004c0d5103c42d80641081e0044070003c0d04007202941201c95083c0d000c04000c01e814200f044000640e54241200d8554144480260061000c3d640090014030a009240d100c6144803541d01000703a4040800100c80d18000d401000c05034010f1019021052002c02010b504d1780001080b01e00c5000244040003013401ca603520b521300c0301300400741d550080056000380c040039045078407410300070705001d082080f564000c225100401c0707a08a021002e214100a000841103166064107a00751a01400a280c0101c000c0c5c035a2155010740800d110b10540c1d0f69100c558a0320803074400e000d210000b8001d0765501b4400380da41760480c0200418035400d11100e02e1181e0303685140798208130b110 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 954006834 1250 954005584 954005587
    0xc170f010501030c03090b0408030619140d0c080601140a06030203071e14031e010b040b0304060504060603021002010504031d03030720150d050f0702060f070504050a03060f061208 79
    0x7408019001000b19030b50500c241038131400d088000c10565115284184d01580880742e4070b1070603004101034030003255800c1c0b506194905d42403040502ca0a80c848040c541929101d60900c0f040c10110307076110b02581b21014500c620400072405440741c5015900c035601c213480660303196846003010b4003a0300045403481c0000d1801d000c660544452480074041c40c440d14144560601100040c035800c6130b000b16146072400c3c4e04020b42003112111224298010f21b2a02411070501d0f04150b11070405200141c40680341646802c045800d21450b54017210056038010400c0e441c248041704086d020b40001c0301c0980c0400d918011544030346007010025420480c004001d18504000359490350300300d078188207401c82d008903400230030400c41d10b507468200b030b022840d505800c1d20b0340c9001115400345ca500034179035002551840c05001000780c00141240d04454840000c2e4801d513101c40f4200c1716802207034002a441104124000140482c6a120020002405030103010143e1150244030225102503001440c0600 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 954008084 1250 954006834 954006839
    0x506010c030f0c06020f04060903020a120201080f0603120a03050915070507080f040b13290403060b0112050c2d04030b1008010204030b07020c01090b161e060c170f01 73
    0xb207a07001061444c40748500506050081001c00015003250304000c02143d034840c01030013035260540e5804028496000e03191814841a80000c2c200d01000d4005a40241b0103400701d03016507024010701a40042d580e46840c4c0782d0036900340040c00303041c01340c500b600c55010ba183e00c41041404080f490b8868200740d214a0714042035a41c40e003403594040407041d035400d0010b104c042a851851802000d00d1b0000e1030120800c1420180728009258000c4285102d22103400e604940301207900090341e0845e034110b00300040200c01c00c001a500124180d0f001d0300214601010803012041d101e01402a440b00211041c85a0001d28486403121600d011203500b002e00c14001040042c10046603a64021081c021888440c2c0d60768411909981198100321036210400c0100a010755041005600615007407900001c024905694812544038606092510903c400119801d10484a2000f28905120740c4030240151190030b20b00008c103400c1c1410000507405540845075560100406401041240032085240e413 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 954009334 1250 954008084 954008087
    0x50d051218031b1504030c0b180c2209150c0827120c0a03032a0e012708011b050307030b0d0501090b01080706090b040e070e0310020d0506010c030f 65
    0x1007050300b4449444c8a8400011443c80c01c10707075498025446500c03002500c0740e0510705810741040043c401e41ca0300d101e058008018041c00501e0408080050b80c1035128002d0340c0045030307442d08164411000c030b00d0403c2c000d4001c100c0c200c07800001448031060708120440310300c071040340d40741c406881400500c54110810442100302028040c10350600c903044419600028200c0701454000c1000700c0c41e2078102809040600d9058003951034484940751004a0403e26020480328540341d01c800c201c1040350354191200f90364025203009082442c0b4051440c0103024084401d40040e0041c00b404802d542003003040850802e100880c507440c82d5880e25a0750565481d80c40440c01003181c2e008155000680c0080480416820b11500030344502941703442c18290704082c06d8524225480d0710000030045078100810004050005650590b48110f031286090388035503130304aa204141d201556450701580c111800001c0440c1d000307000c05c03184a4020f0205a5401c00150390070f010300304000d008107040011002c0c590b0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 954010584 1250 954009334 954009367
    0x705030604150e060a0213090603080d05090c03030412060b09060603180a0f05010504030f0905030a1e020613031a0105130903032c060108010615080405010603050d05121803 76
    0x1040502000981d120307080d203443e45813a0013a1840c20300250b00103948986c00300d00c1202280504600702c0c081c07242900c0c5544040c0d481c0b013010240c0c000035070346002084000d07a044c40031402a490080840b5140d94652218040c03ca444080c1254000d2a03d20506900d040201c011441440d000f0a100c2c195683e100d55035100800e5000c841515002e0b0051610002e1102c0e05840038541c01580002140e00e882d14010308008040000703030702030000100080011361340000384440b80355800039110a079900e800c1e901c11030940c41c1c010025805000413551580954403800e0520481c3c0c000c850080c1c01500f13036050000100400e009140d0448251002c4104e2103140b5005034012601c0303850006008450200d1317400a110b0288400024200f800042203103031801002102e014000c0c80008014461400a8114800f40d04d49550014001c0c101d000409101c17084d0b0041c0c0003580c00c401900e00c98440024001d0081c0e11808842024140407000718102c407031070326243d080d03403036840d4025858001d402c2e2010070f14 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954011834 1250 954010584 954010613
    0x30f020312010605090f0a05060313051e0303100b07050c0105031f030b09100e0703020906220203010918020a09051008070902091531080d020c030d020705030604 71
    0xa500c810840c40d81940608214507000b03004641e281d0b0f44990181701081000d140c0d2802c801d01c00c0c1c2c1c1d00001805076540704c0741200c2c0c002d6505c81e015a24000e443c5056401e12581380c1240340e1180f032886602c0c0c880074001c0001d43c4a110810f4030420240d4445998244a01503520017a0240d84040c0c2000c016500400003150002c501000608103015640d43d6040d0754102500116080340c0d84e401805042ca81c10004414500445c403800c4c0159110b81401c0c607594081407001912a502d1400416000e88403060b01c520b84c600290100e40040c6042541e60000c1d44c800e00c6080302841c81c0540c0b10b900007245107004c98506034018010070800c0d2414641c1c0014100140c40324940c2e08003a031001030307600c1041003c14001c007540300000d40c54604030001c102e50840c0b2000301c00c51002040000d9403518070509441204010743e0b00d441100c5281c80205400c0300581303070300700400e1880740c13143c072808503500060784803141c0004608030340c515440800708a803508194030455030554050000f0900181c4070130f605d20320 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 954013084 1250 954011834 954011837
    0x506301e030d052203030f05010506040e0406090606050306090a120f050d0f0b1009030203160b0f210711121c1a0d1a060604030c0909030c12050c0f010c0c030f 70
    0x3050203040d04c0c0c006042d1041c1d03804070042583e80e880da0b260203409000b03660040a040f5032507030600d1f00d803160300881c03814024070042c499595003804104100042d0300c1540070f03080140c220b50040c5480301c102641c840201c2000c0d2100d06404900b541c1140c8603400300030158000d81d451608261009000d20050710036002c107401020307100e00050106072a9846403880c00d0245684040301da40c138500525003400040501107921500076081484a83c1c0108112001d5010846040790340d0f0a0601c0b00c1d4803100048130a1140701c8003a58203110300f40c2c5d400010703416141004419a24410075902009001d8454036540e554221202c1403e00070951075980040602044410002e550302050000280384c0e0b4880a02102c0100f001004e60b14501c054440590b0320501c1610712074a80303401c645a03064500e240b44507014560740c4500a00781014800c0705200301c1154040b20a52801c2c40c600000b0b1701da5007245480c04100d1007046601c01400205000d090200c030915244c52818040684007110308903005c070000710 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 954014334 1250 954013084 954013111
    0x31b21150905240604092105071502190309020a05100e030303071e030c050d050411040501080606150324060f03070c11030303040c090506301e030d05 66
    0x501045050141c0c41c0d49035044400c0011502c800c9583c500342c0c40c4081c08490040f032812495600080032174602c51040e0344481e0b00f078200c4000d040030803103292107a840020108800940c0414850341c15401501d21183c0070301c800c084001d901d40c0120300b00d0b009034001030340c4448015070420403070034410200010140741e407a2007400d00c02d40e0008245550b106450480010382400c61070754204002070401d10808103145002d225024080030014040d0188c8251100e01c156568003081c104900d201c07850809801c090010310007982c1d10b1020710389641c021180c0c58000c0712072940800c680400a030403648600300000005906803240d007501c040d850070603c0c00a400c044104103640c02034404602845c414031241d030361200300800e68a0025455450070b01c082d17011780d0050080c04005030500c4d0340f010541c3e000300720018040e038600e00082e08100c4e0b0420b07454401f107981f80c81c09489006282080c00c0044200c3c045509107840d04410082c949903000088140d41c200b4080c0c3c09000d0f0868114980111a500005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 954015584 1250 954014334 954014351
    0xa12021509012d030c02030c0307060b0f03011416183f30180f030605041a0f0c0a090509130b1b161a01031b2115 50
    0x9015402c420fa10700c1e15800c484011a607820740d4580030f54100c0e40010701c040c40c200410714107215600c1c0200c180052045403503040e600c2c0c50fa211000c000305006130040084c04880340c2d84104040014050381c0500c00b070203a102d0701c00005802142c0c3d045c820740c0f2403507407146a180380c4004002d040720051003242e000e085904240b41c803001072833180301c804182c18000714141d40d142e250070b0168200034403848000001030a0303004020300a200c5040c4100340313a41003c01021507500c800b0541c42c415a08011542203210301d0100c00d01c49c0542c01340d44a00d00c6200e41c085083c000d028416031201007128400e10030103540b000588002c01d00710140a4602aa0805280007620340c000600a000100c5146188008a41c042c0041c0904840d08a07000072036200e640300c91030417003c294503880c400d44a03000603281007003200004103c2e900c00803144079104842c02512a58503032802c0102e90002c01005640c25061000104441c80407249290b06480c048400300e0680046954100709901c2d40031180745100e6441008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 954016834 1250 954015584 954015617
    0xa0909020a0512030c010c0e0603070807200c030106170601030813030506070c03020d0804170a050403060f06080f0304050109030b06041404060506040e060907030f1e0609020a1202150901 82
    0x3c0300c1c00c01110156486030317800c188545c211140c080325031040049600c4503480a07243c907030480303411030100e280c0f25007030341d58540056800c68a02ca0f11000c03900c03403240245d1100030002c03400000e4108101e0003031007100e41d01c1550300809141041c5841140d00031500402c0011030240050401980f1696144040c40d034944400d414030604682180100d525500c54904240e070521883c101c0750740a045c15100d5080a8031100c9506030341100c0300c0b5000c1400500c00034504d0165007a00c00950b8482c8081c812150071402001c00382489220b4541e00b031158041c01c0c0031030751f0080240c5017903400680d2511895451a02d6082090b10302400c82c0782c0041c0d4452400b681c00b2000000a4407e070b024480100f55818035030300b4071089a040d01e5031200c19401140910034031920104140702180e401001d1400c501055081184000194980024100c070136117107118204603254000b03c0780b240c000c907080c0c904240d03541280c500c5c60b600690000d5101c492200d507625090070140c01b41c403810a040c501207542d01c04200c003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 954018084 1250 954016834 954016849
    0xc080406030209010314041a09010b121617190201050f1801110f19060e06010e0a050f0702031912020423010e03100f151e0605090a0909020a05 63
    0xc00000398000403000d401e560140a21180c1c0011020034085500e05038803200c50790250341c04407000d442640804210385641c00d400c1100d40e220f0007001d0799081039681034003a940c3d2801046034041180c1284002480050004003503c21401c85800381101d80c8032112450700c080180e50040b8184a01403103880c404816035000381c145c0e402c134810b01d041c400c05010000f4081d5408036010980551100d004069440380c0801e08030038104215008074510801ca24100010b072a00b21070f049030503c00e29000252400c00072010500411002c82d0421440e15006002c540d01c040031540f00c0090b92003006103011a1500900b03400014886203007801400c6840d40340001030b42c2c800d034082c04100c1440180b4080c860340300a0f07201070011007405c1c05440ca444c001c3c00309495202031000707070704010381e160001800b5220340d8101000000264a5208805444d9050010b240011955103a5000d80e1550301046240c000d20841c0c0c208680144056181480d02d1504805000c034120100d80001070104005503640b507901 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 954019334 1250 954018084 954018089
    0x4020f030a1a24270307090b0607020d170f070b070c1101050c0a050d050c010f0c0c0201050309070b030c030906070c0c261006030210090f0302040f0b0909011b0c210c0804 75
    0xd40703d00c01c1c04e080d10205440c0a40c42e80295110600d4003c14006954541045420071581039600d040c007a850340c204440b400665184100c11240d001400603030500c0c52000a001191051140b01c04585444904684000d84500002c0c403c0008a501d4003041d030160010b003041c0c400410845050013010b541d020b04140d0792070b1288011680c041340d11306603081c00380621b05c804840900304000031142250000d01400c80d054029041c4040000411411901070004030050031241e0801ea98031f08201d10501d40c0b42c1d00456200001e03008942c007040e940d5128680910701207402c48480125142011401240c903042c1c40510504844520b601c41d10108090145003140f2030f02c4a00060007600c1d50061280c4550041500010400c001e802884020868044103050b00d4055800040c00f03807500024000600e42e641501b54000760386010801d04c02c905400c036441c0042e11030011003680742e03000000da40542c00c1140090503d82e89100302d0000c145a000b00c00581d01092030400032544482e100c00320250b0194 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 954020584 1250 954019334 954019387
    0x6110f010f061d0906060f150a0e01030509190605150a0f080d0513060c080f0d090512120c09031f05010609120201120b0103060504020f030a1a24 64
    0x18501040380800c03c401480c0d03040241c0c065440c4600c2c06103126030702c402e00100001e200d034180c1d48003e8640d40303854150302d080c02c80c05640c4a03911308181101401070801c0001d4030b400241840b000405c0080d01123401c1050f040751003d5003000d0f0081c0c0d0340302801341c17500400c5a0940040ca00c1241010f58528110b00c3c01040544141006a8240703458241440d00d000000300501408201d21411050b401010034212503036454419061940380c6841721140c8600c48041c0910003000c42c0c59210f040982e8040001207118030211120f06d0b1800554120034021200c405449200110002d4080c0d50410300900c81301c1002000d03180c01410040b2203181c00002000541981c4d80d56500601655030001c5a13140502480b000103156560a40d00003415001c407441100304445e00d0b10503203503280e4002c0d001035000e458010010344d281c8030106c0c1c2054a540040700c9841c0820308181d0040000803120820303a04000380600401041034900130903e1011504800f4070a0b507002c10450000315800b110070034014030454 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 954021834 1250 954020584 954020591
    0x10309051924140f0402010206130302070b0f030604201204020316031415040822050a1202010221042903040c1401080601200304090905030319060503060106110f010f 73
    0x205002c40f20a510001c0802d990518801c0a010245c5e8000962a5028030b409401c0c80382c07680c0380d1030100e040c003050b90300c010490f0034013007483d41011300346002942c413484058908000c0c540006262504101a07102240c400c9002005250040c1da038004041c0e03800350020302110034000682041c0c40c4401016407041d1400e47c1200d185104481d4248010320f58010307218000000c90800c0d49510010744540d01030b8045511441c89040f9070a51840100c4008000044c0700da2402c640d50f505966200464482c1240180110b00010003100c3c4021082603603010652030040c1050300b04424029080650040021300700d118529510301d021400000b544180d108008041065281210340206100d0f80400581805084030401050344d0348004545041c1410310b250302500d400540800c0d0451140c0c1e04003480c240d051820201c00d10800100840c007842c90800c01041c3c2c8504040a2821150a4060103926400a40040140510841d0000f100216600036540c00201001d0130508507001440d1180d805501e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 954023084 1250 954021834 954021851
    0x3090d0506180c01020709020c0f0604030e012a060b1f05041d150418170a08160c02040f0f0e060f01060224130506040308090c010309051924 62
    0x408141c00070b020300094005040855030000040d40b03485040c01140b401ca0303400314410510910400211b003441280c00d00b80d0300c0900345030030002d11541140c50b01c280440d501c82d181e802c44c0182c0f0000303051944640030b003409802500c3d99551002d4004803041030f81c408035181a88404c040c0d03004083d0114200c0340c80d10f6654911b082c01c14440c1141202003111030101d4041004840c8440003290400356001f1900003421010000c0141d926041c040b01c003500540c00f41c04010903071000300c0014000548140c503040c0340b5031b903511008495011220300c500000f5085100c40001400c15030050200c0001107080031549460350802c110403140c804546102c1a03000205003e490110320044a02401c000d101414000342129898014240d00810907019202c6050001d41d505580c40c40055120743c0c40800d40341981001d040c020071000303040d01c00c150103018920b0407140303d41c003910130280056440780251035010003140c0420301c0c010141405070350b00c840d641122055800010054400c2d0f03541341c0000070ba642d6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 954024334 1250 954023084 954023101
    0x6090703150e100506090d020d02300106150903140106050d120908161e0302030105090a03141c0b0307081c080a182915011209111203090d0506 63
    0x120301d60300207401741508001c6908151160625074031080d030143c8821101e40003030b10209000ca00c5c04222101c052402407681000f0645a03501d1080c1001941e00910a10f5180c40c000e82814541c0300900e404504403c00801c00212010803d01c8042e28080000464641c0c441c041f03014980b444804840806168070501d00641d0411003500243c00f100700205041d404219001409a42502903808019a284003218411805821810195501134000d000a04040d104942e5880820b0803c0f00070640c900080410355501031f095400c02c1a0792555096000203d0041c800140b143d00701807505030040ca5008102c8032410006156201030442e48054841e000c601e00a100000c0a01648981c1d8140644604100a21500420000c7e0030034800c0c441640800e01c544540d4010014155036a92000b041120740585420700200d0f400080e20303094400e0621014407400c49003c224001d211031400103e00d4180d043c00c81c0e441c6c0000080da0100c81c0303030050410003c0c00407504190222190f5119408025101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 954025584 1250 954024334 954024361
    0x3180f05060a110913060801111222021002150f1e010825030c091505030d0903061505030114070e011d010309061107050c010e0d020906090703150e 65
    0x681070369080001c1c04081c060f00d101440b480e04020701c564015044080d41100980c02200180580c10080228804c0b0410301159500000e42c4541a00a0400000c01181d0190700c05c80b044401888688403c4101c0d9007080030744100011040110300c80d0550811041b07081101d038500903404d20f010003284c0c1c07070004800c84002000000d0000580c2036140100456113002510040703003038010652140201311040f4052500ca11a40302500c1c07806841030000e690b200a50003200004c010a54120381c554658050580d14241a1036000c0022a071050400102c1d6150740485510000280a182800e13a6000000c0c20744800301a16031214440c0820700500d550005c800796070300c003002e0030012040b4003d10000d01003407590501c943e0515448000580c2000032507841484410071095802d40c49150707d041150ba030303846060300c25021488600556141d441d01c03e000d0301040f58028040301107941d58006114179900050b000d9024035845442c283e894038000300002010b000c0b03000b0520b80e82d2500c440d03212141f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 954026834 1250 954025584 954025591
    0x6090525050a05012001021303120f05040303210f0f140115050712030902060a0309020907210e1903020d0f080c12040512160212120307080703180f0506 67
    0x2e802c0822081005036046001c10003e2158180c01c64590248018140e01a102e20280b1a0181e01c005d00048200703d2541c8901071120706030796404400780386c81c200580340c40c8658000900802c2cac5000e001c82400034816010310030341600d00004507803100725200c0d0308250703101410940140340c0ca03a03041d0745800703850f0000540107003164140100d03080f007a078034040c0640c1300d0320030085e110300031234003502103298040d400c07215003580d0140442d681c60340c2c0584000c00a00320100d00328440d00d10600400e0b26517116a4440340e6403d020707d140d000340d10141207454024102034251646c00d00a40a5854040a8681c040710619020780c0141100c0c511510000344506007410410013445082024040c0c801d5118003900c0002503640c0880c5500c0e200d81c00c00511305443e628008205410001c2c03880c021030800280040e1880c820fa4074040d1001112801c2903c0e07001c0012800840c03201440000c600c180704440740c0350462914100068603040c101640c00c1d048000510030f03074040d9071078404401004400c02c1400d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 954028084 1250 954026834 954026839
    0x1060906180b03340b0301031208060103110412050a020a08010231260d11010b01031a01051309090302030a0f08060a150201020c15010f050d030206070c0609052505 72
    0x702d8810b080141e04003659040c1d583c2007003000da10603044d5103480d400c848060108005019200e6a4030328105071860050340c08a80064440b80206080d5400f07802401100c00312180350900705410040800e114042041d07095030944161508a005611804a40f201a081005c005a9074202d450f401c501d001010190103030701100f2008548100103003444000302521080310343d100b5103120907891916020070801c441c0c001340c040c1780c5900c10f501d40c0200e500c0030046024002409111f2403400190b00312403906200c489100d1032584080c16561042c4018490308001150381104180ca400e84a0112010074078100c0160703100140c001d2145400c820134207006091440c0c00c40440c6030030340100300760b10070f244a000d1545001c1c0c20613512841c003c0d0191034411100d9403c0324948203810520300303090707042882018500c40c8a0b2030041420b007000f01e07070039400301c0d0103070010074a9494448048a001e40e10000c103035120380c1d43d046070600103103091208400d0740780042460525035910741c2105044810582c007007072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 954029334 1250 954028084 954028093
    0x2070b0d0c09030b0f06030615013e0307050c060702031c030b0d05010b12060c04060e010c06021204150203090a08070807050a08030a11090a0b0c01060906180b03 71
    0x40120055421592116840c010101c0c820703501180c203a41c450300c00d820042c12507024a003000403410882e1080d522801c0110100c81c600d40f00c030b450303401d50070710030610080c002100d070503141c400400c00320711404000e0781440f01a211080064a140b82c58030055900034001c1c0c00004000c2c0a000f1f08001041810380c0c121066854002584d0010399904845108a40301c0e401134080211100e0080e40100c3e20804040d044400740003a9190940c02054280c410a1196140031100c0c10303c1c102c000384503485035241d403588034681800c001c4107032288804060440e04200600b014500012120b0000d86090700c1010355100341c0b07003400e1600b02c8141100d4107800d07020714410300800c4070601d000910740c0d170b41f00d07080190640e5138a00c07401e14181c2441542c1d0068024440c4d480d02d0010820041e00541c4030701c190781d404102c1159105ca0f1080c15118940d0070f90341c0502403030420300c0a26100070050a060920704000600540d41d0100700094807803030fa0100400000ea529008481034443c020714044140490261 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 954030584 1250 954029334 954029339
    0x70f0f021209010809070504051003051e0304060818030d05061e090c07061103090304080f16151e03050601170c030708100306090501050613090f0b0c0f0309011b0207 73
    0x10001e805100710040c1004142404610a0380c1c05100201c007415001e4428401807078104020b080800041c03000f15100d20071039080e1166014611903009010421501071890325160150444c2c0d02c01000e080187d114880700c0d01c5100b521303401c0004140781105a0303008622450280c00304a400c147d81041c0384401c0324a4640c80e60756664207000aa07001150407030060315940e581c1004001003610328070482d4880c3c0c1c0001403086a510010140007243c0c41c0d070f0119124a4031420000340c403140c01358902d200300c1841c158107001400402c485d0445c3c07010a460310300b03c0c1640c4034900b03010f480114504c0b039010987c0c0d032052105659202c0d4094809124010420b64982016101f44440b444020180e07020001c13940c011601c2202c0c038210303140046070004024826a855810224000d081c01e847d114801c00c410242c1c0410a0303494011311524076080040040700c0040c0b520b82c070340c41903001407800b03640c070004104520101112801840c000c164020002800034404581822642103000281c010b5503c144400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 954031834 1250 954030584 954030613
    0x30c04120c06031b230409180b010b040b0315011110060609060221090d08030903040f14030604151d0a0203010c05120a15031203020d140c070605090c0306070f0f02 72
    0x3041c85d0790170401041c01c2e4889050080c10250066800c60425103042c0046040e5102d071280010440a0048020155590f641c14a0034964860b41c800c0b003020b6007050002030710035000c0b0852020210b8040c10200d541500300f02c2e50a04010229503e03a081c5540d0760f0080c006603030311492010103032580380014044410f400944400031102050700c1c0c000100001404045038032210070f0025800d5210019903164200310303503419100d03001401900a00001c1980c0005c5128443e070740d00d6400f403c003030050710040e240c035283e6041d154901414000e5450b110b002000496010104008029966502410000f03400b03104150a6840b00c100712810000e003409040c109a071003036003c540103540a00005240035950821100c007400d5540007410f021280b400400d40f803501a001009c0b580c2e8861801c1210400084070041c0c8482c1c152030701006c0c603400384075580010b299503000b1508074802c1c1d802c4408075042000002c1c5007120498001000513182c2d90301e01c04e042d800c03400c0500d549203c0c0c0080c00e08110711001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 954033084 1250 954031834 954031847
    0x1416020c0a0e0c0706051602061e060103020310080d2706090e09010e010f0516030e0c011206030b090c1e03151f1512021c02030c04120c06031b 63
    0x1500400c208010041030400c9803843c21114115400b50f000e20081c079060110781c0e9a403090203c180e026004640000342102090f00081d00c0c0d0030b00c0180110507540b140c4004400a42008101d41e405603036118011548400402c14442108501d50316000442003142041c5420b48124003080c2c50401086414014143c000031f02c0380030340320038a2407492241d030ba180d00c0d40c0c0035241050241c3c02651900030070000404154008038450440d00d02300520350a0a440118103e0300300718200a2103800210080849620800f00840608030103440803940948984030f8148080741515508003d03070240b0b80c02004d03400c2c5540c41090103900310f440c10600e8201c1e070000c00c0c1c89004a111484102120a002845c15081405610341e89042c2201e078602003600c41014443e000340c5000300301e01094080082080301c0840b8000c0301d800e51580d040b190340c0c4031080c6c07006002075003002c2c1c88500e41c16800c0c4400309050300640200500103008000b0b10404c6482c03c100501160b401f904408202071103484682c0c40c0940000d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 954034334 1250 954033084 954033089
    0x1b0f080913060f470f030a060501080c1305060a0c1509020f12070504020f2104022b02040b03281a01030308241002060a050703050907060e060d1416020c0a 68
    0x31030605441e00111604d851449800500314602d1004018420214020303440071042c5c80f400c0c0ca5078041500c800c2001606405280b40071107608070214410300c540d00b050030242c031b964505400c201c1343c40c2c111503441240382002c4512602c450360f5141110b0040d480c1001800c42180f1050b82e070401d49000c26080039848100c54000d1500454000130501c27548148a001c40745160f541e96100615280350004500d90002c00381c40a0748a9505003200f005000320840c1169035040301c2c0101c031800224540d01384000b802c070b21000c040c0c2c11300584900310501408c91603d400304007585019810b205201e840e0250402c440301843d20f001424450045c00044c0d0400001500401d800c04000c40042c1141c1502e0364002181800c00d4001175086520401c4a8000174071a00800300074409002960b1030030340490441e030084075650903d80c0400000c0001c41d0103103031031440d086005400c40b454004411600000d60f103c00b074040a0107400351080210048001c1a80c040c10459840035004600403070740061070011050 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 954035584 1250 954034334 954034439
    0x1f051803030411011e020f1b030705090c0714070617191503020a080d031b02030a050c101806050f04030e1210050705030105011b0f080913060f 63
    0xf602981e030081d4664100c1e9011201012040d0703010042c0252501c145400b200c800344110941d00c4490f0401c0b0324a6043c80001600804031986401304010640a020741801c4206000f00892801300d03090041014110100c14003c00c00f1528180c0010044102c58421001c072122100602c5440c10599441442b40f032003689c00840c1c070b4030b00588007601c0e807103250340700035404540c01d14000303000303080440c080d4402411034404004050640c40c50b4a01c40c00f00b41514401a0020040e48228501510191440d402480110342101c403500c82140101c50f0440a92810482408009020046a8010140e1180c84244885110708066501030054601030003220b208141c1e4009402e82800100100130556614403c28001410304020103080c0f80e0080c0580c80c001401c400451400104030784800008661045481e004c0040580310400560081c80603581c0c04035201580e80300000c0c15001b4480a0100c06c0b45044000d0f00e080c0c2d45c0065002c02112411740d001e02041f4061000030800811414808403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 954036834 1250 954035584 954035603
    0xf05030604020f0c010e010f0b0a0509040204152310030e121b0105010e0414070e040b10171006090903021902031908090102011107050615121f0518030304 68
    0x90f0041101c00f402800031403916586000800320280105400190000b030300000d003000700309240400c5c480400c540d4045c054101080c031000c00c1c01410550b00070b1041000c070344450726507140c40c1c1e40417282c2c0001011044090422004401e0390341c1c80c101000d200598a80e050420040d031078000400c0d00c4006070540420750040100d804050b1940c01c2400341e42468158008101941e190041840c150034155019581400204825007400000244a00c29103a8000b100a0a0b0360f0701c0da186141d485004081000c0d80000d0840011030b00300c081c450782d505141c8207003e4801010040840e2048410300d81c01013150070308103405d1101194010031004000c42680003034004065042c00400e2809080302c0d00a0b10360304240200e80c0500000074041d0550102c00da0003805400d4110800d010a80236940024015400c4240864605000841c201c0c00500340680030207a441c0040c010141000030080c82c5400301180c0d5002d50314174010501c0f80030740c0030103c9034400d40544200d001c01030f6213002c000c1004100c031a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 954038084 1250 954036834 954036847
    0x1802030f040f08040b16120201271a270d0e090912040b2104081909050415080c03071508070c060f271104090303020903160f060f0503060402 62
    0x40050480e8003800c440f0309000e9459506ca001c1640031740a410080c0c0d2009900b1044101d01ea00c10b0040101c0c0210081000700c140d480000ca07141c040701206400c03582d1030445001c0003c0c1021424180d4424200b443c0d440c150352460b808003d0100c28450303402002c0341c005484103074240ba084800314072268400d1795050750340d80e1801c203824034009400b003030303a40d0b08080460000307000e5001000034400c9006464480080c400c410311040040003054070020700080c0244802100792a034558004180e03107140c40e1244240340e40300c0203d81116802d401500c29448104803d01c00d100042084480180b0b05600822034280f03809500c182c284100241101000b0040000c28440d511a030443c1e0035464100c2c10410902c0300c141d800d10010694010000003035006038002d000041110704200000541014101401040380d00c1040002c01e000f0400318185a42807012215a4400700300c042c82d00810803a4014202d030a1503014a2604155400141046a03480c4150010b65024054030303040442a030380561580c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 954039334 1250 954038084 954038093
    0x513110a0e0f09040b07020708010203090601030204090201030b0a030c291603021608100e010207030c0b10030c03050304050922020f06090303030a0c0305130b010312050c161802030f040f 82
    0x100a500041c0c1c032200441c180400d01500d40e05c0d46000c2c03c92030b001c40310701503038400b41e0303500381d000071510003a85030019001000903082c16001120158414540054010360480024144040da9001980c080180540500080d20104014583c05100c08444c1c44002c180c1c8003045c865210708002d002c22410000100310401d8004c010360001280314540e145903090310303120b03841e5482c2500350308501520b05001210360000010310880301e000350103954081e12a0840e03210306280c0400a041928003181140c40003011071204074002010b180709001039035445240208108801c2d001500418010300c1180d855040280500700911540ea415159003145800b03a0000400324003c000c170319a09400000f00300051400c1c2980701081291291314200103070703140c0a03600b24a40c1c80340c400040051032600018404070700701600c003014082e10b91a0491600b205501c10328245000d05005403c2180407238402d10018421540702d07910420ba4035821401d510705a4550101140003510141c00722010039010b80500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 954040584 1250 954039334 954039349
    0x192709020d1b030c08060907020a06050907080d05070b0603070605070b0c07060207050309100f09030b0c070c0608010e0f040209010e04051002030106092909010f0210150513110a0e 79
    0x42088000c010300c1101150b030040d0180c00400340700300000e610080099114036101704454001d0f0b84990041408420039a00c010007460007800c400319030302c1100c000140fa11000c0129491900c000c3d624191140d07201d2400e801d040c6000307401b00e8400c1e00302d07400038890301d46d1040541c0c0e019a0401035042e865201c0e9440c0501610901c00b000d032500340001100c40500c1800401041c40d4407094504224000c0e00c40803c0b908440c002560fa00000d24101c1d003040030403178034540c290304a00080303101494008199550740e4a00400d602460100d942c1c00c004201c96050f0302c0b032507a4080701500c41c03021207180550024140000501410f4100b0000c0c1010405003d8100074022a140a1113011903503540c41e58006480000f4621540f00b1101aa40d00069101001103416400ea410700c03101c41e0501c10890b0064a040070028004170440c030444c00b0322540c01e03103035000d800740c3d640750103110034042820301e0140701e0780c0b03052420140c1415040448419030702e00c00c40200c9100031410314020450100000c00500075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 954041834 1250 954040584 954040601
    0x3052e2a0c0605100e150913021503130b090106080307080c150a06090b030316060b13050411040507020d02071a04080106030606080c0a0e04032102192709020d 70
    0x8092410041004c800c180304814070980f01821704c86909a600d000320003d15611032242c0e241c04c0210304010800d003c0b800380700050201c0c40246402c074401c910940149140c0c00461700d041000c80708004034004c0c01000241281c000f80d00d0b50092050a0901303981030355a10480500411450b800038401810080c00d100091003d004e000b140905401c0024122011341400d00611f00507c0c6800300040f484d180000807114078501e00d4170341c015001c08503240d0300000c04d2407070a01034100861101c9144450780c00e1007014420342c031420340003801d01d0542081c841100da0007083d0509650000b20080d007450b4001502500321602c00240038110303400d0b44d400c4d01e40ba018a1b8050300300c075820140044100030390781d0802019103190b00c0403030f15000b840004024007000c041c400d60200c5280440454082441410f941c61445a14080810728544101c821f20482e84140340f180740c0005503140c0400415400b10f00001c0d18040e044410304c041880030600d50310b4401030300c2218500b030b078001000e44408000350012001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 954043084 1250 954041834 954041843
    0xc190204240b0a090e100f0803090916030912031505181b04080f0106140d0c06080a020f181503011d090c0d0c0e100b0403060f0603052e2a0c 62
    0x4505020840c82a02045030044201c580c101f0800400c032030030001b00369110000000c04541843c2c450f1070701e01401c03440c00c40000003015111440e10700480d0306160f2030f100b05061a5800503480741c0c24440002401d410b80c005910481e610218a2660403140301185d400c20544203a10598034424406180c0710312855214800500030350010b09180e84040d840314003203440e4904122400c003050010005400c03a27200005208840e040c8041c050240301d2038105230b21040c1c021005141c01030003512202550810950f000303600c00c108102000d51306082c0c0200724007040c24000d690a41d41000c1c140d0711803854510144400450900018032040c07010801d40504580161581800e0546424650528a02c60146603440b0380d00d00c022409a1607190842e0f03040702d040b084007600b014119514030700600300303801000485a840340c0010010401c140f02c05803a81c001100405d405010645051050807610390f140400c0a1500c90101600042000c0b440b103809001c41005008412a80c1d00350f03907049454401a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 954044334 1250 954043084 954043109
    0x40515190c20030414060403021c0501111b0d030516030e031201090c080c0705070e13150506011d030615191e0509061509060c190204240b0a09 63
    0x42c0301182c08001030083c1da0102d50840920b40c018400d1206900c2180b1000750011003001c1d001c00800800c120740c2070301c40d2003600003051074165010300c81c80d280c00c0321901c107910508503264240c2404041010224003540d50805005600c4d24180d82200f00c0c61080041c0c090588401c40450740342030a008445850020580c0b00034203584404802d8020011070300300701c02094000b40444d4440c46114152000168800014031000b403d01000e40c80171140900101c900c80c240d50300002c00074200880381d141c0c0e40740200000450745015400109401d124800740030b240316100144801c3c5440108129601145184d4011580c0c1c5102c03010802c85a030301c000701400c0303c0c441e2138007050a41d030700c80e1000141c1c2081d08041c0312150f1184200001d070714040e500240c0c07003d02144125040ea04c4803024000c0072a000b0300e12414484100001c41c106180320044507161154500c41d0011032800d4400d000080c110a034a0012580007a006440c807d456030284402d5820003240402c60588211821005049181d6051 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 954045584 1250 954044334 954044387
    0xc02060c0102072a150c06020a030f0605120709050c0f041202030d09080d120b06131a030c0307140904090b0414030c03070f14060f040515190c 63
    0x114001e4000020403a5814020018034150010007000c3c104c0d130000c07035134a41103074614240c0388800c0e18401c84021424402141101d10218072103202420200c222600d000c00c00e40541202d0fa8200c0d1084d801c503d2081c00c0c030761070348484280c0000c0c1c0d01090b1121640d001821351900311080c952801105400c892a0400080100b48803114403142114244213400300c0c1e00d0344903441c07010755100c841802240503a1780203031074149847d8802d0000b007901849810001804c3d075004408951540d01c40c81c44600117a042c44c104020000c04400302c0b1280c02031010a850543c18485404a160710003e000c6030208160b480310f8010108c1854202e03400c10b40010000c1141e00d0301e902c2c0514590348111000c3d6481e000046160182c018040202d03003002d50400041c0d860030306a030340c0c0c3c04443e20b0891f10a55481420352000420701d030301007000901950594586080910709840d0a614100c2e0500702d100064002e00c02340a04c0741c2c0c03010b012056081c8d9400002c10f0060010004a4040042c0a001191950800c811 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 954046834 1250 954045584 954045607
    0x4120f0b01180b0f010e0405040f080a0905030f0705060403020d1a070c1202011505100c050f0102040510030c092105060403081f0312030e031b0d0f0807080a0209010c0206 75
    0x8031900c150b007498040c04114105000c0042806900e030043e401308542815000d040e00d03007540304c190b00505c1200c01a1000718141c44229036074201010100108403501014080c601e01004210341c1042c051005020b001c0c14640841d140380941d1000a0103001088000c80030000707901d40103050000545030a86103450a00303401072551802e0322055175000829290104905d2060003421845500036056045051811b01401001d881c411461010044401740403000107d060081e0750400584000150300e503420300c0c0400c4003031b0446080e16424140703010455000c4a8001001008840c8d127017100c11140b40303600d040964490600c2100801c00d02500080004142c2c000c0070309402000e428204c610490004e84400441030038901000e00105031011000c0c036214441e4000301c37402110601039034244044248040c034600c200601c1004d0f99002500c5581d02c00354042d0000e1101d50039481c2030700050800700e1002e40045c6003c0c1404c101035400150b43c4800e41d001b0036130b0b00d040e0365026080643d101d0003400c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 954048084 1250 954046834 954046859
    0xa02100c0e1008091b010e06030a0504050c06030f010e2e170102070519111203040504050a0b010e010c4409031020192304120f0b01 58
    0x100e103214542001840014a03c100c50f0140300d44510070090083c4003c002d0542000b80310b980f10719042100b189482000d98840e8000b81d40039034182000410b072030a140c500300c2c1c03c185800c0d902c1c4e80504014030403c101c80c4401000c4e141104d003e030442c440790391110107109012031540d1b200c00c04413070440c4000701b00b2078032580f0032802150039041214103002284101c0038280c1c8a00000a40258030074903001d1400c071106800320144520503940a018010510b001c148014414541200180c201080401c4103003040d0040720380c80031203c2400c2201000d814006460660341d180b086042103129000d2000b0005000c44507085111040c10320414608240c0d04004903415140240c4180040c5542e00c03490100d0b540e007941e001d0480240501901050a4803080041c41c0907030070800b240307280f911140c4d02c03075138500001c25440f204030450238a1480144130203410b2021034051b4118a01a201001400943c0c01c016101034400e4070300250b5000700316040144a086031a0006802c45441e44000110700e440d050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 954049334 1250 954048084 954048107
    0x1b0c0f1e05030d0909150e1e0a0c1b03030906050a270209072703110f010806061909080303090705010212030708040b041a0709050109120503040306020a02100c 70
    0x1440c51110540310410316481e0010071803600003166603d10280811461504015100320b48404509580303550f46010310880441030300d001c040300101c0d2048040f140c00d04a0445e40c4070002030002d2001180c170350001071260310307422202c5460320a6040f100d01010310940003100b0742900108280000d080169100d002030520344112407003001641016030003190040c1295000c107070002c2c898002561451000d17124209080e1450b18488100c0c40005402c10001d80841c002e1805403002000141c00041409450071003400040c1c14031261798100401c42d40c600d8200d0f0112884810076039100d07140842e081e140c0300c5054100002500000c410004200700000f10030007100c80913400c0300d0041078910a00300c620704c001d50b500703000181010300043c04a1310135a2141e41040c07258501c040d4481e07000d44144518031056501500054181074100040d41e4000d54403005007010120030350907012640d445035030f42c0c4100d1000800090b008200006458000e2041462a015103001030011050f8140010604052130 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 954050584 1250 954049334 954049379
    0x10807050103050c03070e061e070b010e04020d1202010b030106140103050c0c03032418060a06030209030c040b040b060412050d030e1f0f02040803030609090a031b0c0f 74
    0x2140016a40d072107801094002c40700007a50790300d9620782c0c140c11601502e200401c5c64001000f04031071508080900160040c140c041d03c1c07501d485512529003e0034408069000d00b0348c040c011018440542d89075681091a140e009043c0c2081700d04000d42a40901600000103516501e031400000310103112400e881541042640d00b0040c90303030fa481e18165a400340d4102c28a0382e920a02c0068210f074041c1c81c0e4500e07011003403052046410740c0d0000084200c182c0c504039912080802040c42400d0622440c21809021681015410200000003280e507641c002c0b0380203881261034000141480e19250312100908001404981d03840d83c40d20552428034090300c00031034040c13007400382e5156000d10a1080301d01007403450000d460701090000c00c01c08260b100285910301d15903102c1c015410701c0d0321440100010b11f64900956182d1419004102c02d80390010107500c025000720110000095001b01d42c8205407108050300c0071888024103080044200c2501f00503e46100180017084140e03c0c8000b400050510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 954051834 1250 954050584 954050593
    0x1b06060108070f08071e03020d110307020d0507060e01020a051b0d080601050318190204060b160209130b0c04080105181f090f030c0c060c080a0807170108060108 71
    0x24500111110482203079a240000c41152101209500c140c0c002d58000442d0302d440ca251480d030001c010202070003c41a08040f139400520300c241c10b10705008000700d661030403123443c3c20741ca80090003941b200300c18580351b0f0400800040840c1004403e03409a24000c0200000315103503800b172600a085a8448506040a40c401d904600d0491200007421000c031401580c611141e51544c07001952181c01c040e1030001c0c103c032100d04154034a0002c01c62000349a842c0c0c1e02c00042d9030000e00622044408640000312a002d08110420508000c12034214526a050750700c0445561007200440071001e03a904001c02c900541000d00041c805450040c00039180791100811494076240400e46a003501407800c0809a001800c8207400b0009480f45144c0d009400035000c1901c0c08990750700d4080b0142a002100400c40c6074511005000300d555031003010b00298240f009400240e0b840d521014000c40300b101080101001c00144038911030303113150f07201011300920601030f542c4400b44242c0301c007800d015a0304a03119 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 954053084 1250 954051834 954051841
    0x40b0c03040e13150522140a12200a020f03150a02180102010506030c120f030f03070f2309062505011a0604090b0114040f051003020c06060f040608031b06 68
    0x28520895024010b07078000011000d6142e0008a00c04116146c161000c0710340c4a410710300039205000d0242c2d101e21440e1034000d5007140c02d41c050204004030400055000080c200000c5480000542c040d00580445d82c035820101103c0000c0e1408070480e040c02103014840080c8544648543c018000140c4440d180b80305915016004a0803210201c2d02142e0690003003a244d2001e0905005500603110200b042d80d819101c0c5400c014a160b00415030b08a041100108010540d58040c0c40010034001500e8008140107070403c07001c9d41c503510000140c40e01c080008001c009036070f4680c00c8070041039036400c4802c106840c50302d151002c401c40003807d0f22507500741041b21088010150360030034580b4008100d2030400b414019844010f0552080c17246c1440f8460301407002c40444507010700b0003864442c1914007400d0034082400801c45509501200b4540140003003d6a14030104c4c1240e072200007940c1c0300d21210040340001d0007a104960240b8424000006c13800d51030a070148182c4c1505101600320b881c6601e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 954054334 1250 954053084 954053123
    0x140102180f0d0b0a020d110910080106140c03090d0609050705091e060d02041506030e0a2114041401030b0612010b16060f1e0e03040b0c03040e13 64
    0x1084000c1c955802640500c208001840c1009115040503101400500704614100200211100000c82ca5682000441d80c00c2c00d40c501145803000b604603d113801c24503035144c6200075048481c1c5040b1031035001400b207405e0b005103004105565441e04010a000c114108906208008004004c01580c40d4001c0100120710b078100303c14901d00481d030800c413260303000c0150550f0142010000d82415448210001c040c80560b9035401091000e1110700d02102e06d8519200c0081c00704d5940088e800346035001480000c020442c07007945140d500300314000c0c013040401c1d0b10744202c4508000462542c0d01d040d000c20041a0720903110301441f4001020388040050000712802c00c100d0740101101070303c1c5041c0110052069107002000390101301000c120742c0750885140d40e1810148c1c0c41c0c03c2c1e100d0108907030b207000181d5415424880c4122039464140c2c00c200010000707040b50f8407413060b030040c0394004500060030780c000740040085400134000350503101c01c0c50402c1048a030914800c01d0090300c1c0000407049100500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 954055584 1250 954054334 954054349
    0x30e0c060f07020103020903010c1812080a0302030a1b020d020f19020d020607080301080a061109010e040510030213020c0c030d0504120c090e011416020a08090a0314010218 76
    0x506000380000c0c1450382064000c0300c642e119250490405409100c0c6130081d444c06d02030604059070a0300c030314501c51303139040a40c0d501312032992020003194030b00b0012402140680f81202e410398080c2c03401603541e5030703458240e4000e414014ae0078074115605ca207104c0c4841e0342c0850800e500d07c855a02703031508844d0302c00120381e640c010352520492034141304520344014601605242c0080d840a000c0d98180b0f1070740d17200c0c034115400907488900a0341100c044841000790034441c107401058415012402d100784e00c40001d080011001005028681d250b0101c2d4800c04072545101c015640101a08055150504907001a4000048514161040ac06810500d250216204100d02c285a07038550a02c0c2c40c1c09451841074102c600144c588107100c00d40030401f144580105c00700c0196150022400b04084040c036000c1e40d20003000c55440803c00900050241c1e40444c0005046802c126819101c000000024008071011b60000303001c04009401c40e104100190060304590440d10794424507900081d0501500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 954056834 1250 954055584 954055603
    0xf0a0822080904051015110c092203110a0c0f0510050d2004120302060c130e0a0b041b17010f0608040507051309021f1403070e0d0c06030e 61
    0x10307480280440c00c12818030b5402a94044000c4840101d91030361207144c40390b403181c100b503000700080c1010058110345500b0804ca0205c014140e90040c1c1d103141481c0807414151190000745450401e060401d41070510489010364020b032020283c400c070304c1c03141c80d08a5090b4038074803039506210442500001e00f0325154640e180d8804554551501d03000c101e0b10300c0300040c0004c101c0c0d421302d10340884c0940d10013542c480140010b003161014400c044003903810082d150001c01004008010410804400c01a43c0300382c07410222080e0b10709913052925003200c0d80028010f400a025082850012510080c10030304080c05ca10200d151203045001d070040764000c070131800902038040701510003501002981c0c800e2800651150094041d121000e8960000403c035035405e050032104243c4501100082d407400c103090018030309610400c11355489074124003400341880d20303031055244c0070040009000e075802211401c1120070010300c003080403030162070314140b610082c0c098075002910b0028801e481c9000026241b04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 954058084 1250 954056834 954056843
    0x6090909020f0a0605432a0e1f060315030b090706110a0206160503070213020405030106170c01270303120516021c030e03030a0e0d0203040e0a110f0a0822 68
    0x585401e61b418030801014060001c603080c3c005240304465000c0404040891030207101980492070f0705d80b0345104031204007c1c101ca08050750805c3c88008034254400010102c0e2098180810714642130b1030707104a6800e2681c0054040110801084203110300440c1420581e01681c86107000c1c180c010340e80e50364038802424025000031041200c424083e820311505c64020b0710410450749000b00380c0d404282d00103030309520100000d4010800788401e140038020880600041b400c411048240480d00a0392130400c0c01040d8144110205d010502e918140307103c00300325240079803103080c2582d03e140080112820710640c1e80c895280ca0041107007420851002900002150300914000286141403800f040d44102694241540c810300d01502c2c0600f88080e501c9801c40050014000280c00813150a0a03000d030320410464004200038400380511040b841d0300a0005070000440e0305401c19000c4840c810032054104400c1c1c049030f56240c40e648901c07018440d000b4225903190b03d0903a80c18080080542910082 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 954059334 1250 954058084 954058177
    0x2130605041b0906020d121104050d0c0806070f120b0f0a0f15031e0c030f0c0c0210020610090b180c18030106051005070609020d050d02061006090909020f0a0605 71
    0x1e43c1400b00383c00100341041e040f238042d8500340e40e8400045142071070a40c203e690705030f240070802003035005103d200ea005c4400c0c1802d040d03510014100030f00d5214241000c1c5c08403603440b0001041c0d41c517101075044d410080a8069072141e900e07500050004040e6100e500c07011a0900c0b901c43d01284240036101085402c1c1e031546950624484001024142c00840c00f0308042d600c00741107102c0701003401418200c1e011511041007c0701d060042c8481440fa40b0290001c2d54054014048039a0160000340c0c121240104006a454110320004002007617003040a9031f41c81080381402a80802070004210144800c04600e0b12050244141801e82d6600d2081a500080da2000c2050341030040c001043c0da2440b0f401c0001d42c00006a0000700702400c3c0c0c0c10161810b6001d100281142a010428517811183c00010441e00b94a480d2000f0843c1d40d07207000c2d103919607484090300000c640315605902e501c0a00288107140351512800f0080054010380c3c03440000351528085003c030503c00c1c1c071004002c02500c0790b00c034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 954060584 1250 954059334 954059357
    0x3010608040c15052b050a0c0215040305040e072c190303020319030207051c110312070f020a12050d0b04060302060301060c050f0a0f02090603010b09010302130605041b0906020d 78
    0x1656880100150707200c0c0184079102e005540305c0c183c46940d00c0713050525400142c860000740020f140103404110049200b600d0800e12002c40e0300702c03040c0c0c0d0449100c113094145036650142d08403030681a003480c041c521201070344c10307882d031035171800300c1010800040d140034045a06c203101d01c40c218030180c807006c4c01503041004100c40c030051003401c070341c07402c00c2ca8100585491000d55580740b600003100024043d0b0318a00bc00004000c0c4d1001e060b04034002400020350400196a0b9a140c41513009044401405107000180c08214024041520501d070082d01c4a01c58680b201d001414540c054090a0007061405130700f290b00b454544585d00649402500d035a00f160308bc4103040e40c41c2d1100b444260340e548540c0a5419408500300160300050b407103203039540d20034202031061040200e0042d25180c17180e41440301042054032540d512a044a804854160142905018100007003502e03800030354200c0e0501e4001d0419101c0310f1811105210281d5070400d503540d442408030781300c050700041c21001846541d900c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 954061834 1250 954060584 954060607
    0xc0311031b0901020726010b18071b08160209101a0a02281a010b070b0a18030e1003050c0406050702060d0c081e0106170a1103010608040c1505 63
    0x5000c03282e5040c011204019211350705100007405c400a25291000440c942d82409882805089285502661903110420121410b040103080082c00d50040041401000700004024003c000701c00380c03c895259520441c1e130150f0314007a90402400d034064030034540403d0030314584005007012107101c40400300c1c2c1d00c00224103151855009102010440c444c01d122849100b3729a03242014400f04e44103403218528007403400049e03004120702c0580001d08440010005000d900084600c1c0c15404180b103e1141e031801c078018020300700640301e00000380c0c4040c551001c058000c0030842000104441c82005051004401c03826500304641c040d0a04074144010010f0600400140014500c000e00e640e0600190381c0c1441c0c00c540d40106150005031000c405c0c0101d103e00310250300340c4000081140040f40d030401c0c80c003030070040c881440810050103000000704118440e078401d21065120551940d035a5a480b40006c04010090341d09072032900b60701c0800600c0c01350800c82602402201c0d1203107800c042e141c820 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 954063084 1250 954061834 954061837
    0x60507021e1005060315010b0a09050609130b18070c060f020a1709071521050126030d0203040f03090e070806010f0e130c0e0a0f12081c0c0311031b 65
    0x444c5800d40b041280a4205088110301c5601810034440c1e8542c8442e01c104d8009d0558074658000b900840d81080742c03040c60b0301d0300544220002689400072410803074102c0410308141540140a103500b501000380701c0e132554400c4220a8160140e4001d200300300030160b45900324448c207100100450720181030b016840902e400059400060803050310b88407a0b940e06201895020b100c8464002040d232020b50030510001306000440300f122200400a56052100c241000e880e510b080040504c1c66401080510b40100200c0ba1000f100314003c0d0744a060a2500441001031900300b2400f04400800101d0661407114990384118401d559800e0207840701c3e00151100e02c02c0f200000200f003e5180d110f0441c2e121b1800032800030300003440001c1d05100d0680020300001c4091011403080703180000400500c2d0f541c0c4171394010341d000b0344603224003030b4558913160f0954071401e55120720280c1d0402ca05003041d220b5600c2a03144e828162030901c0b0000200310b800d05603210464011009454107850b8841d0741c50f40c0d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 954064334 1250 954063084 954063091
    0x15010b0306100c0807050a1505040b06061e070b0105040b0d0309050108040303060302090f060301110a120b03030717090901090606021e120408102d0b1507060507021e1005 75
    0x3400c040703401d101e031a00703501c69011805c240e8590348290790315010024010084072007444800410090f605140d82d82c00c100c1200602003030f110303581c04a200d2000700c454282c14400304020b506215601d0b0040e103844088140e003441494400d5141141c0743c006424075850302140c075030b4195200d108560a003001075500b14805030040c0c081513621000480142c64806480d030050701880300044851500d502014299082d030321450410080038044030404541291410501c1780c10004045a0f0100c01c1c1c1c003207441c6001d01c1301d000d4068803018505a84414079003004081070b103020380e421091030b07884200c10030641e50303140f01d884014ce106a0941c803941c040403014080b000c2904040d224540c410300a00c146941150304014055080300e00468445c21079440b98040c1c4240c40c10a40b1a0610155000c8034968144040d050219446e101a81d000340e8036003000150320107490781c515403564a1424a24003c01003201c1d0306000d0b102e0444030882200c5610100100d552002001384196070a00104101804c1e015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 954065584 1250 954064334 954064337
    0x60c03080406090812041202010c090e060d050106123513030c090f0e0a050c210303010f060f090f0b0a140f031b040b0d0e19060204060215010b030610 66
    0x3c3c18040c0004420400508062031904d0110700181000c0c20091084151012084296031620f0b80d9424501c1c6c110550004880d2022885031142c4c0e00c00011680d00071420741c00400702c0d441c0c82d4002c19200050000301d440c150041c01004820f01c4031005c140500410080e00080310306003885c40110f50000c180c0105210400e0a8080c2c282580c1c035030b100405d15000e0b81102104549a001c24959414148107801000b4001001000360041a440301510b510f0340450141c058040c42d540c881d4115200e01c1700720031940b08942141d55960b55070368941c905c41044c1c06841d00003031003d440500c000d880303505007000380d803510440c000e440c510b4111814000d62084414400b4030102c080781130200680f6001400704802a140f10030f949107070103d5112546c091030504009261000d0100384410000c0780107031004200d61040000e00d001503400c0d0700b0f107800b0b124a04450a1030304004840100f0190750080c0c000c59455408580c2541d290541d1800f11000900070440800300c24030000c0d40740d01d031840150001d05100d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 954066834 1250 954065584 954065591
    0x705060109090b0c071a220b06120a0206120903070506041a010e0f01060e041e0608071203050a0e012717030c1f0b0d0503040501080f060924040204140910060c03080406 74
    0x1543c00030007144c681c10103407010b0812008004180c1840c884132b10040000ca40070b01100c101076400034001d0300806016480803e00d290004480c004104106c408113078010044a405191610307049500c6101d81042c0c0d0040080c03000001640c804849000d405002d148005038003d1b0300300902110010403403c68194020f41f02e5000b1152802d00c0f48045101100ca800b01140d12414404940e01e89500c951003103100c8081007100e00082540002500d80340c40d5689841401078000c80012a244d5000030030019034080011a14617001180741d510104032401d846603034020040341052141c0302d0180036500300c00c64104c5101041c445103041400fa000112918000620113600400b10b44002c592083c2200c444e807001900703201d00e68000442542c491202c44170061146006404640b880c0409043d54400008000701e00405140c00300070007a0f203400c054011503c450740d86d00101c0f50703001d10002d0f0030701a4100300085020805c0b80c0d403104080d01d074252100402c2d0b426603601242c0036000200140c0340191b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 954068084 1250 954066834 954066871
    0x1090518091036020306131502030109020304213002070807060b04020403080912011b020706030614060f1b0a061b09080c04020f0705060109090b0c071a 67
    0x1828841d625403800f90104501e142103078821000c019641d501d0b421507411500b0746011005940024a49034051000130080182c24094500700d86114143d07000e880c0d015001000100784203400c0d03030207984140c4c0076844000551f0140c09a41c924030000041210006881c070071000d00c100c02005102e0150303000040720820140f10040d07010b0498000c007004483d0481e0003d01c400a10945020f18080c4060860381140381c5459503652015601c50160a00c0c0101e81d10250350f541081c0a60000c0e0300c00021020004000141080003034880c040c40c010358000c01d1900304045032481440e40301000301c1c4c0c0003502d11450f01d080303655001e6054200d40c2c1d1204815240701042d1801410912910750034510132030300824044c40b6505d4010041c0111003000b001c00c21441c000300940b0000082221404409507401607581d104100c004615224081c0054060700c103101c00012045c490b68041d552460080f05241d016458900d1020f0091080c800090112660558004104501c500700542c102d401d0b000c1c4420340d880c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 954069334 1250 954068084 954068113
    0x531051b12120304140303060f0103110c010f060810060b0307050304240609050c07020a21020a030506010501020d0f050304292509080303041124090f0109051809 71
    0x9403103240301500ea003004804c1c40708204041400c102480d4800000d1030461a1980c04207007100c1071a090107040641320341222620050344812141005040c80003880060054074011024045074802e60b041881422100802c0140070300c2108143c9018180c42455501c501804640d580c00280081d0340ba4010a070407041a4036980750b00800500c1a08404034000c0d180210380350480340d00a201000c150402c12400c00141d0320400418155243c10850444410b0078500840d01c480c695100250444400280402840780024205048032800da08503032084c0b06400084404858a4a005d0042202400400c0009211080c55202000e041031502d4003d0303a030b1440310034a84401d54420f241c2108960404454030304481011124801c94244011107924040025540b444003c102070a51100d603c6004101d640300e8900c40b0903690580c260144c40c0c8240b02d002c04256001c68403241c842c0c200901c03001c3c000d5026140c0003046442c002d0103581c0541c400c0d9501100140700408102e190301480004d44081c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 954070584 1250 954069334 954069343
    0x504030c05040905152409070c0f0503090d05150106021212090114040809010e0303040602100f020403020d03080907050f0904081806030a0605032a01210531051b12 72
    0x50000c81c8822206c9081c2c0b01031089880c2c101300205010b050b1581c100180c107904003444c5190544d0007483d1403030114150400a0450282c5e00850380d200c00c028100340e0912000045030020031028070728030100c60b40e986405a0b039441d9044104c00760000180407600c6130001402d80d45611034481030020420681880500403d0502220200c41204000c02c4100542d64010700082801d60140c1c01545414140b0f0806555100d10b481d51416807a240c00340100e80440580580300115400340c2039a44d55001850084e0030350700102ea43c842c003440b03046000203091500b148150580030300580400d0203525651a0030950b03a014645512522040020f00300365611044004e42c401c1140840004a45007004201030078a00300c011612007a4018808101100800100610b0082d07401d00307051514554282030340c0c1028003460030b01c41c5030a140c401084050781e404614414040b0044901d20301c001d1207413190030001c1e62001000b03403150344902240d0700b4580070303545469402e8200030309100c0024000d0208500c1c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 954071834 1250 954070584 954070591
    0x10031514010f0e07030b0102060a02090307080303010303050a120219500309060f06010c0c0303081b0c07090213170304050f120606150d0f05160504030c0504090515 72
    0x200800d0301040010410043d840c541007880f5181c00c0c01500c80142c0003d40c2c0701c8024112000e8158001201a0142d508001d0325004110310b005903522581c1da8140900940c1109040c0004030b441190007940c9008540300300c07641d81c026100030710605407081c5801c51350441c080342100c000c0f500380c40b511060303040c1d050040d041c1800481500b049190680c00b030a5140130502c1c04418021070148180401983d011038401c1d80501e440303803d00400e81d50b1f180106c500020804016100d41002e282c003005043d80020110f100d546483c50b01c48003549040c01c01c448078421481d07401920f4110520078051441c85400410702e00c01c1501e050b0a0307954540d1001d0b80d084488500e80c0d203817584001003c000c28180341c40145000b40048071180000f615010815807560b0300108070310310030f07064011180c0c680e03400f010950f40c0018040b0005c0140b90a0144044000c00c01501c1c1d5090100100740c0e400c1003039210740b00302c0d02680d0707116036100380e0945041305210107090700d8401140c1c02d00900012080316405851107070310 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 954073084 1250 954071834 954071849
    0x90f0e0f1f0612061d0d0c02090403140a05030a06240f11010f0501080c0114040b03060117090c0112020c10050604060308032406040b04050f01030f15080609061003151401 75
    0x440707a000d040405e015400d100300f4103425800c059160300b05513400005604405405844408c103690752480c046174825405800e02940d040082502011039503c900950b2041020f403e00b04603854403080c00700802410020400781c043d00320580e0031b8580341325140d0041804014100340f148101016445400e4524030000800d80541d90001008503003001c000d4a1030080d000c1c200300600d000c0c420440c8030644100d000708541401c000000c2103c0340d2003000000d8004624207907007101824480c0d001c0f902c41c00c000540e240000c1d40140c007841f41c0d440a1080b0750889102c0c100502c49150200c1c201006460004c2c010381c1e0007030707484a0010100d0b040000441c86520300030030515001140c0c2405010601c024010107002394001e00090040c9270683e001c4500340c80003200c2c0151000040c0b401240648034020044002ca030401d85500f0000260000160a650448066400c01e41d20319520a650392011107030b0710718030b6031031a208201240301d5004048908100780030200d024401840e4409034032400380c0c01401e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 954074334 1250 954073084 954073091
    0x5060a18030507230d0e06030112140a1a01031202011b0c0c0b030403090f060e090a020706241d130305090a0b0c330106080619090f0e0f1f061206 64
    0x100c031701d03901580580c086401100c80301e003594101845158891401200200b41004400100c501c0000c10401d03050f04a6100c44c0308059160104840605c540e230030b1000720b0356010300955419042e4010300845c42d04c1ca20303200c0c545e5624840403001300c9521041c10003e54004005000120f0036003051001948120b02035120264030740d00d04103a44c80b11802c15441501001020700007615243e031122081a0401840300c0c000d03031185558104240217019405070721110b0f1700b029074000b82003440f510110701115030301c2482030300c9034000b4034802803021802c495070302c10109030102c3c10001900400240c050b2280c0078000c403488580301d0801d1211607100f0b81540700300c2d600000b201d207030640300304030603080807900801243c5c81d20400481c0c60b41c1061040c0911410702c038500000a28070345900040e942e000220000b9030900c00d41d100607010041c420110a019940e0030a5401c000400c1e0015013290183c0b0b000740240400040324072304094601e00001c9140c0c1c025224100003c60040d40c1482c28409405140c001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 954075584 1250 954074334 954074353
    0x4170c0901050a030f060209060d020a09081908070611070b04050f1c0e330702120106030b0a050705040f060216150e01050c03070506100305060a1803050723 69
    0xc118690140d01c0a80b00724012034003400000d07003941e0041c00c040d0b48000003680714a11040041e0050103074091044460384003045828415500c103180c41d0450300c0017001e40740a41451039500f401e02706d608501414004040000b032000034807541c00380760341d0110f4201990510a4941c1ea11020240958040c0e54aa000c04094042050148602400c0c06103e8414800003802c075038001c0c1c942c03541114981d104640030703a0100c1503009603031880c41603082844d10b442c841c4061203c4188141c1c00650060380540c13222080300d4000003052140400340c0c0d802c0340714200303a56100180d04010b0900148924108902840009055504082544040c040ca50007901d13840001c1c0710780324024405030340303c4002007140d81c048844458000d0604059090207203407081d541c4409404107480c40c070440f0320003001440340500700a0104401601c101c10360b842a4259a056110341407401c068035903c504078811958440b43c2d0100080c0684010041144518024840c2c0c0005e0741c0c0b00c00030034059810007040360308440c015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 954076834 1250 954075584 954075589
    0x110307091d060702030702100f11060702030a02070f1d1e04080414041b0c0206130e06030f070b0d0902190602010b030d021518030421060b0d021503060604170c 70
    0x1416400300441c402142044a1b40d0001420f0120b10110642842202158060344500c1100703062079908501048a84506061a00030369036030141c3c0a620040c01a80c0c40816410007004141044070600940071007a0249142c4105106501404a12400c0d401c0d02d0013805c069007094509104500420340c4d180c650b440c00991124071500d2002d507178441c51404a40c5440c0112001c001e800c14002c520b015140f01120784040fa5940c41104501c141684d60324000140c0c400e00ba5107654442c040c194266820a03240e41d9070035a0310f80703030350084441040c0d05102c00c000310500c81d4007040c0ba8600090040c41e0110604034407900c0303130045400c5880182d4541403048001e0a041200d109603e41610041001d031144a261101292020b4907200d081428510401003180b81002a500a410707022039091008849489440c01608580421600507007890701c03642662800710019040c00d600548904000711005000d06160352005043d01d5200308240000f2589071041e982024a079a4280000c003402c003021000c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 954078084 1250 954076834 954076843
    0xf0e210307061b0305010e040b0a020a0216150e120c04020706110a020109030e030705010e0d06020717040e011703030615160809030606040608120a021c02010c0e0418110307091d 78
    0x1c1546c1040b041f80c28000058800ca20311944403028110058807003404038000c0342840c0e000420b0200141c2001400324021455015880000025231260f11180300c0c5503080c0b020600700300344d0003070782c40d00144a000100c1c10b0540040495a1242100080d0240110f460003c04c2c7c102c5580403006079075411013a07040541140e00400400c500320002c0c192146403000003804012040080e50040000507000d0303081100d075405894045502078095420025074501c1c2507660380091051210908500c0c1c00003a000310034011161400782408080c43c5142e581500f88401401400a900010601000b00814010900b201007440e0b9210380055030340c400300c80040500d0941c000e0b10315482030349040b5040042500008100d02082d03c160030b626260503119005074144000380310303002070101403800491203241d8103510802094403552200100420800280402c84a1080f0b035076260320015412070700800c02d40c1d2038913120010b0043c12540425200d1800350240c40310740641522800301c035010341100410910 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 954079334 1250 954078084 954078089
    0x537050309040c1d0f04020c01090308041e0b060f01200307170901080f0a0204120809041b050405130b0409050a031b0201081b0c06090d0f0e210307061b030501 70
    0x1070440c10700506130400c820785542072060940304415108200d540d81c0c5554040c1c80b07160700220020040180389060141103041d00300d4086607a0280040a0280000b02c0c0101541d115005007840040d9074546042c400c0f01510458140c2c180452841300002186040340841420b1141e00c01644d03c0307100c9483c002001d00305540c1300c2000050280071451069a00483c2668441d1009104401507100c90464900a2140d500300700300c060030400c01d103010b01c44141c00501940e4030595080100f8220100104059143e07181844002030382000100b0503860081e032076950500106500148114800c0002000c580e0340e080e04503401c0d0010310698007415040b1b18844a5a48030b0b8007281403840300d641c0004c100c41c0009024089960440a1400301d0414650541d461003500310111042402c0ca80031659851090088500008110110049069125404104200344060140c2503136200055448841d420300c2020484148800e10070713800817588a02880c080c1110f040100c912040d44100020309540f0140c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 954080584 1250 954079334 954079337
    0x3290412092306090a08011104060e0609030c28030b07141c0207060b060d050907050612061c020d0b0405010f020301060c03030c020c130b030f01090537050309040c 72
    0x1100100c0040c40c044268844007282101c110b07545070300e40c00002d00c01003021b0700500d15640c43c2c1001d052100002c50b0050080d1070140c0c44822540c95802d003000010300c00c603a606501a0001c41115000e1b0514490440c40342c80c0308200760200a4078024202084040c661003661030740340d0502845039041e04501440003640c1d4052007070346850348904042c500c00100c00304c140c400d594000368240601009501c102c0d107140300142000e0f0340e0b00080c007020707014100950714580380b4040e0b500300113544d1405404440c1ca211380c040412249507200c50401c68401a00480c100c084410842d001005035621080c03441003034800d680c07261039800c0504100d0700b11161010807400c800d02c1080144030380d80c0c1002008519a51624001c181c100003030100b2400c00700c1c4007200c1034010401c00d8000b1403019150700405607410b426021150482a0840e003d030a03682c007900050601d401c821a07144c44040302c01000085041c07810020b07400c4401c494072a0080351484d44041d60a5000031992100318946070064841b03c945a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 954081834 1250 954080584 954080609
    0x2090d0605150901031a190608030a030b041e0e070314161a030c0a020c0307060309152a03090f060506041d060a0b0a03020a0b0a0801060503010e010329041209 70
    0x41d55035864001b00c500c2201e040e641c01e0300c00012002400c501103802e000922510a0003c00d0340e540b1469036a8001c40913040c007190610a6044d0071b800c00d40f107500783d00b00074098401103984030390f5520b80051141c0400b981e2640114000400401d100300c002040700d210280043c034503a06124100d4280352100c0e00904100d05808013550f607204215000d0f46d400a880d0510300c0c0e0b5411501a050b17280011402c9199094002d2400016a26030580d002c1802107000d507581c2c400c1d0200c9110300c0011a0004d8808015420b000660121901a13090f200c6c80d20414900740010500800d44a18501e04032010007102c44540381c000304109400c0500074404c0758940d6803003110104c0c03142200c0ca03455820041180100c1950b40d102a9505c1e40c40d14020300007140c0141c00f1111083e114081c5507103c0d88442c40c10000b0500b10320000802c24840c90841c1d04039014110107008690a654506000c4d0305600c14002d90300640144258208400396403842c01203115600b40014800c0740380c000340401c1710720741c00380103201c02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 954083084 1250 954081834 954081839
    0x301080303070e040f0e0601091a13180c0e160c1505090a0215040f05010c050c060f09041d060a091a1308040b12010504091509030302090d0605150901 66
    0x10010960740c104059007032800c800030f0500e000c6001040400703101051a0308041d5483c11040340424100c1c142c0d0031000040c85244070a4a00707610644020b144180c01c1007003c10790b155203200c01d61040041c00310400780481510a25190341d564404241c22645144140806029042c0e050509210f24203009050001242c044d0f901c03504141c0610030138424285449000045507020b052200c04905580200200288072040030040407070380150058805c98290104c02050944c01220780002d02d55004004159006182c0180540e580004100311010b80041c02014066510780c01041d050429500307d82082103000303202c151802d480604140ea0007803900d4168404640c080e0100d071588414410703a00b00c9515a0001e0408000c0559400b50030307024045000b041c0e410700000203110400081e480000d840e43c030356040004581c0d090000070404030800718040591368258200021080c000e040041c01c00710410040345026103243c030111000d542d1001000303115010303440014a409815541144950f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 954084334 1250 954083084 954083099
    0x11010b0a151413030b042006031305070902220506131e08010516030e0c090406050601141306090f0e0402010c08160609050d02010c121e061215020301 66
    0x401c6030756400c00c1180c0c07404009003005103941101c01c55000c03400181c00031550b0f0705020040c840250703401c48a400b1002c00394000c1400c00c0c1c50016030400000c200070300e103403901c0c070700042444e00b48801141c250280e4500003403085400e00c098500340000340e5042c400e41100c82591455131080360403542c807485c1e09001d000340803009020044203482c0301c0c070103012800c2d40101d03810411290582c00300540d582003a0800c100140450090000b414a94405001921400011036183c414042d103c82c1c10241c0c440014012545d103403c0319801802c18140241e00000803100960294001000310b0407601400104018169010750083d00a00602d040170410381d061454482c0003405c040e1020303040000c0c1070025401d002024003142d54143c005021a8031080982c0fa01c070b0041c150400e0207542501620b130b050800030340180260f0302c03841c8195998542c450708010114000701015142c00d41031119050b01c20030070030307120300c1548041c04100030b40e6004000149000c0c1d83c0c0b0300044089002043c010b02c010031400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 954085584 1250 954084334 954084359
    0x10e1906140f010c060204060c0203070801051e07030b1504150c0f03030203270105010e060f030a03140904150f060507031706010e04020a090501030b03070e04290711010b0a 76
    0xc81211116115150b0500403540080c900c1c4001d04140d20000e0b0004605800490038031055100703405a8841940c0c90100e10700300c51084881c52001c07000110f01f0000b040842e01c0742580510a8100012181d40300004684602c1d00e00d090b1007900f950008003400101c03004e010108000f002494008a001669600d004120590b01d170010289500400450f10b00c0c001c1d0710700100180300c080f0940720303da0b0013503810a000c0c100070b00c40ea5241025080c0498164181a540201d0394000030f00200241e0035075684c202c0707640190041d5028910303000d024040c02d40e0344030b0041e400d59021100c01507900d0360524250307404400b02d60f402041841400c100303600010b030f0040c16040c40c480c00c40c0814865039558000503110040a1401503910070320000d22143d0311a004070a42c1e040da0740a03601040800003500074160350314030b14001c0c0103601d265180018001502c110340300c0d00c02c1d84014008408205840480044044161504404a40c44000000d840340c424070501c040758a0803070341e0040c40703031504c1e04d0080b40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 954086834 1250 954085584 954085619
    0x121109040905030412060c172404020f0c0c090606070209040809060d020712021501140906030a021c0b0718060507030309080301080102120a0e0606090a14010e1906 72
    0x140340c4075903111090042c10f2050703e0044c80b904480d18842e0820f0701c1c0c445c00401c0a0a520b2003c00c040d040c41218008640c19004c0c0300f041900380601c0501420b43d1180d018840ca580c5c0d01d44c1c400d408008400d030040c0304001800e04542c0c00c0300181681d054a008100b1801001804280a1542842100e01590380d12807129013041d007141c480d945d1b03456580c1c0400c040b840340080e030ba075441d0300004221081001d83c3d10902d605a1490b8280d42500c81c8003204409034070390030f1007030642c0c24205454500b02d5290408146400c001c0007000c5400400d8a640828640d00403038100700181c0c4103045c200c3e024080c48070362056200d21249010000c3c13402c0e070101e141c03110380310f03000d4081044004580801014040c3e489184140d070000d01e00390326076a403507035082e0203548101c9205103a150048085980701190307000d0403408505038009012a651043c1c244030395203200800400410b501d030700da550100305940c888079001c1d210610090031a40782c043e0384440209142c1044100080c90064104440c0b141d220400341c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 954088084 1250 954086834 954086839
    0xd390509040b041e020a230103061a090d0b1006140c0303041e0203070b0a110c0303041e090906020301061103030708060f01120518011404081c060b0705010c121109 72
    0x30f00d100c40700b00300d5103c041400020741001340e002e000300d1f000b44140501c0c2101c08400b003005803019024001142511054402c00d440e0850b404407a0030a00200809003484030350240800c4075144458641c2c8084131415a400c01a41c081c424003440850752241c02c4000c82c076402403402d440c10342403c800980d60304c001880035255030560180b00792100c0d0304081501d2000d0300182154840c2c2e45514104c2c40c1c585c080600140030034580309004905003000308442c8607249006020718206442c0554901204018010183d8440140e450125103000c8910500541d1401a04010784030742c10054080c1841e050305440c0400c5038811300c104204a42e00158aa90007207095984c1e0f80c0b883c15440040c0c1d650000c02801d0106241000204501c01034004500510382c0b09045c002e0100794110382d4046840401954050f0110004000b2501d042c914034209600340c4000c180005010b80c1d943c2c1d078245035a0003000c412580759445240400c01942e0003800032102190702c40302080307013880644a41c3e4452181644250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 954089334 1250 954088084 954088103
    0x1a0f0c030112031103030a054204021303030201090201020c04050103081603110a0b1f031203092d03140309100e0c030d020d0801060306140d390509040b04 68
    0x40500c540030004c80c28801c0d03401c4030340303038142846018080c1004032841c50039a401d5108490242000b000c281e450401c15442c030849515203280740214030900a042c080e00590200160703c00454560441001035000390300029940003544002802c103845040b9051241d0b08040046c030114500c0c20440300c801e004d815101e050450345180c161001c3c0e901400c0d0082ca40598a400001d10004803013280c07003a1030b0320608804007901502980001344807400058050517200100040032802603101005190141da0916003001444182d0410f00405d4072000301204180b0940004058012403441a0903011400103130a5107030165826680ea4802915140550340710704040f1034404041c402e030740020a000c1c040d01c102002c02c8030702070359801c4881035480005018400014803244284560070560344603422800814041e2400c01207001600202507a00b140d05112500c200d01d1034a0a21010841e0702c040d05100700001d0219030b00108480d0320442c0100d080908010004180d013003560b80c4154004220f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 954090584 1250 954089334 954089369
    0x20306010c060e011e05100e0c0d1b021915090f08121b1615021b0f0f01060302100305090a05010e01090b06040902010f031e0501031a0f0c0301 63
    0x40314011807418020b00344520b0b2909482c0c0000040d0840e5074442c40d21154000c029680303402c1c50b0102c41c0c1c215510700600b10091700a0041d2004030145076084501c41b40d00ca4244020300c04480c041319180040e40041c00340c003034008000326805000300c150a06001940c00b122070039644030080849a229404002c0680e03401c042c504014005000d68040c0c2d800c240d1050b2940c510b0800b860742c5507010765404011310750070b110108841c4d1401080320b074002d0f0903160001d401001603440100044a4002d604401502401100c0f4030000346502c4000000d4803d001701500e100c40c1307a50360f042c0300c0001c0c542c201c664100391050000d40c0300d0b01500c48607c0450310f00000c0d185d55190301d10703040400701d450050065003030100100e160601500a1004039014010700703040c3c1d0711120b04020413680c200d00000d01080b2440e105440c030ba400303544069400c4002075401c07a0700b0780030761b00c0b040200c51003604103d85203022480c0b410000c13041d004001e50312410f11074507250786080c81d1181c0c2542e80014440c40303504641e01d85a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 954091834 1250 954090584 954090587
    0x9060510121d01110d060509090304030609020d02040e0705010e04020f041a12040b04170a08060405071e0804061508120a0215011d0c190e040e0d0206040302010b0a150302030601 78
    0x21442c0201d656000704060004841d460419034408002c85400f6400c12801088528000d11076a00074602413004500e0b2038510754601c0c001d0140480141d034004039000b42174000d40c84074025100002c80b1000640302c1903041c4000540401300e0005002c2c051403050082d0500004c6c20400ca4082d41c181c500302e102c08409110040101c1c1c46000c41303031891003c98a040c0810001c0d0420706d58005e0b4400d02c2d13040d90398204500389803240d004031200d280c0010b200d500418803d0400768000c80e0080385500c5c025103002c90032180000e0000d0280302c4400003829a20400042c05940e00c02e24101402c40c071400c0c8041450301e04256a00e903541c2400f10100300303000541200b03103030003008904c10022000c280340b442c641c4c2d03e100349545081e006282d84150522500002c200e070b62003030203c640c4914001e040c003411211b00342049826000800341160415070f2240d1900d800326082246143c0c0b440c2c1a8002d16a610741440c0007425100350f0700041d0f02a41c400b600c1440121104200c52030302001e285001038885e03980742d00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 954093084 1250 954091834 954091871
    0x1715041d07050f1c260a0e090709050402160605090703030c0b1008011811010e01141309020c0a1a060105030c1c1e1104050d06110c0d08010906051012 66
    0x3d42c20310840032800004100404074994a4982a00d412241c0c0403074810310700300704248a05d5160f40c0020303001030440d41c80c07841c0c88d40740183c10910074500710031125199004074080740d00040000240d1852100500100603080c00348590084001c405007a12514507034002e01601c10848000700186895400201c4111100040c2401406110000d1120300355002d0090307031910202500ba5a4010300d190140c5055019078107000c0d0102c410307541e0f00b102842c550031500340c9400101880400141c2240700003409140c90000d014441c8045025203e2407105242100228101d0300c141840c201603030341003000c2c5a80007000c2d02e03030104800c1040d80d030700c07a9044081c500c09688507101ca80d07171500d405201100010ba803905103a82808000d820407804c4040c20032020742d4080c81c810306611103003800c04000084c005411400d1140702050103a42071140b403001582c106200420250002118200100001d07041ca016500c004c10055030803000b03061100710002c000301d503c0c6a07001c085035103c03244010100d08206 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 954094334 1250 954093084 954093109
    0x702100318050709140619051e0604081005160c02041812020c1005040b03060d0f080409020705101806150b07061b08010b0a0e011715041d07050f 64
    0x800f6203868640316030390342004040081880014440034000103061f0f0070b0603000d0b5103159000704020101686450100050f800e40c000403420188120307001403400e61145070150026080d0310700034228854010081c9000c444008103201c190020311004011481c1e04030700013403940ba40545001c101042c40794080c000144600f070f8020308400302140105810ba5011402450401c411515075820b2070308071908a030301c2d02031303409584180b00041000c100d20340341c1b81c0040c050340d911514509450070f2403038407248100e81080c0d0000440036000600d420800c51f0a100412190480305820000c0c0c940d034003541842d0100b206e03002002c09550f5411441d000785003002e01c070010031100c0005a40c03071600345090809060510311051801101c18128102c8900034945181070766001200642404000c00c01204d00700c8040401c5c1d8144203100d0380c0174400c10688410107104104000d8090303441d02c12001448111038400d040448407c80c5140410704132440407503004125101141d0060182d00301c08009185c454084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 954095584 1250 954094334 954094343
    0x7020d1b030905180a0b062703100513050c03030f120421020c0102011401060c08030a110301170f0a150b0f03060403030902090f0105060d1113080f0d050702100318 72
    0x34104d0070034400703807515018410b0722428814020b400d100c40500c00b00740141d00201d56140c03280382000100c4443d81c4a0b0b0341d4002002401c994200b108950040e084400075601d042520038008803140c1403100401c424801507606030006d5140062240307403800507004039618400d460604902140510000203509024041c00f41c609000520700705501a6640c0c00040807079000d0b50920760515252002e4000d984d040310b120f5120202070b64525038030b11103203500c02030040344c1450b45c17455855000030480c0c003e10b02900180b504840341010b0541c4407844c010081d40c110744150b0001400d04001420240c0c4002095281e04c004541074041b04001091310b2080100310342c05204510421041c140d05402c0904410300a940c41f550b00d880c0e8841a0720040d009000e0507400000422401890b98001d0340703c014003d40c3c800c429400c0c0410b0b0000d0310078003002507008210a912200342020042c40c14440c000d80c4e000c6904046181520590100b440d1340140305442060646c0c0d655041a07844001078a2202c240c2d21 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 954096834 1250 954095584 954095599
    0x203090315150f06030a020c0703140c120f0c01050d0915050412090311060d0905160602010606020307150504031436031902010203041a03010e07020d1b030905 70
    0x24446207280011201c0d1408095401500403250400607915060104041d04191842d0307207040b80d03480a540100c80024441c41a1750000012400010394800408448d2010b00450445034007048050b5040c50ba44189a40200c644070502c4a0009404407006000b800c1c0551659600703c00c10004180020000c1c0620020404d02780c4c0c50203ea50146220341d2003030108003e0060001000c4030001d03680d02000302420b00c1c0004100c01440c0203405880a5980d600020910040d50368901b4102050101c21510260381706005000180e02802850058902e0744000c40c00c0005c50b407968001c103407145885c4d401065541011900303041c0306002c1e04909500d00c100d070175a60303400100901e40b0071030302c41189841c010000310804910b03441d0714030703425a180d402001020090442601c5084101c41018200d040d444204000100054280b206949021910059603200d61400d171072031800000044c641c40440d0070030001c002000b50801da4000c001000c80c117034820010124541610b11041c81d40140d98402e80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 954098084 1250 954096834 954096853
    0x308181b04060b121b07080a0503040b010e10030b041401020f04030c05090408030a0b0a0e090a0506060306010b03010b0d020409020d0906150302060414031005070e091311010c0302030903 82
    0x30000c080c1520300d0000e680800941d5954100310181d4000d100c118051100900049a40c030100031000c01d031011128081c152906080d07907222101684045031344004a4404401c00003403110950015004014071070210145141500c0d65584075034043c00300504030040307440800d0a12121b0601d5030401403903000210740e16608802c5103480382d0800d100071a06e22050b4100070a0718240950b04034040c0303a10040380e90440d141d03100c0c0d54003d0403403030000b15040000803100040000014682c14001d80d124009807040c1c612500b45107041c01030049c03029000f50700070310041081050b0070003120f0441c0c1081030415190020308003140048d120ba5403050840170b0002c02c200740c3c0a17a4070707171210850902c1202c04001083c0041d6100d00140f50500c0007070350040b420b01040100e980c81c40d8861050b9500241514190009002004103c490a490b079074000341c020b40c02d44c0c0990914580340c0da0891103441c1c0d101c220358880c3ea100d81ca0040160003180c1004036031200d100802d4000c00c19607903c0c150050948003001e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 954099334 1250 954098084 954098113
    0x15041d2a0405130212010c09090f020d0c11100216020409290f28020d02040f0305010e0106062a080c0d020d0906030c08061e0913020108060a080a030818 67
    0x416a000a174842c808204243c031300c4110510445084415030b40310540c000d0b2034412060000c00e0540b03400c00081d5001c101310103809070b0b5403107084800040d07a219221803c82d403100356840c0950031200304207002d104100840e24604840c0fa10349086504a07008103000e0f0161420404400c0410ba0103020100100d04204015901c081924458602020b04140c0c0e65075019403400d03626a080c28213400046441c00580c4101c00d150020842c21007200009442d1503598035800c080e038842c90b4001e643c079075510b10402c5580002809000024801442c1011440f07140c0b404110a031030782300c14000201c1c074007040e040040000b80400e650398801c10006640700c032492540d01944854501760b44a00068000034007043c058040d1107500d184036559968100f06684d4a010b104581d00c0201d0031841c2c4c1480c0c668801010350786c030004135200d407140300e407100318080c4170384005498850050a001d1040c0180003003444051800601e0300c02164042c94070541c141c90b01030302460200d01071900c2d0b844501413481c1ca0869076 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 954100584 1250 954099334 954099361
    0x30d0f021201080c180105060a030c1b0302010b0a1203090b090321030603151027020a05120132150d09050f0a080f0c030c0615041d2a0405 61
    0x2200c0503100140c0144a400213185140717000d001ba1a4002030a000d000b0f4100c0c429405a1600300709410329000c1c0c001000301e40d59480d60804d0088005030744902251a03207052242c070600003001c6006c5411882c5045950250400c410741c02048508180031800949907a8200b00905c0c444450701485000c2030700c800081c41c441d910484829000e031140ca0f9a0100c81a02c000c3c0765445412888194218a810143c101c41080d0b00b205c00b240c04038a1901c9e0100441e2400c1c4024550f405054642a0b03440d0100740280401700016407100c003100170144c1054031006014401c001d032801c43d010040780b040901d040046d08141a0540c01c0c0d01c2800c0c046001c140a0515620001f40f2a006070f0458000a00d070080c030365941c81c0120002003c00c4c200b40a01c01926070301c2c0010f042d24148601c00e4078206118440c045203800d030100c0b0840100075144000701300c80d003098441d0350741c105051000b9074148102080e51a43e0b88548404942c6080e40007002c3c026483c100100c54410f0840041040c04103041100e51560350 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 954101834 1250 954100584 954100603
    0x114090a0627030809061e2a0708100203042301020c0106090225080403060c0201060512011b0810030b04050705010201180f0b0606120f0720030d0f02120108 69
    0x21801c503a0038200964001603000d100f241d5000c1c004501d0241c0e15000d12030780e5002003407002401c0d00302d1401c0640010820703000e09910103160307031800d04100b81c00d60304140c00b0b0f01600d100301454100c2c3d0320500880601050044100e0414100540c0c2d903140da15011050542c40c0070781d680d0031528203603c91034041064000303082030603504d0028096542c40b880c6490480c805c82c584594424901d200b08a8840c0c0708503031a900c0e041c098408030703040540d03940700c0700300740d656041c02a0b006075900c1c20140b00ba45801070f620083c0205203002084074021190380d10400d0100700d50140f041c8104030001a40741c0c2a09100078002e16404070030181c0b28102403410030754030580780c081c050146d402c041c0510010b0b038010b10200c00082e042500911002c440345c607501000384015107450f8120b1800c01c000b10031280c500300c0d561700510704030841801e1440e18800082c14580c06800ba0f403a032034142e01100041240000942c2c4540034000780c001036280721402c502d07000340b190841452894800000004516901080d030554 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 954103084 1250 954101834 954101867
    0x618170a17041101021b0108061005070b0c07030f090602030a1d100305090c1f080a0b2709060127060e011d0c03060d0b06012c150909060114090a06 65
    0x80c40c4200160843d030070001141b20340019581000a480d5140c0200c06d00380550320307418030a20700f400d251602c1628443c02c41d084410030b0300000b181d80c101548221ba5000200d40381c5001802c01e0304242c0c00075101d00c903540c840340401c54020501a40d11002079141c03054100e005282a03015010440050090704c81151442064003900000394641d0038140c080050051b011b00c0303204155103000c1c2c01513600e460007502c80d08840d5030700d540241c13260b1104156000358925058200c0e0b0154085c02c2d07010300610004084138065040040104244105c801260758151610700b40d4101d1400d01c000b18100134219030780140d80e0440c2445c000107006103800c21100e11265078010091440d903801e00d20118610003555a5a0030000c0030141801107100c0313900c8960450014542051310b42d5500a407046c00c039481d650b83c1010034203007100106140c5003554842184a0800201c9400c1004100004801c18001403440d410301170144074500c501c0003924202e590681000b003031100c10355281c81c002000c40160000721407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 954104334 1250 954103084 954103093
    0x1120b0a05060c2808042c100e24040b01020f0d08010e160c020105090f19170705031903021f0209040b0d050705040f0b040f0203040618170a1704110102 67
    0x94803690258070131101d5603040741261345414541014809040c060111104810f004048a00d85c001721065100e406456007840c1d091031142040e104904030240603081c1c04403460170010b8108001000c030100000142c08440002d0350340d40a40050f800d11500c010212050302840d9801122550000ea00c00d0594051090110352a40c940d080d05001043c2c020358003001c2440c40c1240d03001580300f00b0080ca035503c0060050701c1c0f0500003001064002250508070245130180c000c05200002a40303c4510000110000416200c0d1400011075154111003501481c007030b000e08145410b1500270003107015036110055103041d00c540d50502540c0250030004c45140704a0800300000f0191030305155100c0180d411001900e44c82c0e240c503040100400924201003c03064888100c001290703a035124a296401d42c2e094056600d00c0c00e80703041c0045604040e0300d204410300300c0c0d4528021030218201401110640300a803940d07420008400c2d41d0403a4180480601e01c5070203000c000801c0800c8809240210003a0221b4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 954105584 1250 954104334 954104383
    0x130c02010b012102030c091c0b0c040308070f050f0604030810060801230114071505090111030114031606050a0216081b06090301060b03190b01120b0a05060c 69
    0x1140c440105040c2d0f00f514a010030100c071180142e5900654010b1501c40b2840d1405010401141c441c150a048138242014400c09445c140728500c442e032075000e248410311600e05401e6941d074880601403c41c016150403001c3c0c81c80002c1000400c20414056070010444246141c83c1c50b000305000c0c0d00312800c889110040c080040c0d818010351841d03050390480a51440087c032400f0345032440c01d0b543c150043c104848000f11100b0003034264028561180a6404038160001d0310005000355a806821a0403980c5804000f00051101c20140c1c0d0644100b040c49458802040000901e84400d075403208502d48420840002c000313400ca001031030810071030f800340c58803030560500007050b01074644245540c030b0704880c40c402010222401d242d199000024206810400f403000481d00315017458000d1b022546000080c0300961440c26000e20740010311b14402d100a80100c6c000910540c2140c40f10300d0390a480c1c2604d0030881e5104c940e000d0207054007600c00384d141c0c0c5d41c0b482025a202880c018a0302c0b45807444280 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 954106834 1250 954105584 954105587
    0x21e12041101020a0b074d1c0c03030b0415051e010914060c0105130302070803070302100e0c03120a03060504050c03040803040819021507180b0901020a02130c02010b01 74
    0x2c00c161950405601ca0300761b500c11009031010724400ca180e0040c0d490300c100302c001c1d111444140d0400c03018809600310070340d4140308580340c000403648030350422540140c0100955521741c0500220b070016030320704844514183d18066000e8548000b450b50b210741814014400c2c05014a0600e040329803c5131000d040810510080240c0400c81c034030301d400100544414421803122020500d001c3d40003400720340c54004800c0c0c5036402c41d00151103012800201e0200c40d03003816030400c4107a02400081d4091441e203a8a070782e000e95542c00c140c1400c000301341c6807840d8000740001070020840300f10000d0180c500c40d028050351140c0070351015a810020900e40740010621342000e2291a00c10700541402a28686850b04d81c0c40c03164100420842e660102001501052914005411201140d81c3c000303000c0c00355562844005000e00415520410036001d80750380d503008003010810212940c07440700c40c5c1e4034403111004074100b40c1260006034009002d0181d619640d503003a40005a04aa41c0c2d0003004805000c800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 954108084 1250 954106834 954106843
    0x60402090901030605150a1d0c27010c080a03090b1b040e060613080708100c1b1b0b120c0a05071119061205010e06010909021e1204110102 61
    0x24000d80201c0c400d00144000744842d4810b0790014555074074002c424a0310f400040f8540c03400e41100020141c000981c4011050b540c0c1c2e40344d0402c02c09800603080080110000a00c214464407070850041210a440e8140c1d0080c0140308019807c00e013180d42d102c1c00c444000d4080c002540741120b1940807400044c01040b426600d18034542c11408c001d500d02fa02e0081c03040261003001e0480c41e40204104a55190300100f007030341c4170040420001a11555250640c0f040c104100070111414440c01e1160b08015164010048401c00d51944407020382d01425013065844140316190204026810200204008911340094840182204030489140d9150140301e0014010f0010300000f00b14140444d400160102c00c0b0540d440001419083c00100d0a01c440048010158858804121030f98018440c28245000b450b0261403440c084100c0350511a000a00d0041d181c86020605035001c04c0424150300302c0c811807940f40016200b0b40d61142c2200402054820042c0c50803039101c0484280800030394004203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 954109334 1250 954108084 954108097
    0x13051e1f1401023f090918010c031506050c2e0b030118021519030f0c021b12010b0a083003040609050f0109080307090e0c04090b01050d140f060402 65
    0x10140184544d10380c1d180100b81000e0601c0e05000148440712468480c40740c6a4454109940102e109071348040c0b00c103084440c0d00034030004160030901c0703020060391603107203a07404c4400354a011580d41c60b40030030311400e1042450400721420710321801c120021900c0c4060b440d48403103c031001c00c502801103081500702c0b09101c1b40240100d06511070b450140c03900b800360071075114000344031a10701500450641e500d182070750204d8010903514141c42d10001e0592240c8800c003541d42c0014511140303050b401d848075a80383c6030400d100d02400504102500401c0d00a05000000a00400c05540c1c50b003e0550711014400742e8245020301503000301045843c0015031924604000d807545180d600e45407100d40180074040800d850500c40c038254120840c009110f480003850254810b04e40364100400010072441c1e46511030341e46403c80320140701c8100254030480302152007044001401e64001d03001691207004420204185500d016039a5269032400d00781e0f180320704040352418903c0c1c2d4a61003000201d00400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 954110584 1250 954109334 954109393
    0x252013061d0403110d0201050106090b0309340f0510051204030c06022b0f020702061c0e0709140c0301081c02030913060513051e1f140102 61
    0x80d05850800440842100d030018000e113040342c192440c0442861500e0f100300707540c00060b9958801080950b602c101074102a00c0708a81c0d03d441e6041c0500c2c119555410803282d018201c158111601040704100e24802c41f00a03030880015003140e840580e40880d140c0380c403585028588400901000301d1148085507111045c1c9200c0a40380e494948041302c0201f00f5480c1124034036401c03c502036064001a010442100400d091007004000420445041e10005c8040681c07e5006000180040c3c5e161400e594076201c58041e062908807405203004083d0078101050380d11402200d10100700103503a50025041040c00d2000040d0540710548000101e1009114108454001c10681c8484a08010b000070203802c180c81200d040005c003200007041c080e10040c40e80829070303882c1c2c0200601e08050140c4500ca01040004002c28689600003807048035001a48008400c51100042d00c40183d04c21030b81ca003030403405408041192520301c00700780307154415490f82c0980306c1e07800350000300c1d00c0391400c0300014241c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 954111834 1250 954110584 954110609
    0x1006080c0108010806010b0309160e0604110a0c080304020a0504050915100302010c060c03060b04080a1104110909040f06020d0207051b03100c110307060b0a090b0625201306 76
    0x301035581f070f51342d00b014050f040280502c2d44108250540c05500c100544030008020704182040d20802c011201401c0c3d901c0305600c010b22103190b8154011044410142d0410003182d0f03a5983c501c00a800500b20380c1195502c1447c00050020341d0000080c959210840c10081c0390300381e00c401001e0000c0d525640b000030f001512940281d000540c0c1c0d6007100319410500d0074003207685516100c0c400043c1c0c2203904501c2e9268072100c10706080c0010104c200e090004181c80030030840f142d402001c3e101c0c1c424000000e0150101e840894200300e404800f031695250400c008544460301034400c10041d51003448290751030b00c9100000030300100d406007840c014190003030090011142e1514170402805c441d1b0600001e1011410782c40c441c09a092004107240c80c0f1840700010200810020132040c101550801001c4600d803411810960720b079102112080601c0c0c0e204a00da0080c008001300300580b0001004081c042c0782c40791070b040003003c42c1500301c050008403243c0780616050880c40040720114402c1d4241400f9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 954113084 1250 954111834 954111839
    0x60a050a020102090904210305010e0c0912031201090506030303310b0a0c0221070305070611180319032f0d11060109020f0702211006080c010801080601 67
    0x15000500c4141940d00026040500c0400096840c1100320340581d140313552003844a03000e4644184007686240107003410011035040c61020b4a10b01c0008114240ba04000070300329006544003050300001074001d00859968034000c03061580da07101e0a12410030041d042c00301048040c41d010055a110303501000402d8001210b80c08141144641404202c10040c2d2080310070700400e500313104251050304901c0c00801e0440300c100e4005d24040035000c80003003400d40c004046000c1030452040b11420760305841d0031604d03281e0a0038880e005080d0360b40000e2200c0c000041d94105001e08286065030440300f00c09881d0f241c9135110032440207041d039410090004d1508480306050b80642100451182001c006040c581400411100d14080f6564080300110754181c5550315a150100304550140c500d042c1e042d400d00c901101c02c86240c0c050341000a12038016800203500410b00101c04810150310b0341d0803113610907a46000c0c0001440d660142140d03500518082d00c034554042d140c25412212000c009140c01d03172 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 954114334 1250 954113084 954113087
    0x102070b0f03040b18070902070506101d04080f03011203030c03021e0c03040e040b01140109230301090602040f05010305180303040f030309060606080106080601030525020c06030406060320060a 85
    0x100900749450350004201819420170200a480b01400380c41d40010703501e169608200b4642070b4000c0c20f0a5180282c0c40342440b4410b10200b00016841c82c05101c4003898403075140c40b0300140210415450044400710001031812400101c0048103802a1001c04c849000008210142d1103548488034800030300007001c10300701e00c8080c0203010b0929440f098a05060700c400848802003c1941c0c01d030b900e21008030050007006807070300d11018100801d0808100c058904180e13806000d50340400b10b90221500215242e07661029086074665035030004003159125143c00215135042c0c224050280040e00d801c001a4034050348000a200303c141c2c1341d005504599a0750f0b030b501c00c0c0c4503814604400305616520403a00080007400383e04050075098035103000b10345c18403074010040100241018105400c00050141101030081050105074421401c4a8011810582a40303402e0070030b120503803c103c0c000700f00000d110080d80000c2c1903921400040110907680e000420908405960840d40304d9001c100104400707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 954115584 1250 954114334 954114353
    0x3011112090d1b0f0507030308090f0601150f020c0a0902030108010b03061308030c071a010302040f090213050c07050f010b010e0a0803040509040f0b0f0a240e27010b0102070b0f0304 80
    0x86104840304c42c2d034a8426951142041880d9100314042070012082c000155000c1c81300050028110008044c590316111001102048011020042c0802c00750040e12240c030030b00c4080c0c0302150140400340340d141c1c2c8020700d03402907000b407080102651900702d003040380345000b04602c3c0c0240942208001c018003603440364803a584c000342400341441c8040107201c2c005a1405030140201402503140c0c03065601d580144810344110101c14034000f0301d408a03407001070703468180c04180324a0051001a856495452100e41d501c02d609020f0041d2140030b42824034130f601508181502d00c0c0aa940c4c664151040c4240700d07800d00c46004000842d00305000a00c0141400100707194842e0141d0403506c00e076142616507040484041d295644200440030400080404c0c501414003a40602a0511800c08080080f114910b910740101d0920a0700600482c20240d6404640c16a07a0504206c01010700c681c0d1003468000c081051800d4050301800074002808286942615402c0d05024019403030342e1758503618030044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 954116834 1250 954115584 954115637
    0x70f05041e080d0512070c150906060b07060e07050901050102031c0603080c0a120815090a020705161d01030312050a2a08010807050f1c0203011112090d 67
    0x71a148070740000385540204a601e02c01200b58444640c2c82c9040800300c1040e000c024100030034080501c480074001086800c0000c17001c5074401d000200440c1c03502c0c3c1000a80503e621440042c1004140c0b441401510391001c2c00402d203846c22a0740d01c0c5d984006110800c01c00b40718071400b41e003050102084908141c014400d455900040000b00b040e1030703035200d240980241074181e04a80c4803a461b00100814040400308003001c9003815022403a2040d6240c55070031315108405d00610246020030080b041da0340545002940c04421766066400b00c0000c0c0051000500c50007010022514245200003d103a000314140ca41551b18581009403080c0c0c007101510000d044194695950130507010781400d054102d841c4590952308242d19041040f00080c211513042c0c10022050b0408407040040ba62040701d2000482070548159000b404c3d0a00c02c100a411070400294145d402d0002004510600000408190304448000000e40d11000e1800e0b0f40c5c2d03285220040c000c201c108921903010001100d46015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 954118084 1250 954116834 954116879
    0x50903120a0e0a2126040b0a122c010b130b151c0b010e0a0618140609040c0c0c031a0c070b040b0c071e210c0611040510020a0605070f0504 61
    0x21700034800d0b0000e6081d0343c0540c0c402d000d1104042405001590b004a100c01c6248003800107100181290b403040e614580344403500614512950741c0916107101c21b41041e400c1c0e5100a24010505811003003c00240c1001c0601c0340c071460b0820003001103032407541309071485506044a034181078401c3c900594002c00d07944041e281030141d6240c11404c45c1d614165040b01603c0e659980308011007140c07203908014519034008403004003400010000d980c895006458502000300c078082290214603070161604030308502e014244081003c808028070a000d03c0940c082c07291318604241782d0b03481340c1f1100c3c0d09028450700103041001500205000c030f0403200e103254008005409044c5420466a41c00440d540680100c040c00310040e11880180030001c05941400101002ca42e2034800c1040001408030218000041c81207554200c18001e48801d9070960740582800b500344804d08006620103951105850800c84000382440f000a050f14481d00402007010600c0e00ca044c20507050406021030044a400c0303405 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 954119334 1250 954118084 954118133
    0x30601180c0519020109021f080a0f1503050706090b180d14011406100908190501060302041a040b03011131030f030906020d0f050903120a0e0a21 64
    0xf016040707120707880d4444a6800000d401541e43c0b0620030300d02041d9001e203503001000703200116200d4100076102e5104080f4000041d0019070300070301c103006020300c02c0440e181d020540c80110411800145403000c1d81e030346440743d03407847d40e9070b0b004005103100e40400c44a04403210f42942c0e0f031900342280d800100d140310b03c0510022002d0a00960700b1a00c066a01c09850310220042c050b00f400c01d080c05412030b0403203142141c0c001e414100c1444e0b40c3c0b030403040c08441c0c140a0105078001e01000b07500001c090743d4020004e00c1842d1105444081030726000311032900c07482c68824009d80610703051051403e41c1550309485410068008000f00c090b404145c0b1704074101049a0000604511080032000a14826180c00c640c9a0b80390400400c02161a0090400d540c080304801044542000e0b600032241881d19000307561301d031036801080c02c0c00305905030300b030a0f10f5021658150840e08011070540c60941a2040c0941c1a920300d00000f14880a42031018400000d400e0800410310080381ca0400c1c0c601c17103180b034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 954120584 1250 954119334 954119347
    0xc0409020711090a091a090622050109060f0b0117011206020f040605040602100b0916051c1a220e07030503040905071116150e04110c0606030601180c05 67
    0x74064041150040600d03582c8000f5001000864400041007083c01105000d05140051f0703031603507501d00600344495100400120300624001c07049400005039001009005142c100c0c5004400351030300100003402c2904081c540281c55100791034070142a4003103808550075910300101c3c2c0300c509050300e00c2680c0321902002102d140c810588010030040c00c4980c0c4a0707032b440d0718000009040984802d4200c001c681001d007850303500d41c0e604040340c0e00103014100d4004024002103040e2036601c186070b03641c0f0031441e00b00400310042c00a03030311000c50303d0020510000c3c001d480c081000030500d400e0f2640080241c0c940d8586c07030301e4042030f80a40c40d061114012208115101d464491031504594080d030501030300c640030020b00316444800d80211a080e03000800c410039185000d0171034142940141c1b40c05240c0300c5818014144501c91603141004094020004881e2000102c8104d5021800f0800c07a0f100300c001003143c5007400190780e41211501222000c1a0500c000d031a40508064500241004000d0014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 954121834 1250 954120584 954120589
    0x307020118080706150f0311040b09100e090a05031206040b090408030618010803090f0f100503040c14030709110d0c120509011a0d1a0915010e0c0409020711 69
    0x7015400c81c05403035000e440304014907000d82518140d1500b5900040a001d080041800f031a41d0502070342e44c0321884146003890301010400800e2038142c6560320014801c180030300b50744054100790585826500d06211981e4800809641d10307400000104154010011401c480020040701c0380c00080043c4013103030403149413001484110303040c1c1e02512105400018030489240003d0000000341603100b110083e5890309014544a02411103814014003000c1c284140a9864003031210842c13000801802d20f0030b4001e407000300309810845d0222066801908040b854081ca45150074008034001e0040c8100d40c2440c1902014010303a43c0a41c00740c3d0002c2c401920046403600415009041c291740d8071140d414902c03641800d5032006801e0041c0c0c0d914040b03415074001c0d03040440c400030350303810b5030002c0b507840d0325240844241e5038585d00c0040c000007810600914071004034070b00019440b01030340060b490b62185144080f0103000c0d1001d2900300000c000401c814081038000d003c1a0380034000c8006201c2c0040003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 954123084 1250 954121834 954121871
    0x140903061f060e0d060c12061d09071512060305120a17070806060906090a12050609070f030204050a0f1a030106080c09011a0f22080a020904060203070201 68
    0xd070711048031400c01d00307084480c5a45000304002c00c064542070304a80851804a4101c4114080c09004542c4520304161001d02848a19069501e803402c100b200c10b554155010b04180c2e134540c0c9040d28940e0b01c001c140e01e640001010b400340c404840800440407a080400e1b178080c0c0203441414007694494000101180003440020b0b008140644c036107550701c00d04030000f03103001d02501100842c0e4507500188040c460740000c1075540300d5019100e881d659046180080e00c1e500940491981c0702c48005804100015121107282c400e920460850f60507840c0c02c019a41c503880203000b00d50814032508410030161400c1d4005a401c10031610001032000b40000012040e03400a44401c4c91140103618000c3c1c090500f44034000090103e48082c3c0303007030b41e1002c0001c0e10002c010b00c80d80b01103031007030715a0301d200c9800c1d6002c6501c42e14000101236030703d0119062100a80314100140e0309180c60307603c4001801c400108078030250030380c0200451001d5070346540d003900a41000d0100c1045650310b1240c0c2d0180196144c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 954124334 1250 954123084 954123091
    0xd0312090516050103020703090902090103020f03010f0306050f0f2220011808060402040b0319030e040c050c15150d0b150f012c0d06020a02060c130614090306 70
    0x8042c0200140d80c0282e140b02060a51101e41050305c1045031401080d40024000141d81201d0360160303a4004001c0120041d0041e121b5003480800c00100000340d000151300107600b10b0b0310402c42880f8590340c2d61448201407900310f40742690800030900190284030752030302800058003101284511103c4035120030480060010070030003110114015500f20790380007840c81c002001d420f4400d03800c6608008109446402c0034000a0040303403200d111041d40c1e40c082c410180c0c03004081248440320f9007a0305000300f0021000d40903500035403804424181d4180314204a031000c0a01c14020155280d6100d810f19a10320018441001050501c0119805903210a41c10003c503019649440c164203007000d2140007030f03c001240074400c2000c01e4001101e0798008400c801480303120040700700ea000001d141c2d4460400780805560303000301c001548030100600359024101d5500b0560840307d07140d60f950f04102d0584101c01180c000c00e0a00e890800940d0b10640081e842c0761a0842000c2c244400040824035041068 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 954125584 1250 954124334 954124343
    0x80f0a15021207020a0b060a0503120c030f0f1c1401030f050a020303040602010f14071709121b15010605040504021312060204290301062012030106200c0d031209 71
    0x117001c401400610412160449401c0360400c01c3c075403804000039035038100e007e4240014080468005505034080c0161a018041c0000381540c0b6104040e861403654801501100740f15080c440c08540f80361584600c0551011101c0d201240707074215112215554201c0101b15640d208088030200180c800b8000340c80240102d80021603040002801507040c1d40300b280c42058201080707010000030350751258140142c03411000c40e132072541d1161440d0504007191000e420149003c0002c08000c560602c4803180c541d049460f040d03480c0140c204100205011080c0701b480c000600c28403091103c0d140550042182e150440c0b40321040c242d450341a4150412002015600560b01190800c40c00c0c000c000d5a080054083c015400f1092820000200c00e010602440c0301f0070410500111349411502900128582042c0c00c0350701e011030b03510200082da03100340582d40000750404031620046811f6521400c03421100350140009481c03840a0041c2c0f0402032900340e00308041c040301c40403681d4841c071424081c030303029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 954126834 1250 954125584 954125593
    0x224070c082b0605041e0207031209030203030f280e030702090103140f0a0b040b130206160312020708191b0818010507030503060d050304150801050307080f0a1502120702 75
    0x40b50703401c000c40c1c1d290b0384032a000d00e08115150f1030000c0c2841400c0e00298a07094016110205400c0444400d01482c20081c1c6191422000310180f5070000047e600c85d40800f01024855900c016841c04c8150189a802d0b258200722003422610441755008030180d0044c1c201164100045500010201d103000c1e03100b560006180b41001444400600c071a50000410305e0081c07170b200c4001e6460400c65000208040c21041d2200e001c1141c007030001d071315841e0468004048503240d080450412445460b04e100440c00314013020200c1c4084102030003075442d031a40000c03566080c0200010100c980e051460600c008000c882c90500d4064607032030103c010140d002c3c15480781c54450601c840c080c201d03010201d05060000520098001030350100450303610010075100c00c00d40d0b017034a240035450344c0169008000d00c3d21107451006811580000e1040c100d50040341241c6105a0747c3c1602c585420411100c0c8105401600521002c901082041110b981034035100518010a114a080141406035440301c0144c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 954128084 1250 954126834 954126907
    0x19061701110a2705041118010914010311090603190605370e0702160b03100303051b0a060f0c2d030b030703030206070224070c08 57
    0x34421205000c41160030709140840c0070307901400300440d80500420b040c0e202c00480c100780030000645401020040d00038440f00743c01900d01c03401d58000c20b800c011001048009810158410202103040310007219941038410340d000d004402601d41c01c2c018544210003040500e916488240056100360250928058841c0da94003040c820ba07040742d17001d20710440d00010001d50110301c24150090010107440015032f4800c20011150140506a00c00556500400304110392142c003c40d000000c85c004071481269642c403400d05001a0000340ca00540d0003207904801c1c0300280c01140100284c003241c400319010800f0314071045140c491ba03a0002c070f401ca612400c910b01d80203290301800160112600b4007200340c110b944211b5022002542d600744a903440120032500302402640082c0c000000581070719821902c0b030401a43d03c8000351031840040c41013030300300b91000071545440d010520701c445000c103c81e203901c102121049070708007080e01c0c03042080005052008114100c42140b1001440c00c003521203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 954129334 1250 954128084 954128129
    0x30c031403040b041424180d1a071b2607030f0302030601090506280c0b060f011101051906050114040905100302060d0e1605090f1906 59
    0xc5412004464a034400d1005002011115003541c00741e40184010541c04603d4078005041900003800c2c0c0034501029880301410460b42c0e800406c0d101034400c03176508882e03064100f03000d014100e107440600090b40c0f8460040310500707410301142d00300c0464580300308000c11034403202d80016044130040380c505038040012404000002801c0b580c0203044201107082100989010303000303c0f101780b400020941d0010003e20380341e019001c40009040007a0006464114181010704c1003100105299200c02021103003858070340c890f5507003840180d40203e0340a01c948074081806200384103203100505000d0350030f1641ca0742034024805d0710702c1810404483c050844880313011000f1100d00ba082030741001f01c0e180c143c2203201501c82c212012200034007000150341d95084120031015160381c1000358003450010701e040b4240c01d10f1308615401c500003004d039000005060001d20042c0b41521885070000e2007400007410300d00840346801d909c042c04941021007003c0341c03510074003180c0240d0846031221a00311204050030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 954130584 1250 954129334 954129353
    0xa0c0801050a0c030c0c0b0703060833130f08120405031308061e0c0f04030302160b180d030c081b1225051c05090906030105041707050115030c03 64
    0x10003e030404021001e080e0700005c151071883c4070050000540e900124405906c203510480c000c005450a03584205840084105941005c518018038154040b5142d40310b04d44114a0034050700d000805a0014030f0381d40e03520b04220030001000c1e03541c58014014904040c10a0350000d100e544a1000b4540d10f0041e200316a40d1a4103640000c5615442582089092584440880d140b03c1c17054540e0340450f500c41000200754400c51b07900d80104440854000205500000c00510385500c3c0c20b00c1d44146500c405c2d414415000745291003900c2910504850702ca4100200500300c10380c00b07450040d80d088440c2c0c441c01002c4c4e00064800d240b5400b0f0030300350750a4520510412041040b10348501d4601180c011040148030140c40d81e00f103ca484203000b14040000c2000959401d0508071540000c1c141c0071a0054616005000078502819107800041e46c240b03018410790741316903407205506074584400cc00411040d08800d0040342c1d84d6684442507148442c894120300011485074052031340d810b0441ca08401b14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 954131834 1250 954130584 954130601
    0x150c06060e090d020d0e01031a0607080c060708090a03110a0b0c0a1b0507090c02160806010e0114010c030e06090d0b340e04140a090c050111120c0a0c0801050a 70
    0x310b42204000c45c0c0895031021506000d800240f80229610b0040f406170421104042191607010500140e010100305042e4084c06280a01c1c1c400d86002e69a840000d603801c84045605075200e40203240603d0000e030140300c64a00d84e0401d401110800c9881c0d5982e044400d000347c2e001710302c9035001f0600b5208290300c8103403460400c00bc0c0440c0c0901d00460354820b651a1800c2c001c200c10315803680740c2150304038802c01c003006000b4003440c0742c488403130341c1d031003009460b480280a02841a0750701800421350400ca102d003024400c034182e40e03d05d8000c00360703142110360710f00500c10181c2c0030354100218aa0742d0740310030302c82302c10b00c0c000e0024031010b0801c4481000d000ca2a0086004681c5040e101200c0c8202d120b20600113442407410403c94a005050018000300100b501c0108040e00303601c1445842404ca03444a000188905078145030151200015a0401481d20720148030340d1050040b4a55180f0b010043c02d961520310341112403082d644e070b42d81154103605070000603940c0c0d501d404021200e5100e0085840 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 954133084 1250 954131834 954131837
    0x908100f0f060501090302090a1107060504020f0604050607030f090b280e0a06210e0105060a051906030b0301230f0f0f0606090d050d27050307150c06060e090d 70
    0x40503d0940040c140344070610000e0b100d0894140028840d0740345411000003a00808071059503800c4c285004001040140c03402c0e40242401c0280000b24100b080403102034900041c042418580b4a0740c0445004c404042c800040000d100c0000492802000141c0004c22040049002c5a4002e090b0301702130101d0000f1b40c40c01c2100d0319000709582c2e01d0b058640c005541551a001c1d8541c4180c11100c64100321702805081d042d45480445804c1c0803040d4400340c01040216840c010344da50342c10411880321070895070394450a601800170009540243e0110211980c050000b249141050183c07844445440710b070181400114001c000c40700c10307440340180d80003c0400010b54141480f080402c04841c00406440c0036100004440f24160386003007005020b241d01804a8030b8052001d0300060440200582901a040391b1564000904d084010b060003600c002030014480316142803d066810300580031f080d001d002c025200d0700d01141490184502400c0b1003812480c19042c1444641e10f408075100c050710 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 954134334 1250 954133084 954133091
    0x120301060f05072a1401030c05031303121109010801120c0e071806110c03070e272505100804020103020c0118110102010c020f06160908100f0f 63
    0x5900030820704020540c600d801c503202d030030520b010030440003503c007001c40d03c0302400e007a0f5040d1981001c1d454160741038883c0c43c4844402041c01942035492501c0c07004007103a4240b001600d4000350110740800d950080c6000c003036600d01769030b8103800c84900d55000c004200d000100c5000c40e50f04000000c0c01865070840e0070700740002ca921402883c032028000c1040c400d0540700482d0101c0c1c4200c10020964001008140a8656a8001810540300403442074004c0c061120040f41d50718010910760101d03202001e10f08100da0b99071020310b10b1541a11441d510070090b41d49100303110b46003008443c5450141303003d24400b481e00071001c219001c6503940b10b148901200001005210fa0200c10141c01aa0a00300580c43d150801c41c403e01501881100c00c42900c1c91005080a0010074580c0144070502a0002c2110b0341003503400301e840310008600501035521882c0810101140508603127451b0100c7d151071548113494056141c100391400394251802501e511410190095521500020400002080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 954135584 1250 954134334 954134339
    0x15030f070e06030f011a0405131e140a0906020f0304030906021207050c10030f090c09060f0509041212051905010807050310180203190501050901090f0807020102070b031305120301 79
    0x30404194140520304002010300c00c60411b9002141c20b50700900310007040c042e4005916028000105544160306200040300c1640ca41200ca0500c079448441c16100085901d035550078141070050300d400d03c003c444896081003001145403010700594045c0344207030f603264001403a0990003494020600c03400d0154800810410002401c0012090001c5105540d103025107804188250002d15000240c29041420203104008100b0019020400d4071140b09007000b0035501d48c1e05c0c800503030344a07009903900140c5407404100130504007540340700003003400d280c8030006010320102c0030261503090b124a5a4a855a08003c00034102d60052502401c0d141c0010445c1e00c0ca0040000c1d03031880d00c05100701c1440e42c0e81c094400030034500c810001801d0b801904860861800c0b041550112001034001c3c0c440354a001c02040315000180140190682c0140744040084100d4862045036400703240124103602c150080082d4908a01001e18415102648000407814643c14014100001c04010030340292042006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 954136690 1106 954135584 954135601
    0xc120103060e10051608150306070c1728031a01120608030a0801031a0105150c100603030509030d0305010810050c1e1c020a09031115030f070e0603 65
    0xe000407076981c80001031f030304041d407108584d040c2c0003000442e100301d10580711160351600902640005500d0303100e9980c106d0f40044a07148840303d0914100da18041080d403044214881c0e030600340000062104d00640d010320504210341400f8201582c1c1c00c542c01c8581c0890090010700d0122a0744050207003011700130010912044980700080d203c0a40c032005030b00f1000303040310300c0600340003481070540080176140e03000151300f08080c1c4200c5000c03136684401800381030011402a20b40c0ca940311461400e1604120b000a054001d044c28580100b00210000403001400050800006020740352822800fa41e03109603c20200b02c00c1030007406c5c82c42400014000c0255191140c001ca81e2540b4512100099000c3d882440b00450f025072010000302388154100700c3e1120000b08800403401c0142e03143c000c5504155030f1000031001003020892019001505c4000e10303c41140c070307541180b0f4030341c22 = true := by decide +kernel

theorem cover : BRFrame.Cov 953956834 954136690 := by
  have h0 := BRFrame.cov_init 953956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 953956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 953956834 ≤ n) (h2 : n < 954136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
