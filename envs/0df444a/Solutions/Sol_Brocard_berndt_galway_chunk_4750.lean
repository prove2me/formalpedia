-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4750
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:49.220444+00:00
-- url     : https://prove2.me/submissions/934dd485-1625-43a5-b96a-6c787eaf41a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 854136690 ≤ n < 854316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 854137940 1250 854136690 854136709
    0xc161e0510051b0d09080313051c050f03071203110d091b0b0d0b01050903060a05060a050a06180f150809010f0908030403091208090111070302040203011e0b0f030402 73
    0x19600b40740c0d041030b0401d5811084811501e0441d02c0641c4201c0340d000c2441d4028400101425032070000d18601840f08044800c010000d101e010702078403413100c602008205400104180940c007038265169401103c5da415640d400600042c2e600c4c0180200f88a4054000e200c0c0c907004002800403141012020103001004100e05281660307180e03201c0d401c003113110080380388a0015069008884c0e07140c8030440c64080464450151090502c40108100ca0a80e503000a0442d88111700c1c040200b91940ca070404502e408050b5444a82c1000007181c0109500b9000400c0c843d442d2171265102424655070089000c0f692090302c58015003044400f840c0c814140704408a9911408010011842c0220f01c1030f1182102d62050040d036078aa03010040c8420143c0c007402400041010380500c0c8810350941c3c680719420310806d4002d0b414010540c4c618500c04005028070401590020801c64581d07a49548028500761000d595602c80c041c00240403e020203c0c00a50b0851244a50000c0c1181d031154280400100c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 854139190 1250 854137940 854137969
    0x910060509032b020c060306091305100c110c040b1c0c0806040c0501090b2a0a050d091a070506010614070819030b01030207150209060f0c161e05 64
    0xd10320f0a041052081510014000f0754900601c001052018000b0305203000c100c41c0d035220303120400600c4800e98036515034a4000300c0c0411412854a118648907140440071070046a0140c100b015210000d40c09c41109420307044984292990a0105803c1100f1114644030741c9a2260000d13104001c1407443c40f14900740d407803140c003401781c05580b42c800540c82c200c01140e00300c0700707102825403d20a0703581c460940c0000300380282580d803c1a41c403070188a440b600b485c003004440c0d2602d504225140c070301002003000547e082800d4504403a80ca02c0001d24140d01e600a402d041062205050b07900c2c0710043c21a12059044000b405159003000000c41e01c0b4122140c450044007824840903010500000042c010718030310741044d480150b200203010f402e6540c4000d0342070505206201500204203011031150903441405030040c0d4405001c40010186d01400f030704038048003030104105001c40c0000800070084111103a412200c141c0c1d4011003074040c2170645000414510340a801c00040c14020400d00318007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 854140440 1250 854139190 854139193
    0x20307020f06040f05160e0103020d081c050609090f0a02120c13050714030408090d0303060f08010902031005270309100230181c080301060e091006050903 68
    0xa10301501949420750582d400d41d8000704044d040b00c02c01000700103000100c01d05040d030038015440d000100100301d405100190050029140c003000f041170b0201218240c88010340010440065254154020107088401070b004074076007004034410000004a0190f907402160042510b0060b540c00d01024002259541045100d080c5a0844030f03a40c1408001e03d0000103a40011030341f0305a100280480964048154031f110100148004280000101c880180050702d02e6803035034229107422801000658040f107100d59240c030004c81c1186041d04800b1b0180d00031070454400d0711100c404070301154015950f07515035840d4004540080715002c0710803d0b5125005090740e0a000100c00801c50108291624500580006d02c81a03c44e8450b0385101c6175102e81c101c2d50802c15503441c10462018400e00c440340581c59201d0f00b0340c400315a2000181503405204400e900c1d48007009140020341500280550400b040380d8030503034401424580c1e0418450800c4031038154181c0d107070846c1034030554400007050303405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 854141690 1250 854140440 854140453
    0x91302090a050d030216060f120519050a0e07050301020f0301181b05030f090a1718040e03040302150705070504050621210f1207200610050306070207030602030702 72
    0x40d0b50314003000b58803ca000c0e0f0054044a1200400e18280d03440d542c101d5418000d0400301d20514a62000c01c44501151078400018151201c00b9401500e00071408040441810303d4104592003d40d9000481c01901c0314045440d503d0f260010142170380188010401c1400b000c1c001000040507000e00c640030090302101c001100410030740d005004107014960500460400824003000c503605e410816801603080c40600f1030300c00c06649105a41c10990903594041c00d011602d0100a082d60180142e4610002c0c4104014414040469101d4009100030392240050340403130710160454108135541203070b0100191082c141068200402085c016090700e4000c28084650b005548409500301d00c8012100000d1440801025080816180035584480c050400b40003091855840744185d5811456146801c68a07660f03030784007111030203100d440e10760300c0d4407588070f000d0135032180416028000d01c40c010304074010944641c18940d0311102918200b0041e80604420000700d0140e038080c5801801d141f059900 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 854142940 1250 854141690 854141699
    0x24081314070b0a17090d0e0d1a01031e0308060609032503170307050904050a1107061d0c030c0405130b0a02040e07090b160c0b04030c0509060d03020a030c060f0c0e0411091302090a 79
    0x30039078600524020000c4c0750b00140280500032140d0414003411194cd14901606030b500100041d030041c00d510b010b410041019000ca17641071044001c904080d40301000c0400d10100d03504c040303501e540710565084800074915107030719a121088a100e846a501c41924103015881804001e140081081c1a500d5440145030390000c110001410018003d00e804910010b0251140c01c9a40040c8105406540181403204094801054103c400d5004450000e8550b40380280303541c10548400c0c0080c000c21580d81040a07006d8103501501c191075201c810712066545021040e14007210a0044d03400100003804800d04c0b0314884846810410701c110f001007900d0340e4448414045401940046800c1001098103008500300180c5156100200b01c0350b00d51801c690b40c802039261180c00702c5c0a0100610081801c00380300040d00003500e81824a4020030410300c41840041c10400d4103415640f082e420020000c0903c0d800b1010340c0d5220324020150065021000c01c180002d621501d40c1c42d802c1145e0000024 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 854144190 1250 854142940 854142953
    0x40b0a0c1523100e0903030906070c08031512010e010e1504020f010f020f070603090203060a0501060801090209040603050a0602030124081314070b0a17090d0e0d 71
    0x88225a5440c0c066101800c0e151071204050141d0006041619200e490400d080c600300120a04120001c46004143c8420b50720b1407020501d0742000c001c0d14030030b030300b0302005840004c000e40c481e501c058190b074195103403400f088664251402e00540144420f1000c150400c01408489028500052075611565120500c0c039003036801d44e240300c0076540d6580244601c050401e0040b2030003402c2c5444c0324074080c41d01307500041a032030380240018100420ba00141e084e15000304640490a60070070200c40b8100d0340e43e40d0040242042d00130481c024020180032403140d09c41409298180c407071544400d9440e03800e0480e034800070b400500702c00751b10640300c481c00400301d00140152904c0c1809054007507680d605081034003001e5010403551440094900e0440c050440c3d200c01c195411807145503170001d280e611410485001d040310701703026102d40541000002c40c1040b0324003c00360800c640e2150400b0500800c06500205011a18281141c00001c40e0f400070a01c9810441e10a840040c4401c1140c0b040341c8071340 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 854145440 1250 854144190 854144197
    0x8061305070233240102070b040605070305160f1a04200f0a0b091f08040b06060706020a231303023a150528060506070609060606030e06041403040b 65
    0xc1d821501342402c0b01c0c0003034800000d0a1142c0a0006010700b42c501000d4038501c0c4a2845a42c00300300c0082510380800d4850340490302c8000c0c01019600081d117003403c01d4a0444032040c01107490b07011580440c406010006d2400d84181d03085401410803040f445094000180748030706543d0302041d031040403969a61a10b8034040940f1410800c0350311003030608107100003031940f0030b526911520690900300200f0362114445521a0380300012000581760007003c60300d14054004000c1100b8000328156201a50042c5006000c848c049414a4202c1c552800185944148581c1404240c1c01e1602070005d41015583c41e090b9001895110020341040c521641194074492058050307046010144828415040100004c07400e40c41030804c22414180c0600307001d02c82c40b5003400101c000c1e695242240001e0361384400c008003030142c03a40c0d81e076524914040c0002c1c24200c00880389549003000200d8240d100f446641c0d180503801c8002c0204d0344070340d20703a010840e25400401030588000c0201058554601019 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 854146690 1250 854145440 854145451
    0x311010c020606030f0a05100b060d110306010e0a080a0f05030c0303011e0801060609060804050a05101d010209100c05010f0911120606030601060f0309050a0308061305070233 77
    0x42c20320b0742460402c05040c800e607000c0280321980110f449034046440400c01000407426003c000450b66603d4003c6106405034040d91602a450300080752452480c030002144505002d036034070580341071210100008049a4055008e56034080361460303000880666801c101c09014800700c0b0b042c0801c0d0b00c0c402e4959030003600840259400c0210b26a100f110030101c10002e8502c6070028400301c3e08084000305004a903204104c00c20041c0b10100c0c00f8800f0610074541526004000d88030000c4449425401038075529262001c2c00030f141100c0703454070310103109440040400074030500880051590446940c00104802c0d80d15541e201c5c4c07030381c0b45041039114101c000f501c120110151a18400300b0400550229500b60794507411400c00c00c001c2d60b030701245160540742541461a180054204203c1c0108400c04008181c0c0c480c0c415208203040c0c100013036602c103070310448100c0c0d0356840108101c4286c40c015103c49000d41d00111070309400e074005030101c0c00051075005401d200c4040100200300340301001e454 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 854147940 1250 854146690 854146693
    0xf07080f0310061412070f050c0a0303021305010e06041e0f121e0c0b03270102520218070207050f13021e0c010b030d03060605160311010c02 62
    0x401c00303d5088140c48405045030340903a820301340128104040240024445010003504030f113034101d071340e0140090724098a403440440d4210780c0e41e0300c0e01400a5002d400940103840308490001180d40c0b04084000200101070841410b040c6406e42007003c812040005802405552802052171107a080a85000b0810821000c01c58800b6040942d1905040303401004824121502c0c0404100c040c3e00d040100c42c48081011f03600c0e503030b10001d0a042010814000c4940c011844909450401500601704c0e00403040700711085204030300754030604000402c1c01e9040b040c00020b00107841c056100615060160341d955005805c0c40281d000440181c543c42e001200782041c0001e00110076070401c0310202514042e220385920090720800282141d00380d13081c0298068000804c1c1071442c01c207680e0050b085800c020010388031200015101c0c060a510303180e4502a11441002091542c403034065413044400c4c40d00c0e00c900d08100343c0c2c6030141d12980c1d91020340070b200d03000e50b5804e00400309101d801000d03440d660 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 854149190 1250 854147940 854147971
    0x1f0201090213410c090a0f05030f03040f0b0310050a0909170a17091c09090f05190914191412030727060c260f07080f03 53
    0x1044045000d4449040d20340441c031140710400040b4030410700803c211800b00d41c00c8496600e004000c000c0c0d1017900715a0740c10030400380000500b10305c1c1c0762043c019200d0031810346203861070290190f40d0700e000352b20895000c1c2451610810400c5804401180c02c60407040d50220800d80311404120317040d949034043c00e0740c29501c0c601078040c095040304000050340366507500c500d404c104040080c10003010700082200110030b4408100030395410402680c03005405110011440781c4002c018160201c54454600c0150a09a0b0002c842415100d0140324019002021400b84a1104400001c1040d61380845001a010685150000c0c003049074120000a1425290000302549043d01070340c0c9402ca2424450760012048a10911301d10080c2c1fa4401c01c0c51a04813890b038440d1030408a450441010211001000003020814603440600c4119441c002c041c90768035103031212401c901000c04c0424954044400340080200031500302c0050a559000760652030074880707200d9103c01741b0303803040e95541c01e00398000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 854150440 1250 854149190 854149211
    0x1020403080d0b0a0311040c030603050d090e0702060112030f050c01050c090109120804050411120a0f0e0c011e030b04050a0c03060617060f01120e071a04051f0201090213 75
    0x340214042c1c0881030b102e010713404c0e10399550740da4008107074440d0a20480c0c4035100506003a100380c3c80039004641003021903a6826184c08060600d003594011000303911141f100064089000090f031038121241d20810483d040203585044425181c0171003044100201006408407a103406d01656001b107105100003a99040108005003c2c0c003203071b030b202002544900c200f54000c5132242c01580c0444006560200e05032015a10700c1c503091066113024101504030f4000d122031080a584001080c244030102004462533074469a035580c190000c0490010307010f0032800201060b5140610f82c0744a441c140440d0380c40004c00014240c417000c507402e40b01165500c511b421038540c180520720041916040500101c03044000c623035241c01000380b0440c003818080801450741d034410403000184e403100d1501040922124100552203400c24822828200f003043c4c0a9190264001e00301d030201c600041c41006407450401c2500b030707074001500850042d9543c4903105005610782058403a00f4403050007001035210b028 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 854151690 1250 854150440 854150467
    0x405010b0907090803091903020909060411040209030c010e011e050309060f070503010902090607020a0303230c0c09090c06071505130f0201050c0a2306060402070c1a0c0102040308 79
    0x1d140c00c0402c4840700c020441d8203408006c8400c80c0605507400c1100b01d4881048562403080c41c1e20013500f00ca0040300b0070134495801310b0403030300403840344448002041c48482040168040d40c0300c01079060308580500451580119616104400306040c0480e08100940c246141003158060b0321020940000401816504c03d018695000b9046021181982000c2038018298041409410b40c100d60000b09103115a0b41d1605446401e98001e02190f60541c80e403500800480719420290140300d094906400003920400c240e0740c1d03001c1d80fa070007020010224030800040ca003010709100114040c00034140d0041d2a90300007420810701800303134546580d4011800d9000c4560090500b030100445084500001e149a450003056a40900e40a5110006026107a08040f1208402464401d440e40038a140c1f14099640340300000040d0300342c0e0080d50350402030005038425080010844540c10505000b000c0c0c0305d0002c48130701144680303d02c0c00c20248020303d60890b40300d50400d4600140102c0e100c8018100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 854152940 1250 854151690 854151709
    0xc010902010230130f06090501110d0815060706060902070b0906041106070303181101091d0a021c0216060b0f1012020f0d060608061203040b0f120405010b 68
    0x881e4030f01c820a088414020820031080a01440103449001401d039210500da0304420340035200c2d030301920017041c0d95260003a180c40228494503001ca0590040c046208401003201200743c055501e81000b1941c03420803801e0310f000f8024215600203030074030030640070a44911442d009800c0e9090010b0351850141048071403d03d0050144281e580300f1420800020050984102c400d64160b0300e9a07110f62081c50140c018210803004052000015034013207061058003808184541d40a03203490003404d84a2021030403000004800a1003514807901040784d41c030301507000340f00c0011080290b600346008603c40700141d030b00240c036481045007440d981e1000d11803072348610015150200d5140c0141040d01000c206607a0b000300c1420705010382034004204020039a0101e540640750211200c2c0c0c0c50448405440040011340951400180c00000040c01428580f1441e0f210695a074001e44c101840d0030001d01c40daa02a960b4101c500400717001c0c0b8001d030342c494508940a58414000807078852a5103051110119 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 854154190 1250 854152940 854152963
    0x609011407060b1c0510090c0e07091a0a091806081209210a0303090201092114070f120201051209010e0d0e06042102034e090112020c0109020102 64
    0x10540e41d0400017040000d2005881914840100e1881d41da41421131210003154842d810300000d03030341040502c41e8045031840941c0d6100c528921004c0b1510340184c414054400c4100106240c070300c0501040041c082c00366080c2e41a80f0000c194940c4070440d0604010801c801c0440d8040007250200a624100c0450f185418480c0071150b040840310329a0369030b40d500500c01809040d5110841c0e0150391003a561000540314070b46407145079003a004140000008100000e4401844c03541085070302800101ea4a0210303107500340c0760010300c0e00b07003640e4034801e00e01030408a040c4001004aa4803404804940e80c1c81040d038000002204007110040c14101481d004408003040200201032800d580c42e60700755400d039104034410441d00e1007901c0d00d1000420808401035418428000400ea06a0340d140000d6031040c01c3d03200c200f030030910542a00024071600980c0b80c03801404040301c16595000d590280110765414540ba041601d00c190000040b0b9104031201c0c001651548504010341d6010044800c07400b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 854155440 1250 854154190 854154229
    0x12060b131a03100e09160810180309030b0c0915040312020d09090b0103060911040f06090e04120c0c0b090315041104050603330903180609011407060b 66
    0x600d45820100c28200460058050306103070000841c0c140b40c4200a01b0150188050328100314545030b85200e40d407440007122031383c2102c1c10f020800b03c010709040091304140b5410348801c02500d0441d9503c0270101402040c1d981c1c10003003885010402d607182020000c0081d031450381c8a581e1070550030f045800589409642e402d56000c40b040403085940f0019000445c2c010300f00000381e00c1c2d40300d00100c0c0900700c10341c0300c0006a030400b21802060004c500007030080b502e5500d804101e56070358481c00c1d50b2240043c8a19090507114600180100b105038a0400e03030080f09207403071203181c00c10b03694551905926400c8012405004503030308196050421556a0b40784014a807107140346032940c0d5081e2403100412120740030350348680c04180c240e18108600300101c28038100b41c005400e0414180d940381d00c9218200031001603d00c0205400540c048200c0f840200100e00c10300450040005101c15640544001810808440f80c0e44e00703e0940e145c080c0141030310070344010031043c43c50b20401090005060000c2d105 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 854156690 1250 854155440 854155447
    0x2304150e03090d1202010b0a03060b0406051002030307050a090509090f0709090c14010207050a09050402010e041e110d0905010e0d05041d070e120102071b060c0312060b131a 76
    0x11035980b859540f410319031003020758a00c45040311089000d003120a94150700f1002c02c00010040201350382099084000c113680420610703540d0300400001059103d09080541c10800110303503e030340709a00a0041d004d0ba070030b042982d80d60319000304640000849062000e508507100710b240098050208074000c04040e0700a00c01012991149280c1c1c0710310384140c818108a410a442183c3d0003882500c000380030050034a03410310f131b0710f20701d80300644000c4408034000344207084400344500c1c0030f1103410322a0002040d0100e000400d0752100d0010b110003010b0034500081400b00000006c5039026800220348030344000304041a0010020340341410852900d41448018042441034a6000040032801c03100d82212500343c0c2c544030000ea50070100c000074117400440d150113400415005400601003d03115000010302c8031181c031010b000c03a41a5014400c00280c921006c240401c0c032a2408000300c03a0300420005001c0e42c1c40180404035030042e000800d00c6120700c24100048904101e55105c40a4950b60301c40c134 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 854157940 1250 854156690 854156707
    0xa02070906080334051608030a08040204020d111812060402010f1803050712020306070309120f170a14070206040b070c080706060608010f0902070f02042304150e03 72
    0x49030f00660ba80130071841d4041548908504525041340d442441603104408000918103001d13441d607400d140005d4848603072060019001c41c0000880782c150b0b4481d61401c00c40d448039030802000e03500c04003c1003035a54913602001246090000103001d03505036200403000884245003800a41d0741280440c11564008404200141c0d03008201c1c400c0e202c8031340c6085144030000b000c04284050460b0806049440f40742004184102102803e05526008a04444003951403013012003c0d20311120006100c445813403402d07201c030380c000c000e03000f050955428034819100d0024051100e14804845424400c1e41310070b0300101da04044802d00b40c000040e803001e02824602500da000d1030b40320260101d0104040c0d01004028881240705a80899912190501c61070b0b68864000704003160a004610199988150015841815108846070703681d100e804814014465002c01000301825110303040728840e603290209002180200480c400c5108a2180c102800c440200d50200c8005241b80c01190340100700142d0f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 854159190 1250 854157940 854157943
    0x702130e07082b09030f0f111c030f020a021804020f0d0f031b0609140607020a0c090209150a1e080f15041506080402041103070c030c020312040b0a0207090608 70
    0x156074280c4900310b41c843c24440b0000c864401c1164005401e072528042c1207000c0090b0801d40002490280d50451020a41ea41c1009043c51040100105501d15145020b0000340180a01d0050441d00e00580d40f502440c2e4010076a0036428407801d281c6030400b0000c1100314a040c2c2c00390819108180c6810b4404100e41e1746800b9041014500a01400009038041268a0140d00350000480e40301c00184140042e9240036504858610300c0a03120f80200c1000070101440024040701c03081d04820b030f03034441c2d41c580480b00c0d00942c03008400f150080320f291842d0242a56000050803072821540e164138541181c022000402602140312b0301c00c0011580603c00703c00400101160050600c090708601140a440020020700d0300450f00010001d0400d4000b130941e403c4041c0314480ca000ba41c0070710111106c2810502944404c075000004030301d0354082c80011a114111003400c50b84007a084030300444c0c0b0705508075650780041e0302141076941d0006944500c580d05015000081494101c14001c044c100640e46 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 854160440 1250 854159190 854159233
    0x30a0801120804051002061e1e0604060305070f081b06070305090f09070c020a0b0316050c030d05010906090b0f1e042405010f020c03060a020a050702130e0708 70
    0x35000c01c05848814000e22150303104450003060002c0c8000201450018045d403074400c08c480d540c48100d501100c00c20b00c0303071486c0f600c0742c03184070554212240c0540c0308800122600018281c02d4005a5594021001440c20000d40003c1c1c041e40b101e140e43c0c2d40c503140c855442d00d02c0f5150f4a503217015030041d40c810181c4561042c0c40100e40d040c03c09641718945480411a09800800c41c103a0203103444090025030b46c1c12140a900351170003901e90300019500e682920202d48020b446481c0b4845840400c1402c55102c1c20103000749090100c15a4509070040c100364083c0c85080c2c02a00201e0364030300042040030624400c00f94510810b40d14515058540d01c00142d44104004482c2034103218441c0350011991a58010241c8600038548039101c00020a1114a40c121a00480d408961910380a2102d240001101c85074560000c000f810203598503c101c0c00690811034206082c444144002001030351900c254042c000d41092001450031500d200c81450054a60b200c8505a0008102c0c07101035051604103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 854161690 1250 854160440 854160449
    0x1201061409090c21060102010608010212010509100e0f0a0e0a03090509150a1205010b0901030b130c090212041707020310020304020d0510141e040215090a09020706050108030a0801 79
    0x2000344070f588400005182d40300d03210f95510313010f008002d101c07000d981540c2914081d40080e40200710340ca4940890350300303e1191070300002d800580700c00100300c14941017081c0c0c0c1d405490425003d0501e541c500070401d4040d000d8a90844a507505130412081111074801d810400a040c1d000300340900781902c014003510185c0c06418003e61181d400200b01101050302e08801d900c01804000c1701c281e56484c402c81111001c3d1007200c455082c0b000d942690700d4100b503400d069940156400790316896907000c84401261a0404517040700c41c3e5400041e0604c080d2014100d070030015507501e4002e19041c40c01c0800143d940d4400178103c20240b000201503200000d800400007a40707000183da07902c55000203040310340400e5008203103204d4038510040501194010900e160b1580ba5a400551501c0c00b202c01e64203040750319030007140d0741c0c200010090b14011002502000e401c1011500e0700d00d1203004502c0e0b040481c1c02400e14190001605001c001c824880e1600504c1118003550800218081c0100411410701c40d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 854162940 1250 854161690 854161699
    0x30312061e011205060f120102071a0613020c0a0804030f0209060a0b120408160c0e090606010e0d0609061b1101060b04261b090a0504080a0c03031d031201061409 71
    0x940f003a122030716141b0840c10010301c010722410342450300c2400703980722540444211003425800120f000300800041c3c050f070030007090409521005802d64009402034441c2c01b00a2040d2081c0c4008203414500801c05540035600d000302000c1a80180140c0d000080d0585001d441402000c22200e00403900759440c940719074540055a80b690b044c912504d014000d0720b202c1c42e10f0034001c2d2500300300ca0104213004849030400390194650f1142d01c601e4071507204865450220714510b5540342d00c0e01c0c0044241c949a8820480051a69000c2d1103400840b44501d550070192031420740e8a500e0f4031b400c05418050702c06110000e1142c00e04180380c06c4018026031144401e110200c03076a41c0c040c1014980c41c03032a4015960120f030780240790004494100282c1d1700002d4001c0d40d00f480400d400c07030101e018203445142c11581c3c01e031404610340d5040322116060381003581010380c0c0d01c60300248e00d40c440d5a550f44220052005640303406106c21080602d41040c0c0c4000e091043c0c41d0300c1d00604911003030542d520800c0484 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 854164190 1250 854162940 854162951
    0x120f0903091507150c0207061e0311120405070617010f030b06120f0a020f030f070614070803090d0e03060403020616030b03031605010c0509010903020904050c030312061e0112 77
    0x280780001c0b40600b410091058001c400f000c01c4545180c0d100480c05c141690884484596402058415031444010760446e0034003070400d541800e00030303002001c40f44602c206091404600c0f20f0b1003070702454146c1d011160b907000f0480400c541e07640720040e402c003000b4080c0c41c2180c55150102910a001c200e120041240d014500012441d6a8141c43c4d03000074150082602e9007c20b001d1829525105080720483c031a841c510108034503420f00090281103915903138002c080c0c060408200343c4401031900c410302c142c1541040084000390340074001e1400b441118000b0500b41c13000040c0a000c40000120b900c0c040d40c0280100310201e0340c00600036401c58070320000c406030800004004c401400f00001401c0c0c044c84001410380090841c1500c8102c5140518002c10039104080300c200c8451141c0d5034118000341010f001400546010400070b500207110310b040311000810345003c24156000444030000881c181d408014580c00c1401300d405071504101d08815024400c540080e03c808040c0b1300d2001c5d41035450 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 854165440 1250 854164190 854164219
    0xf050a030f061503060608070603020408100f200904051b07080c07090c0513140604090b1c032006040b0a09170301081f1107140304050a030602120f090309 68
    0x941c40a881d1100d41402c030f0000d81d442c1c0c03c040010f00482c5c4100e44840c412070703a00058040c0710380300352001d540098000c1d00c140e0748851079040140c003100003065440c540e03a98208900c0c101001038400c2514081411644a5006d1000c1108076031004200b10110b4861860b03940c820640c00c0c0031501d960394400c800716120401d00b18500d142100c103030000044075140820101030250000c0c042c000060000d8407441342a40c0341c0301680103803010440456003243e801e000030701201000390454130301c40703801404000e0142981814100715055440050b40420329040014015a440141c02045039000f10002e02640c2855a68001113400040091824554a802d100304010304116120280c1010f420f620f40c80796118480e454a030b84141d201c0441c00c0d00900710210219006029140300d86001c095100d0411060703403694241203c060091000c1030002704404103066440540000c09140501350050300d45007014001103400301c01400300e50718034099204000324120300004984044205807002010241d46 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 854166690 1250 854165440 854165453
    0x207050d110105032508041b030c1a0d11031801150e04142a12060a0c050d09030914090f04020402090303090d11042019200a0c0f050a030f 61
    0x1501951170603440001d10391650281e002c0545030107a4040d00158045491502e003100c1810640c0c80f005102c214800f004201100b5001505070310f111511840d140740039207000008044075004035407102d031020080140042ca030105d61642050916440007040181402600603c0c0c5034141e202d24454908140d0000b070400914190203c208100c1508441c52111a4010b4800c6980c0748100e405200344100d1b22104185881905d2111051186d8040c0186459486842d009007490544500030f00108000042d2240414440c030000b2030700980d01c0e13a2407141490907501340c0100b000c01d09440383d01240180b052059110b8035441d006541110b005948117007c502090035409400c54595004050b40c0c00c080601c2009560761142c02811141002410481c0e00c00000400c841c40c0e035008143d800340040302020580310140500c41000d400c0084407100c20b903001400c06041d80c01034010540001c50350780d00704001c4c2441007001e40303004806003021609200100715008154800542814190254001400301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 854167940 1250 854166690 854166721
    0x10e0f190c090e192702120c1005071b231c03090e060111120a1b1a0903041503020f041d090c0303090a12140607030b010207050d11010503 61
    0x80d070790482030385000324481203c099034800c280c03015030400111841c1c5c0c640c54184c1941220f450007414221040039001c0c443c0c03d15460111220500c85da04803001603a44410b00b0844112041d03640300e80e610340b40d203880d5807034080140103100307201054002070000e0071400300c0108030b04503050701a036410509100010a4141c0c08030304110340d00a102403201c10f0613448005482516000c10a0b168036031100d5004444cc500e81c50070705085d60308140769200b250000f55000304003100207880c220303100c030f4012000700c10a50b440c00340c1100c44d05100c8004003450321511410075403100e011006503081c9840c10070703162442c2c0c6600d100c400800da0300241004d0304102550503100900000690351181d070807040e001d802001d0050324030034140d101c3c00b02d100c40103190020488031441c00241002005a2a003640c10b509092030000459903070341c0c12124105418020000d00b8440c400c0c694011555007905400a401c00c0d16a4100314007608014450002050103000314010f0100d003860201d40e01d91352030005903405039 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 854169190 1250 854167940 854167949
    0x2a0901080609060d0c230a03020108040201140c0303130b0a11030109020d060801020406020f0f010501120b04060e01050a020904180203031e0418021c05060a050402030c0c0f06010e0f190c09 83
    0x100d01c8140403a80748848043c4194058805c404140c003282800d01f000f083c0c51740c1c0d10000f80001c0c9900d000800551183c2e521210181241028a04102c1b2000080d03007540c2044031f602c14614144040ba400380f100140400d80c02000c01d4501b0056400000c4480003680300501424548540000d6500529142c981c000401405110001c5498540b00d050013500e03406c08181444046c4900041040c101906106007412291081d0f030f19641d440c6280e64402c51150000c10513180660b407842034007103c810a0149601c80c83c1100c0c0016550104142040b0032943c2c01d4410650b080414042c1d080141c4000044468200019040d409040168151802030b44500d40008402c407003061518004c0d0006a00600035210031b0f45044c901c00020401d0000c2114000c440c2a684039485060420690800e64000d5801c01482c1d1a600d00d1310000071201483d207039600c2c107814808e50044004002c00b0350760004290704501e160000d07550708c5c100f440c00d80143c0b260ba207000300c011603601c0901d41509400307402044000e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 854170440 1250 854169190 854169203
    0x5070801170a051204080610080c0d08040b0d050930071b0b1c0b0d030309020310090c030b09010c231b0f100b10030b182a0901080609060d 61
    0xd50015810304c80ea4100b44a048004d00c03958003c10000210081903406076504400200b040b810080f08000f4600305c0320701e094904ca0070400010900c04c80c44002840900540400841d072400c005116078500301058100104106a21840c40c80d458410001e458490041907c4103841d42414103001a1403010316003000b000b80c0c400000082d0207040880a0704005d80e030750110300c031008142c1c80c165007a41c100200140d48019040803410009001390300210071207001408481c03450381c10313011303000c00c0b170703407240015181c0b400c214004100304212140b034680d0041414009104201c0f540030041d010001298a0a070110800540e01403043c1c3c400301591003d41010180d4141341040d01200d540b200c184906031b04036030260522035940146107014000001001402d80c000820440ca0124020003110040640c01100600780045000098407040d000d1007040c0c191102c400110314041074104a0400c2d29800b106040c4200c000a07a0400c03505503010701c0075100c022041d541c1100141042e134a40c40c2c0200b01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 854171690 1250 854170440 854170453
    0x60b0301080f060702060105151c1509050615040b07171c0b010908031b0a0210050a2303060d110d1b060305010b030a092d110405070801170a05 63
    0x40c100c0001c500b6440607208040d15003035140c8580c200d8481109000361904480502c2c10410170001c03002c010f0400f048403038641da021003080780c2c800b070946490f00c08005032070150000c203100d10280341c843c0301e400090807503446940c0202c88c54001908c0c02030784204041c01c20b001c120740050000d10007220001c51070075414290b80d01c42c20034514245200c030b141c0000322607240c080c04414070350082c084074041c4d4904800550509180101486445032210318001340ca000d150100c00050b1110806040581c100e034a9140c0c44400c101d0005050007641e0410138040c10034210705100c046104801c0380d030000743c20b07104c04814202c0c6080610b62001da85a4803600810711910311800c1c411042f05e1000d480da004c52104440c180c0e507100450a4560a00581c0c240b0b00c410404100d030036080d030380101005072040244000b00603d042403071410071696845000501c0d4031a1a000420a0304000c94540c1c4000b15010002400c01c00c0b8020a089014007940044e01c210400c48502621b01f00f2031910800d9100c42120f2a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 854172940 1250 854171690 854171699
    0x5220f0c0308040e0105010320090a24020c03070b090108040204090b040507050f040915091a010605030105030d05122a0a0c050f0a0203060f0c0409020307030e0c042c01060b0301 78
    0x155210380300d06130302a6903d90020599611030b024040c0682500203124100c2451059103091a0340170008541e8001d100210000700c0240204510180b04248100c40390706060040000e410004c080501c54884c6e00a504184000386102c8151900c0060038a04000241d4892000c18021326070f2031801b0b0a44044801040204a8001802802d4542c16102c1c0c0380d204198400f400155244048018401400c1014805054400d9440031031201d00a10700c16903c07040b19031085034142d40a8014400085000005102034207081017a01c07507641d91840c10602d00100081c3d03241c074801d409000c1c1801d200305000c01c0301d01605100501c501644c0e132800e48a0340c4501c81500642642c1d03c0240403915070213024025003584cad2000c1240c0c43e4454026000d043c06a550b01c2c50140040d40050000d243c0340c1c000d2002141c10074883c40035510891070f9840c001480c59a08030117a14207861840d80764400c0f0300b402c51100542e42c112090350900740c41c8040000100910303100c040d0142019420906203814080000103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 854174190 1250 854172940 854172953
    0x121006080117031303060c02101e0908120708070212030103150b01090f0b070b0f04020f090406092012070b04090207030918050f0108030403030e0607080705010e030d0e0105220f0c03 80
    0x2c202c4111a003c49641c146145044030680380d40d861824201241c8682045502b5019003007041d459201c1c03819107141c1007034520011138042c4107480030400030320041c0030400e0f026010400d0011200500034a00d003598510381d52402808503d13417200000747c1d114602809680d005003008800740c00c03032000032a411500c902c0307611041d40044c034040d42e0700401800070500c1000305c29181801550060044a00d400c404800d005510390301a108484855503a070469010800d041010b0700000340c2e20080703c00e2950a04104505549440703104662500280000c00a9105490403101164030042000d41c0380d03a03980c01e0a079104c80050307005801480306289803001c1c02c1d080343e1100e403107100603280e80540b60b603c60801e550f8a00030741c0002008180710100d0403c1500d080e070301400b20584610340e11498801d0030355400d400c1d2581c0c040c1d52041039001148030b103082e841d180141d1401c100d07804002c0080d071919507042d80c013000d41082c040c4a1a40c188032450113010701041c1030507103240c00080310704816a0b28900340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 854175440 1250 854174190 854174201
    0xb0f09010602101107020307090c0c0c0b190509030a11030f030309010f0606090803030604200d052202030604020d0611030c030106020106060305040f020f0a1a12100608011703130306 80
    0x7010913107010b003083c1c0d45050401c00c2c1c812554000c0d009045c0d003428010404001e065140e82d500c2404090041030002032049040380018008140c403c81e116902c20b0060391a2008003810300d014007a05101c1d001c1142c5000507011903498004030462010340004000c01e013885d00015803480350303002c004204400d07150150045208851400c400300180365a50b40100c0d0f401070140503019290304100049280ca1400c3c2d084a4803030384039800d00c600180342106102a43d540884122410b2540398030810522038025034070201000e444110340d5180c40f2042d80065250394000f44000c2c07082200c0710b484420302c0718980c0400d1014400c15007640d030780c0c24008559500c64100f4483d220040d8205100030901070b109000352400303107038041c403400d40c402e01d1039003006083c11032444d41c150407014200c40024450811107003450094145525580e0395184c82c903182c00401001000c1c049034480440040045035408074850381101d500780d5000c006441a904c5950441c410344415001d81681940003000780001c85c0d000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 854176690 1250 854175440 854175463
    0x91a04240e06181527100c050408030706200a0216081b010305040204091203150f1a030a06091104090c020f06150d152711040b0f09010602 61
    0x102c50302a5907032140c2101030000f605444000c0d0f0840000300e03070826080300c0c58507004082040d2008064810021400501c008041205401e600c0203070342c03542c8050b6074481c0c0c031406480c1c0d283c840d107054204103243d0790324802e10f0001000c0c603a59140b40c242c9895a1448482010790b5210040d0340d034a4a1080256603104046404050b0812841d000900080014500b0617480d400c40c0101c650302400d500546c01420003c106981142e19165650300191140c10340150040131030305c1c0000c280d40000b02c0a22201e029822809080115900521001e00c0d001982c0c001e4040c0800802e079070340c1d0385100d584040c150380c0e8883d024250034490910800c0c101c40b0050300a90302c3c405410080c1c140d000900b20398600c07078410348881c00d41003617021440d00724a800142c0369880c0c010f000c00c000742d201d540e2840c640c01800f40280c0c4c18113507510714242480719800e1ba4400c0c1001c980d50540110001030301d9810300e45000d1391046120b0303030341c030b059800d0b460b02c0e00c03040c8515829005166070382d0b5603940d500107525803c106c0c05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 854177940 1250 854176690 854176693
    0xb0412052817130312050909070206070f020111040b0f040801020301060f030c1e051e04090e0d05070308060108180d030b030c0d0c0e04110a0605090a0504091a04240e 73
    0x200d02025a80410a582001c1c0341d507410302c400b03c0c0c60741d1100541c9013440c61400e820400e017040a014170341c0715980b01500504e102d900410f614036044a004040002e1019648110b904100e449083c1c100800207507001e8a1510030a2580c600c00c4019003046845076502c01c022650011000080ca00c2d0010070040311034038152014080d10464a20407220300607024682001c0e81c2e20702100b150718600c1034025169060641c0c428140081d03c400c1307130703421503042584a03040d01034039100380104901d03051103000500a060b0900901b00600d035070f005403010000909050410107a03100050180c409884000e03451020b040640309048061480100981146016140a1301c154010300a40b03040c4a0300c020320292f0814405c9804c0f5041440c28011800c2c007800a4520305401000e0b0807181e91004041001080c2e181c0743c4d203941e802c10700140604160304d9800603100354580310742d010114900300c0101c00030080c8e0100b840419030711840c1c1070745506414000042c1c03040102c0e101280315410b5a0100504240090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 854179190 1250 854177940 854177963
    0x20304060b0f130c140d060f17030d020307021516170105010507110a0906080303010303171003080a0c060f06170c0d0318050904150b09010b04120528 66
    0x240070302c5981010015070030258040450802d001540d203d00b0245820389400005001407116504180d0040351004580c6a5109400c01400801504010003407074101c1190145028a0061986a000d00030138900c0081d00000000c614620078800205203c02c03030081121241032211031103000503414503540020960100c03400401600002c5034a0484405030740d61032031f03d20b013592007101c0010b2180c3e550350081204c120229014030329004190203065814015a101d42c034600b0014403a01148806d12510003a0300140b00e00d003400e1b070009030142c0381c100c24000d81d500807100048402c1404240041c001ca0326005020390030300d80640241040307429541c031402500c0340c80c0d12015210920040d11641c0070011300d68140000340a18034421107109210b001081c4165a000800e004500c2154116080c941c42d205201c0703103a009100700d00390303000306a07080c5480b981000302d2902144994002e80e07880e10f429030241420070904000da50140000e464a03504205205020509a5011204115002114070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 854180440 1250 854179190 854179211
    0x108040312020f0a080a140a0c0e0a0b0901180305070605090303220602210702121002070b190c1710080f030c06010e100902031302030604050715050f040b0a09150302030406 76
    0x14025080c5d48622243e00006548801c0d03008c00060401640d02010b0100f50785c4104000c4e5580d40010f0018961116090b507078141c5000010400555070310540940c0101072020700129100190b03400030340d8103500382250f85942032800030f40780d0302943c10540028080204685103030b14401891104580304d42d001c0310b43c0e40360780c0040180c04070340c01c207041c4001840510484015141c005110312401c041c48040e1441000840414403c0c1d92004c0e4007521200841000e0104860f5801249500c401080404101101142d1001000350f42c00c9003440c0c020304105c1c0b02040d04840035941d400d004207842d5080340c440200c5a40d65985a070860301d850803c0e4003d6034000074004400c0c030b002d588252070030007e11940d40c1c2810030f40d8000b03410281c040c03140083c0d82c448510040e2000c2050600540c003840080404500d0507008044c60b42d103000d0400100302041c021a00321382658000e417030503108090951510344600c0031086401d04001e0340008400d00080c8642d10042d5010b07070095005e1030040d0700c18003120014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 854181690 1250 854180440 854180461
    0x21612110318060d0e1002040e0a020c1e030c0f070302030607110d0c0503120f180304060c060b030c0612150d030c200402030a0204180b0604050108040312020f0a08 72
    0x700202c01401840c00c44928420b450300c0001003000c1d07404610000b0b03600c000051443c4c41d00c404946280c807010703800501070281e4a400b0742903d070301c15a201000e500d4001c094044079140c480c01000350218203594050310041030400d03c02e448000034054100c07072000000c500d460f07548a107188000d90190040c4800300e000c0da0f10515030700c0e4140b6080001000c01c4006004c0844100b481c012054840340028000d60001060300b401c141d0107040c1d4280e1a4000341048000d8400c4c101102c0d0a45400354410041081481d80240500302404d40283e80040d40044141c0841c1c00c050000d480c3c80d5000c040010807514010a080307a5900900f010464403584440171000e00c00f141000c10f0380900411044000f20000500c40850b00c0000350b4011007403481001010080b80503070300b06880807040c40c1d07008203041c0301180410070204003203002da401c20f1024041990224429205501940b41040301506c000340c2814024603003145541c1108034215907418007403400142c9900041410030002d80741b0300c00b04400c00074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 854182940 1250 854181690 854181697
    0x25091e0e0402090406060b1605160819080c0f1c020c030309101b0c1e1a03070203070b0a0504030801063b03010204170c0618040f0216121103 62
    0x45400099807a1215000c02c0f5803254000d00c100d580645660003c10800c50a4028000c071f002500404043c824241c0f40003410540c03036140400200d6107a090402041000041d130480400c00c501400c0c0c02170100b810300600900c07960200300481c3c4285225000c5c80341000481c03601004440301e07991010300385c1d80300072038480240c001201d5042c3c5c001e01c40d0703400318a00640d41c40200c0c840e60801503502002e01c0303040d645c1109410b100740c49400c0d00394010400c0302400c0300d1440c200c0b400440401c440b1403c040c2c0000b0031240c0241d25101d040c41c0070002643d00741c000c1013154942a0008010741ca07925200e1701c007001820040b24200c0006107443c0001815a001d00b41c8044842c0040350000030310804844038040000e80c0c01881843c081807000d140800b51400c0c401040507151044a21105500241010f440c0c1080c0c00000c6003d070604111250600f034400301985c10100f0201c802042461112038082c029000c0c005910810111031600310701041050106031001c0c00c40e41d12064403101c0d0200990b0707100d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 854184190 1250 854182940 854182949
    0x90f041b0b0307081918020307091103040f020109050a0902030a0b011407260c100c1407030f03021c1406010f0207050d080f040308131208090925091e 66
    0x30710500204000034000d8865992185242050303c500321840c512560a444034448001d503551a12116202541000c2c000000941000001400050308981d1030028a100080c805040c943c58560420110380c400c0703d0620090038018081680c250301c800c40e04000358030943e00d051a8610749100c04040b94000c6250310400001900c40c2414500c1903204c1e0440b4508080c0c814542174051800038040c26070700c8025005070440d20004140e003000c01d40b00c48040783c4085045500740a805044522924a140115a50940d02d440e080060504c0745805502034041d0042d032001c155940341c40142e032040a80e001841c00107404001c17259a448090041d00c444540b00443c10040e08803030f9060202d4200300e088517250f02c0c0725101d070368501283d01500e600c07175400581007119800400281d00c0361410045045a01030003400e44440e0200c4007030703035400460303214588100d8012100640010001d6030f810403001020484113505212503424802c0041c01204c69010702080e000c88540060900c1000804400644 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 854185440 1250 854184190 854184209
    0x1c0e060109270201120906020c030a030f0b062709041401051005063a051b03090d120902031e011401080a032a030807110a0b01060518090f041b 63
    0xc5560f81c00444854000804043c10540c581e1018000903510344020200c1d1030058000d1901c44000314002015140038a455814090030705e080d9422a03038828084030050101e2540c100d0512502e48100f003001c0c0c46840002c0d03400100f0a0801050100d2071455080a03000070000700440c0e900c2c280f410b5001c034540e001c0d0270341005080c040f2000b0818010032440c209035501125102c2aa07031080074400508510b00d0380d007159500d450a101e41140d01006000c0107103048050325055285c4014066075400b40c41801d142080058030300c3c0d1341000c182d0340c0950501b540103420395080c6103403255184801010104103c11542c41c0844960b10060200d01841c10b84e0012000f4007480d50030780d202142c8464030031a0001c50f08807000d64443c040081d034914840c0c098482e885046030742c50061030152403404d060224840716001b4041c094000303425400094150761044c01c1c42a168460301c1e0946080c0503060703404640049048051040d80990320303510314400c0e0704c540c6480d00403403070043e04411001d8492007012080e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 854186690 1250 854185440 854185511
    0x20f06041118091b120615100203070b0c13031a09100b0a05150405061303030e0d120305090708010c0207080f0304030f0305070312050a050703050702061302061c0e060109 75
    0x840206a01e00b130751800d00101290341580805e03c00f24103018082d90a124401100d10b00e000c0700c2e090401e4441c1502d841400a50701f03040b0b0301d4599031040c90004007485540c1c81c0000c2e00d000d00f11000f2000c2d030050340e0010007901c02505074a100b5400d200b000daa2940c0c107845101c80300080e0030458010030718076900180c20000c9051800b01070050364200140b4101d180d90b0107100c0810552038050181c541c4420118010410f58514180907149007a0360b514240914201090360010998070400d020500a6a00e070000310b1342e461221141c203121045d00f0140d11942407000219406078005490340c20383d000c0c0300640d6405075622840c00c2c0d0f68400d5100050100321421040707008240034138040c4c44054080e00701542c00001c00002407045a50880e8004610795846080c400c0c00d075418490540d0104460004160300c1c2480c6420b404039000b070b018002d01c2013000162101c61101c01e408200ca0701780c3c40150600c04a001050074030344501c000d0185500803807a10148400300c14108400007010f4010f40c0a4010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 854187940 1250 854186690 854186713
    0xb0a021c350c04030b090114011401021f0605030c06041208030c040f06091e0b1c021201080d14041802030c070b0a02041814070807020f0604111809 65
    0x501103100d24641216880380090700c0310115110101d5115082042070582d981c2d04514201c1c032202005401344070541c1c0740c0440826202c0c0d105900c24155445842940e0701c13843d40c540101d15040301031407a03000707000105500b000e04a10b140c0102c41601c104400342c07045290100c0500ca880d014910074a002a0a9407402801013480600110340100c410b00000746026140e02d0841c00386041c9910060000b0082042000882c01070584044450114801000105d10701800300c0720034050390404950802203100c40340e0074890180c1c1182c42201038910303005125070b500e654558a480b81d4146031700100740c1c01003828100c00c0c000006c860566403885441d0f8800300301003441d440203410007401c007401e15808000c50b00105003600e80186c0b0402444c0400f50342c0c1d5007800c1c5014122070a0100300200f0390300f4203254004078140000c8890b400750301c45c9020441540e448208900d081c06414601c0741500401c000e100c1030000780d41c002003010006580940d20b80840501921409030221041200354000180070003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 854189190 1250 854187940 854187977
    0x312060f040b0316152118210813030903120c0605040605040218190b1c062004080723120723090f07031e0501090c020c150903030f03010b0a021c 64
    0x303035a82d2003480c1e07581c1f0451507695000ea191203500b000800341c1c103441c00c20541d554082e0a07194441d0110390380c1000550540d030007a140c3d0100740402000004200300340c0240a109504440c0d4950f0403c40c00c1c406810703c0c0c02e0000080ca000e40381a40581400401160700c602070084c1e841c001e600e0800100040f0031540d01103401403405084140e4002c2c980b250000760301601d050494200703405800c0018804d07144460349614405a071411204d10041440104070403040410101e013141c500c840300c040102094020700e011800742c1c800325641300500c4161a81ca4410004550041d0b4003e6900813568420035410250001d00646c64540d021340701c1000106d903c80310014a076003204203814003144115542c20301d02a02c0b664a00f2044450b0754070001004100f1103130041d8100c0404500143c070703034056828017050801c1c044a6490b100b0300d03000108013025403403c10458003008544620f191b20dd51311a100042281d1100d88440c0c0184544444041c281075200702d543c91f00c4440f501c0d8103500081418210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 854190440 1250 854189190 854189201
    0xc0f06120c0f0c2506020d050f0409241e030321050a15050a1a071a010605092403160309050d020604030801080312060f040b03161521 59
    0x21441070040c40109940c210800282041100900c094600100c0050b26100c40c3c00e41000b2003d100d0000e082e04004098001c1440c20301c0020701d103811603441d070110502108600c1982c1c03024000510b06600340c1042c080e040e00d00c0c1e036007041c042919040150345585400d240c4801c0f40c0c2d40710102150050030000280520841c020884110080c0d00c41900c450b4881c50880d50304527000c2c0106601d03040c070b25400c07041d68400c46000c0c1c0003c8400094160170304c0d05410b0071040c80d582078061864001008800c0c482c01e10401c400380c0100c00d82d610001c1d0303140c1d0f000500b140c0042c00303c0c2c1d025004030250007040384100c0002150922020030050b05603a02e01240a0500c11105602070a259580d10140041101400300c0001109a07800400c000d082a24004040101c140e001903400d8005110700403004440c04400e5030090070485003854a100981c00080c000e046007984aa818403540d45031411690a242143c400c0318148022800008070142064403001e200c07400041c012108807214040d10b80c0c460703108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 854191690 1250 854190440 854190451
    0x601060f02120a1809050615030421122c1c080714040906032a0510111b040b0303041404091e0b22050a030819020a09080c0f0612 57
    0x80045609004c4a82452410b030b0801d540b07180d107840c02c2200600341680d60720310f5000e1120080d072851605032101030420f500000035084617010341c0352031782106101d16600c40c0c2c0441d01220410554888030703081108140c2e4130410081c19490808441a03600b0042082a900b51031024502001c0c014150110ba50032001807000c001c1c01040040032511120740350181019008103030000908a0a40c10415400040c6c1403c2130310108208030421114201d2a03400f000b00d60303060320306008480d00104150b030403501021000c810f5109128140a110032118012580d4400c240d031b040010480d00802e058503481039000b104040c41c410005403036541810f034880365a00380500740da4070350b5100422441000081c042001c0d00d0b0b286000c4207200750101c20402c1c40007510f200024900c0d0102280e95425203428051001500340405540040c040541c509501d00461381d00c020219501c0f6070200d4007410a41e034034000c200d100d1003548440003603800c1c04c2c00a240f180c07100901107800e000510524044140c2c00500307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 854192940 1250 854191690 854191697
    0x5030f0613020f030402150f04090f0912180801050709060c020d020613090e0106030209010905070e03190501060f1a0d0213060917060c03060d1b0303050a020601060f02120a 76
    0x2400101c01c21440035200d803241d50380040750380e4281030041150410522040c9a022141004801448032545c01150300f2211fa00740c0225880004091040091100c0d01d8013800203c030a0606100507544485800350004060f000030180a817112049401c80e08100c0d48000810440b803400c1c00f2090290801803103007880280b003401c2004459002c5000c6801c9819002900300121506100c0041240a49072054406000801034145550000350000d8070600c1441c110076591404500c101c1d00c46e42240d960840c018003160300c60b610103204a40c0c1070380001c03807e5446500c0e0403008250481072600300c03001c8a0228a90343e1407440b45d04040d0105030300036481c541b0030360350800100c0d01282c4104140c0d002010561a11901d02d894040d002081c040704080c2c41140e80c018000300180d01c4240e42c15a17030807100c10707220a550700000d8a002182d4043c22006985a098120320000c00c140e032100060144d144035031300303032841070766949810340d59000354602110242c0c00c406e801407400c40340d620180c1040c001526 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 854194190 1250 854192940 854192959
    0x109050c1c080d1409010e0601141804080d0b0f030604081c050f01090e010506033003011e120f06201603090b0403230102120c0901080705030103020105030f06 70
    0x1941c803000c0d54030a0f0b00c0c072101d036512030352444041c51070000c240c0e0b404a07094000b80a02a0b00c0c01000d0380b124014000d45085c503109081e50803054889280300e0300b944880303107000b161500f07150a0440c101d402100191942d02e041c40c64034500d90400380c5441c040d400010b002022540c403660345100c55608240c05800000700012a13080c44c200c1240038040c010b020101c10305c00254100701c0c00d40240c510407d800181c603070514061285c292000194010403c110000c941c5e007103601000031a40c4441071f07040d402c82071900880049550405082c40c0e81800c40080c1c9000c01c810b030b5038138108049485502015281d100395a03880000b040840d0040000e16075600d25100c41c0c0444500b019600b074002800c51145440c01048690400d500407108002902035950741c541081d11303558135008940703031001c6043c065044940b0300380410b0109406551400d80200121552464510003003030580c0c00c941207043c002400f02000c0782404d4080d40407241600c1e0180d403020710f50f0b540c0034a5400d280e440038083d141c00440b8030303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 854195440 1250 854194190 854194193
    0xa11040302040c0309050706170c0309031207051603032304051b0616030e0a0b030c070206090a270b0103050411010c020109080d021b1203070f05010b13050610020109050c1c 76
    0x3e07c01c8a014180075250803035800090403040174101401045a15511820410710012020000c10384110514264100300c0e103503070710b0340100c0e200c1c01490030381010841300c482c0500400d42c0540080041c3d4006a4403500e210700301d0044c4d002c03c02003c0e0707009011358001000c82c188100012041c000c60020150040303203072035245207880c000004142c0382500001d03070714040c82040707207000e10300c840c02001808099411404c047d0001d0880b84902c00000f44116030000c2c02c3d0245881d40c005203c0240000ca01c4044e410940c4005000102c51911182030740741d2074030009814541c02440341354000c9800410106c1512040b2005590044000390140c3c1400700d065000502000100144c0d036100d0070f55400340c0310301d00841d140048d07442d6400c192540710700d0094202014609000045d5000c40b604000c1c0c10641d03600c2d60802600410315a450590882d0001080203110200b42d0030460003600d040d06d200c111001d802104a003243c418550040403078202c0c280d5007089140205060803003e524103030000118515 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 854196690 1250 854195440 854195443
    0xa0605210c09040f09113006010302130203040b0601032c010e0d1d190b0315011218021002120c150c192f01050405060a11040302040c030905 62
    0x1101c445400e0000011680e6082c14030b4060442c110764006400c1c84a42415901c0319001d401013203070940145ca24403602e58145550005110b01030011082c2c2c00304400c494801e680d1200000d02042c0d0107a060f007045160400000c0c402c507841641c025007806403c0c0c80d035000460107000c0750441c017880414003003100701691200745070314a03596188200026266200e4003c0a05000030310702d1903020311180c140701090b010242c050740c4214400448522130b49005900d110384c2003139016007010050002c04010403506030984c000f000340245007622a00c840e9030f0f01001003016201240c82d01c94a01407512056801400c0030b50001505100b03500544030227403448154a100d50f000025202d05551090442100e901046211903400860b400105894051185e4440c1d912041c0780c4190303030400c090700b1400c0c206849500c1001903069011543d03600d45600d54607141c1c1c040c3c00e0a5800343c403c0d00900002c6000d41c5258816030b510118040302140c10540340d1303000c2000030a0f40001000c00c1c0350301e031951003001680 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 854197940 1250 854196690 854196757
    0x7020d0204020a03050402090105060f0318010e071e1a090d0c080d0306030b010e0c1602010219140601060216050121060b0c0705010302070f020906120d051b0c0a0605 73
    0x83d60355001405260034010450f042506901c07160280104100000704011080200c0794080200701e00400090302010703500c0e004080a81e102900c500079044003150526081180395000917064011101c1261100030429902c0c44424500040c40001c0100c0107003030924540d0040c40d1805a02d030f0810b003d03a500c44460501142001c01000a580c3d03103c02e0082080400752039000d0100d1184046003490000c42c2c1c0e078854801d0700e044080d82900202c100085a1003000704820014110703000d0405c2d6000c91415500c450390080343d0040b00e004050022858501c000785501502e60100400c0c00143c0c6070800646000080c4804140107040f10f248401015800380a081c004040c5004e604c0d07a14a10081034909142d61f0b038011504250042107020042000c004111107250b40495034500f068a50b00300052050f40b2488400c0140e006c2c180e01101840d0b04880503228288034450001c000295038800103443c0e0a10b201141d03885080c56205001040c07140018010301100301c01490914540d01c0c848030701c141c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 854199190 1250 854197940 854197957
    0xa0b0a060303030e061b070f02060d020705010c02120d09030207080a08040501020d0806090103080a051209030a02011406150a050c0102070b2d011a0702041d1c1407020d020402 77
    0xd4852038100100350341446056076030072401000d420f0b00d092603c25100700f040940745102030030302c0101c0d1000c10302040c002100c0000c2d6000304003903031300c1e9410b0200301c000e900506005c6e600c0303518007168241c1d018000301c1d064003480c085010f483c1c0b4260254514000030560301c0c10940c214458100c02003468041042099031281c05a030010391204d2800f80028079003070440360480c2c100701d001814441d0984a0035816810740f50700c5900d46031100c44809040760300c3e005010301c00001072075031414451020700100040001c5a00c0b68001c0c07145000f52105610b10050603540e441d0441c00d45041006a840820054220301d802c03803611510305400041c115003a60402d95003a00d01c041c0000c10312040c5134002200c006060f038640d0240e10800001d22070207224180c1441905841c140004200720343c2d1f0f125508940403245e00800030810b4402c0d1903ca0a4000c0d041081300781c8900c90185403101260540704080e00c561701ea40e540b0002c40c00c03803181400013508540350898100080c5d903e01c10041c0c4d118009868010f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 854200440 1250 854199190 854199211
    0x5012307020a0221120d0c051804090602070209040317010503070b12040606080304150305070309050a0201030f0204090f1b020a050601031407090e0f061008150c0702030a030f082211030a0b 83
    0x4519280c1b9900844000400d03074420311204000401d4000c07079031031408a20354400c48000800f001c450a1603030182c03090500003076201c0440002c010815800c240031820707455540d9040c0000381e8aa03010304d5501c40081c00f5a0480190a000601c06001041c2155502602ca4a800b0900951ba80c42403491038009800c0942c02459a10f40c1c1c0e0701e19036141c81a140d100c041803609100401003921010b4480c1406800a410503850311540002030130150103c030014117121004000503020907049000038404d9242c01c84406e00c103428901c541a20010340c000340240c005014120503445c40d0f488008403d06243e615440f030096100c005007040151083e10310310448000a848002680e5035010305140300205003042d103240f0701d4800e001000740001d0205442d800c01c0e40489203038841205012450003100c90081d818070950810108041c1c1c00f22070103c101031503880c1c11140f51600780729400c2041c012500c0a80c00003009000320b001c07680c141e4074403400705400380c15100260368035203c410a1080407030b400710340f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 854201690 1250 854200440 854200447
    0x70914070e010e01050703230d060905010f050a0b0c12130312300e2e1107030302030703020903010f0b0312040f0b031f0305012307020a022112 63
    0x80d07040301212100e8a024648014219180c0e0000703401c6001c6e00101508000f0211a4510700c1070000c0441528407001001080d250441d1540841c06016140900700c1d505040c94000651200c05070070081c2900c40007442240b1441c00d110758460f80e81c0140124134032900c6441c4290807551040b00050600b4070b04090401074442c158180f1022480c02c40d403100041108000c403904c501c441082c407006442e58a4600414107842c14080705018080c01c02e02e08086028a450704401e003d02c40d83c1d0207001c86a0680152020360040321000c04a030700d2140b5500700a24200309520020303209900070b5170b011301141001818104c1400110b821101e8480c0a42c1540769180180f00c0d540c82c04225000202803002c60440c5020f040540720400c400c0c0302d00c81d45841c13403008004550003407440703c0f070342c4064150b4079070981e4001c0e0340e4113149001e4046040e2189130f102c8030b0aa8280000c180d82c032198840d825580003031074508059070038040409048842800800c001d07a0341d08080c6001400300c02c0d42c0c23100c8411420340303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 854202940 1250 854201690 854201701
    0x10306060f0e0f0a020307020a080d050a140c07030e0a03081303031d0a170c030d090e0c0403020117040201050f040f170102120f0c1c0f0609021317070914 68
    0x44104040c1c00c00142c01545004000c0e00444608540303034044580c90015071207494001301030f454913a440600615018001c1011a04480c4640c0010301c941c4e1124028402d8034000c003084461841c081d030b000d4076150300400107000401c0c025140c000c21442c2c09803150740329039502d464000d02900280c100d01c070b808010175802c01c10b1581c007468154624039083e0701c080281001000094010300e8a01c1494a0380c0f0242070112050794040c0654079418902406880701d6440041c80203203001d1041c0205101954204c003c9980c2401d80c400390780a481e81a1105885105d480140c44c02c1c80500400c1281007140c10441d0404098154010f00000c090716500c92104508008503140040b074840d011800aa00c1840200c103181e803035007902508015191141002501c0e1601ca11f92648207240340022016200e0782c40042c03808040c5d0141410262a02080141d561103100c500260b20503c0b600c414201880c40080c442e840340002001284c80b0b01c1030031248029a00e08146040e10101260700400032400b408104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 854204190 1250 854202940 854202959
    0xb031e070b0415080114060403020d0609060c020a031805010503071d040c02030c060c03090c0105030a02270f0406080c060a0c020406080a0312060503030703030504020609120f0f160b09130501030606 87
    0x90142691400b40030091081b036020801c98001c9100103407241d04c14aa6100900415038044c0c0401d42d0400360502118050303100285d510060700008900043c00d42002d0071610200c80d070250180c03030b0142c2d60319245448000f0221501c5021a000300e80c0c41c4003454007801d640c2d4952050090180c4036401440e11407261002250034030000418522012030100b003081101c0c0800300c1c003204161b001f401c03c0c135100c2d19100c1d0004002c0c000c1181004c2849400900030402800c0c60b40040c0c400b010803220904010703611001d00003554000c0c41062080e038003402c0f4201e16480c01c803001d000e03164024030305911405025000a000e039519036001000390341100c9400320a00d50b1196280300801600e03502446070b24540800f10b0b41e00c1c4915400903007011fa4079004141150354080c1110314204004040342005000d81f100703651114282e1012504505c1002050050b82c40e01264143c114041840c0844e001450008034910590202c0c00056020a0004141d4050841480741e5406940150400250103003080303180b9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 854205440 1250 854204190 854204207
    0x909070e211f111b0312010f030209090a0b061c0605040809121906050615070c14010e0a030b04020303070c30020303090d02130c021f0b031e070b0415 66
    0x1450103040c0070005400204100c21101d104401c3e801d65070b1100100300e643c81c114021142640c010b0000d040000800c048c0039100c800a5038000c49450380e8035203408a00940c6d820111034010102007508001641c0e0f4505001100c0c0c0c001000c40c007010303600b00240c3e250002c5460891b0200e03074904020a0000460410389074140300242000c009019000500f010742d10400c10030640200066210000540c181d204c1d040701d11202601007000c103885020f203203010140051a03008020103c01e0006110300258860f07401c9400c0501c0c09130403401c0c02c9056454804c4915001481642c0511080040c1800207101d00d800e0001054031080c2c034094803040142c1c1c84000076410910807070200b08100380c0c1c00581c0c0c0c044125449144115140d2007481c205102040031654410040303006649000001e045a41d004226098171060003100c46008140c40469001140c0135a141140c040d484118401c581c007075030140c0c00110214610071681c05a944000d40c1c0c03820741c4281c01c203a0070b0f554016901d207002900101c49 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 854206690 1250 854205440 854205493
    0x1c08030a0513081c06030c0b190503010f0308070203010912202103150a060e040f02070c060f05190e041a010807050714070b040509010b0909070e21 65
    0x102c10b6482c1c2520f0b40e80950060310303044810031a944d2240b400380320a5038003400086601420030b40b80c04c5c0d030b41c040c1c1b89060f40020740400140c40e045600c0c6444036109004680c141c0e22403d64482529085448141c0d86030001082203826650351004000410410b850510001d0400c1c1d0380d40d2a4040480885d844415490842003a01c2c1d00010042c0c58a95548601e5009100c83d02e030241d80700d640300e0091040301240342005d02d8001c030344032201103052a442045048400310565040c00302c0d210001c0d02d480ac92142600c05400d000105405020441c881d49941032122810300e41300b414408a142000b100c0203a400442000c03c1c0340d01c0710207a040c142070080700000c1780c0c40d04d00514414035010001c2c0400d40010050b1040000006103a41048000803002031044a61021599000d454224144940e8464003c00b4414990346000041c460303070400032640a0b000151070480c00703403141030381500c01489140b104d50b0701c80c461010b100c81c8140300804503114454103000520080c4c0e428400503040b044200c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 854207940 1250 854206690 854206711
    0x525080f0d020a030c1e0303050921070f0f06050702030d0b0f030c15070605150102010e07030f08090612090d0305071803021003140702010207030e1017061c08030a05 73
    0x24041c03005500411040e0040342c150410105c0d14071980f808220303c0a440b079a91920b0385141d0304000625170b240d800a0301c102007040450340000c031242212620701034402e000d03c411500400502c2c0002c1e0144d83c11076200d62162152549031640d0750b0f0350784142d8001320792aa0050b0700204502122071100d0003002d40c12041550314014144090000c25220321002003403134011510340030445080b8400900321003495070440c10030009410203c822800c00b01c40e040c03000e401582000000744c014075000c15190226030f031000c00c410001607107588a030585d0300003e1006502600501182e22804481e0b401e2902c84d038500005031440000940740a006c403140985520304000081c040e1104485801040301c09403a0100c41020165102c04411030240421079800b01000481005000c0000d0b01500035001d4144251035012441c80c4800c24850203000c90b0003140d002411a03803031450100700e0300f01c2c496040300c405880c2c020b079664503010010001c0d00106003110f41c0781d0000100404600948a802e81100c00e100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 854209190 1250 854207940 854207953
    0x301060b0403120309080c070e10091104090b06160501140c09030703030e030a0228060f0801090e0f25090b0306061c0b0c0304060c1e03090525080f 65
    0x49802c5000300420a07100f040c150f40ba91460700703000005043d10400c00d002d000300e6503620780390700185446220517200300001080010001c10000e540340946034012001905c2a81400d1801855001400b00303488507540281c4100580b4010a20f50254280a940100000309226001c0c4184060520009050100c00402407100c00003d03940401d603903003241e41611346031001c001c04800280c00c080075120020340c0400100b807000818551000381401407800da000810045960b002c09580ba0300041200c100058160001403107030302c031264003c25049a90604803040a030100114502c2c0021140105165020604c2c101314828004030f0340d040074200c9040c0901c14045114007007952a0f1025083c644951170380100089a2a1000500342e00540c00850380d06039030401000201803a4400c0c0c5066442e1401c2001c8030801e58003640451f0304800000b508800000c07401c0104800900c04001d08481502400f0f042100061008580c11440d80c9200c1c6240100d40c5029155031400041c3d400000d510340099 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 854210440 1250 854209190 854209193
    0xc080616021c1b1707050c0102100204120b1e01060e0a05010521040516060804062702061b0102030a0204060807020d0504090b010e03010213080f0a0b04110102031c09020301060b0403 80
    0x241038440b0002481061240110741403078504180801a07902c407444c002d000c54001c003400310010307401040d00020b800351101c441e07091f00000146d00c250300405002d01081c1a40200255030300141c26800519a09801840300700a0a050700300002a400100000e00e0a415101d840c906030710000c0040c40300b401c1c15445c003100f03145c0061061000f0701c10303181c0319203550303000600340081808038580220700d669078643d84580720343d00904031103410350703003a1070f42c9140c420104190029880d60030041803c4083c6071150340426400c01c95154084a08100c94402404d507aa01b0325009001940c02500610009038031982840c40080c40d40f100200031008550005025001003a0094100c1b030a8610800010030300c000000e0058600004e042c003041c2e05036100051100a480d64039041170155010f48003910304180e06090015540e40c1440805401112003201050000d10f0100310091414070600540f8101480c22041c11b0400100c0032103400c685480d48212030440c5400c0c425a0080d000c64104a4106400d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 854211690 1250 854210440 854210447
    0x60a1706121507020703050601031b0f120b0a1506170702010b1309031704030309060e1b0d051227031c030509010b04020c030406081509070c0c080616021c 68
    0x9031480d000040300d40c2c01c04643c169100f4440790380559040011550309507900d02e0052100307a0400800070010088800101d45803012040400444080b40b010351381014064a9181800802810121540d5520340e181144000c0c0b41c80d0840040550780c5a9a04a50001c11401d003140ca0003801202164075140c201c0503259281c820000d518044400000380300d00780c0349404e5070420b042c00c42e201540d8408a080204150303040c3c0281c685070348914028046010b17516450ba50b41c6818840c002201154401c11005074100a01010707507084c010405c848240510708140f11641e0302070100d120407a810341c3d03a02c0c0509085c080c103080c04100198000e02c815840c0009903496424a10748150800d522070300806e407082d4007500004150311008004543d10142c103201c0750350320383c003e11542c0c01081c0d8030030004800c0c4104106150080340040d01d60092980ca81004607141e004e0000300300e1b001500c01802003180001004228422031900c03045441c40c00001c80c02038605103041032400c00118a05135030428040c0d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 854212940 1250 854211690 854211703
    0x60b0d111e07030203120a020a17010609060c08090d06091e0b06012715110a020901090216080a02010606081f0312050418050106090e01140915060a170612 68
    0x41d0740100d50b84484241c41d00b00e00318424407504000c030605200900083c0380032640102100700c8280c9601094140f030b040c1150409100b4400c2502147c0c441d0001c104244c01161204042c130b10600d042131401060700c00243c4509183c240983e112607072807982008120311316200358036448003480d0208401c01540d8800c0d41d407840041c021410002200a51084004011101c41d1641d00319000e20010544414241c008420b0311080e403c0003400611082c43c2d42d40c03000c191101c0c0341e6006040034402c0da0901180798060340c802403101032158150b11000e804203c81001500451a0b0303a400401c1c1c0d1454041b0044c500c1c0000b42c41381807503c00c8040401d000d9662401e000080300c2e48a441070b100b0303517030142d8280c0c0c140c02180e2105140500c2c665051a010b8401ea0040e81aa1241d40f101201c0c1600c1c0d10311484222400d01807000f811030340b0681030b81c040c034001e07030100c0d80031403e0a54190001d254202090060304070170b1240b000b0070201210102c000d548000c0899001c0b00560341418030351181810681c1e100e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 854214190 1250 854212940 854212987
    0x12061409160306020f040531020405030325050a0605040213021801030b01090810020d0c0503061e062b06061407020f0a0915060e040209060405090a0f060b0d11 70
    0x2940000c1d07864180e1117240c01d440007400000c28440b49440c1004c8400102c1c110803281460410040b020313841482501c0c805d81c1c064407005001103041c4191140c100d4145104002c2c948505242410307900005002000000b164034800c08000c1044c1c100392052000317401d0401d41d100c1500340180311000c0f40074942400c1c0c1e07004000c240b1b00440c45c0740301040140d62480d00703600300f90054041c0200d05010940305400503c2034800240c410007802c1055101200c80d40000d566190744070480720f03203005409083c1c000010320000300501e19442c28040700780780941c01ca003098204680f000c0344541d548618800d441210020980740c10986607109010350000c519100d01034000b40301e140d07100c0ba40e01280d00c5a4034144060b03c50301c1d008104a507030400040c04007980620401c4000b0305800b44a00b12070030b15009451203518081c06290402d4141000c1100c00b0000814110040d40e807002c1c00103c0c020700b4042c00c00105164030f040c550f9609146646030a407075400720781c4050800700708900012031209074809000c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 854215440 1250 854214190 854214203
    0x402010f080a060e01062610060f030e0a120813020105032403010906021e090112051302130b10050910080403050f070c05130c1409040204120614091603 67
    0x10b603141e02416000b0b000c990003208500f44040d0000c9481600700b091000000e4003402183c0d403c0d407804400824401e01200d450101d004010700070805c0d180600c11140e5285810f050100e80c0c0782402c0c040a18010303041b0000c0d201904a080e6000c4a5a000484070390440e0a54a5080c4254032540000e41103102c050001914030304d0390f0506201c4c5079520004210a040d008000b1b20100a490900da800ba400c40d50b4226440c20301900200454180c100803607045100c10786910001c80d5139045180014800204031040c1100c1240d4844010b940e10607141610515804000840b59200414400704a590848803c2401810040d02c0d901d5601c8462030f29080c149450265065aa14a41155940240751245660078000711300003040000c0c05c00c0344401e4031404e4a41000e010740091507842542c6e050000e1a0200740d500d5002c0518101010050801740710140c0007601e090f980d2000e0100e1102d0040042d10b1850392805540680da601c45e6032240c03c414000300911126403090340f071040b007407454031005062 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 854216690 1250 854215440 854215457
    0xe10030320060c04030507330c02060d050709150c15090f111005030c070201080423010b030c0102010608121606020c0c03010f200d09141606080402010f 67
    0x103040d4090005910078420700e050320903500784050700200d5500180803c40d103600030040c01095545056046007102810702000b0f004950110741c0700b07440d680c0b40360626010040301c10300311800340c0c45e0540200b44241883c0c40c00940c518000c800102100699000340600040400c5405a19039100681e40c000c1904603403404060004010f0520003007080000c000d00f03800122203c0b1060001205800704a100c0684218000300c500280c1198284400c94000540440601c82100554404c0f620503501c18801d21080840c03000305800c1c000c0d44c0703091455120301603440d460601c038182000c0c481e00e900c0440a00090110f6402c004450f82c40b0043c0c10b00b0031314000130118843c6905c03240100110195600030404640d2101d240d001c07542c40d4043c4520142c084c3d8242007074031034609480e01c9420661400307070800c01104e0b514400f1f100d0b4940c3c080002505d00507214000e5002060f005480340c0f07101030060008000741c40707005c216109200705030380c4075105000b0400101304c09030b60024001041c40219180107500c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 854217940 1250 854216690 854216717
    0x60503071d1f0b2701080a0f060b0c0304080c0909070e0a180b04021c120507050a020604141906050a12020c0f0105180105060609060a1101090f0c0e100303 68
    0xc851001115030b10308030181d2000900a40c0d80030041004928206044040c100100448881c554140059034001100840050040c4085034441c6440440f0020041a40c0c2da07144440750b9a90010100300c00143c20000d4200000320040250b0141080140d412301c07620724005030300039201c2c441441101a0121050300184180000794403004500300405001d800780e81c420309000700c08180855049001c2c030a05c854003580251070301e405040340c40c1e0140841218062518045076250080c180c100e86900c01e41d1075800040e0b485e0800f81c40600f40c2d4003a81010100d80380208004129110008151601200c10510404d9070007070441e1428603241c03e00d00c94201c09404007100901c6406003109150188564404a00006400240c011204c2143c00b0010500640700c0030f080380c3c0280e070041e52084040003107070310a0605070080c24034809142441c08110040c0c1d01d0450940d039003220111401d00007c183c41081100301c40070343e0003500180800300802d113400050050101c40c3c6000c081d040c0302d0b90081d40507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 854219190 1250 854217940 854217961
    0x60408130e1014030c030a02010e0301020706090b06030c010f0507030309020109051021150315140702030705060c040302091b0f0d0510060e0127030c0b030901060503071d 75
    0x500a1031102120507a602d000d08403a2800075081c0105805030409080e0050035190000d000092100010043d01030800f00d0ba00640300420080b1010703416540070710050021608a11a1000050203403150300d13403030703c0d01c8410903007421004443e00341440308445e002c5c0e000381e40c450296112680d041c28005100c3c241c6000680d81a001680640e42c0103030303400801c451440d4000034200342c014850881009508800a40d5006d8400100082c0403c0601c0001040851004004502040e4001c403000840440d84003064001c511b0031250704e80940d04c00a40c40f02080010041142c0c02103000c00c1d03143c2007509680c00a440300d400603005d0041400000581c0ca82106d01c58116100e8038030b250780d020b59500046114034050541141c2034100d205a01c140000c60b50f0003000046003e000507540c03ca543e58031401b105255078a5000401c28558000e580480000c111081200140c40f004050743c0e22442e001406901355a11703600001c2c0a074108a81c200001c070318601c102082d0f182c1300344d41000c0b540d41c7c600700344 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 854220440 1250 854219190 854219227
    0x3605030c0402032206021c0b040509070b07150b0d050607022404030f17241e0118091404060506180123090c03010e0906010f0938030c0a08060408 64
    0x198844264007c800601503901d80c0611764110b0151824070403a40c070060032684a00d60344c1b00d4248440000c0060800088004100240c20703503100c6070004211a180380480e0305908034107411900c036030000003484102601004907034803c000000460081040800c5298040c0c0d402800007001d01c241020321000304e034001d40c10b510304c01c80c01a01e802ca007481e0805550a80c000000b410380c040080b410884021810915542d0302d2a0600f840a07000d00307a110801158100d10740e80040403114081600032400d0056801601c210301c1c070401104040c0e04003410f02d0412110090500342c80f42d2800411000d40c0c00b81441070504403865000c002020000070001d90188102004116038000282c44c01c01140d4040ca80145060301c5185098a500d692044c501907550304081c041c40044446198080001c80280d800409641c0d10500088420700076103420288070300501002d401c40ba00c88440c004095003010030842c1001e02040741d07040e800c945402616911602c0250000d0030401000408465140d4184e41d83c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 854221690 1250 854220440 854220457
    0x60807090c0e0910140102030f19051b01060906080a0f15060506030c040603180317040c03051b010e03010b0f06130302060a1e110d3605030c040203220602 68
    0x162900f6151071110040404858002c80034441c601502101d61544000287d40354022502030041c6402039039803400441e03a000fa90400c08000d13007000811b0704000c2030543e14a024032040004603805040224030000c1e40c030f40303400c50541d6901450f40400801c0c000075503595540c1e04150842e1081151240e00300207011541c10080c4c21000020074040350140310380c0280b0440307004d41c2d02045480380311031082d060556817a50240000da0401034060080e0b00388105184c1040c803412104994a40d00e03038070141081e03d404017499184100808403403455801100b000c80544048000b04a014503050000b03c0500d80e480140d030041d200850991040d140541460010b941c0003000c00752200807604008020305240010340d00315042c4100ca010010703005a1290b40d890540d00b010b01008194084111580441c1c88045504072282180c0200c010b60300d0620a4041901060620f039241d003070105240c9000010601c06029a1041040020500b81c103402e25240f004c2c3d41020715100300e51030421030080c0c06668075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 854222940 1250 854221690 854221699
    0x30f11030d02070b04122d02191a070f050f030a0207050114010f0b030105010503040204020c3c061501270b1c05010803190c08121801060807090c0e 65
    0x50b94002e102c050310444d803085104c0d5a007141d8880798018111004540f01c4081d4030743c200c2144200d010903480414207007040a003441100c8020003040052282d0340300c2c2040c04d4607034204940c0690041009203400716480078007800d001180c801c40d104010424441d0300c4c040441c3c1d40000c4003058911060b601211141c0b50000000d02c00c0a1010300603944070042032040d1002241000760000e8403032051010340381215016101e02e400c55445d6020720019510540700f4140601540c29844c0d8860b840c030300001004524031440050403880008079886181c000c004401c80d550086041100001490b4030f484220700087c81c0601c4140000390b03800d0085030f6025039082000301c0710000801d050325141c0280c1250800909850300010003840618221042030064101c01d0300100000030806c07090380500750000c44c21340b40040752140e040c0c40362150f40e0402d80c4a940520301c05c2d8107104021000b5500145a042c041340200185440d0001c0d40750740750f086204544100d9100c0d6a90f404407030142d00c2500710a44040d1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 854224190 1250 854222940 854222947
    0xb0310090305070f0c050a120506010308070201030b0901060918061202010c020102120408061b07030206011a0d090b0402040e060c0901032a021e010c050301300305030108120304030f11030d02 84
    0x152001200714075019603030040484503400230303030180a000c01c1c400300343d0000050071081c0d0864440b030140d64080b000c2070b410315403108070854054a4040c00207000304800d507150f00e07205003048100720002d40c00301800b01080c3c1c144041440750505514620300b01e20b0742400e0804801440b440183c0c00c000403e44004d80c201408280060140b901040e490f00c11042c540c44103d001084140c50b80c41401600c1c00980113034021801401003c4c840401c0b55260042000c030241032050908200c0151800c6490450327106803c0800d000450502d030117403103160724002000d001c441c54135160102041c05903003041810540c13105c013000e101480c40105900048030818040c13654440200000e0740d90401e416101c9480004841180c080c800103201e030320078501d00b503525245141d00c2c0c002003885000b040c0194014012250020340034016058560852117413094a95030345035032400341107a0600e548584641c00044c010070422000035401083d98401c501603040c00801400c1842c1c0c42444e602405021034019031002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 854225440 1250 854224190 854224193
    0x309080d0c02070f06050d0906020c030c0a170f0a0309020f0d05030310060912060b15040e040c0911030403081e0901060f08070302180703020f0f04180b0310090305070f 74
    0x54000c00c0070000540c086440c0d20b81c2d90300101129000b18072860700010b0060151240030002a00102689802a0307400341c14a00004440c604540c481801c84c4c01f04c0d408006054200140500500541000c0c50708039400c201401e200c0002ca071080900311420165100407400465480d500c0c110304412015141a0318518140741003607480d8419a204116825540000640d00e8441c0d48040700383c80c486600301286c4071660381d401d00504640c0e03003c03942c0100d0100f10020440c0c0750501030401000e0071203000700305007000c3c28082030829040e0000c0c05c17140d080c80340124400128100f10b940060703241c508030a160b40c4100e2a0a00062610040101a021740050090700041500500c0c151952940c0c580719080c0c0d08e030802c680c0e506040c84029000b00d007910f06180b002d4501c003030782d652010060501618110300d4550250180d4410091510504c034041021721a010301d103040c449168018600811030f54800500182d81d0380074201a880046840e011035008152060050b51b1060f076222a000d428141107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 854226690 1250 854225440 854225467
    0x34030f03030b040515150c0a080f1e040305070315020d090506060a050f09060603071b0317060f0a150c1b0e0912341101030b04020c030d050403030908 66
    0x14815598803c90411001c11501d17864100e00700704051009103800500305d920b024003845a0092005145180509201d1001140c1103100400903080c0c584481565080085080340c44040d51031100102c0b00e00034001480002c4000860b00c0c03c0d69000b04e08442c280b0825001c88001c2c1c030031042c04403165420b1011603c00c1100c001a90f5003d00c0040b00e070032080036196000e0003080f140325005540e0220882000c51202c3c10724030011a00541c0074540a01c2009105a1004000074028021000504403050740d000800c41a1012600704c2c1045500d00f00f00c020761000640d450700c250050b0322560b059540a08055405031a110400c0c981c49540b034800c180407030744003403558052485030f10580c810301d00008900010208004043e020034000344d5040c610301ca0303104201c0e8020b00302c81d0103d410b00100b049007071811001c4c00e42e0315944680e03850200c00c001d5800040a56100703c01c0c01d405540180286221000d010083c0c51688003a81710000300e40c0d40c1c81c24200c01138840344801a100e21000070318030991064 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 854227940 1250 854226690 854226701
    0x1120b1c02120f0a0602030703090b0403090609090e0a14010e16050a0501030e0a0308220f211d1c05240402010c141213061134030f0303 60
    0xb01c030b0b2260920101d1903600d856a03d440e405814641004201e000010b43c20380c09950001071904d00010090411782d0745003040e80003035409070f01190b1480c00803c40769034414021000303003000e00420300c451522600040d541c4d4014030801403042a210294001a0009600019a420110301101d00b5206950820860902e85021752030042869000215282d40030740603001d0030602c020000c0500d00d80e00d44003107511001c00713001551b0740c40c1014000600d10107a265101c0150703004816217207484020780ba05c2d030a105080f00c007140500801c640440300142d00050340110340000e50200702003070703805600000c0c0f000300382c4400e00701096280403400d000d000000445485118421015519204541c080c45100f403200311740003400030345040140c6001903040180c42500c0d400704c504580c2c40d0701800260f0f03000c2c1d402121400c130000032254002c01c03403103901c65840b07030030300c600040a080003c4212907001c040103a005000038a51a28100906081a10480003030040d81c02040610441c051450300601418 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 854229190 1250 854227940 854227943
    0x1b060f050c130b1206060328020c1005010b0306010c0302030d0203040c0821070f110312180108010f14030f0d03050403030b0108091507110312010807060c1101120b1c 73
    0xe02402c0802c0c03500f01e00c800c030340d81400458400440d6660341002c0250310b5000809064900780000d07007284101d002d1010b04140142a5000940c80d80000800c05251a4581d010414000e003064010408208140300b00c85d08840203107010212150b40d410242d2942c070a240110540714400030401c01070004051650058401c00c000703076444045243c00042c00546401003900040d101048208000381386001c000c801d04c1e200d4040e081d9284881c400181c01c0c001020600590307420001040a03507554203400c04030400d42c0908207602c065041000d070807590003160080b03580d10249400328040580e4208507080d044807503101100d82c1d10994840080c0504000d41b4200e0100e0309104e1310a18941c00b4202880c49040750b43d00404030303030000b2036a002204202030400c00502001111009641e4000c0c030050040328020102811603515000000d403924801d41c3c080410000450803420010706005c0e011911100c091078180155440410b00100400024080552100d11340c8001405402081410300045 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 854230440 1250 854229190 854229217
    0x302040f050f01051228023c301c020a110a0b280f0f08071202040803130e09060a0b0303040b0d050a05070516030c0f1b0905070c031b060f050c 63
    0x8c0140d00c64035940c081e03000c00716006450594803041000b41c0006440007200c54010041d9414210400340204003155603155041008144121030b40480e90412065003000310740c280010001010a00003500c6454030000140b4108044000408a40d510079a650140103903a0f0309541d61a80c2c0d0801d08500d03040c19001041c050600f680d0102d000d8000d44501c0c0003c05a901c070441002c0716100110740d9400e0042091040c0444110040d15803e068400b600141811a00442c6d84402209200c4200500c1d580300030800015501007101020022542c00d42002c414030010400140a00c000b900394011a0400041c03104080341c4580e5000550b0840303401512240800c022545511500312018403070181040d02d4540520142000248a5800641c04c1400f415640100740709507034502e00d03c292104511401c1c611080c60a0004c000c1e81d1103000d8000e910b03410554400b001d242d90181c0602513140e4245200100d0810003801d1144075081400b0440100208001034a009068004e0540104441d40b004 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 854231690 1250 854230440 854230459
    0x705150a0e0301050136020301060504050f040c09030b0c07020603040c0905070c0201051914160c230108040302010b090103051c110c210109030305010302040f050f0105122802 77
    0x60a06202c1d0320306841c0c000c10024251402c4117140070307001042ca003400381201c00720f001070700386c840c050f102a42c080c05155541c20f03502c0b4034001c20040034203020780d4000d101714945030707050316000e420008241c2101c4d0b10107400c80c0140e0f034041c50f114081c05104c030061340080001040100f0054080b15800980c0c4010ba0100165244c0c444100c0d040c100c1036000901003041008056005003004004440300030003031030f00c204c0d803c006048184042e017000c6120100681e041c5840d104006101b43c4100180c048806840c00c2403007185540c0c80030004550810381030254800204007414401e41200c00e08810240100046503541e02d45941e5441c9000294003132000300f10512104544100c4024502000400083c00c0c01d10840c403c000d40b40c4944513465040320f12041c0b446c10901c07428080c0c100359034040d1314001040d6142d401400150758080100b070990b18a00710804c10550030351134985040d0f980980e035081035180c0b140706551400d29071b6010b0b6030090100e6521100800307401c41c3c403005494801da558411 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 854232940 1250 854231690 854231717
    0x9060f1b1413030503041e0806040512130e090a03030c020f030306040e0c03060106080f060a062f0a050a120e030d0f03090c18140603031602030705150a 67
    0x104180d900c064800014008103016000400e4000a0000c0c00c0072100b018080307560301c0e92014030f554410f030700c07040460032004a1340e240300108424105c020105c1c1c00260910f840d2a6440c26111122201c0e5503d07905804100c0520302a51a65940b01130054200c0300413003400c080d02181c1d6969107041c021800a4100807821058502c0810500c1c1c24001d0f10006605544460007000094242480142c1591080c010042030666003041307111300800325a00c42125904040354005281072005080500440c1d01c0e1030b0400615510035168036108011903a00c01c411100710003c4000c400096031080020f103d040000c9041c0000450090700e0b00c0d00c222581d1500c4d10310443c1c00d0b00c19244441081c2e0345a08404004c4080c140941141c4001c103200d85400210151325641d00c8000f01d0580e0000c1d41c03049815604804218101c0c803840f0034041c540580c2d01d03031618109002965a205000801400050748103008007192020070504026000052004aa200241c00150023580141440c0360000350f02c20b02003607 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 854234190 1250 854232940 854232971
    0x31a03011505060705030c0102160b060d0c0b030601021c031e0e03030408180405100602251a21041505010303080f0c070515010504060b04260a050109060f 68
    0x140d0101020140700c070480e01c1c02c0304200c543c0d0420b903000c0e40e807400200705180d490402072001b000c0310fa004000c01c0481038a141401c03841080020043c034092041c0404243c0483c40c441e84a4044039080a03805540e03a9071280101d042040e148940007018042402a1109981541044000c8090b0000f80f90045140340d1078002a98030801d1a503001d500308002040105500d00014411f444500c91142c0c40c040207800481c0c115003080341c0c05100c1141080017402041c2c0c1c14892070840780102e1783e80030280c1c2000000440040040d00c03c2c00901006528480c140f03040d11b074107031544680880041d0f41e40d0b0600a105003640c000c01c4500700c0d100400501c015a0700e880d00c0c0308040c140d07901036231018401d0381c1c0d480040048072005468030a03454001c1c000200054410440032a00f002c01d900003012651408040c0301c1611090303041404544414402800b80c0c824803001c1801d1031000a001d04802400c2225081c2040300c041e00c050030701d500b450445410300409811644100003841820440c40c1e0286582c407 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 854235440 1250 854234190 854234201
    0x90b060708070201110703151a0117070f231207020d050a0825030605100e030c0d0629031002030105220f020414121f0c1e031a0301 58
    0x400622080c80b1900140d40f103481001d5591442d0000c5500c0c981d201d44607079481030400b80d60b040c8801d44032a4280882000344401d4403940d4800c0c203256500d841c5500040d00940c40044c1000204000700d0710a550171441101905600d46a2074100310300c61410085049080d44101103104544a40d43d0104490720300c005180d2000030032070b03901c0600340001d0303000440d030003100504500074020310881c0081d030b50030300015454440f004540303000440780d1410013409003445c69044950248031041d80c02802580b13000c40e1504c1404002c844003101e0301500d28000004184000344d0b4100c130000810a550303000c2049581841c00300d0304134100c40d404540d00142d032050348001d014254100502e580c022041c100f013480c100f0382c5900103000c007040302c005ca07030f04110407604241d00000d040c1004120700c01503420182419216042032a0281c90f04511040c10a41070440c480f201c1503450746e8507541d5031807540c0b003210401140c5c1199100c2d03008185142800070301174505080300740d0320700c6d03158050f0513210701e414441d8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 854236690 1250 854235440 854235443
    0x11d07050409020d0f0e030a081506072405090a0b130c091d120a030605040905060c1309050c0c011401240c08070f0b0a0c0c080d0e0d050301090b0607 66
    0x141441d01d4181402c080194000c0c0c042e41c91599118104040c0d200c41902607569180c10100040d92910780d0150010100c00028244141c01c801c00e0344e031b00c203043e00d840044448040e00300400013050000010082480070708101c0c4c0f01103440c9090184040042d0201c1c1520b4030071300031620031600c0d0b01c40200c0c500741404c50307100c01003000d0326844081064080507044102440103507410381c0b03650360202c1b86440c181840b280c403011142800207003e8050f00d40511850307002e4030303041d2402c000b204c0c4a941d405039a034501401091074054040b41d0710114502c00302c124005000d25081c148002d04040004a10b180c1201c0104c031169421b251010070007040d108410340c1215200c514070603074210b0142030300500b442c0990000f400c026140030544081075180c2d009000c0284203181070510300c5864100341212a001a00c410704c410b090004240905522800306400d075504091440c3c0d4400fa030014000082c180f0090030910380c0248504110807580040145040721a541c10a02c4811001d900300813583c402e1040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 854237940 1250 854236690 854236697
    0x50f0301030f03090e160333081018020d02060f040303030204050f0102010e1506010c0b25090f0501050d06030b04060c03050901090c090e0325030f1b110a050409030503011d07 77
    0x240d8544440c869000060b41c0795092240088d40842c402040e040c021000500421280710b101040081c0c070020820034a506035609030070031404440e41d88071a0184140c2801a1044250505c01303419940d401080311014007103040714564841d52854080c000c1e4100d403140324850705061000d40034950041c018403280d0503585d030107018801122b514810b1038100280009040045d40002c6400055851400b03d00400b18090390030010f18200101c41a09010301d004c410410695000c2049860b480c8400d15068078001d0800c59203440b0f0034105130700100003030350010308030507907000a0000f4070806078403006900b0b04507a8140455076942220b582030b1548000f0050000016010401541903564014212125400183c0389003440d840442c40300c0c0e00b54103402080d8080e0502e810001c054100901c0c2c0c00d01c02e0541084215000ca0005d09810700b1220f52000d01180401ca041080c2c0c2d9840d00746038005060001d0003040480c0031801c008085810074042c61031411107102d04c00d68a562440145881a001c2ea0b5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 854239190 1250 854237940 854237971
    0xb040605190e0f39161e0812060d080712090515040512251d22171605100203060f060d0b131b090510030c050f0301030f03090e 56
    0x403c802c0440d40c549449440c803484802c10180d10081004c1042c0041c10641200c032420060281403a02200b0b2480340200406100090040c2050710403892300e00c8103150719580c85101045401c0c5004800900040f400030711402005a0450509030f0065281d507081d107015241e0b820320206102c500340c41c00000e842400200020302d011480e40b140000c0c41800e40315022100304d54004400c2039145000103503161404140300b401c001e14103850485441d000c450070f480c10301b06100c440700c4039007200100c002038240000c002031090744070441c9044040c083e6900d0355042607154042d1780c070700b100c00d085030103000c0e002506200c642c441c02520700030a07005082400c07107007418040200503409010380e9001d07640c88421010059407500d014610b24440ca00000c110142084125007070f50300380d10580700a0280303541e82400300303403901c10a04020341782d6400c0008014070010307800c0d40d190040e05110103000e08000004001c00103050500100f0b1031081d114000680d881e204403411640c0b007140c40c0130b032034031415 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 854240440 1250 854239190 854239231
    0x6150c02030606041e020a092c0402090408130b090102070803070206090120061e13030c1203020405090907030201020f0a0b1b0903150603060603030a050d0b040605190e0f 75
    0x103901105d603000320580c454100b0315241c940703101641c02007a40c0c100070402c240c038204104012046071b050880d10b29001102412410051814040c030040c1c40a402007520b44001000c001104045450781c00c0c0026201c0c1156948101151a41d0300c40c20b405801409620740000e0b103040000141c4280541c02040c0d01d007400c080500440e80210003c01c0700e2400d1110482c0100d01d070300148880c034060410301c1c56840075000c406034501050440502210805050041d03044e002c44d61000110036001da00114007019298950303000c80280c01560407543d0312080850500c121490000b032480c04403032003a0203458180c60965207003601c841c101100a003140601c1000a003190012400003000a80f10888041c2400c5c1680c010901e454640640001c03822080e030140b0249284c200901c82d4001002c40007189400d401810007406406103c4880e02d003a034940142c001c082d501d80c1c0121000c0d15003e005020a4030184401001040c1d41d44038500d860625000801e446010003c0034610415901c50f00391102c440c60b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 854241690 1250 854240440 854240449
    0x1214180706120f02040e040507090506120a0b180118050709050118090203010207061103040b0c040b0d05060307080a081c0218120c1201060303110109050a030810080a0606150c02030606 81
    0x210055800320f01c1e800c10002c44c030803001018050107070340140001d101a034180f01d469800c8a002414644c420000050203021500d00041c1c5c038665075a00988911031516582898140451800340340e0401354248104031000800d854a11070080f1f00a20855000c150b0b5924424110b440c28003403e031a44040503046d40800c140e40e040500340c41d2010740014a0031860744c841c802210754180903d01a110008180824068044551904641e00c04007051a0502e81209208036114100d00240010f0f107810018103140d0303050002100504421003900c1d0080c0d500d00d4801101d0f400f640c801e480f14000405800c108000510a94004400103410200a000120200540b1844030402010302d4403800014072000c0d142c9220081580b01c00030f0011442c10308501e00034241024450314012140c0c90a4198404540b0021341058013603010f05142480d0f0f1941110740403641c04507000b140e011310035020014100b11b441d5110004584095a030030440c840243c0c0121110000c05001035030641c0500049040e6191 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 854242940 1250 854241690 854241701
    0x20f0607260702130501140d11030f0327010e0d08160309060e0105091302030405070306090c05040506060a080c090a03020310050103030201200703030507121418070612 74
    0xe0607455122000554040c04041e18601d20032506080200d40302c400c50421503070768010380038100e905115a60504512601c84080950801e00c41c0100744480340910880d4040903c0b0703803101900381e0304001087c01d840c95803a801001c1032581e400c0ca001c0e4129584081c0380c83d035070381f60038144d54295000410384108611403401003810ba920440410085c03503c41c0410b142c009080e0702c1380d10760007845407030180c0281068090703120b20340c10b1000400005c4050b035180c0b02d002c40c2c060661200141c0301d80351402d1141c40c0c13109907040207080d07501c1c1c503007600309200e024421403046034000c0741c082c0030342e41d00c107800e01100340100c01d462400704d013660002c02e0325140a0340181a400700c025040741c0714030740e0b00d0b00060700d40301119001e420110307074600052050603828005c400001c0d0300106a4005041c14410090303541c4604031019080507034841c042010f031441750383c0c1c0540b002e1ba0241d00f800b04416505207032099003019610300034000030b503850581c0710900114000040b50215264980b4404404002002800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 854244190 1250 854242940 854242943
    0x3220b0615120f07180e061c080a030e0607210b011b152406050a020111030c03061002010e032b021b010b04090b0601030c0905030f210304020f0607 65
    0x148203014040400c642d420b900c40c4078100b20b42403000c080c1007004010b01080614090703c00c0400038440c0501c1000c800310304d040d412550543d1a0381c590720300c2c100f050b16040030050000380f1100000030746000e0107a240e0130140500c8041030a80e0390f50b86031b02d0419900c4036207590340e444225528044800214441c1d0740305507140141810900d1100d048580e608003c2d01c007100c02101d13100c541e1003a1815020040c40b6410400c4030910050012212140d074048180c0c030544a0041000800601111602d04c00c1d0040200102400201c2c3e480b810194550034442d042210103078002c05498101c120b10600c14003070001708454000c05149030002c000d050401008104483c0400070021006800001082d4401072200c4109903510a40345007544002c182580c420751411403081e801c00b480701002c250103400454002c28242400527201d1001d074000c2d500c0071078550205915008041d281da00503140400d052070740722003801e8204815401c400c000b0081e07000544020390409030828031204241810001806083e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 854245440 1250 854244190 854244229
    0xa03030302030411030102030138040e22080406110a0b0c0f070506041b0b09150903160b0a1202040803040303140705060717061f0e1504080303220b06 66
    0x104d9007007000c64260792003a80a86038040004400c03904000642c088407907002c1420300e2040c1c20542c003260300c180500a5005821402703640e9404541c0714070190f500f14002c44000444110003105078149117810b90007500c2501e0100c0d14403804204400004030350014010380c450007a11550b02c032242c001001d50803034480304d920701000300283c0002c5482045182d00c02e40c4a001c0345004040c04000440400113a6480100818010300c001e0225a54019072014000040118151110f050701c001034034001d140500f05901294141010500f40120710043c1800310b0a52113000a40b409004404100d1040d803107104a143c000748420300005e48505031031902c050800c41d909007000420789805013000c205a6580c0c001c500c1d070384c0d807405990308000307003441e8880300465415060030086101c070301036865101c07001c034104410800c0782d0700350740e4400525003100c0040c800b02c191100c3d151401c0319665401690b80803081c0c0c007003003052040010031210f02417005030b102c0f41c10b0b1041d84518060050600c0c141144c01083c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 854246690 1250 854245440 854245463
    0x7020d1209021806100f0e040c09171506030a0c0504020c0a150f0f0203093a03020d060512070b0708040909050120130b0d0212190605030604020a030303020304 70
    0x2690300c0d0381035041000302e00c0080c81c2050401c4c200b00106008004a40c0d410f0040000039040026008283c000d40e48100340c9001c80c10245200f022a584d99403508101685036004003000d400e0800010000000500160844d00a4403800209603a407500764800408060b0104000c4c85142050f030041c10703800380060100c61546a4a503215840031644254000728907944071005151031103103014038104480e03080401c40c514103041180c0c0b44c440c202c1c000b0b000003c01c4d0441c41118000490344040d81d902081150751782a10030a030300020040d500c11a03001380b038076080000124a0f442d02800c2c44110101c44030007409050b141942c203130b185030840c50084e01d07002400e210005220b41603000380d10406208500000f003810032020007041000030881700701102c031070038056000400600381d10b04091301c4a0072442034440d060421014043e01c0390590301c84071300031380c403062080c0600710f01018014104159028401c040d140c00c01c0c555102011a0003079405400e4003000c2000c28060342c025030300f26000d080619074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 854247940 1250 854246690 854246693
    0x6080c19090e0f010b01030b01050d0b13021b07151709030c03040b09090703110f090609030307050607112406031507121805070b090a0314030a140307020d1209 70
    0x1101c00d25410800c2a40040a042201103003e10405d00c048600742020401c89194500080c210f015968204290590300c0d1804202070340c1d03e910324140c0400c1890295079844102e810183c1c0940d0030488030005100d04403002c9046644a510320a19914554070040d80c0c4041171501d00078410041d00c0031206000800c07020106d1b08041c8002c0c80a4580425142c0e41c610a83c0180040b005004000f0001c1529180c000b151030350501d0210f52880038840d0402e03846007464000503640b4030030b000034540d0601c40041c03084200038012600c58031032001034485c0800809210b00f019140e5600c080c1c1030612a068905034182550700e800b02c0b42c0c02120207011580200342e10300150007400c00584407800441c0c9618400c0e000250035001309007124103155070003420800366544407680c5400c0d60042541030b201c08180e5104c6034459038a03d5004680082d0043c04540a180c1c1ca10340b83c0c3e00402c03204d400104c0603044d18000c1851038041302e000703600035070041c51140d03030080040f101610340c0741d201c00d6840e0300d0360941c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 854249190 1250 854247940 854247959
    0x312041e050604030806060c122203060504060b013212040606051f021906020c06100305060c0315090402010201020d060605031905100b130f06120c0306080c19 70
    0x11181c841e20042003282018140a410080c3c002d00c400e200b0b041c204110440c0c07a00218440b80c0859524002d9500c4070002c0804241d40c0d07000f040707000007000340b806001060103070075003015000324003130001080880031580c011208260401e481003200300c01e03107604885031242c012410818a64501643d410000c02c82190842c0740001e5406555050310381006000703034030707101e1100f02e45544107013041351114034114806911081030102070041d444240c080441480030540440d1308088900c803d079605480c00e00b480842086186c08290754621846000440d44140d0f14102c81c0221046d002140491022a040042c0450018801c1781155001d01085c00d003140035014860103440b450b240c2a40785c0c44d0841d0641d0b04000342c04030781c52080d8184818054064110207954040c1c0d541810100c1d40ca015501e60719045100ca54001e50080307041510000d9610b90000701512003040c0c078002070116010441044095070828054100d02c0d401c0500400c0303052038903421300313a03402c001c035403145001e1591982c555 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 854250440 1250 854249190 854249243
    0x91f0e070f030606051c11040911041a0702090a020315040f06030308060405010f210812011e0e070f030e0105090a050d0203030c0702061809100f0e09031204 69
    0x100c022071800c0405590a5400d0701841c0e02a0130503140950402012110782880b600c00c00c0c0e002441d103035984071003940c00c0702070900300c402510041105220380b0122180504159000e8800c1020f49110000d00714007110755981160400c40d0000d04150094407120383c1329000754409031070a24541280d91503028940c030746010b0a80e2010b02c9080018115281d820301030001c44000f4217451260380741c00018030184111080c030718181c1e00c000c1100c3c98914014055440031142656020b8a6044003141182076031a0201c4101d060340c00b00140e40b0100020f510003031450401c1801000c4000240d0b41c006a20035102d01c41500750110079103000f01e00d944504220074211981500d55007407030b8114102801c28000108214010700c1c00c0c07440114914686030304150124065084001d1051500040f049007000b5000c2686549100003042070310700781850461039a43c48514402c140b2890300c00c0600060350b02c0c20154062040168038007851a1140d0060f2142e010480148115051145547c00031142c10004184 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 854251690 1250 854250440 854250451
    0x618010e0108010e030705060106080405070b0f1801020c010e060d091a16020712030f1e03090c150c0f0c1802030a06170c09071e02030d0c0e091f0e 65
    0x2050340d41844407035030030b4510700501d08070194010094140081c40009800e811680c81d49495510f42e01c0b41d241c010300b8030032a5801000b07050008101048419910300c000d2182ca1420301c40122042c2c0c03480c006907180d28051720f0b0f441c0403038010700c01981103040c64402810307940c0c1c032150001500904d540e035001e0b035072008140d0b24000c2500a001c0005020100501341c90011060000b481d9480c942a8a461a1241c484004003088600f03840d051080303002c0d44000c20f20707000100c0e04156200461800038010100c1c44c85c00e9440c0200100c00080c0340814442664090040e503540100a51450316031183e21904004200c460013a512000030700011a404140c00c0c1c0d0403100805692030404c030441030300341c0e1041e030000f48194200d28003000c810040094030480020065804880359035405e1010340e50600d03154083ca9117018165400b481c100d90100050441d8040040100214240c0041c01c941c01c070a81790f81e20307070032180580c00308150940048a10600044d603d1030014050b888020b004000300080d01d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 854252940 1250 854251690 854251709
    0x60d120f0e120f1006051309051e011a120c0103090f06020a120608010c05040315270303050c090a060c05030705030a0504030605090111030612070515130f03050a02010503061801 78
    0x40d043c0e15810030701100c02005403102e000d004040c04c110004119030122031010508540d80c016180030403c060000002041d4000c50054a00d00b01c065528040c255180b406001d2038525075003054039140040704041240b180b8001040e40000040c0150000d1940b0034041c2e4459034541c8146000804030300040448410668131038885100d0802e00a05032185500103a00503410405100c0710303143c1c01800da40481c1d4000a4005907940c0010f89007000f040c540e24070390300c40c0c40302e981481103445005600b01032592080d43c0030051603030b90400c00c2d0110b0045500300e07035101c07007000300403c103c5100f204c8880e03445004d0384c00e0f24034010301541e641d07182d41d21580c4824046000840e0400511400340304a0754803010508c02400707000c000381c58100551000600c0c01c0d00c5810048007a441030f8200f0044400584000b803c04403403c1d082ea074100c2002e41201c0011401c59200d140003040122030039200c1e80c01c0340c0d440780041081000c9a0300559541c4c2004114941000d101a40c13050400b568805980c02001e5405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 854254190 1250 854252940 854252953
    0xc080f0c1006060816050c16180902180c040f0807060e0d0506071d0a0806160c0807080d0e010221070e06040e090304050618010305060d120f0e12 64
    0x45046040c910281004102649040342c1080055000708003564081c1c4ca0094003403080c200000c007900d00340102c8070705030b2080c840c100000c25507900325044202601c203085c2034121a9043c006041c4203803400d0180081d000304400d98030552100c0314800c0990012008021107044c1034490440109547c00d07a8421440cbd070740501030421170541c00c1100c0d40900a4195414039496204d503e69507510030000e04860101301c1000c4110014000c1c081c054244a0002060340c1616681d501c9c1d15655400107844a035450b000c07001036891081d0281140b00c04c1c4591003801c0d50700b4a0318503228a90343e0380115003951902602e6004440d5840420700c0200400004002c0c0002c2840000b600d407585100010021024000944081707105682e80d1000d8504485110a003040a642c5450009003140640d074409604040c01013070381e00c1861107194a40d01c40d803500303a804109664410f03003007110100101c4400761402090240400c0458800d03004901e810100d42082d030541202d14011070071040710170103104540d07080030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 854255440 1250 854254190 854254207
    0x4020f10020c180403170c090a14040f050708040305090d020a080312090f1e0f06010e19180813031205130e070207050123040b0a0305070f0516030c080f 67
    0x3d80320b0740965a000c241c05125031030039a030043d008000321403040c24180078100c00141c6280350304045642c0b562029042c1c0c00b00035551120307a00c1c50801704808174419400c0455424100c2501d10880344140c9541c0d54024041c0c45544050b295070b03000c0019190040c41043c030319000b42c0c441d2031103c0014140d20b001036541d1120400d20302c810701000707022400c07581c21480380b14031043d00c00100804030344000f002c10102004130400740d503d01803c0c880344040320f0140000005007246d0051f801440f44220030440d1000409400c0602d049030080001240d010807202c8988000c00c031848040c10140110880360010360b80c6985a542c500d590141d005000030b0000110000701044030500d24004010940901ca078604004a02a46800882c014903041004d400d45140170b40d03c8121000c0040c5120f84d4034580d5850f02c132040d4900503800b0310300702000310b42810085075006118406041113101c460360384c141405140070340805d403c0e0031384200381c0c00c00500303202c084007168880300144000a410b881060b647d4109 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 854256690 1250 854255440 854255449
    0xc0516030212061611030409060b131a070605090f0703050c01030c02010510031b0b1612020a11090c0c06090109050601080601080a170d15030b06060711060304020f10020c 75
    0x40940b0381c5840d420001c24010181d50400100c03184040900f400d840140038210b0b0f151440c0241e03800340c0c0015080500005031142100020300002e01152a8030b40202d850380510b4400d802c0161a615400a0400010000c2007040c1e0205030807a10103029101c801140c0f01c02c003860005e40341c10a80da1078101c0d4041586e00d6070140b08801a288460000f40060f2038160100301c0386007810310010303118400d501071240d01d0046561700d200152003c0142240c58100714103650084405044084846881258074211003a000013403c80b10540d028112940001400085c1b102080000e040b48000b0384081c03000f1442079001b800300d11720031034080d0000621030f5414140a8030b00481a402104940c20071401400008004140c1e941d14541141d440c0c1c07041060759031410900c0c4210441401c1c045e1503d081d220b00780c28826482e9003200e0144098510075102d1004200c000d214004004001540c2481c118204d030070000003942d4003d00007010501840410000f140104003440e440384010781081c00c080300e03103151 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 854257940 1250 854256690 854256709
    0x5070f091703030f060f09010602061b03060319021c11031203060907051815032a1605010b09040c030606060f0e010c050c1f121505010f0c05160302 65
    0x604200d000d000404061140d01c0f80f001609030345401080c800090619192407481000042d00a800402c0e10344e99034200a456603002d4581d0071081c214074202001c80010ba034182c03030041c0001400f03400d05d850f02c941c01c90001c41c43c4040898001549141c20103403030440000c00d009031801800380494030fa000804050401e16092010407820605000380030b02511200d01c0d86501c07203c0c509200360769030103c14240100040c030081199121126058000300100001d010314080d041c0360082d42c00e1088400c100601c402450100300820040c00c1c000c1001c0134402e110140813103401140005107507412180800e540c420210380554a480300008200304101140c460840101064a442c04180b029588014007035550014076904001c0d504001c10144181030051501100380100011a4040310b103821000c40c01141f419980401d10207401c50740744000038003031511400102100b8001700c81c2881c005464a496110b207400401c0700c00d00340c01000900c02c1100c4509101014041640180346104100705883d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 854259190 1250 854257940 854257949
    0x60501020f010515060c03040302030d050c0105090d05191110060303020f0303010506030a0b0418060f0c09180e391806040506192c010303020d05030601030b030105070f09 75
    0x80c034003c00c00c0002c421102c10424aa00c04407a202e81c0c0d80a8504468507500030b0f41c20281d414020742030340f5000203412000600459484200034003055907000340564484151141c1000883c81c10003042e807030340c6145050700c01014020f0400100861803640505c0c0703486114400f503104203aa85100b8401d00da01002a008c20075030210040d4910342c1441c0208a0900020b001c81d0480340d160348101641d5030f110b41280c05220b0140b003403a5020120f600b4100081c001111200302590704e0002d008804078414118076007618016558900c140c00180030300700080400080c007070805d02480062102c40004440c0c0700208000e94102410b86a4242e0b0201c02d0020410b0589845000c05a8400b021742d8036005d45142e000760200d900107500e96942d004078400c264200c0c800300c81d0054a00000c0340024040070441030400c100022981c20b600c4441c4a010882d400303000150140e885500b003150785034480c4005691084061402050000e001d00100c0d09465044c2c0301c40c800301e0800074001c034015038403170385076001003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 854260440 1250 854259190 854259193
    0xa0c171204081b010e0603040b04060e01020f071b05030a05010c0207060519080705040f0e01031115030f060a05270604020f04031b050904230a02010f050328060501020f 74
    0x40c608940b0a5894032900c1c1e14071121030488480c010386a00905c860074180c0b00203400650369182074030303007002502012207080390268a80f00560060590501c2aa511240e802480d1845e00c42281c50304210700700c0c0305079506051881002c0c04030f0306450511a0000a510440010030020121280a401c00070340e5003101c0d0810000b0b01c03106030304c50f441f82003020802801d4102205152520002120f036403280ba0807a0182241a000000700714a00440d01412640502d030619802401002040701c0c0d0000c420f480400303106d05002140114000c40e0340540c1100004000c0e810741ea03034480c082003540f40c40d0241d040304c849a200100d00f003003003891500c6a210300102c42c02c6103040d200c4a02c4610a000340d0002030454443e04854112440301e98400c4800b40100030640940c0d8540361030b120380741c80a184404820110741c402c1801e05494001248807800d541611006074403540030324125020340008011428040d4103425800c1102040f407510001014420404158241040c0c00640390007020600803045 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 854261690 1250 854260440 854260447
    0x3051f12050124060c05010e1221040803010b0d060305101d0a02011418211009050316060209040525021f180605090a14150601030e0a0c1712 62
    0x407005100140070030b071413142c03c015051000d6824101d005010201c0a012584110310b0b4080307e441c41d00014042e91001c403168004c440e94030508041c030442c0d00703a8000f06403c000b03100600c1210350b4003000d00303a60040188006582d503a2500d0b400d1601a00100d01d05200d0f98620390307a04045410900c0c9060b6843c5000204041074003640004e01406140301c013042800c1000c00c0814400800007a094800400284200340c80e40300d91304691406030b40b00d03407030001510862414000c000703400c1c018030301065000405507081c1030f80d031120102407d500000407500280e080144500c150b44030b208082c02074400b00940d06420520150700b08111102d02d50075800d42d071110544042003030a800d03c2410001e218200030a0310720703c03500086411010150000d21450601003000483c4100007410a04030340202e0200e1607801402c945140c55480d441000055401c0e003000058155000350004025004501c1c2190340b415001e407141d04000c203140e00101200c04000c1d0a080d00040c08003c005403000c00b8884840c40d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 854262940 1250 854261690 854261741
    0x50102030309150a0b03030c01020c010b0319030e040b060c0607030b060c0a020f03031b060702101406150f07080309160608190906020d02091801080d03051f120501 72
    0x54900fa1111280c0301c00a1520000310ba88501d900468551000507040301d440d801040034481c042e4104140200b025803074165280384602c1c0c000761440b0b021401d154840c0c87c03018030b81c9085440c84144611160441d03241d1140301c0c91500c4034001030046c0c00424000d840ea40c18905030080036182e6100b04280300d01c8040c4a241d1840300041b40d581041541124004010740e140c1c0c010a0550140f200550f00501603020041101440030807110300c981c0d1640e003034a0b00b000004044000322180161301000c4448c41200084081c2024001d441d0680f8000c0d011605110314510050a1617104e032401300c0b4524400310500101010401c9a445880e480070070091400e030070000c000f131815400414401d6207210300001c00c001c27240c0c0e80e88800d18060304100d0135907441301b08450f9030380a503224001c81c038010b49004221400341024250894140c890707420140258444000c01200a02400390040354991515041c0450b1200c08110840040c5040e0076401030807519402e106085501e040c1c6000040c4886440e8503d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 854264190 1250 854262940 854262943
    0x14010906050406120f20070506010602061003060b0f04020c0304030c0f382701090b1b0f0307030305010302150a1715182707060e0118030f0c050102030309 68
    0x1604c0e209800e03400902403958188140140041348081c2c424007921788801001101c0181c02003030380b40d02450072194030742d1703032070310200d0391030404591812281e04511003e000248854224680e1008002d1000703d5090012001508a1f44030340d0f03200882d603000140400402501600c044020107140c000d4404052411006200c00c000003107100311144046e50503003140100ba5500c196a0714403945042c2d450358881074088141c07500081c0c00c4500000042c0c030f0040507607c170b40b183c2d1007a203401501c40c5042440401d1068102491056420030038000c600c40c01c41c480000b0000350800c1030207036801207900e5245006100d2694070f91074804011440c1042500c0f5079a8100102c09590883c2d81400c1c078255682886100d9030300d01045840b540050380c00d078040d07611700700d50028034004e010410110742c1d80210b1241c1d04900512020548030907420040b020803c660040f011034404040c1811f042d0b41340941040c00258588040d0422108a90046540b4041c4840d42164002401d020b00085103507090084105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 854265440 1250 854264190 854264207
    0xb01021e03270d06020703120207060605040515010207170c13050a1508030405130f090b0702010b01050405090103080901030e0601091b0305010303021009051e0a06050f0105240f0414010906050406 86
    0x1130985900007800d03e08051050304041080741c0200d40071501c8149501d4040040d0400f4403981e0321690429010400b402d18060280032407200580050500514284105003c013840c1c1d810040c0c2400b60340307034803101e98a0340d00141000000e4420000b44625080c2c100300120384e20030351a81e1641440840c184500940002168240c4108660711401030b2012844030000c0c11a04c000581080d0425407010304000e200c002d160300411b250380007030004c0c1981d40011038403070185114440d88030b00008010400300340c149009080040e01031402003011070b031015025140010130ba1100403050f07a0740f40d200c421512540307034003400c5001e145024030075540355450003591481e01c180003800306a0b540100c030040180800c01e9107058001d214058000060404820351184645001903a8140c14540010444490700c8c00142c1030b500000e003a140d00b072030900c0c4a40a00d191181e50814200801c00c02e1947c0c00444a002e40020b0202d00c0d1005890880003000400150042d8810710031301c041440103004068108050307 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 854266690 1250 854265440 854265443
    0xb040510030209040b0d12031a130209030111070b04050609060f0a05070908070b040501030509010203070804030c0c081b040c02010506032a0d0602070516180b01021e03270d 76
    0xb68540002c40c0000c0c00618041c94806d1303001504004050810800c0e0711a0113080c581a2070801a1007a45804465149103854090394403801c041d0700ba05810840794043c10400402400000d409011880355103400c3d1710021081d96500c18130b03030410082050400c1501da0090b081e030702422040c20020f1001081050150210303400c603480d0000980340c5449020860020310200003112480d43e0344841188403503102e4001c8900103810400011010754050080303074080d0302ca0b641c0f4a80e581d610790318100c4980280180071503040d400320740001400701040140d64040e2881c030140b950044484003c01044840c100900d406590400c07040104580d000301c0e49807007014500790b01c481c4c2030222031b181d10040b00c56105c1040d880341446100006200c090b038040c0c4a80342c4a14200c8043e074040c0d140408031070415200b80a07030210780320500c507501000c50f000300c183e0034410300440d01c1c0c3c4829800303405030510607042c0e1902254004110781000d8090440b6900560035400c9005807181c1c40003010032410a15080d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 854267940 1250 854266690 854266697
    0x901170a0308040813180f0b0f06161719260901140c09040c081605090d060c0f030f0b01020717150907080601350c03120904060b040510 60
    0x30144041c450484501918400b02e0141060f100e1688040f61001b50043d04800e610f40888800240080d11840c000c400005064540c181c10010420000d0343c130404c0141e840c4200f21864100249085141200640721840601d4035000400c500703030b00030b16030349618404224103071150000e00001e968070000b406144014126031a95211540b601402c815a00080d9030380d51001002180e00340341c00074203503500f001c079070a11140032500000c40342c004040e900350300c5541d01d888600c01c5090040d0000e080c4050701400d061002c62090300d42204132444044207001242c1e01404010740c096040c0300d42e110201c4140810004101c540700001d5807940c0c9401503c080107880140c100b025541040a550070746081c5481e04800d18140704038648507a02c601c146000c9101c1c2d000049200d6a0303040d44010300c0c0e0000c404880b03001c0c0304138070000c0034045605070044850259a030051a0394405010900c030390001d010155941d216100300344022a042035120513048101032000b40b08550b508d025107a0700402d0b074039 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 854269190 1250 854267940 854267957
    0x20d030e01031d06061216270515040b150a080901140c0c10061a0d0905061807050409030c12180906031406040201052d0408030301050901170a03 64
    0x690080c08180781554000e003543c07000850704040080c80030321800c000c1c0e0300d0680c80d005000c4820340d240c242103c40e60031448240701c20b00441107058002c0c6200010003002c0b40083d1100301540d41114015125211300021040700341d40282414003404641d80c6041d9940d1512040c08a1a0000350144010810402031110085990b1076805d41146481000e4078245458a05042c0f11070000c644c00010070984d1030180314031803940303408240324510031910b4141551000c03c1c2d80801e00d040382e5204442195200780e40d1030400020030300c100f2105224201c0780800503401e1403021030700c84c80c0c0f80c3c0039803049100380c0c10708500c0c200180c0e200412441c01503100303110701030044074100c0c01e50748804810340001204c02050300c001103521340d54000800303d80c01206d40103500c02d030480d00e07142c9816085074040e0200d10b0400c91001140c80001064a0b05441b020ba070b0100000d4615941e51294407990086145500c040010300207407600c9121603004000300d241e000908a48d41115580b21480d019010b802c0c40500c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 854270440 1250 854269190 854269217
    0x30522080d110d05101701180f080c010c090602070506093003030c1308010c0801030b15030f011508030a0e0d1a0405010903020f0313230d2d020d03 65
    0xb000b0380b841030305400c0c0d042c002031900c1543e04490f02c525100d052070001d603e00808280040610402500c2c8801c100c40c03007001c410366100d98104206254003100c559000b0407400380310b04d80a100310300b04481036940c2c2c2140540303014402840c20102d030300520721801042006a4007650f0304480907001803180d40e02d1402c001c2c4070008001041c041d81d084105140000403c000101d4030500003411045600c411204425444950350343c22650f0641181002c29a0b040050022504420b049548954450540d016000412000c07030704048c500a6051450f070f444001c0103011406400e240809042d6810080d8181080d46138003c0180c9403071000b450242d03c5c1003005e0303818081c4148149400411521074000c0c03605152030540e00810b445030f010b400500030307900602c0501c40048100c940708801709034003040e040d0410701e4070034003401407116104a644003078280e840710707440362009454228020a060305a02c41c00c0810700c0000800b40c21940d6400360044130110041c0c0e210341034500750740d4040c83e0440c0ba20421 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854271690 1250 854270440 854270471
    0x1e0c1b03090b0301030506100909110f04022530050901052115060307051c090b07051b0601050a03030305060102070e01120c09020a08041e12030522080d 67
    0xc54012800b52071000001000344000000d12a02851499a00031511030307842d0102000c031012100001c0040425800010741c502e0156081c1b00b010360010001071405041d003002e2808c54211a40d600c190f40b0081c1000018000b402d08456003840840c4031031369950b10041c86456101c00c801d20705400b03128001c01c9690007a446081591000c9800b02c5c1c01c421214480c01d4422000705044444100f9410218500d03000d0b82840820b40c0e00480760743c0c45050604513600280070761195890802003486a59050b4079002c604a054101c4c0a90303401e8880030303561021418440c488100061021140791700540c010841911010101c1049941601e40040c139a140c0c900100c0c24056294058644000c0003000403036000e05490481c1130146c03160f203500200550302c40f8030f2001d900a81000002007070555000a003c9140b101403d100c0d0035001000b00100740569803001c19000c503138002c2d4400680d0303a030108590101e14443c1c18030050303001d010204804003540e40302d101500c80c4142502a0613291a50858401c03003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 854272940 1250 854271690 854271707
    0x519050109060f0f0b04060303230c061513050f011205030915300412020a050303040b0601260c0a110f160b0403110904030e03010e011e0c1b03 63
    0x520142c14882c0b85207a400c00d030042d00300e404000e1221444c02d20000c840d40f505200d00c400b180d038540c80c2c101b0004000c0202410184c0000f08915001c030042046a041090500c111440340c2082c1061082c81c1000b10284154040c4041030010010300c0d00003801218181d664a880c1192011601000c60014600c0e0080c114020031299640005030603840f03044091010b03025040c00c0404621100418010903403a90300520169031a040081d82c510104000c10584e45024030b03105020700488090311070340e0381c03804d00e944d2080b04c068907881500c2c01440010340c0d01030031395111010114140f158101c003140c2c400c1100741026144441c10b080000e0b4003086030f40550543d20301120284290b42041011504007902d034042c07184101c402064092010032074155850a407001d0f40d130424004092000100180f00000384040d1080d000d1000d04c00c2c180e4420741d001d00805552203091000451b100c6450078501d2170110f0320440c042041418882107aa001da40100d1244440c0c00d40068000454030b5410241c48122 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 854274190 1250 854272940 854272943
    0x506040c0314030a02073b060405092b02030405060403030e030c0405010302130515030703032f0709020c0c0a03121403070e0d170a0203041802180d020a0807090c080901090519050109 80
    0x44001c7e4000440c0340c0008201d2240078160b8051005645007200709490746005514030320821012180010242d402d9042c0e40741c441c040c3e004403441c00d512600040d0761a0840e5204030001400000390354241e007000d01030000703880d800307460901140d41103a002988031000c0389021070190755100c0c00101c0e5901d18440241080784081c050352075190b240e0400810985150090f40ea801c48a0000711300c0301b100f0404c41c6918040f40b40042c00d040c07410040400040e510000c000c01491045a400c01080e50b241c0d01c8290085108610070126202079010242c252140864a1301c0204800d000700100d50f50004d0b410072582208490b00c00048246140500c801500031964170500d02010440018482e0000000e106403001500c0c1e101c0d801c60310090f50230507403182d80a82201510310100d100c101d418085001d10303c2c1d0b440144126032040d22207020301e1800030650b01000c03401c4c1d212281403030b41607007000c0282e4000030100c000303010103011911040d0307a4203803031074012501d0501c0c595410706100c800c0d405650b0f0316 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 854275440 1250 854274190 854274269
    0x30803040c0f090b040e070b2b1802040b012f010f020c01021308070302010f030b060d0f020a0f0509090f090a080c010b0a12050c040507020a0506040c0314030a0207 72
    0xa0344801c5610004e200b10703c0068003072460f00722055500741c00042d0241c01c0700c294112241c41c0448102c05061100145280340128903520218220205842d00603101060341404c82990502c50600411050b564401d07a030b2810b1201202281c0620035000e180c0300400c449070444441c8a803800d880c3c06006200d42895005105c0c400b1400300620913040d0010078104100d211002011500c0d064900c1c0ca03180a0311009003c1001c00c5580c1103028040d030401c2010b040e00804060620f5441c0078001c0c10b94403a41791010660b41c2c0003c5c6000305980007840352404070668603220b4100070244010580d04403020741100d0742408a40c00050071010200100c0101c268490101034454007142c110f01d01820608440f248104910b40000c25191520400c44c0003564101c0014445242c042d000d000c01070201500c81d40850244c13030390500105078108200b034012407040c08503915036451402e1003010b1406003a03e014640c0c20401c04915016800902841902d03010100d10347c9005e0b5013034480940398880001c10098 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 854276690 1250 854275440 854275469
    0x1308060c0414030d0c031d131b030e0307150915090323030f0c0f0a090e060607050d0807170109051f120f1703090a030e19030803040c 59
    0x180300a50040c00c00c031518180844240b0710960200764481c100c1c0320504d00052074040d03448021900c51448800024090300001c0d51421404010400000e03810114418450711040c042c2100d00c0c4000700341a800ea10351030200070720811020000c0d02e030310807014064184d4180081c5542214919401448015484050480c006100403581c10203814440c0058001c5000c00399841504080064482c0c80040e003110b0b440e10b940e550b43e00c4000010704c0545101b0b031030705007070007000182c0c1540d030002c084c10703009504c40b0016540390113003111100303d005240e00d000d243d0502c080000194006118110500a4200b03180d041e600c050044414486982181d40701400d11400000c1c000e143e54070060007200c0e0808410340000030849507550a003601e108204032800200b50301e102140c0c2c0c03010a040b441e846082d81106108622100d1141c54005540019080d0410380c0680e04254006c132105c045020300365036a20094132584003004208030940300140503040000002000c005104002501522362045050300 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 854277940 1250 854276690 854276701
    0x1746060222030c06020607120213051e030f1606050f0f070b150d02030309060702011814030f0703120509030a06091101032a0e01050409320f0c130806 66
    0x1e902840e102c01e031901c0d07051480108030b2900c04102c1d2445949036490b81d4202e80800d0b502c010003940103016482803002c80720000720303542d900d56010503019a120b0351450301401c048010941030110195030400d00b580720840c21450741c000f80034040d040b101e5604045840d140d00c9500801984036904800c50204400945882080740381034a05016507000000c61000d03110380d506001c12021307400c0c0040d60551062040d200700b4949600103000d81c40c410314088003c40314801c204003c1c01d0464029a040c40004c81e100f503d142420030480d00181c203e100104559895034440605080790041c3c0c900c00c00c080000c0e45821520b0803c60303107c44e07075071021081103c282c0900381014110700c10301d841d6000030b040c240d000c110440540c00700202415800180500c0046250040c2e80d88002030b64030a0600009000c00520390941d8403890203c2103424013510a21145811a00c440989801c1c0a450074205202841604000f00f9102644600c0c030551007a40d41e0030400b009850520345e81d008507011311440e801c010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 854279190 1250 854277940 854277997
    0x102070e090d11012a050706060b07141b0d030c0506040318050105091309030903080309030301061206150f030e01020c030408160605030a09060617460602 68
    0x8400501c2d42e40d50021070001030385090300fa0786a0041c4039404030a0380624000240b12a844462144501c0c1444c42c80c1042a55480d01650030950040d4140032000c02d01c3d20901100e0b0240701c40e5800030308090440e8074100c80c030011a1508001035180908941244e860030180603150b03510345c0f01d401c5011108070303203400c4c41c0c000d282403000c24001d401a852110000340c254080c2c0c003500c032140c0f00140070142d440e02c21a000f100620300030805400f002080400040844c103e04000c5001c0c290880241d0740d40c5d0f0400c071019089500303d0701d10040c0c0902d0300704100088580301c407849801100070310302049a444d580c0b608602a14059030080741c1d951000076500030042000000b00203c980380002d0f103540202040480700390b003400e40316030030210700100001801c2186580c800805d061040500003551600c91b403200c01c003034404c18240459a0f10542e06c0000011104a101c0c5004000b00b500e00c422076070416800410a0040344003511589505612030708019094040c1e030041c03000c0e9003400d050b0190300e002c040c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 854280440 1250 854279190 854279203
    0x1e15090201090506040602031209101803030506091501050c011b03060e100b220816051e01020c1005090d03020601031b0e01051c05070905061206240102070e09 70
    0x3240800c405000000c0c640c01c04009844c1210081d4000d541801039071075442a844100400c410b02ca4060400c2d101c1200144e88107585d0700c45100300c1400c10b012450b10b400b504441004d04440c3c0320780200c00401c0300b1900a070030681070003642840c0c40c9480d900e002d42014007400706861000200c1e106030b58041c0c6c07902e906612000c12182c2441c26000d981e06c0e900118011204c00d4011480c942208025244084250481200c1da48506d1f4108200a41d52820ba02e8141034071604009a00f100c0c0d144104141d22346000d2081d402c412403011000300415640001c4d40d10030707481c01920300603242d81071030280d0140200c05403100c04101604400c5640042d1900a40706e200034001251410300140182404480141c103071000d94648411106081c0d090504101c2c10548004190510480003540d403000a90144084001400c90110200b59814110704000094140c8800c10704103902083c10403017420084a0a000c1e2040405c4c2c2854400044100403401c290168101860300101441440100701c40051013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 854281690 1250 854280440 854280443
    0x106050f04122603190209100e011814010807030b01080f06010504030803090a120c05070e0a0635010b061605010608190516120b0a020d06080f06010f0605071e1509 72
    0x3080c100c20003204105c0200c3c00f6078a0030075002071002458440d50307030040345000d03040003050402440250803d1800c11f40c0b001d6942100d008201c2202c007110381c55800004603030b00040241001e00403a03c1d079500007003d881c4000d103e501d071810018007198584c3d00070011980030355004100d09030359180020829035a00c540b054100c68003411100c2025003a07101e40d554210302503004010303080662410f030178400d00110250580d4230452396407032300113030001e01d400e81002e5100103141c1c902000b91a41c00c1011202c0000403005080b0b9051160075041d981d02e0a0403100504540c5050303001d00340341810114018099034204070301358407a11080c503400c0e002a41c40040f01900c607e04503040f1003401c1580c407079000f00038455100e0703564141d0504030025180e45412540280070394401410003a00710449000d48110f07504ca500c0d1074006000c40d80c01c2d80000d104d0240584200182d8403541840c202009005204001c0c010301080000014200307807007003049000e4034181d08249100c1285540090707410080041100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 854282940 1250 854281690 854281711
    0x11220e0c0313030e0f0604080a03021002210a201c0207080a200d05040e100602031603092309280b03010e03031e0106050f04122603 58
    0x120400441000c89200780900d8255a400382c1442d6000e84880080300714456000d5115000089151940720103400240b114070300900c082d108034200a81007840c0b02c4814100540100302e451806810840d0118a00d0040c603440710b01d41c1c1c2c3d100d03d0200108514040884039200744010315102d04502d10113880f4800c0d050b001c40f091800700b90104400c0f44285c41c802001c00d20b0502031500454000d01d10442d0881c041607560801d4a0080c00785410403400e02c90140108101003400d02540e81d409902d039920404e0981c003400c2c05030602d00069542d0052070501d90603000c008210400f010700c82c5480c81e00a015504100c0c07401702818202c03410344003076024424000d0840c6c3c2c00041c2c42c0c00c3d602c281801703010203010000340c102100059140251510406103030305992074400040d02c15408100651140c80c01d5800704144400d9045203854144041e07001204105050041065022481088600315100000c280c0103c008515080504030145604031312112070740310f10000030414000040d4881c0a0100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 854284190 1250 854282940 854282969
    0xf0c0302150106021e1c080a02130303031b0309170f0d050a09060f0902090f060a180c03062c270705030705011b060e1c030f1107050d031122 62
    0x44031907602c5410090449203886c80064004041d4014841039030003076070480d00540303031014140e640809076209610403000240e0321340701c1100850507140055510746252605000061998030f8001e280000300c80c841c1d0149200059a0000b4620b0000321400084040018042442c00150981c01003076810b406880d07250504401e0016641c59105036108164020114402d0b501c034140804a540c1c0700518290300689146808100c001529600f034a80d2440d180020901400000000b002d40744241e10511005032200c100c4d4184c158240c07549282013802c01400703022980d4407003d100d4050300b500568802e068040c08003d050445c041540e005451040c1c00f00c4c0e0303100d0f07070301e400445141c10200c144410f4082c8506001000038001d401c01c80e10800c01e0001c0b540d800100043c6009440c442008220201e41e0319600c0741e00300101c0f4080c500d407442c001e000260030301ea510f4581c1915035000319507110405581c1c4502807480a40711041d10f0310181c559400c4103812101c20003020031510140640413841e040708 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 854285440 1250 854284190 854284243
    0xa29061b1005070e010804030516021c050309120c100f030204170309040606210207080408060106120c080f06040c0c0510060e0105030703171806130501030b0904030f0c030215010602 80
    0x22146d890082d589650340d03500d00b464481c0c0e07034581024942d008a81c0316040091000110501c0b000c1c0d0040c950207030000e0740e43c4035002400c000c81d21180d42030203001500101100042950f802c00841c011500c1400c2842c603000310b850048009224070340222034601d21004034114000800030241c20740c00e4069a040000b6500c23103900390342d07410401c001c181f40071031b071403404800381030194000d00100d912804040d42002d8131030b00d001d421722500f40c118100192028100014003010740c01000d950000c41d08100c04c0c541070641c0a1071900c0e80040c0300902654844009400e013510492741071050540000c25100e0650b0085040406058140300300f40a01c10348000204061802059030001c4a42c000c003143c555503042640030f12650003030108507100c0741094030103280e280c030790500618401501840c1300f41201c1c01d0000141c11038a2002a41c0e0141242004100c0000c2d003151044180a5481c02e0443c08904103140813440c29031403030034009100c500000009801900024000300c1031400d98565680d90050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 854286690 1250 854285440 854285447
    0xa110315010510051c0c0807090915030206030603100603050d0f112d01390e09093a0c050616091d0a29061b1005070e01 53
    0xa000305907110003030344030003006240550024400c0e5010058125098030114555a045a401c5006c500104646a04004d00141d00c981345002400030b1200412024002d044d02e81112101c9020082c000c4a00001141513039804014190f150045070106010160316072422a8032610844070803808603102c141c89072001d50244800c000c7d5125854020248165101d4074281f603291000c0192090007001c032954041081c0a00415038001c000d032a000c00e02c100190124101d041a4805c5c540c3d080860b00700d40200c007035016441c00b007448030031030340c400b5240c0f100e9031382500b0022040045031700588040400094050191f11001c07504000a54074407203044015400e40304089154801462504080c0c0010750321404240f0b440e80c1041c4a14012400c2d945841308800c1c1400446100b1100203001c0040044a999600981c040d40e00024550110180c8018030a1062500c030300042d446113102091000c881c041034039041407103401e880111205034600d441100d00a040c10b9406000241e40c103401d0300b055500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 854287940 1250 854286690 854286733
    0xf06090e041707200d211106070207030c0e060f150f0a08160c08190c0f0b090f03180402031b1207020c0d0b0105042408010e06161e0509030a1103 64
    0x40156070400075003121854201b00c0c824200d02c2205028000031803070050b440410400d03204410f1500200729890450502c07000030300003940300d010751905c1c000802049031204001d8281800d810f54101584005c0305140003007500074464900102800442d14000307c070343c41003020340a540001140070144003401c4040fa0b40c13000300c12001d02041400c00080352402d48004040d02d1505040c0740c034003070300200f41c0c0d500e500b40c0c40c4410301542c1103011035041c0680c10308144904c01800d180c4100440c5001100d010105000359443e03104c600c5981d01100050034403080c01518100410307030b00545a582c3c00c0c0c6171400200d00c40c1c00e50b40c00c80144191000754845041402003102d80c1ca41200c050070302a860603003080045d142041da0b482c50000c070400d0701e90103400030301e002002501d408000410004500903070149811001000500305034200349003440c960380c00c401280c00c0160380000564010300b544030250380920a14117525007520840c07064405000910340010201001101911070400b419440010705d40d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 854289190 1250 854287940 854287943
    0x1403100f080606060418090204050a0e1006260705100309121404180e0d030606020c1503070503061c0507060f0302211e10030b010f06090e041707200d 66
    0x820400041c4801c80c94a42c1e03401c014104000007094019523030780031405403076040d00d9854101d0b40350741d02c2401c040000c0c481d05542080d07000382080202d140200b402c0d000c503100c1e00084040c0302a8841410740130801d00040e400303000c010303001920b00440808018006c1890440503240403115000d1401841d104101d0b840e0b00300620910075080ca410010115038120191900d41001036075070b100e10100700014000000d89410a49001800a1a00700301030b060075901d442d8a44100322428241c410300802e08103a0742c100d04185061307502d80e80c510b0013150554a0704043d400d070f40744240c0040010400d000410a09481855a80d990b41c00448141a0260300503d00c154409884440402c680d0b21400118182d10062080001c4049040344050200c003401c29900703034914241070b00051088c016000c0e82e040c01080042020b40941c0d00e010001000c44001b8058854000721a6000c241030000e01a48007222000e00c6816903a509440d103020543c054403504000a012410260301c00f80f846e00240300c04805 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 854290440 1250 854289190 854289199
    0x40f050601061b020f0a0e0f010f06030b091602010e070b04152604050c060d0b10020f07032031060510050f04080118060e06061806011403100f080606 66
    0x52813035007002402d1541d00c40c280c1d0800316040c0c0020301d0682018110340100004034145080b035040200b0301c5201c8003140c100200b4103003890035142c59a287d10215070750048044a80c0050801d40308800c0740501029154020f8512400354085125070302400244111140380f1094007601d1403545040c0d81c40c045c500030784503c0c405640754051038000c061001aa0003481842554451400100000c0b031030340101250401c4245e588101980504050b041030000f5907480c0020300c1c04945d0520080e507107095a0000404851101b00542d00c0d030042c010f08004001c1c80140141078121260005062a08210f001000300200300c206948500c41a841b54105542c8050125130703d80c02241d4060781c039030740b0420800d05402c804200002c0c95420070b00c940c18048070040c0d244814560303142811802d880480031480c0150b0046010711007a0b0740c0b4000d40010130500b030410001c2c182d484400594000f400144c00e85214100001040010600314440310113640c007030601307513094944a094080c0e60359011102613801 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 854291690 1250 854290440 854290487
    0x20702121c08070c0213230106020d08011e1701020f0f03090615210705030f150708090c0103090f120915051e03040503070c0608010f0524090103090605040f05060106 73
    0x2400c81781d0b0024001c1400e0b0030010303d841004002c87c0c81c0341620903409140140c00c10740c1003802c3e113540004203600601520b2401c46031943c4040c1a0001501284520300d80801c0484003516481020740548940021540c512034441c0a100c000c0c0a0741e40c81103a4a4120b805031800003103020313550f5815054000d5003e0001800b5021400400c0c11012241081c001d40b0300c5051780c00074842d601008030303602128010015045003100b400405010100c05000c40081c001240c04010351020005000320715000c0900e001305800450f0b0030300600e6030040b00d401800c8032000d11209450aa0810210003c450244e40c1020b03003604180001c40380c42c050649480304460030100e0240d4120a1300d0055070b001401042960300d044015951121400c4a0798010700c0803c40c20340040010703c40c0524100024802901c000080c0340c444559050b08403a1411000349045020949103543c0c0d1081d44401c03211607010078104100c6c102410008180034171840308440c01c0c490003002084092040004200d16410040c54558 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 854292940 1250 854291690 854291719
    0x10627140c0307023301050d08162a1401020a050a02040b120307200f0607150e0d1e0315210c090e0f06090a0204020702121c08070c02 59
    0x121940043d01c0c80c1c0c11481464001d9460040356035200380713035060684d105455801e4032280c0e1032690605070701aa1054200c004400e001c1400c0c2c004a80750707504455000400c0c0c041a00d0101d60003600d1038200c11107008050304e04407001c0401c0c0e541c801500e13188014504070001e185c004a03901c00b0020350060043c1c001d119604010304190308001d00b19100140320718500132425a60302d241d42c000c00800d1b41d40000303a0300201c04200c94107000f61a0040c080e80c00052085098010540a102d2580b0003800d40b000101000f00064003940b18030310b01c810000603101c3c5140c1c0741d9001040e41050047c8280c0c0182044260340c6618002c5c402c025040c0031058041c5005841d0220110b0018407c0d6618810500440c4010002030940c0d548040980500c03d0000b4005e04014085172401d42d0402c088025548583c0521448a000041100202d581168090707170302c01c59440892241078049030490002e116221082900c0310083e042103070405042d6076a50260707918414100ca4402c0e0103600a50440445822440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 854294190 1250 854292940 854292961
    0x100b010903080309010e0129030d0f050a020f0d0c0203070e0105030a030c030c0209010f080609010e1f060e0c120c03060609060a03020c0a08220506030a1d01062714 72
    0x180c4c80101500000786401146090500355000004208141500201c00a0b0311546400c8040c242c1d038019002440c5c2c40c0c4440d02c010b01000b1107602e4504c14042e0105880b400c2034400c210382818441040183c0380b01b0340c100d05024140020b50041280b180c0104800810b50610141d09181200e20050080050324076541b41030310f1020011a00307a0811944903400000350700c81c005400e000701911014500c06038506054a4104800034120740d20990400c00001640500016000742c801c480306004491005030b031a510300144415441065002c13072078000c002400580d0f001802403960f5040711501c41d80c0d02d03510044c080f88002c075000750b0303c80000c0c01070b0070f201c2c1072001c0500031441286c00d0043c40e000302034003510300d0201159402c42c0d42410004080d4000080081d023040c4c109424411341a60700d00341030001d0050702004148200040d90b980c036100250b80040c1450b21150f140f803008100813038075204035100c40c0343c6459003001c0c151001c680f42c4000008500c07034110741400209001032a81c64901010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 854295440 1250 854294190 854294197
    0x61b03022a07030605010b07021c052d01140612030408120711040203090609160f03020f061b0c1807020d0804050708011409010c0e090a02210117100b01090308 70
    0x241ca07034070a5140c040300040e0325210b40c6000e003c1c03020000d41c83d901c41d03104114880b14441091032840c1d0a0340b443d400080d10018643c02d1700c1e0055400a0000007407285c0542d0f404c0003941c1501032035030808044d42801c15425102a024400607905030800e00d40800e40340340e40384203500ca904084e13800000b01c03403000e2042601504032648903600103440c008110b0009810fa03001550380c076500e0b402003428011038280c200211175000500e0154029060319004e00341d455080c075440040e00481e0448440d49040d03072014111011400261400d41014112107101940c40246030000f0740111660005000041d555121403032090072660b00916151100c500c0c1107401d694058001c03901442203002c04030300e151080c0503000c1e41307d00e0310340c420805180403642c00382034074186030b03c50041c89882940303410710303440310150306070722050b40400569920412035807682844052003001c901c1140550000c43c003056800e61007140c031001c19044401a44901200c001250303111007c29010070803441341000000c01000c042c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 854296690 1250 854295440 854295517
    0xa020304050406082a06120c070c03120801050d111e060313031701030206070b0702030702190302101437030207052103150d0f061b0302 60
    0x19a03040c169a14042001e948070358002026036080030b82d15080300ca243c022401382c07811207071300f1101180840c400450743e03501c15010f142480c00154400100402401811101305550144401d424540e40f400e101d00c04540c64810300c4002481400000740500e0411510005990032280c004040e459400c2004044c810405101c14500c182000141090341c0d103501641c0720741c008a4414002c4121460002c03d1411444407a01d400c030700080c01840541c90b083c2c155a4815840b07181240540c540c020f00764618020840c0080d84403443d24886940382d1240c2041c1021a8403c1c0c514010328100040c003031b07541c01022000405210320a001c40c545e000500c2d41c0510b0745182d0000000c100c180350103019001c001440d1036030400310307800050b4070040000400050841c40800800026050107030f42030700403684000713070a000700f070908100701c0200e65950254000d50b1310b40c0442d05071500300c1640f52003005021828800000924400080e40d0000d01130700803074010005114640d1030300031107085080e0150240700d84 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 854297940 1250 854296690 854296693
    0x90e19050c3f0a0b010e06040606091508060a0305100207030e030109120e01030f0f0204031a1612020d050f091b01080105060c01060b03010b0c0c0625060f0c1814150a02 74
    0x3140104202c040c00078007912241b13240f10604e1501200b40015642503610800030000c40f400104600803009500c07040003900d51501c105680c0f25a0005681682981c0001d442409400e20071529041d01360b0047ca8214405d45981003101c00c0c40f010142259503407038014107903400701d00c01c94030100d102d11702500c240c8030141400942d00e080d45d0305040131104134030039101c1c1183e0300180520030b01c41c002d0000448104080c04402182c581b40151101c5d89000c800c001c018410003050220043c1903a0f0151510912609810000c510f030410504075296419280ca00150240e400b0a104208044800b2050a070040e1641801646800c0500810b580040407200c03065584210100e03a07031034000c0c0154001c01c5240c244684450038499801e04100107089000d100e03040c10804842400350503210302640845021818103d100103080400107800c800140e902e0a920b01000064016004102e12056100005800401e42d484005005101d49912103a0750b0241100b04902d0034611818000e1000300f04910 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 854299190 1250 854297940 854297953
    0xd050a020f0406080402030f0a030f050c0c060d2901050a0e0f03010501241d041e050c0c1c0c02090907080a030c030201050916090e19050c3f 62
    0x40104101ea006504050300081c469010300056250030010151411280c501405e51122155009040c4280c10101171051010200710302d0000e0505010000540390301400503551a20b0013846a0000d01c00f44000403503103114a0034134089011080f281041400d81a15803034034003900e0007400d5400401d01d41440d80d00c42d98101000324551402c1c0610b500030034a00700c8896488548501c03134035030b049501404804100041000c164449a03812805240240035200054034040086150084a04d0100280c41e15820282400b54020544009041c41e6082009480b500980c0da0024882c60030015440c10002e403041c0304810152414103441754000265008850565658107102c03030038140001400d50100da512074800042c190203000700c1d94440400c0000d002c0a0303e00304032507003608501d40a0114503c1e038680c619421040104943e019014900725040e030038a03194600300b0340d2102c000c0c000d1070140c0c20707080d00b00180b0035103414803002c4c0407180301a2403035a902c2c10f00e00c0000c11010000b89400da03c22107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 854300440 1250 854299190 854299207
    0x609040207140d0924080f0a02130803031b18091e0a0207020a0e25110115080f06010b07150b0603090709060b0c0601150509060a0c0b010f0b0d050a02 66
    0x100f1401d00c00070140d88416050615107140004007605003614000461040391104050a600030b003001d034845242c040c10040340e00c400060400030b001d042d0f0024103c00648070089648130000016620405103584201c0d8180150208001d042c000e51103005e03030820b60403219510754642030001d41e920641c882810903000350b0000c510312280d44103032040c4440c164000385803801e604002c5c904001a001054600580b41056030119004220311500d01c020138043c124500c41941c41503015030030340d60500c0d0082c040018590039040482482d0300c0f4181c0c46108000c4406551000824498100c030b4580319076034101a0f040d05d902c2c05105e69600341c050740582c2c0e10068a665500c00340514052500d034401000d08500300a4101704032800e54014407840703141807003440200c060004190b030540c1c9000c05108030002c030100c03003510240507914240f1b87c402000b2600e00d606a0340300c641040040d0180421015076681c440003440404018059180e04801c100b2031001c51000c2034200340c0d0418000c000061804408 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 854301690 1250 854300440 854300443
    0x203190e0310050609060409080901030b0a09140a1b020607050d15030f12111b04200c060a1505040911040e0f5b0506010f030902060904020714 63
    0x2c070240c00e60060380d52024400b441c10001481c0da0f01480c244d40401841c403842d01d0300c4480d40a0300442c90b0405840d0294010a51204685a001041205004d00c50b403694601d110003c2342c8211802549540303407024201000c1c164201843d0309501b00d802070071a13a1200c48040b0f0780d546c405108400519100c0f0304260120404d144100700850242052081c100a0352920420050f4269183d0003000070243c3c060300d0359500420052112801c0c2d0f10001d01c0c0181220104015080d000311024200a82060741920780b40e2101c02011800c0c002c1080d1409659007010200880d8145d905003103440112101c01c0c401820161301138860070f4002e1290280700ca80070f900142c1079071100759080c030058210826820940c5000c000d5088009454201200146115000840d2a0400f100c0412000b940703658000005070b10303200107107410040004141102d000c1600daa1002d000d040d0f40e03007800505034000106540744603104522100f43d00602c440c0c9082031040c100006500094002e50b806c40f01c1044e00d4800080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 854302940 1250 854301690 854301703
    0x1030807050f120705210d021305030a240e0319021906020915030112020f06040801051005010e030c1806030316110a21030f0e0301090c031101050a0203190e03 70
    0x603443e030280d584076203901c0e10382e00b84008000c01d0104204c41c001c1c00c1524a1002007941c5403a100e88000503140c004000d403006004200c2d602c02c0b5014007035140c03c0001e211100c601144d0200000307a49010182d107145641046a811400707000c4a904207105a060009602c5018910903540784101c610005e03104003040c6500c254840c0c2203542c5580001e181406051403100c050038070703500d511400c0c02c640c9003000c600c0442c2a0210b00074810a0185410a905d80e217100c01d5501900c01e6000800440c42d000c100030007400c199001e03036070110707610b4030440281c2e140000e0074540c80c01002d00804004004481d401c54240c0000e00181e40c18002484680e40c1c0525a0070714225107070003098004922801071003405400d0300305800030000d2801003075421001400000c24a0007465061610424060a00b4001c881e40103552210340e40c15401c05c503041090100760300c2d4040503240034248004c40b00100c1d400545080c41000401c40c0541c0042c070004150070007465446080100742d007001c00038a80c2c03403c00682402d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 854304190 1250 854302940 854302963
    0x10c02030f0a0605010807050307031203020c072903062d030d090e0702010c020325020a080109110603161d0a1e06020102040321030e010e0703110901030b01030807050f 74
    0x3440082c41c01d00b030080c680181da0040107084d001d0300d40701e428040400e40780c41c0540805840d0406100705192003c0c4268100e0344620800019030342c0068440301410800c100028462140101a01806140c141814126402288024000c800c80b10315018000a0440c504181c203103910042150000f51307403410312480740611040d03614074100740d040510a566042d80548070008581c9407119503070849400000311039890511004101400c0700c1c0c20410340790000d02e44002904171103081c0000403e928150000800e0f944a031503852488a0f450003449001e0204480150340708001e0203560105900510040c0080c3c1d114441c050340801d14100403800c20b401c40c3c1d00440d40b40c0e1a161106200c48010340f448400350402d44003d503d010f01d0340d1100280b01d003590760610700f0b06280ea04044c0e50b0340e00a03440062050a01c078003d12a4010b0150055110040c0c4d01c02910104441142040285000d0b4034940c10390758000c00e0319849034219114451076820800c0120355510800c41c1341e0030501313410070100c0c0c50340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 854305440 1250 854304190 854304193
    0xb0a110c060c0a0b0a0e0d051c0912020d0e1338030714060318160312020c011b060c02120d06030c15021015030204060b09010833010c02030f 62
    0x207245070f00e0584c03051000180001e107003500d44150b481101401288848103080300c1d20786540c0340c44240040b20500e06004030a014141d280076080805c101e01031101000082881c0c080e40d820307482c00a401d0f104c400107650400e81c050310440110200c1c080341d030b000c440e80d070106440c0310038111000e840b40c0d8501d0b01c1480717103210720001100216200345010010344014007001c10800100900c1d000125649010190041202c080303801c1c40c6074440e10081014605031240040a80d0f4503917528180001c10803888510003005025030468100340394014142081c04c44620314620130414400e0310b645c4024854420107608600406e481d59140c000414094008006c40c508002200303440d40c0703400c84060742c05510080c6242d00321100141d2080e0007150300385092000500108528180320a107450000554000a61092030100045407011100000e841c15179002e0700c42c0d0899466860111221010840501c94182500e0000c00314444030034103600a00c01e01030504d920b0a842d40e03400039090250017500c500e0036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 854306690 1250 854305440 854305453
    0x803010503072102040b010309020d060c14091e15070c0f210204050910110d0c0c0f080d0f090b070e0109051005070512040f0911040b0a110c060c 64
    0x294039050010000618104404507203c0d075544000c0010a6184107020780325940d50034880c030301a402908003131748042c0d005004007044800d61812500034108458035500049a0300c111a21801c904801c80d102078800409402e001c02c4402007000344503d000101d5a000a6101800c01b41c8a1201018141070f6100f40810040603041c000f540c210440c0507807110800840001c0e5000e0305c5020300e404808a141c0580c0c010855a540d144000c1c0742201200c820f05001c0d14068020511202c020302400c1c142c0c0b000c5606000460300c0390011650071200490241170240b01180ca080080c08090041c80d041c030041c00c01195400000050a04a0703a600341700741c2c0c903480741d0010041c10940c407090381d21440c0424200505010304001c003080c516200d0809800a00c1400600c40062044c10422a0100514030358042d6546484071410703011030b0300911440a000d0b040c91501504400c216040c4c0d01910003002c466810200141d20031100c0c0020401030038498000c82181e00760580700d1400031b2180740da01c2d2006050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 854307940 1250 854306690 854306699
    0x1209030a030e03070c030f02030a021e010306120206031f0510050a020d0801150c0501020c0d090806010e04052a181801060509060f0310230c0c061b04030f080301 71
    0x555240ba404001190410485100001c00ca106080103981d0000303550425007040d440403d25100e0005070180d4060340d45d054940304407000d2800407603071141c20390f010b101c0c46944042c08218404c1408009500040a0001507020b500400d070036200c000001c40a00c03951603880e00410050300300d100305000040d100240076a2903540420a074507441010f490030b20401e40c94012440700408141c80c0e2003081155000d500002e004094041d00c0000b80c2400c150f803044903624902078003d130b506104444281c013030303800000f5041701c880000d18896a0480c01401d20305100c41d00810083c410812851540341c01134030241d065844100b10740c22203804200c503101050a1800240c50410462500c41c10141c0c1080b0040c403241e1a01d2981540089080d01c8603d442092400002e0030800340a10100c0041d10705810406210b00103010580e100c00007108585840d00da141100300c107031188241c0700b01c4991040c0042505510041700f0505940d0080341c9842c206520307540ca02080d003000d0141954840c001000610 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 854309190 1250 854307940 854307947
    0x7082508041e030f08150a0803031005100801090c09260f01061a07021516021927060f230d0309060c1e0503030a2d111209030a 56
    0x4440300001114103600410a54004101c9900400d01d90700300611000440d02e0301d6405c07200724840c1c03032005204907c5691540101941c0c1e8200322041c4500c4d4031a41800615030801d40303c1003a81e041140c0d5011226800c07c074040010b0502d0842c643e0030403000a500003070256540c214078600160f200c150301001c1040550003860040300b142c412082c2d901d405070400c80005001d00d000e588001c400c44894032081d4500000d400908280c00e070a03549c40000540b40280f849086100000c0742c4225010680d0450030204580d00707901038000d808903100c15044c1c03c500000320b0480341056200222020a29603200c1d501c40764102002e600c640200910329420040094264505201c0c000c0144c400d0341e030070445904c00500340d40203841008203208100c3d19a000740941040c0300ba02030f140018030340c100540240317010303a526440ac40703841240b6131814801654480d8892805c50303021200c4420b9802140000060340c0003003640b0f40c84241c2000080003030301c0e540c2c0ca40c0c0701c5c4607106101d98000340d500c07440d50001c0907 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 854310440 1250 854309190 854309213
    0x703020d0810090f0603060c11060709030f02040504020d02120d0806030120071403030f011701050709150915081905100b07050f011a03010c0809060708250804 70
    0x400d0000c2182007102e0454415200710031280c40c500b020514110400090b03000b0f000a070806052141064101d07400d864029806810266018040313850710b5407014400c803107071010b030f000040c0741510106d40c41015203440d8110a4003e40010a0391903100403560001c2d604d003005c070300c0402107038002010903e180c940003800d2070790002050b4000c2c440403140d80c400090310344074020ad00e19021404a100024000340d0aa20001c8040c40d00459584c0d0400d01a540c03107120091260480e01c829810380c50007081018080d00740078000d0f9444051000c0e0a1901c0070b0140c4010b400e0240412135081c1000480303804d2801e44411001450701d4100082c10318140040b80d8607a001c0c89051102c0c103040520440d058024600c0044400d0441d50076100c14251500c182440020303003111100d903090090040382d0101c4841100c40461088000300300e0f90103083c10544d12000c0485022007242c00190003e140b0070700400040394801030010085060356145804d16400000e02444c81000030f4000301000100301d0a078006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 854311690 1250 854310440 854310463
    0x50a020c0a14040b040b03030901230403050705150a140a0c0b0f0f090703051f0212070207050f030f190c0e01030b04050c090609191e090c0f0b0d0b010c06020f070302 73
    0x92001c03810f00000320b660389c450601d1040c1000013505101d01060184807603c0581d182000343e031655650369080c0656150094000c03184035402d044070f440d409603041070450b01310320601d4642c01c0c2e200d410300a04c48415000b40007500103001d03000c0300240004d00c104007c64890505251b510006007400b001c1f001292038024070a9450b58004c450510104400040c210f01c0441e648005150044203075110748064051102152002e45419062185c0a9000b04070842601c07000d48401540100c6c1ca81007540d44c0780c860356558240d422085001011400d060540303000180034003031a1400310ba44041c0483c10500983c410754140c05410140400c020003403060728006c1c0b108036040070741d43c280b900014410130b1019018442d100384240c8105441c2a00750007036207000450f0242031080c400d040c1074440c054090716108841c1c0f88600040803810303030410302d03248065491410200c0e04040082c0c4604000704103408200703040c80080011140090000d00052030b5165040b03c44584820062174042d03e4010003288 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 854312940 1250 854311690 854311699
    0x70501060f08150718030501050910051501051303020d08030708091501120c0302030105090c1203040e0601140d050a0614010903030e01030c140a030c120b030c01050a020c0a14040b 79
    0xa0030002c14400003490140100d0a420310061030319280700c140d5407021032840550b0141074503a000424410f043d4071080c42014820284c0c0c030aa000500c0784000c072001102c6802c4840c0d5034500c09405940f141d809002c1c0399000c8800000303495200c0c2c00061021401400844000c1d0001040048076a4800080360304000480024241046404071141d140001401541c0124020304041020b001c600300b0000000c1d50090001c010f142071100c0c0058440706028031083c09102c004a90b200700320400821101150010a00e280094072140011503d4114000c10411804030a000144403d0401e00c29035016209803480001c40341c3c60900041d9078011101489414047c3c08217040000c680c02905902c0d4181003444d000400d07440030001a80c04080c004100c07504900c000c40c4020b07800750940c0c041c1c60742d8101501c5541d081302000410b030040c3e0b8142d50085415410070036002d0b0455000d00003030500b10b000c0d80103540a40308103c005c1243d00d0f1040c1c0c4000190310041618001c1810b141c070a00145040540c6e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 854314190 1250 854312940 854312969
    0x1031101090b0c070b0f1b01020a140403050a0201080c0712051b011404030503180303011202041b050a030c1b030e0913080304020907030902150705010606111b040f06090207050106 79
    0xc10f03500d40219201e01094000000760303180e0039030b03d220b00b2607030500c04415907400510862000a8000c1d0441c078a03100219002c3c0311810000c1c2c45420545044960000050206014945c01100d111501812908540c4010b0042000040301c106d0000d54810341c9a8505480390101d41102e520402c10400a20340ea03450074190500031240e00000942c002d803d0705080c0ea9a4a5201e00c8058000b1001c4031030b800fa00001c0b0000c14446032084020a0070340c02190309100c0b0300d2104003d25400702100b030315200411410014480401c5c000c3e00030400c2c0040342c0c10410001c03246140121301003035036030008400180c000c4500a0041c500900a5900b00c07144420321103100c0a01e03685c00c020b0313200142c0064440c8000030300240c591407107600400c1603581d0140c150458004040d40c0c1e401e01c1d801070103085900d9400d01c41c0200d034181c031801008c41e20202d518000c0888107074000350610108201d0501d40c1c0c000703888100042071170711940a00c00080c942c1d101c1c016580c40403405e28600312003a40d04090300421250 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 854315440 1250 854314190 854314207
    0x1020c011e0c02030f0a15060b04080703030f03090606032406150e030c040914010b03030f030a020a0c08270f01301107122c130501031101090b 63
    0xe1103081180c1c00d18100380c9064102400001d160889600100400f40715006c408000c0154804200000081c05032017400b1640d05c3c0e40070038840740510302800186611054081021038460764400e444502e480c10001a422100d444810943d03c140c0c1050303801d85101c904900c07001a40c208004d4507251300800402c00d60342450000074103240c02c203100310200320107603504c51083d580a015048403404010000c20203c04d20f441d2040400d581d8800c0b50499501c1d05590408a040110895248482c0c541380700b4a15a00d84050b04002d4009a41072004c108400b00000c002032100c0c001030251030700c83e02c1e000c11030491109a40010203012034505009803a215250b104c141d0304160f03260302e56424600729980314250101070800c03007038a0102c0d5000d91400c045002410102c68001462510f008100328459407910104c20b07a0746081466481c00480c2082401180403090711810001c0110700414090002014126820940744280c1050340c4004844a850070035681200c4440c00510180b0545410881708 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 854316546 1106 854315440 854315477
    0x60e0d020c01020d08090a02040e010902030d02031c2328020403030806060a080f090a02030f03120f010f0b09040906020a020a0c05121002160b01030b0601020c01 71
    0x2000004d4100c00d100c3c03031000c1c3c80b410146000b0300000728580d080c0001004040c0c05140e01e95625511100140d0703042c0076209489049078021030300d850b40303511010b04132110301c2c0c009180d030b41c40c0c41540d02e24100800410f0740e400f00d44a03010605a658140441c0d800350b49003142c240d184280c441540305821441d80980f0640340030f6961031207140d03a104148201b074403070203a4120104101c1400550201030107204030750b01c039040c0c40c25a07807808519800311f850700c404400c11506c42d800c045001c0c03c0c1030044000140c0e0003c144038092015500d0300a40f8980703196180039500164800144114840e00e4682041801c298801411969084803140c020345417a1180c40c1180c3c02000c0002c00149031800b000c840000c0c1c60307004042c4c001c0c007400c0071200380203500c600c1c0703552124850540e0f040045185681c403140290700420403d451441c00f00002414041d01c1e0103000e040c42800c18107801800f84 = true := by decide +kernel

theorem cover : BRFrame.Cov 854136690 854316546 := by
  have h0 := BRFrame.cov_init 854136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 854136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 854136690 ≤ n) (h2 : n < 854316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
