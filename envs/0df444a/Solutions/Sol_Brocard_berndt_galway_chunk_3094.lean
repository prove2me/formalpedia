-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:47.809533+00:00
-- url     : https://prove2.me/submissions/6117856b-4860-4d75-a934-157fbf8a52c1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 556294964 ≤ n < 556474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 556296214 1250 556294964 556295009
    0x120411030118021f11030c0307031e02070504050c16051b15044506050d0b0c0c0a05151005010c121d06040311100306121515082104 58
    0x4014072204c01800700d007032104481c140041018045820b1824011507540300141009001c0308001016510201c010380c02640700b107a80420f150b02180c10030f44001c21282c03a0300748850441d01910100090400304200f014042c021300140c01d2503001420420891710240d1403060026902089112400f560010001002561204042d1104202c070b661741020301100034800c908850000714500a1110454400f0001c0300000b51166034000c1c40101c640d880c440d401c40c0d4402c1400c00006100c00d0800c00c02043ca800b0101c0280099450958071070700707480855004400032903500c041035600010b61400780902040e194001e85240c9441e0f900b0900c6009100314040003168141000e013441c061507181c2000c29460b03511420081c0c000f852090380a410000007101c00e008503924000540c008241c00c00c401000f0707540002820521154002040c070b0040c000c207880c41805024550440c040243c480c034400940c8031004154408002c00301002845040005402010349005600410305513003600d140190944 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 556297464 1250 556296214 556296259
    0x6080f03160f060507020a0c0b04050f040b190b07120e01140306040b0604080f060604050402150705030f160b0a0b03030d090c1203020f24070c0812041103011802 71
    0x21803003418a0344a031141c41c3c0d01c60055400a451080240e8001805417081150010440d030290540040139800c01d860040011a150032144085025540e2044030b010291150034a0a0981a94011880c0c02e540d840d1100e20141c0d000d55416921080215107041600f071040c04610800d000503900d8a02d0486420140e0902e940301170081c0754850f0740ca08000b48180c0300c80014100402c1d20034064154030407000540307400c203a401060103104070b20300010400142d40d080a4502580c88540d11a9116000b0b0314116182d4440c21544601021001c613113a000c61101e944001c29051068201c500540c440032600e000b51000065402d0341508180045510000320b9400107180a000380c080201c840c0c0e0704c603443c58141d0384101c010b4006030048100003107164010080d0301c816807800344101c1c038480e04200d4509140303000030b8000000c100f80380c0c40d41014045c5100c01d0303540e49007820144081a041c1454203403000a8200807190207542040590280401e4800d608007281d0b0b0080d000c410000540700d07044490303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 556298714 1250 556297464 556297507
    0x7020405090319030e010606030b1c03090f0b0703260f102d0b0a050a050a030b030102120402040c05040506030604050a180b0708102111180a06080f03 66
    0x1d03403000f4841100c01e6064460484055031080d100040c89211007500039095401d250806030900d0b0030070703440035525190920050103507c0112201c00280d0550319045906805030b41c4810840415080081200d0340c045009003500f511940b00c80d4001300882c00e08440c6070590720b003400020950200001c21a207403280c8100e03440a442c10500300e405403185505800c45141030441892040c0c039414403144140e03200c3e203000c09045070011050801080b0035004010380310349030b100c008001011540c0341130203000303030000301a40c0e0000b40295101e0542000c0c1103032481043310185d2190b403c00800c1e04225004404a03000e841000c1d0180f8550f40e1881c080c00060701c8050850746a169540d46010380c0303801c1d400441e200151255002401c107045c0300200030401c0340c014050350042c2c0386552080222107400b500d000d42c1c08920a0b030b59180d20415003010480511303010801500440e29a0640c41d1081d491980140302e5140941c040100c0f40d20b8a0650b07540b650360800a90702030f4820010090f0030f49807600f18505 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 556299964 1250 556298714 556298731
    0x16030c020c0415030c1208030705090406050a0e04030e0910050132030708070e180618100e011a0702012106090207120206221a0907030215090607020405 67
    0x350000c0c001c50300b168003050801882c00f404410600400c008091007038000d021428040240e04000d4444400d40d110291684080c00f000203039500d602e441e150040802009c0090036007400554440c0c2400584004541c111b000030007540028006241c2200001c0c06040058054245e80b400d240054803184031480c0c0010540d80070071403003410050040c04034032001200c8401d55840342003c107001b815030707000035003810144901442c8a5400b61a14404610142c078200c1980080303031602c5002c00d80b030611340d400c800c0c2500040010803603040300c03020300701007111010804030103260f9071028011583e0030020181c03622004100b2208015620401e0784c038a0b01d01c040006492461000c41c1200100c030707011350040c1d91054010410f0818040484000103468140740040d1009140441840790518000c031515811340001c404c0d82d17418008642081d030242e42c0031042d691114207207881c620740d4502d038500c42284101c1260714117001d105c40c210252800740c01d02500c8981411156802c103c05044010483c1a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 556301214 1250 556299964 556299973
    0xf070302131a0705060f070e090c07060e06180601081507020f0a030c0201030501060534020303070f0c1d0601142503090803090105040905040201110a0c050103050f16030c02 76
    0x1800d80351902c2c03411418914140015030314000c41c50301d182814002858400101001e10800c00000d4102c020441c1511045420607001e1b0754540b41a040c60013100c0019007681e1401014040c0038070700007025801070010307003400300620300040000d0350317181c000340140102c40e00000030301c2900e00c2e500d100140c0c0291480c01034801244034000d44c2460070008038820f07070008503844c441d50300303550f054030426025140714a00319251242c00f4181002c403d8000c24000c0d1420408014074105a411802d80f241c078550081c10340c0c0d62141c4600700042c290918400c151619841c1d60000520711110240e6000300b05004840d0036226070b40c480041d59039982035000d14508010401c86401c8465601800100c40c030380e0030500002565103070030020440d1509070403881580e4401c104101341f44ea08203058504031a0740f0400881e00303a40e24801240d0905210006008074170941900b1400c0109200000c0144c03402079070100242d42c1d500009500701442540c089842e420355210140003503108e9048a0070454880c01101c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 556302464 1250 556301214 556301219
    0x803191b06020d11030103050a14010b060d1b2d0c02090405060f060105090a090b0d0c08030a0f0215060105030417031303020f0f2d120307170f07030213 67
    0x300210030000104031062540011204080350440c0708407030320001001500c904540c1141c1d2920b98820030142d01402400d9425071580c0e90003401d400410040101404090316609020352290203040f0b00215141500305084440e00e0903032145420340c04035008020614110500003503852618042441d254040082c60503071303040075071500c0081600851055004041a181041080d05642c101400351350400c04100110380d42969085507210030303500c04c41e0000910000d44000a40002041e01e40240710659400c4001118640800640b2003602107451701018450306140c12a1100c07204501950760150400105480e9481100a158098880c40890032012070200e40050b2541048800b03281030803030107d4000c20184d0601210420f40141e000410482004c252000d480d243c0383d051240e4890103c64180c0c00e10707007011501205660980080d6000580207070159244d641c0300716001070200c0c07115442607108018204019204403005803022000d52500a002c0307000c0d500c0b4205500300c406211001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 556303714 1250 556302464 556302497
    0x7110c0307122a152309040b01092907060914060f0c07080c0a050109110a0605040806070305071e02070302010824010305090312010b0304030f1404031b0308030a051f080319 76
    0x51720504142074002c50b489074007100c204415180700e054680d041042c09802004061140010300b0080010300e0050b43e500840c0001c0e900d014001c1c82d0000e0300d10713800d004000051180c90101c2a43e0400e07440f05031822a07440900412200c5000d841c500840380702081404081380c00500507040003100442601c08283c51910360900f0740c1d100c03030b0b02600c01e140302401c45000703882d00200b818010101414020f04003450080c4854480000400c03030f40c141074035200040c000c80c4c40781c14a5000062419070301d4200d1190a08002d5075181c03240400c81c00b06a046012032590310754500341c5507200d41c03101c0c1d005800015001c01100031342005805034003d13100503c0402d010040700412180608008000c10307840e031403d410000c10082c003030010b100602100390800b50030254010b04031000c5e0703a0080060f0032a000303096450403018190381e101900084022040c0100e80d0001d4120341e009408030f90345a62440c205d26a40101c000c01482170b04020b6000300300c05c2c020b028080301101001c8a1a0501410411300360a8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 556304964 1250 556303714 556303757
    0x503070206071e0c09060501020a03020a1e1211120405030307030e130e06090c09040b0c0a12020a030c02010f0e070e0a091e060c0804030807110c0307122a15 69
    0x2ca0b0841c444030000c5c014000c1174440c101c0102403d200909810341c0301d881c0a034560b0807410019207002c03044925000c01c0d968001c5070300034243d448070528120b44e854142c02080b4400402d092039a40c0550401c02a105072110141d50a0b540024059031600103585e030180da800603405595a0440c4402c2074002405505120f1103441080c00c0000d866503261064401e81054402c10440e4408c11002d800d00c40803504090289920251122802d0740d11315003000c050300c03c2088100280f50071800000c0d80070020364540c00c100c1076800260024400000015a00c5e070135a40781c2e004142650384509401c01c65134080941031604111003510000744000c854481d11401c00100c1d140c41042c040340c140500400c0072a00c5110104440303031824820b40d0030f00e541c004000b1035014005404004100200240c00c84c3c1c284011804400020202d49103217950f000e1180c04600c0388001030b20700800750341e580042e1142c40b17440002c40481401c480000365003070a01c1d689515082002c11400c005001c6816246540f4005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 556306214 1250 556304964 556305023
    0x70b0c0c0c01180b0d060b2b05151e1c02032407050703030603020604092a020304050d060e0601060e0406080c030a0615080118060c050c060703021b1203040b090703050307020607 78
    0x1032600041c9840c000d0750945036230901112090462500040010060307080c0c10b200c1c044c1504445043c0800c061088904c103155042c10045d50003070309048d441c0381901050650460451081e000d640d003218900b0480c042d003d90100200319590101c0000460325440382d801400d41c68442d050008815899402040e25900607030008500c240e91461065003842d0b102c0c01105034120f90808000150031041d4009440b1b004511481d8010701001c41d4020800c0413a41040403420071501c1104d65941e51100020880c48008001500813440e100c4041481071000ca80600c101c040600280341074030655490a0060038640031001c80e100e98004081030128003800703440b009201182c4400e41b407a00350704001e07088404141d41042400020070001043c1310020605680c40301c6181001a203426124030030300340c8801821502e070000c0c06945035080b120481d0380050360140c1c0c0214001c64455680d0200036a462800f400098034642c07041c08200c0c01407400c00b0003403812a100c0c425000302c001000201c0034003c4510b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 556307464 1250 556306214 556306237
    0x14030c0301170304060e01050315060313110a0509040f1b080a060605040207121d12010905070503150c0a0e04051905161d06070b0c0c0c01180b0d060b 66
    0xc010000c2921401d081c200b41c4071408051032805142081c05040c1003134040b00707981400000700029417030700c15650f5801400d60000c1d05c40c3d07589c0e01c0c2c040885103184415540490f20f2900704682c40748903042c04040c44007a268042d00e840001e03103690701c0e40d03401c1030048941202e01c00d4404603100400164038203444001e00b0700310000c00d02c00c0b50602d016020f4880d01c0d0012303801580306100c0e00c0f0202d0a5800c011701c55034406d003010b1043d081c03085e0702c4000da40d102c00d889580210b450000700015180540c03280341c035280220b0580c5d01042c1c03114101622855103c0520040c00800380105500119880040c000e8180744e050143c200071203100401c095410850b06441d070703038036005855400d0980600038a80c1c007400c08600c6005420314920060500361032031488003a1181d00280a0105807100012a1540e1750010000c10355450b000490304500d51140792030510314044c00c1c80700729440d4095218141205040d0403058400c50a06602c504a40c201c0c1008188040d191000060708020490040c082c10496 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 556308714 1250 556307464 556307467
    0x618030c2105030f0907050a0b180906060a11030c010c0507290a0f09081317030403080714010b0d050102130b040f060f020307140105150405040b01060e0114030c 71
    0x16050541c10400440c50810000000200c05226154410100c9520050341181c4829586400340c2e40703850250103820042e08061400c10219007030720500042c1800104101da12008490100c0c1400510702c0241d8515800c14000d010704031185009024540e800007220044900b04180d4140460940700b040c20301c0d102084001580c80103021110030352018011202503d16501c0c031485110b041c1804c0c00a22000581e40e1365054000c0c681d0340c035003020314918bc00c00d07022611103c0c00c0b0309611502400d48118031440054091740c00807414003005442c1140c1d005101c0710309045058841000d031100c0883c80000d25540e070344090480369501d000c1e6080715401034000680b81c61030004808200fa20704e4118446821060101300046d000c3c4184010a403031040c81d2081b0144c4c00054113a2550049580043c5100c40c40d20203041d10303120551003507119045e00720310b800304508031a05000480c0e500380d40240008404030300603c1010300848041907003010614100e41500c0414640c0e865541040d600c00229260 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 556309964 1250 556308714 556308737
    0xf0105010807020309090c0c0a060203180d020a080702010323040327080a06090302120304110102010f020a08150a0b22050a0f141309081309021c09061803 68
    0xa000100e540c2c4018980029894842e61500141040b5002402618001c80c0000c3c2e51110134030a1002813521640440309544074102080102440c200b1428001c2c0d0520030111003500045c80082d0000d441c540203500a403400c0002d030011800742454180102c00364001080c0f60100d48511880944901d0095032514070b1030046d080c843c040c084214105004190710a5000e120b40c82c0045003100755903a0240000030340310684d05e410781c201004c420102503094004000c0006000d007108618031501001d0b0300030425002c184032180d040740901001540020806000250b480741c220240404420008000d481102e40d509075603009940240d080c1e49580490107108010508040720581c080c140c21107004c1d5015003450450309007080389100b01040703041c640041b084181c07a1051040140c00040c401809020190b0406445d6075000c10003000b000000d4210004110b84075100f9510061080c200c00000300e148000303c400580848402a19043d582c0c1040b1135041c0c0c40d010341102010312a480e506410304 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 556311214 1250 556309964 556309967
    0x5030118090b1302130e030405130e0d051e0a0c14070e10080610120f170d0c1d1011070513050105030607020a0807020d03050d0e060a0c020718180b0f010501 69
    0x2c1205a80d4045c14105400004c5401011080e1011344400345e549403803c03c110034051000d00700f007025000c401c0c007840c15005a041c5c0c4c0040100805c0c42c01030724042190701450448141e61181040e41000240c121407040d0004408100c441450745802044034407054841c0e00d9004c00d040c0541d10f401000f840f040041264041c140252035208101414119040e8544503509401c2c180c0f1100081001040d0010700c01000f00e020450320a441d82c000712162101d80c0209450004c0c114018900085204031308020302e0304009242c82d40c40d1510180103098410031958050b80d2000510760035204034050b600000c2815100c980d1030480f010742d544400b29103945005c0c00d1508042c0c0290508046400103100c1c03401090048044132601035068940c000c0794030150404682038003442c0b0024030a02c2c2002e07060850002d0001d602d601a6540803c208040340d14030509a030b8407103984c80340d4805109106502000c002c05075010f07100d14003001050300310380703c95075850011105042304c802c040d8103100b4005124a5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 556312464 1250 556311214 556311229
    0x8131b0603060815060928050c0304030908010c020d0f1b050123100b0711210f0a0203070e1008150a1a060904050403140703020f0607020d05030118090b1302 69
    0x8951404401413141000d0300412400030f0010001140006924150020341c010418900c0c0c0ca2480700004005905080d41212040d03401a60b007903001079011600170880d6403062040c560755000f207400421104400390780130754540c0030f002d0300c2e030040c4200c815040b1039403089001c01c0780c00391b842240006507189216649181d1088540c200f07269080c400320405c01030b942000040d00980300c072501e030251210b6661816a03503400c98068000e8000b040640e00740d0744042c0004038001d0304020703e801d4800c8400d140c00b0031a5500344952000c0e6040e404654200b041d40003050f40e00342c010031076044001606440e00055481c06460000ca62144800c1c0c1c810003050a1441c07140340080c40b0300002002807501001d000910a02a058145101d55a15400300e010180101c0f91080005000c081c00c80e1070b82010305000e51608040e045d91401c0340a0307a030000c4e003c0c074030201e01c485450041c2e0311018256402c2040d0464818030995500d140d032691201d448000c030701e032210614825500200e020010035903520510042 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 556313714 1250 556312464 556312483
    0x5010e0c01020303070e0d06020a03050612010c0c03080a1407050a0e0d02061b010f0510080106050d0f170409020706020415020c03190204060f1202010807080708131b06030608 77
    0x2540008561004507a4044200c0e07030041081c0c03034a0000d076052078002a0110041a5006240c144000340c807920858240c0c01c140e1052604640b190402e070340c25903a180c20b0f102101c0c254000201e01c0708650000038025030080d604101c44180005150300c10000d02100c0d48001d45222001c00c00101c2c106103c164042e01a0511032400d40e480e11038403c0c0c0c1d9001c200d41d40100c2c1031900e8192410300d800f54000c2070035400340c0610060303c0340510050030554400700315004103000d50959542000d40101d1941407006a42440c658041420313400d401203034480203000300c021385002081d100708010000710604140098515a4003400380184e41e1440e0070703640080b140103406c1400030354110056482c0300b580d001c00d2604035423000d59501003000c062840007030000e006541180550301d8000c030300429020101c0c480700114a200313880340d035965110503034207641d1003204840c180001190300c40091101c019001c40009117510901c00b1941c000c48100410801180d150040d80011b0380d90581088200f10400c0300408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 556314964 1250 556313714 556313741
    0x2040f0b0a15090308031806041203111303020d051c030b041802150c0316050a0308010f140f061b01090b06040908040b2a07031a0c0d090804051005070501 68
    0xd5008040c0e40605405060712000c0d011301c5d008000070b40e105128008880400550300251519483c103850006401e940c03401b0345400103485c201441c034034591080210b0343c00c0c000807950300080714030b135600300030031940a2081200c1c0c9000b0001c407101036003010040a0740c417000940300440e507184c040c41031104503014081c030071188002821500340035840340e000b4160300d8243c0c5030b0802e1b40c556100c1c12891840c0701d24620500a60140c02d1b0aa091140204000d0284e5100361784001d0305985e00d1312082c0082e00c0c03e028401400e0007440b41c0d0795a03441c080340940d944503000340540d81020320909410b0400c1c00c0d120f145448c0342e5140c460b070204110591034140d81c009400c80b4100100030980e05d07007251600540c0036041400400117450400e0324080c1e05030034110310722029002c184510345600d4649030a103510084030411543c5112a0364005600a22440b403c9818400713410407420035412800380507000030964250008020214968503481008060034100c2e071a00c035900c400601c4d28608503142c1400070b40c03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 556316214 1250 556314964 556314989
    0xd030207081e12120609040309050a08160906051810050901150e0111100504051005011e0b0909060418080d141e07120204240f0c0503041205030702040f0b0a 69
    0x101c82900141d0082e0041c3c0146d90320041641d5900d0305844040c405d41007581d1041c0030400008062900288040540000d600d0505620b80da6440e01004d4840300e005180e40b2914035404001800301128200341c0c084003c07010b8080c6c0941e240e011404010382a00a0301240c64030314241b607240d0750132580782c04000c40d080c6440c00c801d07140298855100e00180120500c5aa180d43c0402c05100702004228601c040d08041000301d540c0d00c541c3e40c400401c0c021850780c00100230220000e1650408070503504011800340c101c8101d541e8903002c01c002045000303540c4e4168104858a6004250150080c055410b90480b0028086030307003240c1d1860b01507000b4904c80c2d081c1e0300350b17001c0343d01d00e10000c8a00e900a0170034280400e101c10061184800381c0030700e0f04140310784640640d0700d1902904408142c00c41c0d011a4030344002c110b00a00341241e034410b4019001d08194800c03c0204241c10303500b03420600b818000c07010399040451a132700180950307500c0300200d90015160030300080c4a103400c44050b0000d001440304d45 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 556317464 1250 556316214 556316227
    0x41706070504051207051003091a0103020328061505010e06071a1305011a010e09090c01050a0c023f0a06090c03050109140106090b010e0d030207081e12 67
    0x302607100b80c1c00360f00c0c0035075070402d052500c24500b0820040a400000d250302c0d1103200d9040000d004040001d8180d0720751110f01c0c2d810007906014108541aa50041d024091544464050b0701d0030b0585844040712403004802d010300420350314400c0c60107841182c0c0480d9031742c030300d01000101030300301b1981301c1485640d04001200000700111000d80c0c84210342c440d10a229951180141904c0c03800034405880d41d4206000e281141d02100952851600240c0303a00020006140901c404000126070201c180e40c40385048548940c01030001d0818007016103424403c3c083d0700c2d0301103044011040511081007100c0c011480307209414a40f4460240302c811503424041ea485040c032547c80c00903480c00740215030b03540c2002080c01140760b0005d02440e0000002c1c4240c1e130551510203040f603310718040c00107510b03154002c5140e8274580919004414141e5845000d00c0301882000441102c9100c2101503205140b00010000018000300200411495a02642490340d031076031400c00c0c0821440f0500c80c1820000c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 556318714 1250 556317464 556317467
    0x702010204080c0904051e01150e06090f060316080709050702010c1403190c120b03010203060d03052a07090c0206070c03110f0709020a090e0114090406110f04170607 73
    0x80e050450040350704c8029505c4500b00242001100001d9041a00501040e4111208150445819a040b81d070210008c20341e9801e03400c5100c08181d48040d84880d004000c507003030000301c001c12600424002c00391100c3d80500045404480c20980c001d0380305800414041140c480b807486078641c00703082c500087c415a103041c00003c0c100c051088003c59010b8010002c00c0440380c0c6041207503000d80b0011420480c16244610142c40000c0240309002107908000034034645050600a582c020030015081c40302c810701b642d800b5180743c0c0116048054440510080399403208400c4180301c040b1203003801409a007070900300c0c40c1c02a1003104040d08195486001480201d81d8022180804550076207442650f03030f25400c4040e41086414070710481d007485200d6001c81e072059036a00400e004035454641e60200c43e591944c00500800034801d06008046415001d025400e0507441316034094803131072000483e80b40400f8882e915070402404202c40030800f0174180301501c4131540080d01c032545040100300500c0c3ca04070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 556319964 1250 556318714 556318723
    0x909151005030d0518041d100905120d1401090e0f070608060d030e030f160504052202063001081501030312020903030f0712080103110d11030604140105070201020408 73
    0x9005041180001c0c4172034070102c203110f10705224140200705001681404c0b500311075103002d4144102c03690040307918401b40901c1c5842011005548a806420700c0c0e92016071104468128540c026400c1d52121058102c2031140c190041c00fa102c61075001696400000e003480c43c022500142e80100d51050b0800e10001d9048900280d00403c1181c5506a06981e0314040741e41440c2c160b45141c140c81000040c3c00c9010001c00c60756141c12000c1440390420750f48070700300810b82d00f094460440c000020340301140954015900800003d0000d403c943c81d180640032203a1808080c01d800050000c5103030609002c190408400c640102032050082016034884054942e8041c010b00c001414440b00c00c01400103803101d5015548104001810f0340d072204400315000b03440c0c0d40005030468142521840c20f066103402071075018140c07500001e0768001852441c0500100040700941519000a8161840031a40d020000c1e0380c405e83c40ba1140b042210b044041190940320041c0c5190256401880144800c520028 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 556321214 1250 556319964 556319983
    0x22090b060d1505062d01030b0307030803041101050c07060e0310020423150a08161803060b060d0f02090f03120f0f0c0601030c0f0b180603040c05090915100503 70
    0xa8001515884010004824054800110010f005d80f40b01c1031099510986040c142800e003030b01d05210020082d0708041d240d401900004100700018404103000c210381c03406000f680a0181070407840c03c0303240903803a407409040740e01950000e40a1424030146040c2800300d180740c2040380c50190704082c14081030000716068144048a0220000a160015030700c022080c0c40c49180d004869648220780f580c001c6c00c05e24202d500203404c2c0200001c2d081440c2c413842d4810b05021000040c020814150396400300a4a80354280300d6000809202c4980a0f441074070a10004180c2d4000040c0c3e07544245060103c560328811419129030410004500c20034400310403100c95419441c071031a90361018560984450041140c040d81030b1103144000b000f0011041d00400c255080d110b848640035070799121113030592150740725005002d500304101030450300f402d201454005100d06180c2d40e0964a48001c10310400c2d084504c0c40c0d03164003c09400d180c10340c000e410a9000f11000d15000040c5040c04080b0b42e482041c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 556322464 1250 556321214 556321253
    0x5011b02010e130509010b0f0a15081b13090b0909031c02040e0108060103051209030a1509020d0b010f0501050304050c0d031e02010504230c04050622090b060d 70
    0x29014122554840c0b11403d001042100b0810080c145880e007140200007084583e4069a81400c2681c0380349000d04080341281e48090464413511000a0200d81c83c0d40060280560100001e9107000300220400c0602860750711b8044000c451882d04940905440300200b031540203182e0311043c0186000080b049501413030f5140343c1c090040c028080b41c90024401c5074062001c0d030345060700200c5c0020000c501c42d81241d01a204a58440700009068481c0c1c1c8550405c007a8103511040c41800080ca02012410202c1c1810344006028841a0042091612032080880e0719401d00390050114000600c0144080c105c00c1c40c000d070462620b5a40d00e980c40100080c181d10651b00000210100751145800100040c8140c0c80c442d0a056810006400307410705982c1210764101c40060f240213100003d012140c0103241c0001003154a184409020040502508680c0c002c502c0e202075200144e02c0c210292504c22418000180d0541a0704002109180140241c0d1090324121083c1d000704091084460103403050703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 556323714 1250 556322464 556322477
    0x606040c171b04090501092003150d02040f0e01090510020a02070302150705100c0e0108090d08370509010203040b040b22060b0405010f150e040b1503010f05011b0201 73
    0xe8420b29869030003240c3c48008803038240400490051201d80250710f0400c004041d4650f41d08003565883e095000459041e01c00340300244055200e89408484a9151800500001020602c0500e194241d03058403103088030b0340c0e440c1c241c00b03010010104221074120680316411810590300d0340009403114001e10020307104041c50100c925030203840104440804d68080c080f5a50085100102805032111602c490301103481103080c0c00300c0354080e0841600c1246031394081d000f200d9aaa900b640c007414054048042e851036040000003855514088000207940e0560b5403d003400300440d40d000780c1c2c0c002403682c201030340103006000000ea1207a0a0030740082e44002400081d17940d1000000740051100740086244030b00c124006d0520030103501140750340c88162030500140c1c0c0c0b140c11600340405548a40810009403860400c00e15118042c0410344a00040001c99010082c0000640318184150502018900040100048600502508000c0c0b0302800c0c400c3d4410711484486810072841c0002a050040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 556324964 1250 556323714 556323751
    0x306071d060903011d070915060903060c02071a2d042c0f01090509010603030e1e190f0801110d05062403010810140a0c09080303090606040c17 63
    0x1000e401c04803407030100420124800c0b185c0300320155540000d05c00c09102618120084144180e040240c005440854031000f450610f0740d0744007070082800395002000c50140900104a43c1110b91240803042c9884461544489040b0491030f14605800c05900d854000c1748031200d0510700071070640301103403894500700300e005d03030190965094409811100034404c0c03454800c0015001c2034558050584220a104110302da40c0e49020f18202c510381c0c000a40460045103894a440c6017181101603e40d050081040b8001005008512905000090114140d00300c14090181c1080061070000400300c0e000240505103100701b2401191090040a0181d5030700c400018141e40c0f81c1c0e19404401402c0f000e2244070750302d00c0b41d04003292a0400e002e2189070303000e000f1038011100080e020b124080c0c0c0b8903540f2450162a2000513800600e80540440c0901825850000b044c43c82800a584a0f000e00310180c920386c03410714104400c48c2c10618080b8103200985005d01c0c42c880c180d01d00c20354084400240c1d45103001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 556326214 1250 556324964 556324969
    0x100206040c1e0806010b1b06151201060806040b06030c091933060e0a0f0b0705010b1002070602070b27010e270f04020303070b0a110301060c020306071d0609 69
    0x91900300080f2442100000120a03503020300528004103a0000c51000d4943c0d03055154840d241500d18800c1d40241488040359803a00130040c2c10140809000020388640d00e002c12424400c089902350382000741001000080d040600c2292000364040742e000c031303032482d116a50008103402d514090400b25600c109440f1014121030940c1c000c441e800000d200041c0c80c4020581410407580103080c0001c45840d00444142010300184060b20410300203d0038140c10256014001d803c411801e0f0382540d00c07554a07102c184c454040c0207010305620780c050008d01c1c0c189503020f4601001e07640002d007072444c03c01040038007520103080c15408402804441c407482c0c188000403200d04100d0601c4650006407a03860b1000004007651250b10441860075006881d40c940c41404100700d000c9601035015042040802d000401480d1210381c09111004009001c041091b0b12240680090704140082021442c000040d4a03080140b1075000c203440c43c204543c81d1a1581c80219130a070f0202490040001145881d00766 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 556327464 1250 556326214 556326269
    0x912030f02070b090c10050405100e0d0c0303050d0c0f2a0c060c0311030a051e0f0f040305100e0309041d060906060109150c02060a05120406020306100206040c 70
    0x2e41c0155480c039250502da9032058694141441381c40c07180b14625405542c05000b003090341c044540c000c0100002282081c81a541158446803040c1c1c02010182c035800003542030201c1001560080d40c80a440f90a01c10750001202c080011400510445001003a059940040740340302c0328500f1394940842c4004400c90301c410741c03042a00181441d4100c1da002c25902c1e40418090941800f994a18190b40303c102002c60300c0307119014042001500070007000c004400014140c24550380303d1600b00c1c0c074021940400c94205d8000c0c1051490001c0c00041c10003d201c4100010724104072034030810001c00f4009202c60380d40c2c0c41200042ca003d6030316208000c80ea040d000031280310481d10802a02c2003132070302c80c4d10161030f100200c480c540403805c58400801d250701c0300380d00000211800d0700c0d0381c0c541501c01e03004c0280f06c0d0488144a010001c0400c422900500c082d41c0d01070182d4429140961a400c2c03030800c000302004460703101c07411036019030100408508490741e1081110034220b20301d07011118403080024003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 556328714 1250 556327464 556327477
    0x2030d0e03031c020c0c0901080d030207080d0c020d0e030c0a03060b0604121407060f0801060503060f04091208130b040807050c0d2a03030f0e030f0706020606130912030f02 76
    0x450b106101580808100340c004101c252001c5c0160707101500503a0810842c0042070041c0140c0d40d0041c403614050501070307801043c07040d000b40641820b081401c841803081c0c400708810700005030444e040460919420110310482684101c01404a944031500424003400c41440701074000c54681c2d000304100c0e2245d01c1150040c0110b481c50100d02d02c4542001c00c9103401c4c202c8c406400c0d100e103020005480348104203882c1a00e140d0350301d40794140d00e4510b0846040d00b0281000740d00c203220301310040c803541d0381e8421030361070502c500b5003003000029260007e4803100004020325603981c00414041e00280d0b000c0044c550159004a186031141e049080080c42c1a181980043e0025210030614040c40550101c060001c2c848480c07000d5504950640d01004030071611009021921407254030403500e0240c1410081340a02904889070000103110355071400038258004c07000751300010b05100281c141aa101a07d032400c02c8800e11440045a940403003c0e40019402020140e81da0311184d211403440c1c049412 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 556329964 1250 556328714 556328737
    0x614030a110f032b0806030613030e06040905040b061e12150f0901060b1303060c230c0c1234140f03060609190e01020f0a091202030d0e0303 62
    0x1058030034512441c02a1485540321064802042e24104e6a01c6040c440d88122009005060241c0311003041045c2000310010131000e02c014502000e2980d140e002c080c1004024819010919003090b04200580e01d5000e04a9806035a4a01c1d403034001040c860403000401d1015603030a280c0d0403103070300300c1d6091140007580c0d0380c1001661018031180c00d2250340103034050b0000350001c100c0b5550b95070440119104546040f03030011605001000883c110760f0160540440c641424951801eaa00c11119408035840400f8580140894074142c1a68100004018070310256460619000401a201d549181d40c0002041c3c40344100b9603a2048044641c0201040302d80f40c10b03a22105172545520b15a4a8603204103900401e40d03650004600e00d40024028019034010340348141644643c4800182000d48600181805442d0764218465104c01d100900540819503820358640840071001000300c0455400301444841401c00d100c0541d0300401d002c10105050b0030900080c541e4000800d055000d0b080301005c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 556331214 1250 556329964 556329973
    0x705060d0e0106080109020901060305070804060f0e15151816140a050405090f06100f0c081809161409011403040c0501030e030403030e0622030807060614030a110f03 73
    0x6030b0700d5815088200c08071f100301d580f15003e0380c03551402c90458508848040020f0301c0c4001040206065a00c00c2da1082640c0c00049028000180d0603807030801c82c10301e00030200f02c13000c1c2001f442d070b1000c460b000004507088172755030301c0345100e03000d00d228210000e40b10a40e060741181c2d17501840c134091003100240d0460411450303207452199801800707a0700710344140c0d4000d022a4002039a562801c910092003001c0042603e030150000c01c004640d00090394400c0c80512051540c41c10100345070703802a1608c1c2590341046011880940305003c080da10103082c480d00760002c964007800f615080a03101152481c8a02116103c1500b440100c4065080746112951420000240018824184890720a5030001c0c0c90900440e054213030700580e244200e01c0b010300014800403040c405450418000c050100036508010580311202008210046842d4070444102000280702c504001d01801130304010240110080071141d01c0c5808641c0703d59215030b004115000c602c180018030740d1511a07a51504201a0445 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 556332464 1250 556331214 556331219
    0x200a080d270605010e0a1b11031b010b03190510050c09060406030b03060c0f0403110f03010e0a05010b0414011401020a0b01080309011419080a06030204020d091101020c030705060d0e0106 82
    0x50b002090203000d0301d880703072440c1400248440c07414003c1e450b62a02039001581c46d03143e01d6001311820b4400c01400c4100340000c11901802c000140d2041140b460180b00008448005074209890082511607603151050582c9486008c81e46c0800c06e4510660890f502250b07079519011585c80b00d101e03102c422548070001107408034000b0382c0355100b050303000c1c4c082c2d003140e207262140c4070b48240c00c2c0511100703060a014104030a00c0000d01840b0390090640025000340c00440002c000642950014403c000d40c42e848191a00f00b440000d01400000300b8060300c08000d0504d4283c2403d69410050084030005e40c400107550103240d00c00c00c441000250004003200b001c2d40c6810620b600ca0307004612407030016a400b0f028120207400c440407250302641d084903450841c8142c12040e0781d590801003003184c140b659221f0000c00760716140014520420246800190b03c0400c2c60700b4144030f0320100d03506e0304541c00024403404039100054014103a4004031070071900d80801c0d80e1900064451083c0c443c03250b500f8141300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 556333714 1250 556332464 556332473
    0x10506120411040504080c06060f0907031104050406270605030604060c02100507030509070e0906180f15060405090606090a050603011503140607020303091002090109030f03200a080d27 81
    0x240011f200b43c441914000c0d10381004010442310220100c5a10002034400304e42c229001e81d000e14000145610b1050400c1e9580d00000c00b21074540d40441442d403003d0b03881a0905e81403d015415a41d1060030403c812400e08005ca079030741c031000340010581a503807049815124001c2101070034102d8154014049480c0c00b15000340940420b5a91341c16a11901402144284003031812501c9240c1d4540244a5907588452004c0c4e00d03425105115075900650400141d000003d00541c0700c08071a1000c1c842081c1485418030080318402454681160040024072030950b40d6150f50640100101c0008240c5441d00400280104903110300080315081162001041203c140300081d031000c00300055030440c1d40c0e02c80c03003a612407000311010215600a29111104024258041c02c5040b00c11314101c0880c075240da64507240150942000e0f4007041600401c8081362a8481034660a401e49070051310b001e20650340e804089000c3c2c800c030400b100e07031251301050306801c0603a9808281305200002540317010341c9091 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 556334964 1250 556333714 556333717
    0x614091605060909041b0e0103080a021b09282a0825050415030b040e010c090303051c14041e0218280b01030e0601050612041104050408 60
    0xc0424000561103000401d407030054183c41803c907020f0101c81840da500ea503007030540403041d4486025905890000b00c3e04100c0c1e41001400b070345c46481d285544100d860030182c43c000c1380c100215820240c0707108150791900c807070080c160080703014003110010580c4c2d10440d08042407c88801c0403010b20f08203005507107480134100100d80700c2c1c826450000c0403000e140e08940d52007044454800518004009005411039245072000d443d200e0715205051640b252101003460b50614043e00019448071043c110a00c2c1611403c442d00b250b00c1d0013081484101c0002030300741400d621000d4203000c004151100b80b401c1c603c1c500b121085500c0c42c00c01116402c060090512802a0f07015101001c2c01e00104466541c1c5008000085070001c2c0f02c050b00c100c01d0a5040e00e100750003440e10340e5100ba44544950300e001603041c0104412002000030545116050004007142c0d5442490710142d404031004205548403402110045081e08008a01d16982e600b4466801110f200000307400c580f4040030002404074400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 556336214 1250 556334964 556334983
    0xc0207170a020429010c150c0905010206090604030f030f0608240123090604090b09030d0f150308090d1b030209010504020c100b0d020d120206090303040309060c061409 74
    0x49007088202c64100d44040d00320810b8420541e03003144e0312046549513004600811402d07205d84402c22106083c90000019500302031140c002188206806000e151f8051018a520100810007415185843d0303e00501c0e0858040900040c15a074009020001d0001d40014002c1c00702d0300c00321588030102501c0a2034105500b55051070140218001041c00d2a040c060702c0c048010002c0804070000d0a0f00030840144000762502e9841980c070203483d0002140011033621501010010315241c02140c0c82c15810307103030f09000c5078032201d00d000050b0640c8a4070080701015030b9040fa00752500e5401550104483c403202031000361007109100100c8900c1d2000039401d5042d02e2094940840303d998400602060b400b0703e4403151001c0d0081c43d1581510181c0750720102d440c01005000d030388542995004904c4002501a00395024419000d940c0c80303203501000440d0700070065034019403035132600f41c60080400d26640514000c118680e507981c01030010f20b4111320b84441e0b038042d40220504280310b24599a101c5070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 556337464 1250 556336214 556336219
    0x11120c0c070b04080303010e070e120601030308060609030a110114030f06040b040207020102100b06130603020c2401090c21020702040c0813060e030c010c09081b060703030c0207170a02 81
    0x100c07008906207010340300341d034201c4026000450550b4201000c840c620f441c001c0500c004c208240351800380c55903400c48c2107200300b41c0d0040030b460309504505005101c3c0c4402004203020b41d1041101e040c881d140050ba14a84581040c510504254000c004a8501040104000c60350764040700340480300c000030111500814040701d08020341100602400141d000d2404064007581194103000ca400800750007403c2c403040c0c0280103e11f0909400c10600203170503180c2080c4002540410341004419003008810070101c0c1c00d0494645240c00e00f8942002070034140501c07220a80c03215080c16900c0d002c1c201000f0307030410a036202e00100c041c426200c00250408102a482941020720fa1034800703000b043c41c18042d0040442030410103030151910005401c0030501d0425a1208118604455000380300703140c0f004085903500347c0c1043c03a00b02c003070340750040041042a00f002d07041a160702c596107060494548503803500b004200100d80200c240d040006503030006044030792040d01552200c0b404030302c40070700754800c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 556338714 1250 556337464 556337473
    0xc0610060e0108040b0105010305101e14041406220c051903050f060d030c02042301211103010e07030308090f0319081b0705030304060b01050307021011120c0c 70
    0x1c00c00458a108041d0f401500d0b901950b00140400d5101c1e400c01a444440d85111403c803643c1c5006040c3e52491165050f144000c50314070500c1000340d0399001b099001400c840034012215201000307030078448040c0200c0e02c101c450b1800083c0c92119408e07100352106100f03070200150358501d40d001e040c42c1c0c009072483c3d81d11a0318a4030300131414020310613240104580b041710142548c0351400c2c01105540d17104103030140180a10954010395840c010f481003c00c0040b10f00964810035901a000d0741c1c41130700402c0340066100c102c296030302241c0c2020001d8580104140851030300800100340140460f030540c4005020b070071004000d160300450134038092403407101203484030180004820740324010000c1c10341d00300040600c0600f603184101101500480c0401028100f01003d03081c02016500400c021111900044200b0041c4000d91280480c1c0c81020f0030201c0c40c5141180c0003e46546c42c0d84009440255a10310200c040705a072001c0d2a04090101d04e094001c1c1440c10201d074551b0401c1e031451086224 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 556339964 1250 556338714 556338737
    0x6030c020118080a020f07081608031e070206091017010503070b040506030c04050d030e01090f030f020409140a030903020a050f060706180609031e0801080703030c05030c061006 78
    0x305200c1d0098020705050303049441c042e903a40340722065122401d1031085105518040b244203900b403084100600d6944d00a0503203041401c10811a0f00c81640f01002540040c48440e0018030490030b6a0940d018407190b09503100024030008400740103c111958012241403d015200381c0c1003802201c0c1e00751a03280d00ca0b8035a90320380c1010340d6148103000322102d481003403008104504008026540100311402d2450425846d44042201d250480f013003540061602110304185503007291903c00604100d200c2d800c045415621198500103281100a0090340d41d17480704024085942002c8284481d4102518010200c0e41001016500540400c1c0d2081e0032030140001c00b403400c3d040000d21b0110190200f03082240648030749009180b4280c2c02c1c1c3d11701c442507c1a10004149108074000e15100381c413400d2580060500f040c05040035100000d0a0000c000018401004002846130440764586004d4a10001c3c600e0038900358040c00a04046a2040c0c02c18080ba40f41481140d0f81519229a9456500311 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 556341214 1250 556339964 556339967
    0xc190b0a11030709030803040812100914070516060603050129030c03191410060311040b011409030c0901080718020f030112081c0c030f09050601121b080706030c 71
    0x1005440040c0030131041c280400000b8052000f03903070b001d03008030300e00f9040a025110401056a08840c50415901c2c0c000c1d0a100240c0c0c0c603c038000d9021500a6480c94a1402e01c00c041c080b48640b0b20401110344401100800700b05040d000000a582d1010090140220070000c005008042c8070800c400000240503116041c1000104612801d900400500e2000814041c100303941102e00c2040d82d02c00482801842458020010343d0519032000070700080c02451420180e149201d09400c50b4862828100c03003040a81e40a4000b204842000e00c10551310080b0302d0000380741c40e18101c00190400403420000801d5000420b046003181c000300f9074410035044a0316000100d224180d20400090414001409103400e6840103000d05840740a5061804444402119050100c842c41c9907945886001241140764940640c11000b89002da0038080200700350b8850b40ca03080705000303043c000f11080080205001d000544c010582118040000c4644d481700303c0152079440754099880441d00300042c1080c100d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 556342464 1250 556341214 556341217
    0x10213080f07060c11040e1603050a03170f01230a0801090605060303072604080604060b21060a0203090307080c100b06071e030509060a180605130b0c190b0a11 70
    0x350350103a580018403c5e240b08210003007218598007074040c402c118401c401215a84481c00c003540c028402800440d40520f0010224003030030111110342002c003006d02211411000d070150548141141040c0480d070303a50242a080c41c071a110f50740d0f0100542200203106181940402002805484140704699580702895620720501200802c1007007007504451919078280c05102c0492506c91010b80ba2a60308e10074145050000d43e401e4a1160b030b2046601c68030310b41016032501010141d400303407a001044441072074881038014080c4c80103a0300000080d80803e01030049803046907020250700d0712b030340c2c0314000f056130340c1c1e8100000340460307203800303184071a5140c03908c161070403941e1200d2407401d4103100c201440c8440720b00300c0b400c41c280001400840781e0b0b40da5042c083c20350204290b0304d60075920560502203403913208991003c0c0920404201c8140c2005044440a065030115a0101e65405280b50500e14290a16041071a0380301d0040c0114204580b103a01c13940541c4034140103114000040e0011002c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 556343714 1250 556342464 556342487
    0x30203121306030b0105090a031a010f0b0d02031b040609080d021b0d020a1a130e040c061409030a0b0f06031605011215031a0a020301031a09010213080f0706 69
    0x5a0307141c030041000710b12a401c007901d090418900a8100080f41001c01d03c0501c1075041201c41c0b0189450348a1b04004101102d8010000314503030384485da01c0c244000615224106d4041c0102c1c0d000000110301114510114840202008a056607a0f581d000003d00118582c001e0105a000704099410203501c0010346100203840e03400c0c07143c9041d0f1084104a01910079a1080740c002c0f081602c0014040301203403003880c1445a013001140d89520300d42480076840308940111039200c94074418000841d203101803000540f44207080540742d14100260203055400341c00541c50703261003403e22000401886421440c051220b95100710a00e0f00c8210030952902800d84040e030071341d0500d0b24100410340c80b500540c01c110442c10000200c06041c0c0c0e1400368001c80c541c0041c0c400e40d405448443c010030703000000b20360001c140d0f4400c42c11075042d95120b042c030b130100003580d1031a03c0c07003840420407466083d81100c00a042082c2c4941d003c964880c03003280c4803501c4403001c042a01902d20000303140f42c01a180e051b40b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 556344964 1250 556343714 556343737
    0x7080a020610030201090e190c03020c070f030c0308030c070b040606050f0607020102060a02030c071e02090c030103080306010e210106030b0702011a0d0303020702030d02150114010c020904020f041503020312 91
    0x11b130760402c651b007100e5040013481e140001c01c11000d0503031800300901c1440040c548940d805a59800d180400c03910b010140c0d070000a00c80b64a101c10004201c10500420589602c110410780c3c0f615114010780082c010090b0140000030100c0900040100c603602c18411110709607030f0700c03120321180010401c5601070354001070301581200000a12849031035000f90b80c400c0c6031900c0282002466116603011a00c4041e8210310070400d503a4100035850181e4217558004003e0100f0f51466040d96200303205400080d0075207043c86101024034041d40d81d1011100b80640c0320040d00403034041c80c200094040c110500c000da48602c40200032172a83c91060080034400c0a00c806400d00c0140c00e1401e0006880810209604156003072240c6d0005079800d00491040f10307807560013060030b0300d0303126001c071011081a40072a40368054200d21040c0b40e6004108128034640403a2585081e0b5618004612a28940304400e0340c090b140038000d8452000044180003684e0094045803407407048031100204500c9298220791 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 556346214 1250 556344964 556344977
    0x305060f16110708120301030605090106230f180720030a0809150103031205060a05010804030f14030705041d0108070e0a0f051005040b0910090207020303070807080a020610030201 79
    0xe1a850040b003505070603940c0c1204942d25296200509801e201e641c2d083c0700c215185c004010400d00c84140509508224090020403001e460301003280c0c1c0800f6005440c200d1120350307071840141d0303507100d404c0c0c00004000a800c84146444100034899031305011698840802d201c5000315242e0316084a000c011051740d07030011450721070000003e030350f2071000801c2c80b0f5452003020320950b00e054000d80000c1c02144070ba01d8002c62a11030141e0f40042c2c440081c4418081d41c4248000c0146070f9014401d550410380504103060312981d401c1084407110307034042040403000ca0000502001c0d5034030000601c2140d20301c002d0070030005400315100e000c1801c01e00c0345074842e511014050008034030000c0d865800c0705481030f00145c9044082040c1040c0c8404542804a10440c158100085d0500740149800304000301e51341000340c42d024802d40f603025114050910026400718401085450400441d90b0f03240d0040c449a0b12149035103807100c200d9002c110054014080e8001080c150f5a1175680785c016a40d05860b000e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 556347464 1250 556346214 556346251
    0x30105040e03040909060902010207360906060b091e0904112701050a081f0e0a081206010318051002031e07080603010c0f0806060c01021905040305060f 67
    0xa0710500d0a10051400104000030318180c45120f01e030b0f8913600c1040c000c26580a0f0740000f900340903050f404240500f0a10103031050318a21513504030402c014074000c0c03490310500c040d00700d0b00504100310000c180a141036008100001441c01030400040f04543d034800c100c03044d04a101c200a004070607c0e4021216401013800a212108503c40544000d01410201062143c0d52114400c00c50070540400320082c00500c00350a140380220040c0175048000c1c06903c40300b04024286602c9440f4000f035a81d036130b80300250f10083c00e00034603800303030303048a9059101c108110034200d103c030742681c600c1e02283c0b40c20350340015009414011f103405a04a00942202202c1800e401c02941c4000e081c010031a82d400070452144030101843c13401540c0980d1540e0003450800d00b810308441001d1881ca047c4420101c400202d6a441301d44942e004d1030a4030610b480d03a403c540110b003e40526260030540d0800406242401c031752180c058000c990141040710f1854a40d40343c0041c0c2d040c41512850b5680c0e0944000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 556348714 1250 556347464 556347469
    0x709030f1104150b1201170d0c110307060302091201090503030a0f0b090f04060c08101a070c0e10121208040203070b040b0a08010515090d14010c03090318050105030105 74
    0xc055000388081c00210b10242009281c0782c0101141e00000001300c00801c40c000050403941c840c40c0545602c8100311030210b081d13001181d07a841c9181c07102c0100402207514204000340c0075000903501c0c1c1c015003100c8000740ca5007000b4029411100c2c0307150240000075003580c0e1b640300501480b480260040c02961954036282c2410f0051f0100c100140651a01c82c7e01d03070602502c400440920880119103802490b040a28042c02a41c1181e101001040250018400e40340c541030a503c0c100d403280c41562440c8000034500c1083c6010301500508445440d03000080c20103c0c3c0d0700c05501c958201e401c081140c58075010110b268040d40d00000d4007905411071038081c990300541825030854001000c41c3c50740307039a0b40040406603226820900380f001012810169044e081140c07640544012a003901d01e94424001e41d981d06d0003804407040c403e100c070070b40780c2080c03241000091005005a200900c06082544030141c05403c0c0500200c00150080c0c0c00484419851107403503003a00c805a56562869103043c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 556349964 1250 556348714 556348733
    0x110604030f0b180304030c03061404020f060d150e04030f210203070e090a0b0f0915010c0f0f03020a02090a1e0b150301230108040b04020d06091a09060709030f 70
    0x3c014a0005201a1030000c14200013910065208212602820381540b6000d42034034000003500d401c0c50008414000166103080e124a5880c2c4181c4000c0d888500d1085090050008204c015814030810381001c105c0340c0d44100300764400ca010351a035a100c803110314000c4890041d142c0c0c518076101c0c8421040d40f40c200040e0000c0d034018001c0c0c50451615400c0c000010000803042c0d5520441a5030b846581c901801d200e003800d070031000219890f07400380c50051500c01c005228028801d0421252107101402c0000444102107510341003ca111014000c4d49000380d81e902c040e0074103910900c03201300000d00700c088a02030030b14100110041c180b600c29419101c14007400c000320000d98060106481007240424500140d8020068030b91884a00e0302c0304130301a2240c0c0312101c00d842c104440c510030000800d00010703d4680196041c0c4001182e0201410004000c0c020004000c2906601070b022a24401c1100022400355200800b078590341d03124100196400301c80d51000a00310000c4a1040340481c0a140f03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 556351214 1250 556349964 556349971
    0x304110f092208043303181502070f0807110a0302100804050f030d06090c050306060403031d09010e0405010c1d04110409050c040317130302220e0307110604030f0b 72
    0x8441d600709a140c10514460035403844845c40c007403200c4491141e03100c0005035030070029912402c08210401d040e081c0c05026820840010b083c1b2691201101c0424400740c0c102e400c8180c000283c03070300318101850103121503130080c40142d44201c0d203c1444182841c12507942c0c0c040f240c0c01090050411803464003610000c0006109507039502035440c5405400c9000d00041461010f060000246217040ca000c040403600540500420044140100140d60301d80d03104503001e82e03402d0b04001d401403801c0140c1003034a2000d41e00706174103c01031000008124524200c006c0c0543e21610081c0044414a80100c0d0700c694003000030740030703085e600c0342a0141d0300f4554042c10500760b040615a01e842d8490540c8016940305031400804420001800c20030b101850f191020706214851000d80f500181c903090130400c4019001c040c1c030500b080d07a95200ba07590070b450400c5035020307106014480124009521034507034001c010182c854601c0c8196005152500000303c900341d81c0d0088188880d25000d0700c44044084005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 556352464 1250 556351214 556351223
    0xb091b0a29040f0e0f1006050c24190b0a1e03060513020a060e0f040f0b03120c0c030307080a270e15010e150c0709020304110f0922 58
    0x9222100d070401d0460000e101500650258040e201c0c6405281c0c02c14a43c001c3c55a4038007296402404a24011440318608541244c41c2003900c811142d08882e04018043c403c040011000d00e24590390100e982881e0b0707100c2d90f00d03900c9024003803055011030f0741503a0a001405502c15001c0b4020300c80c00000040ca2500741d03460302e00d480800d5840b680c0b10300c1211410b80721003c00c060f00c5c00841302140350a01241c40a01094900460b41c940c8050200740c1d0740c2d045244042c0b040e42c40e0341c0307100e031101101d90240015000060840c0c030020243d00c00c40046601403d00301065004846c4a440e490400008071070042e548419000d1410a81300801c0707070a0100401401801c400c0c107901c5d0000709130001500c002a0546001200c041d0402d035144403410015950280d051001c100700e45005a5900d1801003003c0f9034001c58107556050f4044983d0500d0b507280c010500c0e181c0302009100a00c154404020102c81c4151000100c40d180c000070442c0a200031558640e60a9103021310384080f0015801c034040181c0709 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 556353714 1250 556352464 556352519
    0x6151e0f0f0c010e120a02070b030705071a01030c050301061a180d0501020a0210050103030203070b0711010c09090b06040e04080f1e0a02070f06090e1803070b091b0a 73
    0x108001d50141c4964455603458403000840940b0130700585032003101c1d02c43e078607207444046d400c00380d1140181c0c8180c500c003c0000c0001049680104111010103512000001c4044013130441c0301200c860a010030381d036401d00d07001c02055900b014440d020a403005240070315162155610a220503a01540403400c1043e00951200203688480105a900c54419400582c403047c40d07100007864441555010740c82030b0300308801000402d8000c0308980314540c00c4446800c081c0e440340002d880c20321010301103d0380e42d0300e44008460074540c04814101900c4941009100603010101001180d0059025900c0c00540240208000a400800800c0c41103000500f60f81061100f10341e4200000e00840811854032000076042c04095050004801425884441240341410040c0052a06c0c2700d50040031800603100d1b01140f65650340e81c607580301d07c449080071650340320420324241545080a0b03907041507030711807a0100c5017100608503090586103005003071001d2030342c41d0203444c80a071400b405402d410081e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 556354964 1250 556353714 556353727
    0x105150d050c190905090a0f0303020c0c150c010f020c031605010b1c0605070306030503030c1e0a11070e090a0b0a15080c0a1e05090c04090f0506151e0f 67
    0x6400050600c07078014003d55542c00d5241c05840c00541d04020140043c58124404841c00141102e0104a400350140740050311081c0318444646010040c100d41680000c07820a20070a40c4c4c1114000c0c40c4e030b074040700001c1c0515070640c02400140c0c0210702c171005090b0070522440c45900e4200030301c2d0114500540000c15205003030004100d2050212101034070034111003103a80184071807402007075000030341803408010261458941c6602c03400040c02002c54410005042c410340c504841202d620350f142c421600e965070b80724440240c4001c900d401101c003940078002c00060704440d0b401a05110b0110a0b026000b146a269a10021004010b01c1d001203141e0b50720081981e80144013603807010700040300080051403030b4001008410515540140d003105c401511004245450082c83ca084810036604d8804070340b5540c00d44111806650003407159240741020340305540001d908a10301528061b40e00e890001c0c40f03803042d0131551007148004140662041a61a49490804000c040b070301624078a040c140709 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 556356214 1250 556354964 556354969
    0x9150c01061d0403020d05092d030105071e080403050c030706061802040f0b030702010912030b100c030804201903021306080601210212150105030105150d050c 70
    0x4001814915090303540d400140211600c11090846054484202c911607180c60f50b0000e5540020503a90703020044082349400c41030700e401414009001152640c0e04640c1300309480c2c6542801815203941c40382d800c25001c110000e004030458018a40680160f07001c00d100030f80e043e186018082c2007201000000c110700c445e122024400360402c07034031602010a07041c2c03030010082d1440070a0050310000510411041042d40b481e007400380103c901c03218a150311390350380e100160300402210101070642e00068081020a540c19400b1104407d001c891240f642460b01d0022100c50600741001070200d102e110114000c200d080144000c400344010100d021351103014045400d10703030b40440513000390b85501307028801c5140030f01034103c1c81c40910f0010040d003807500d0b80341d1796903040610a0304003042c0a01c0c2640030340d59054100c1ca141d2a0040c10380c54401036101300f0030343d072006601c2c09078005460080000c0752601d018000d16005204401c580c0e918060080e00700082c0e0b481541044a6501c2004200c2d20300e038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 556357464 1250 556356214 556356217
    0x2d1c1101260712020301080a230a08030406140105010c02091b0c0a200a12030203091509040b030d0e0120010606030608121c02031e01171002130302060915 68
    0x303900800030010705091160015142061141107480c6150040c0010f10001000240741c004091300011808080a4040c01c400f900b40e800e94903102d030a01800301c3c070700103111214008500861141c40c1c10130006e0441150100b1040c001e01890340003407801e00d0000054035028000e1508a9586840a10306682a0040500a502803025184e190b004441c040050020b503040c901049084544142e00e9020a031f030000d01241d034240600285420400b0200c4149442041a5240907001408a42d0b07818152000440b40b82c1102e200c943c803e43c01c00c0400551401c1c0440c03001406580354890803035901c1c2450066460850503481c0f158a401c105000c071811890900580005203030325100010410b040040c094246608450301c0088144200060006d200c0c503094140c0441c044100b006071a500c0b00190030010744d03400c2d084136200c000d49c0d9001281200c640c0d0031907140346403d40125114480c0940314442a400f941300300840e02020380740c00b04050f0600100818212000a08440c0f0b040c503410010b41e43d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 556358714 1250 556357464 556357517
    0x19080603100203042102061e0606030c0a05040905090304151d10031e02030403020105070f08010311060d02070501050a0507092603070b0106030603021005190e010203092d1c1101 78
    0x147e00450a12540041c2d5038102c51490610520f0640540f40c03480101d080e03032001400282da001d0000582e0003a881c072940c26603001c2c11502405210070304251021582e80d412a00a03060441c482e100c410040501459407000c0c0b04072100c8624100310001403c000412810121640a1640300c480400c4426a4082e003d4507200498078016182e00309420b00908503030f4002c1c4031405001000c482900e030aa042407900d03044980c000292810300520340045020f41c0584124129840d0020035800c0800c00190401e92080810a00030881a9a120022200c00c206482100302c4441e500000d0038039001c0200080134480c0c007200c21a880c00445a40744490030724240d2207800040e90303858052085141101c2d107800060201e00d0024141210400641c4460200e01c009000703002c82c512690711941d00900680e0004000107004600c00700303c07940380a40080003040400086840c0800d5411a031424a01a060310340701031b180c91840300c585039526850390b0000703600c1034113001411090550754441c161010700e1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 556359964 1250 556358714 556358717
    0xf1211040608090d090617130c1205060a061409060303040e130c120803222012010e1f0b04050c090f0a30060203070302190806031002030421 62
    0x1280340c40c491460400700b941c450300b0204000c20340c04100642c1d000e50342e55010340d2000c00003101f680364280c0c40c41c2e0300c0950040080000421070000150b84141680c1c0014042c01101170381d45655031000360804a0311070307005207203440400400c2c40c0384600f0305407643c50303100b18007404807840d090703d4210310511000115855510225600f55031010000030b0a4542d00a01c0c4400071003240d5030700e680d10440c0502000344601759000324509260456550140000320058100140200314000d0f4580c1050200724044054003401c1181d107e81200c140500c42d41e80402e5000e00078048040000ba14070b244c4101d0f402845030016120290f400301d5584601c00d1900807a6030b600507595800ba50414403650201404065200e0070442d00c1c00c001c240d0304c04c01030b81496205980ca000c02ca1320651003c1c040c940841202030020b6101004200340250140d0080070400c00088007e9000300d011682200c00307102c11600e00390150404034450a003200c194010f150003520aa480c1c0950b02d107181104005600d60594210 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 556361214 1250 556359964 556359977
    0x30d150506191d0a0e04022403100803030907090b060c0102120703050606070218131b050a080a0812100306020703020a03090f1406070206091c0b0a0c0f12110406 71
    0x262007540001c000f4000000d4103006031403810908000807004070b41c5102d14540c0e0b01a401c00502150b440c0c0d4070b042404103500d0b41445d80c00c1d04130080320056400c212081040c5894450010035240400000d4034410826038006080460070b1450100c00740040d5146640c0288052161011440c420b002070010440c501751594203078503181300002d080c1c84003c0c2065000d56420088600980c98881190440c0d540040a00d036294440040300c000022101d01c000c0e21003522100e0007401c0200190303541e42240c0c801c55148040ba80c6405e01c1607260401444014601201040f0032076108000b41000c40d80000090309402c100303540d948032007051380c0c01540111700503000420300004140d04030000801400250b1490310440c0c0c24030500d04c10b4494100040303071040c10040b03803c404542c1c0d032100302c1c1c860b2480031f49001b68802c505041d20b01d83c01441c0d81d04545400c0d18400103030000c2024454004000c6044d500e0040c0c1075035031a81554220b0006910a210b43e460b80ca01200d0f000105000700020401c43d919003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 556362464 1250 556361214 556361257
    0x9010306080609010905150408093003091525030c080c06161e120b060412030e01020d0c0201110a120c0317011a0f070204060314010b010e03030d150506 67
    0x46c0c0c1480c07606203140e0100200c0400380400f194011040e9001d4a4040c3d401d0008040e480c0d4441c40d00e0070754000720203082051071904904d00b01c0e0110240c11070380e00039207032521320704c1c2000641e11240c00780c4c02c00781c00048030b04c20701a078a0082404403510541d020381410480307030480c0d0311b5200090f0b2064000c40825400003040c451107031030342c111064181010b85071682c100c9403454926008800b41008040410040d00041c2148006542c004203500f180201000d0355142d59000200f0040844901a070128420b0b541c0e0390b401d540003050701001e5484691728010704113050b900544000b4040c002c0070041d8800c29821400103440c80b4003001100685841d20241d15180d494010140e88048000b002944002c0b80100000340c0c130211400c4911000280c103903110a840e2a07054501d0040800182d4814140000002440b00341181c101d8000c0120000744030030b002d41001940c1140c513103500160035600c02c202e80803450362581d01082c1070005078034249400d2981ca00c005080d0350402851210314004035180c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 556363714 1250 556362464 556362473
    0xa0c0b15030c030c032e2310050f151c050105100c08090418060f09020f10080601081e091020040b1308100504020a050102070305060606090103060806090109 69
    0x480e1202c0084005007036103480341000c84e451340c5046010f4150012600b4504103107921002c503c403000340941c6800c0002107154503070f80700d426184401c180e240700b0103000401c002026a9403140151400500600c844120500a02100f042c11107120840e842052080c40d800741c040001b4440d5142d0701c1070000c107840d41050204140d1200c904061010310000042540004040c203050340c94580044400140f4100b0002801070302c4200400024040f503d0224000c5000425a001c0282c10340280c40c00c00040d082d01d014804450703490b0380b15002044088c0001551903200380130456000c403940343c0c140052004200002c3e01c03100e00340c0391000380350400d54003101583c0b03040c40350311070303080030641f06078051020358114841358030460162031015000092114518814158060024240a41150214000099008010701c0d0546040744640b04130403002600d58400603c44040c1c94006020b010300751517040c10811310740d0001e08001d040c980c48210000307400c001807100c02d200310b11001c0045020580f40c0340 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 556364964 1250 556363714 556363723
    0x40c06020f0c010801091104120303060614072a0909080903010c0e1c030203040b0a050706060806270c090403020d0806040c05030112030e0307090b030609070e0c0a0c0b1503 76
    0xc18540c0c000aa02d00050381d0020f03000341119100d803000a4000c0101c26000c4061040742c000d00d540146100c01d80c0704140d85035104208560060342c84c40f030803901d01d07100390360288070b040c90243c012075842c1c41184401d43c90079280c10390004284800303030401c0d0380d9080503015180b80b520291882e64010400740c540d82000c1c01a10502841850666005200342000400e03002c0d002071600d241c50002d4041500701402001100c015050b0f5074000f58a8151010f0300504660114004507005418400300181c807600018031207000700d00d1088102d06400e020040c0c2404844203840340300252141d0300d8005500d80b142c3c5031050203940240d000e024501321014000d0211480941914001d41c0780418800c43d0542c044241e038152800310341d440f00b0700000c500b4110303412824405140d074140900c0c8000a00703040709521032070342140140c0c20349049582d201c051f90341b21003031031040c49403040382d10b40001c1c0c0d5110301c1c200078100041c4900380400c010794140c407641a090780c11503450842c901d0360001a02540303803c01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 556366214 1250 556364964 556364983
    0x170a0e13091a01120b1306020d06031209240201091b0611030408100e01020c07080d1701140d02180f012310030b010e12030301060f05030103050307080d1103040c0602 73
    0x910b07545549481011581200b05010107040181100f0104641605243d841085541c000ca4155102c900c62100280204034620007140c030321003555002d03080c40340200341d202c08440c2101c0e0024401302ca000e07003048001154100e039004555071081040c0c00101003d01c180141052410021503083c01e054020f480f0031281e1481400992040c04200f01c0d036400000c2c80d41c1d0a15100c2d00114100c10b4007044a80a80600c80d00800d40e4083c1c0c0300701050700003002683c921032403034540d02c8809242c4030104080c00102c0c2070007a0000282d45181c00c54607800d201070385800452029040117460318005200140414003611040d100b504440b004024418040000c11982142c013003008011103070080000c1c01c041100c25809050649030400707685640c0c080c001c440080c6001402c141e0720f103544009000d0700c0e940309004040c04180901c5030304100c140302d01d0503203050702c1d400802540341000303d44070f0742843d4000000c0c1c9580039482e409401549803202d400b541c0900e100da0072948240b420120044e04044259 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 556367464 1250 556366214 556366253
    0xc1203071b0807110f04090f020906010504030c05151c2009010e010e190803091918050a02040b0c0f01050105040221101d010905010f03170a0e1309 65
    0x20020000442d1411007141c03012940030402c1503e962414003c941401007420045502518094040003808003034521aa1094030031568600695950b00042d11240141c1c0400f0380403104152042c48542002c01650b5841c0350032100040c00e0400c424140f2191544840030100301c40d4030341161021103201c03400c0200d51401400c00c0a8100301070040000c08011a05403010704100d02c06c3d084440640b6201400410415103c0e040c01c03d0b00d8072806c00982c1c1c0c1e4415070b031541c0603a5080001f590442e030000400001d65070000c2c01030a001280c0705070f0201400c00a04003e501e00c8e42004001240143c100003090610a0440540030320103134400f01c2802c540b81648580e00840c01040019500210340c80c0802c1041401501c012040d201c030380e00d450001c4030a81290300185128800c0d8400d00b8404c5031001e040300c3e209002803190380e0f00d650228190108601c001000072606d1061300d041c1004401c00b40812000303a00e840b02600141d8800511b0b00045030341c54102c96950f880d0303010180f003600c84030704a018200 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 556368714 1250 556367464 556367507
    0x22061d060c101107050f211801181802040e010e07050f1b19060f2007030908060f040c091b200607030501091505030a021012020301030507090525140c120307 69
    0x1082d4100408c0300c1d101159038100081c00d0781c20301c17500c0144c1c400d03040034145641c6540138125201ca6032400940c094065a094000701c04000190000c640a01c644514199960142031410704c1c3d210115036048140310a10600b00700a01c0a076105082289608030b900540e05000500490300b05a411902012000540d980c10705a042c00c0b009801540001e8004410401c00c0e50b81070323a401c040b10301e1100703508010224014101400b84003280c43d44030501882c090b881211010765100040700495815580c3ca960a1400c0908100510f0007012185030300c148040d0500c00701f008450300c5a092040c12070b4000042035540700188180409803048501b02d401079400d2052290030032000990358000303158001c0c480e40b1220061000700d0720441c221800b10741103560640d100c1d40c483c0b8015444408501031001c01c00d1a02e00084c804030300c00c1c8504901c142c400440790160524619007121a400e000e413000400c20002c10551a6030780d010000d004a441e8400b428580785d082c000c10040c0884031180da0388444c20320 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 556369964 1250 556368714 556368727
    0x509100f0e09180601090f0e0d120209060f03040b070e0109060210020a050f0c0a03140a0507260708091804080d0222061d060c101107050f21 62
    0x100300c1d4501e100c001044420a0031a030340c3ca007040101c0041550409024041c0d0000040c0075100c44c0c01c9020b080040e03c20900c090101642540c2d030300c507540c0561100044d0704440035a01c0203482e030b00601e007104018100390300e004003221300304403281d100791412690b41300c88008020002d40c1c4480d01e040002801d10700f00c0c50b0300d07141900c02581ca000fa90740d0f01e05419800900c00401130700460444100c0316042c41c5080c3c0701e1100c451314076101c607078915003a800709881008030b84c04005401c003107c4040d0f9a6448032410000191240e0f00d40100002c1a0b49541c4d680d660b140b5800c1c9042009041c81d98801c4407015616003400c0d081c40380d90381c04912001001c43c041c8041c08005080300741641c80c1c0e1840000d0050b180c260f10440c0410700d100e110720004011a0552010440b240d200b10760b00703404c0b40c2e5100660510044502404500d01c641c060f041c10680040e801d0800c4c1700401d810034055942c00c4962681043c010b82c440500300505483c5800b0700e80c0c0010045650910398922583e0700b92a2004400d05003c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 556371214 1250 556369964 556369967
    0x1e01020310050609030c030109080406020111040e070f0c0c090902150901020d0c0f08040b04080606030c060406210e060103150504020102061501120e011e06030804030206031003050a030509100f 85
    0x28210700900e846160007044007001d17038404006107100d400e0000c0091000c010541400c6061742d1040c040d1200550811441600710100701007118102c407104080380180d40e8810030304440c1c0560200f00e400801c400c41c50131030003042d10002103030042c1c100400001489480b0388100101030a6100004410fa1000c0c00030054a03a00800d40808104260814000c62071182c9850b90551101c00e50003000800042004240288032002030b100b41e654a03800c982d4a40c0b2910109940c1d6030030010b0b40780d40458100403e101c060b1080354151200c08030030410a203603089400d8818240e900c00003c3c8071042d030044004000340728101001c0100e21840c0d0070708004904003600001d41f81c1900038000641500399881d030040d140d1040c004076460681c111002c0000d4403071054501d01810728000808010840809400d88a00320ba1041030100c0e07520219551a081c5140d091140a400092699a160071140e40000c0403800501240c6082446a5076060b52100d604080114001a40319008100311140881c40100d9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 556372464 1250 556371214 556371241
    0x708010906051507060e07080f060402090f1501030e070b191e080a020313150e1c09180b0a030c05010f031a151b0606152b110a021e010203 61
    0x198002c40c02041100c42d421b151460550a40e004546a21952580b02415080400c405000e0351007243c64002c00d0321401410a0443d100391002e8200d41d030443c008802c190701980c001915649120306403044159107148400700e540008000d480319402c0c0105a100c226480204c45509241b0400c4038518442c025000038601e040040422100170323400400b08079502f1003a032407000616070204000d48904515003030400032f0280d01e50800558425201031040140030a02c081080440c00da80364106a0329000703c014254581020f04e4240c140c0d18a1000e0541d280c0400f110051406000d4510003030b450b120005150202c800c107540101490080700c1341200c04050508129240b00b1103040302c0c1e02001e039941d0f22041c0b05000c04c41c0031058070304000c40c03c0c0c4000401c29038450311085079807890f20035112100040b148504108041c075540e681c1c0d003c1360b4000000e03015150200000d98001010701313842e01c420f681584400c0801015911000d801612150300c42d010340007025243d0020360850611003807521a2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 556373714 1250 556372464 556372477
    0x510050a050d0c020a02271b0909040f020a03050303041401060605090906040f360309150207080d120e12090f12030409051608040b0103230607080109060515 69
    0x602d41c4403401501c44610800090045507001414151000030445880030003c40100d80d10082c401964006401000180d00310f00f140c4a038019500e141803580c0080200b5000001c0045940d00204600003015855101500002e544290000c40d03580c103003428a100307030403080032840301d0503810000c09012565009041c1c0751411401c0d920700c50140ca8100c0000d028203400c962031200a498490782c55070348440c01145903001d11211108901c40d600324215100f1272242d5078000307000300e180d5820810100c0300e51080c0d51100001032055984494441e03021038106140d001e40800000e010069200307250155105090004001074002d00718646d41d690801018000c9251145c170900b00d400e0160b400b44ca0f1100b10340412a000003e4950380c03a25280c1c4400140416030303010b080c0f45000c00c0d0b01c804183c040c011035030103140c12404200e40d0780c0ca145e940740e4400e16654400702c1c01c0e8802c05161741c803094040017514001d40e000d481f10791071341d8101014081201e180da07110910070328144001112061004080310f01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 556374964 1250 556373714 556373737
    0x406022703070909061e0204061d150703020a05030f09102d020304180c0318050a0609060b06070506010e100e06060c01090803070207140a0518090c190510050a05 71
    0x194640c117400d212006284010442d08044e8503c00c00ca041e07100d0640c01042900c46a44400541c0005100c411711341c0010001010303040020004499400c10500014200302803292044a40c8801507644a1781541c0001b6466031221b140895006054036140d10bc80040d80c4007898824608070902c1d040e04400482c130b00800201da2226818100d6081c1301b44101d5024014184490b04600c0000007014001c0124025140000740303042403a8524461070313034881c00200e8001000f4000b0740c032281c603004020b00d00c05d4000c40f01c0e244c1da070407210707426190403020f00b00242c000d0028001a61400340b030788412182c010410302405151100c10310030894403c40468000000751038494403030106c02c41d00c0e030040c01c980318041c1c6031001c080700700038000307034005500c905941001c0403d100324034480c014064038004031b0007441c3e48aa054100700410003015400d03103a100414034121001c010441000c104011507254113070240030f00d00602031105050051803040a182d4038a400f42c5444c0d403188004029010b8182a0403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 556376214 1250 556374964 556374971
    0x1002100b011e05070c050108040c140a12060504061109030307060b03030f03270c01080109180b010602010905011103060d02090406091203020a0e090702070909051504060227030709 79
    0xd05902c104100c2a54600c98030041d00e506100c0c0c08040c069800c400011215195040760114465115200c1a401503070701030011090b090505224520f0b0340d8100d9401c0381c20811f0341500080e07038500340364500190ba004030000191400d240c1002c03020b54a10080c003440c101c0c000c20450940752000021620400e03086400003403a42114400241148950001c0280001e400320a00074400e014400a04001c14410b0f904a03451050360407207625610f14100d400d000c5403441d401041180041c0d000540200c0da40090281e6102c05580c48000e220420380050005039944c10b00b070b500b0004c1c244500840c00c0d600802490030740c40c0a0000510f51400c03806d000b03004204070700104003042342580000741c5441c0d0101034081e82c6603451030300400035005034401c900011144c49000d0052b05203141e140d8062209035000e030100c181400741e6900607041c0c190301242d903446a554480c00458000041c24091442aa0056580e007485143c6e404040c0120b002a035200801d80349690442d54005075000c00c0307402111010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 556377464 1250 556376214 556376231
    0x506100f150905060c03091806010c06020c1905030c07090504020619181d010b0a020c0f0a03061103011406250602041212020607030b060711032802040506100210 71
    0xca84410b0158032294000401180e503450011000c4003400302c51000391840114181c0203c0e40c0d004461f41520440d01050000b10700c070021039080e400030107944c00700a08403401038050041e030b81d120302c40814040d111074002084d640e81d049070620250000300380b042c8040c4480d092940014080f4400d014a20202203020000045010700a0040800d1100c0c107041c0c100c0084c0d6031f0402002400b140401c0130740e000301e4000021514010600690712000c2c0c0f16402030020b100c0c00b500f44884000c8042400c0e5000c01d86010010000d2843d004a490380c060b5a07424985a52600c502e41d0032400c3c004408601c9a4028040e454400d544d500c0150706051204401205010346411b0000c024400c0390800c0340f40c055842298800e10802010a8030342240715400c891541c0e8070040228200c3d5510b8000580c0100300300442e9001c10013502154490031001020b90700c40070750b032100250b101101d006640c4464041c1080d08010352a003441455070002c1d0940d810a10302c0c6461400a44a110340840032000640d103c514 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 556378714 1250 556377464 556377467
    0x901060e0112020f12060a0911040204081501051804030c172b0c0f2006190b0102070b0403200a08010b1f02030a0818060c070506100f15 60
    0x200081400c111559032550716210000c4032418500780980c060301424150b0030041c20403860390f4410003101c8002d083c4c00e807034040800c0d010700002e5906032011860406c0c3d2044560f260720003403000f0b204490040440d006020b4140d0003590050b80305512504201c40510762003400519999401a4503140c561208400c07071414880c2144e1a8001340c1c2d59090120380da0002c6400c4d102440d004d15034202003c102d407500400300718103591240400708009038000c03680f0aa501d00811015010004140d43c1c3d95410700c4510000e0719080080707400f1300e0258034000d00c001e050452840743d200c500c007081c8081e091050901c842c00d0700030f00c07440c44000e0441e01d07000340c1a1b02c1840340a070502c40da000002c25041a1954030142c0300e0180c010312904520405a980d41c40400b4500090400c0e44400240c01450070301c4004402914142001002d6450740c804004228028410038001c0c640b082402a003080d80b203880c0d0341001032811200501800c005102804240602102080d41000f140e80d260341616421144040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 556379964 1250 556378714 556378721
    0xc081308120306240901050903010f02280201090b0f04030c020904110a080a020a060507080d110a1e0206150f031f111908040204090f06090b0105190b030901 69
    0x480c11406800c444400044180c030085008003c200c603c46080c681100c03001080c010952003101000008024a940039409040076042d106c3c0c0080000690b4540d000c0341400b85da01445c940c1c1c102c14a1658080188100d841c04001e511400d88000c000908460f5203041c816503002e0810340541c60030710005400c0500c6101c40e0071100d41d0107042c8441c182070070315281003011002c2c4e000c103120310040307031000c143d850340000d00b40c034031603001820700b19180e1800308156800d80c000703030051f207140c40e081054074603481281c02000e041c011345904c1d141c3d882c90b240400411090522203052020100c2003100e10041d0b80c0011207a03009440c907600c40c41d9141150340054000600d00c2c0c078880d014092011038150810140b403c43c2c01098421800703210391000e40682542900c100021880d6803441d00e4190181184220b41080d40a403010f400084e02140c0e50f154000c14844180d01100c1103900d03502c1c00350030050701d001c04d64010581980e0314421103e2211000140140d075026240304020044000b8640e02c40940 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 556381214 1250 556379964 556379969
    0x17012105030a03060f1e031b08060c0403150b1e031f02041d0949030c030501051810091821080105040c030b031603030e060a0c0813 58
    0x80403070350740341c4000c0c101a01401c00c620078030400030100c6400080060b80c14180f050480d030055402c0e5140e07070856a031854040c01c40b10484284070301c20030000c12080f03020001c550240e0b400c5102d140d211481c610705290004520210000428280a40004d00f612113000c1045e115445a030344442803458440420300e410403000b0b60080c1e10b40d5404212501a4499006009441c0e6a0407522a00003010443c00000002507a26029541c0000800d0100c040030341a203ea580d03900d42a000c1c200c0c0e102c201044500001d818a520b10410100b5040030401d405204010301600139081c10304c41036140c030b400070300d410b1840310000c804111411b0000340c4c240308004600d0081e001464040051200701d90f0a081100b92100b8101c0c1c00342d140c2810110410520f03907580c1d20240081d90344240503800c001c14403001d00040074548007855102c5131080710a98003406401c4040c8031400107900742c0c03465070900907c0814545403240c0500000c001a10b0051350000319070000039080b00d000d554442245002d10510300095 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 556382464 1250 556381214 556381223
    0x40e030406270305030906030a060905011d0f0403021b010c050717060901020906040b0a03020705010f050603160b030f040c08150f0c090a0e0c0d021201060906170121 73
    0x203808030304950016103074503600700798000c0401c410310101c80c890301280340c501015020794010700c00700121f4501440150351200340d005010031050380c1c40d8144825500282c02580c03c8002400c4141d141c0d00b500501103a0100720550040346a09003510065100c51907104007000030720910200d6519640103900d0403070039580c440125045241d954064400e13608036226030388164040d00300411407044050080c0c0c0c100b2680200b00901e0145801000d9005611100c20074046c90f4003070040c0d030041842842900700288401c10089a03618100d0101810404280e18080c60341c80c1000b070038080c003540342d07040c0c030b034000505c480040060b00c8504100151051681c88829584240e40c160991807104010366801190501c4105000340c865042e004002c0c002c07006040c0d00801e140c13004010811440c5156500840c041010614081c11044140300340d9110541c51140c800c0d000c1c0041212030740c458500c00c018199481c00c84001b0791010b0180020f80d10610600030401d42c071318114001c41310300c1d40c130102d0003d502 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 556383714 1250 556382464 556382467
    0xa06050315030304080f012f1605150610030204030b04060b0a0305030c160909081606020405030a03020a021305250e0909010f05010f15081305031c05011a0a030209040e03 75
    0x1c9550159070f03480820b1051849500f00000c0c800c001481034808502440740220344800c0d24014542501d2383d030000c01c5441031645c64009504007041d030621500000c03640907592360900780780850600c85034000460001c42054410003081003c1840944007941150b072120010410304050000a1030000c6d0715000604113004c0041d1004100c10009901015200c0f40c00c01200030075585c0d10401c0845000c2000a08085030802a151003490860900403101c0d00c02c034001410191901e012a01e80211100110302581c88a100d078029480c0401e880100351b9150001403010340b030555a00703072a441c040c0a03451600c44030002d141810302e0040c40c20300742101018200c0041031504800e12800b9001c0360451000840c505000883d90003c485841c5040e07410300403a41d01c2d00d564032541168060300061610016980805035240012410310050802d581340c041402e82c0510207001c0c003001c54006902c291080b904070245410022101c50070b403000c14160341401a158070305240440e01038000450941c915020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 556384964 1250 556383714 556383719
    0x606020304031b060518030a170901170601021213090207030e100923010e06190801080703050a0f150f0e15040203060f130605090c100c020a06050315030304 69
    0x900001420440b4090403074a4401000c0f25401040003845003e4400050800c100c41e440c6080c1842e800c0300840f10144c100c030f83c0c001003a10f5842c0100340411842010940c0000c014081d0b40c1e00490380480000c10054407002810f1060000c1d5541e0402c2202d0b2400c0c0c04042912064007028403103910081c140c545056540d08850301c1c000b40b408000d070f00220710a60400c0000100315105a1020301920b1100c5260034054000500e039400c4402101038050400442d25404646900c03080e01424111100d0444ea000c00118840060048281600030340100c1e485240c040000c5030002071440865a0480d10041142c21075081c01d41000340ac50403c000d150f401c1c8402c0c802403004c0c9611104001480f881a1980641d2201e075514405c0e10540b40030b94980e02450200f00018101c01c01290400c0c4020400440c0d40407079510541510011641021035070031840603401d250810780152000369586240807640284641e0001c0c0101c110741c084c5104014002c000100b03581d03044165904c2c5000001d0840e5140c66 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 556386214 1250 556384964 556384967
    0x10030b0f040c090509070b09060705071806050d11211903020d0e0904060e010219050a1d01050a08060a05030a0f1a10090e19050a03020c0a081e0304090606 68
    0xe80541c0c08072940348000360001003d11107449414019140b443c0130305844c514000f05c50129410075400140c0c4050104501e40c0024800c00c0383e04010030540c00e2076003080ba64000d2131400c035126071788000d0059508042c040001085618041100e8004a484008130500480c20604a00c0e0b8180422043d1065038194056851490381aa902034230981c21203007150a00320048030000c0301403404a0304080b20101003030014505070461703098110880001410802d68052120408451601c0d14020030400a441e0540c654002d03500c9444900d0081068000c1100c040003c0440c429032504004100e5042c02140d031035a80d1880d0800204801000c81d6001c81d00f40c2080c11242c155404225519924000a51050f08020300b049105094a903104040203140c40d0341320380074081c1d280c0c40e100c10b401150713000210050401c400c0e0382206c0c0210000c0c9541030580c40c01914005204e81401d205803002a01002000d40c002494040d2a0040d0311264a02459040d20340c82c5016542210071308078140710010640a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 556387464 1250 556386214 556386241
    0x130203040c05220c030b0a170c09010f0e060603040201080705030907180609050a15230a1d1f090905070e04030201050727142e020c011b0b10030b 64
    0x100e80800f0821020f41c982c0011760480c2c3c010a91107400c2030b1412402c014210f14100b006107403449680079a00912801c030300081000b5001d0308850207550b400c203800e0080f407000074400c90b0701074020744829142d0305043c0c00280c1840d6000b0141001c00c0340000c00200102d030b060000100400c5480f1002a6541c1644000c0010707100501414070080c1c40c1c0400900100003a00a9070000c5002903030040710302e4140503007200c00290250101844648006d681c200e02d03141d06018200412001c0050703641012112201090004080d048101d46031207120310301c0c20b40200c24120000c40d2030001d4005401511841e045040a003113500240760b0205000400c0123041e0190002d501c60b803800d981c1c0d07901d030b0140c441165000031030740503010000e0303100f003042841a015295070007509810024040052400f024005040c07062a0039034800e0a0441d00503042440c580401500c98602c1c02401c1003030303074101072000c4056420484000500285603400c0031a001c801c070054420091500705902c6800c5180202075a0400d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 556388714 1250 556387464 556387519
    0x1a040615110601030c09200d0903110a02091f170102030906060306010303090605090109090f1406010e130c030e060117071a0a1d0604030b040b06030705130203040c05 73
    0x800c1200c40208901c40740030030002e05a9600182c610341082c100740445c0300070128084d010501c59803400840803040c900c0400b41080383c42404020420034140d00d801004085803480c1c000703295001505d2500181c0c0c5115030301e9032041202e000c06100c110300b40300c11f0b0021001e43e808900c02007034003000c0c0c0d11548010340080d88180c02001c01c4a0711a1105d409144d2744a0091001400140e000e50b000d02503d84210000c0054280524147c01c03d2521041c5c6c80c0300300c0781c546d0142c0010a9031402560f09030000034015a52203030b424246151900403510100c0d11307816600d41d5079031040c0c2ea83e404601e0542e00075484003030442c1c5000102e0b19103607101ca1a40d2a0744024400c2541c081c490b5610014611780401d06021861804c20324050800000c00001da441c0143c0620449404d03400103800c0e000c60702e170a0050700007140a5000d01d40d080c10182420340500c10003608043c02a04280c0040c400742c2c60750701450721000007070000140c4d01e0342d480c00c3c1075112141c0d60f002664072014005030743c0041d105440d48904c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 556389964 1250 556388714 556388717
    0x1d0c010e040b0432131127090105090f0d03110d0207080d060e040210080402030c0402190e06090f010815040f0b0405161d0301020409020a180605040b09041a040615 72
    0x45400500c0036200d040302d045035803506911000304d5040c00175588024070800f80302c0240c91018103500201500c03514204880c1e03040280141c0c2000c101148c80240226030704903d50502808502d1807100849441d100103100500c24151107124000c150980301c0e00700d40010ba1840800c648903406868250381c2607100100928416040070030109d8100c0c1c1d007440c0d9600a41d40202086100850450241d030800d40003001030b0b0381b5000b80118040d8948440c002400340322800808a4100462050003411005482c0c80d0180030f08000d10481c03649491ba49110b8010711000d00300f415540c3c0d118858080508204000c8a0308507080c40d5180c1c149814640010002a8048505210603502c0c2041203041c0c074000440c01000507408001a10510000144050302c468090005480c280c1c03100704800503613010000070000276909040101c074000d8015465406001c071898104d03c0e051030715404040034015a150a8400d6989007800110b102c0c094244611410340a030091054030398030300106901c1140100c4010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 556391214 1250 556389964 556390031
    0x61b06041109090705060405210f070602190c090e10090c0303142d1b07030c0b0c1c0c0506070306030c08010c0c0f020f0d080901031d0c010e040b04 65
    0x80d24800c004c950f503801e40700c029185038100382c80c0c8002c2050f6840405a041d600340c0142400c10040b83c0140481d03c1a0800200100015444d0080c0249425107440783c040b0794003500000100025030311210b1008940440c1004510151030124403414000c2d030886143c4051301e0480031604110445040390100e03030090302c0b0400742041c00c0c00159164450b000c4120382c030140c0d542e017061002d90200c41030761160742c058100c0341c00c1421410140d500d40301e60714414103040d40242c0003001000000c002c40b00190151100881c103000606000555070300c403141b00621009040d024180c0e049100320042c591075608203007150700c1403e00d8000940203010b540816605030000c00e40c0442d00b040305002d40b03601100e155444070125010b80e119040c86c0d1050304800c03070b0300c201c80c0d80f80c41c94996501d00c0103024003801000f006075540484000501111010704001c1001c0000342e1050791860f50100703903107450000a080c40003600d02240300140040081d41040c603402407030300740300c982080020b40085261158900080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 556392464 1250 556391214 556391221
    0x60903031b0c122604151107050f0a080307030b130f050a0b0618010e06130b03090d02071202132004052d0105071b15180311061b06041109 61
    0x104c82107840f00f41111200301400824901c00340c007140000790300c41d000349915011140e11000a00c280d0790484c1e0742129a600108040052050600c038146800d030108001340540b01880d51001c0039070100509602c2415510441107041ea1a0460001e170218188807040080304840d10041d0003c0c4401c2d15621051032403d030300c0c0440c0d030900804660402c0c0310101c40c05100e61200303004450580d004041c0d40c0d000002401020030312025043c0302c40140074846405616450001c000f00d14000100d01203000f103521400c810041d4010070541c0895054040c0c542035403031440710030400064010a102c090409801c581503d50360031420303010b4800d4075400c58428441414851074200c1111100c5500030b5609a03140d0418100c2d8001c07002400e8942c890004405a8001a5203e0311001c1c41544408040300300540603009495001d40340034060300510b0071842003107082d40c80342041001000e11040c081c0e06c00043c041ba100d40c0242d54102224200c208454483c030381454120309805035101c07424018500e52021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 556393714 1250 556392464 556392467
    0xb22061d0601230d0206040303020a0524040602071e0309060906080910020912011e050124141201080f01060b1c020a0e040c0905031603030804060903031b0c12 70
    0x81c0341240e00c14140085914001008244280d28584229a024001076030700c60050b01c800b40900000c1d0f001390081d15070107441d41880f504040207040350701180392149054504605921041ca5001a00000c0050721820f191500c40c00442618005460340e10300124000c04040c4d10405140c20350740300d6503072240d859a0b90b600c1519502001d88100700c03c0e40102c0055178010200c1c4d4042c0101e0030000b418a485000320801031400c640b207000110051034200200c06055407140d002c0c10740100341031100c00c141080307100c000316030a2105065020420880001c1c40034040d080c041664181c0b1203071080340b2420b5035114107040c0d403041d8900d4604115403d02500099503036040d02541c07051221445000009800142200c00942c82000c8010611020000060154465110707480e400100ea480300ca0b10242050100b600d85a001020360120082c80503042c000079a1101441c1e030459440340001c07519101c10314040d409401c000303012481c40b071480385800f1512a4003424400c0c50714050704409800380d428070030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 556394964 1250 556393714 556393723
    0x90603040c170f0303011203140705060a05060111030306090703020c07080303090c0315010b070f08031f08010c1403040512030f07030c030c09030213060b0409060305010e0c0d0b22061d 81
    0xe0350003c0e400c284010048901112001050b0521902e0702060b606511000451950001081680d1581c1321130200000784e8502d01c207007034009d4801d0070284103009561040941d24070006000340d0150052101050b503441c000c2e0140c81f100b221700320684460b0354840305000d90701d4000300c952009504c640e081f040350609000c0303101c404001890481d68030507801d01003009459489150101c40d0f41c903d01c0c1d0070301c01050300781020b5800342c00518003041c8a00d180d504810340d032009540082140c2d91401c2d13485000150402005ca061010b0512407640307030380d00c0d804c03d14107249441190925035500013040022000d00c01c01e2561107681c458a08108510b0b43c0d040071412500550201b901040d00d0620500152a0100c1c0ba83c800848040000c60403035100d0f51101c009070001e500140b009921803a051040290038003800768400c0c1c903c401880303021250000143e480690034400b8110000c2c85012038806800311911041d0f8105020b0022607054007481c01c00000e05500120501103000d00380080054003000c01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 556396214 1250 556394964 556394983
    0x71506030b0c0703050c0d0e10032f070210030b0117010803040603090206070f05060105040f020f040501030c020a120806100f0e09060d1a2a040b0f090603040c17 71
    0x704001160796a0410300c102640c4081019003c0c8482030000000b2100e0030464136903080c01d035079110a2810852802c0c000809151488070041c5400d002d0800300c410452000002d0905460a0141c03c102c84140792200da03102d10380c4003942250103040104001a003580107040814000e03624071603400406580031912000c00e0103001110b41040008106045c400e80040c0721140c0010003180ca44401955900003a0700c5451003229141c2161004100b185414442d0107801c182c0000190310342502c00c8000361080c403890140606040e6250043c0c885540308108100b01d05500081030301501903044c01c0504041e03000c40714a449804600b5952071401c0c41a9119111250300d51202c54800408500708449000020721880d008940c2000d04004074041940f0230500503540c2d22409120309100d8501301410014864864600100d040c02e4418051044201d42c1210032034502c1c1e45d22035003c102c08041310700c0380c460f40661240000c810300c414010703040c400a0032251000c20424009072103c88140e151035122 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 556397464 1250 556396214 556396223
    0x2060108070e0a1d01020304030201090210031512140f071e0819020301111c0b0f0105040b2506020909012106050a0b0303030c03010303020d0912110120010207150603 73
    0x40210343d802c4a5904500d084400714541004080503400f8000e00326041182e043e40183e45510703402d400c0d82030011701c09221015070b2809129400d00e0b01186d400311400780c07080e080540d420481050902009044d01050540510300351650451144165691103d490040c0c800785011074105d400d42d200189104400c0314040b0b03002e0700c04c040c407410f600340e088680000142d801d55200c20909401c08803c41c02044400e01b0b4510280742e00720640005400c5444108425004202c1a9440d8034280c1c0c111058408945030301511070380d00d00031000c1c004045160740301c1e00c800702000404400100030382038028100e50642a9202c003000e07039032146407204114080102c41b691161510007000421196004250310107610388000c1410342014010130b11b107902c1180c59031820030011005008040e41071001030a079002d5441c19041c180e0034105120303132503202000010002c0c000c00c00483c2160340036018400000300c0c0640c04000b0841d10b00102c60207548050021540d1903d0640112050041c5110f41d03810360390003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 556398714 1250 556397464 556397489
    0x30f1b0e060405131205040603111e0c01060503010c0507030f0e010e040f090c06091701020a050a0f0c0f050f0f0601120303051e04050114090613020f060904050a020a0206010807 78
    0x10407003808010400909501d0040301110340e8980842c4500c0ca80554a03c1a582e695039038a00d8a40000e084403040807054090700030810035038100f9110503000070602441c9400a60761540071a1443e4014941740c0d00003a0107508000c00310342c1c7c150304100a40107140c029100e1400e0b003104a101218980c0c0f0742c4500c1030106594601c005071508082d40a041502a240700c0050102c0450b01c51003510341180c0c0c0700c180040c0809206001d5a800e4141319000411141c0003541407110320307400a800c0c0d0003101c0044080000c01201641c00500c1400201c02c00c90b08070707030707107081c0e1044a041840e11103083e695200e96500c1000f45c01102103000090090403264a0400d011004c0502d03030381100605000307000c8480e045c52016070800380c6501200d00d01c0c003e500c10070001a0b4020b8002080349070301303801000080187c00c0f9404100480c0d500216402450354100c0e6500d4142ea80c150006806008808480341c0280c90401080110440383d402009569041e03001c9555a0b07a9912109650341d03054041d43c0e202070351 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 556399964 1250 556398714 556398721
    0x14010215010b3001030516030c060c0204060320031c0e10022b030b06070f020919020c0102090a0f0302210709020f1201060e2b0b01030f1b0e 62
    0x20b207480584441c8140241000903001d9040854204000d0403c0d901000c03201c81d0f00401c104201000700e00150301103459400ca881c8c0c0745465503090322085216210901003c1541c0808564569015501a4ac0c0c0400444140d889101440986d200d030302483c64060720441e4249440c824008226281195142d501d5400114102c0180a50004418003c000354880d21000c0c601040c02d14818030864040b0051500c65a191840c0041c1603c62a40750f06014050421804010449901489681c1c68059800c54115180c06041490041c0f1503401003000c58804104400501819002230a0310082100c5804c80540c0f69844c1c0c45110802d1311000790b015905005e118914050700806800c21047c440036100d1883e625040e28050ba84100060035446100003102d1110282c0408190301512062408861b001000700128152210080f81009040340c0702e101c20008039030605444000c42c1e8028031405095035070b440e0103400740711201d40c04c58a440c12072142e10f40f0458185c0205048400c0404152402d44 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 556401214 1250 556399964 556399979
    0x50a03080c070e07080703050f1501031526010e0106141c240c0207150c050705130c110a0308011202060903070308090a1403071a0c0f071401021501 65
    0x280007900e284403500848030000741003000408420f00c00c01d5151142e0b9180d01d0034010080c1141e60007010032403540c484e0b1044c803801d60303d030b034805d160241c400b070a00107003038040c001d50314030b03110078503444440046407290115643c0c00702100600c40303106183e0001d08c032118031a1803c900343d50450084100700c1005034009041403802d1507801d407071300090405040c4542240d496190602200030300400640d21610b40c008005000d07445803505021191000c0d0146600308440311001020b5018a80e08001040c0003200910400f40702c0000103001c0100b0301c6225500f089020406052600c840c440441e25108640d09107000104501c001254542d666090680c01d1040b01c03015004071400c1680c006005129100480e00c0812108001d07500071040251100003c804101001483e07800008003184c022101c1c110507100001da000c1500c0c20300900c41d22008110180000a008031401c220b0b50740304200b0300c8100b40001085002c103540c808002c03d0720303101c04000103980c0d80041001c1c2d5043d4000ca20010020013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 556402464 1250 556401214 556401217
    0x306030b06010c08070c06021516020a0b15090a0c0201060806070512151206040c080304050a0306020a051306080601030b01050408030a0c14031216020718020a050702040603050a0201030f0501050a0308 88
    0x20340b04241d03090505c41a9150004070311400e03041480541e0000074100c40750340310101d1203036104a5411031007000110584000b901d0307404850004103c440908003003800705110f1181204100001381c41c000a900d000c43e42c0501401d1079050031b81c00355203001004a41e0080c0880d10171700c00c0e00703c0e85500c1c3c6009007070310628044580040c10729520740b81d40b03001801150303146608202c400c5108001801542454200f807c00f41020341e0047c20240e004110412898983ca11310b50200e9410001c0180c4409417140203841c0b51044020980c40c0244140d800303d2003036000603040703000300f100707030303410894104098015545881740d401141c2a551041c0210303070045105011104c00c40d0702c00d1001c0c1d10b049500d903450034519040381114040d101e21090400c0911a640d10304500440c14520042c010a0710306182e51072203100040c0b004110341e40001c0c41d104030600500498100d1b81c2c0c083d00030416a6901e0528549800c41082c00f240042d06100001c070a40c074060003024140e0710700030701c0440010f195a9a07915507 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 556403714 1250 556402464 556402487
    0x910050912062a0d020304060f110a020c0126010e0a050c040f0e070905041d0c040507050304030c0c0503070f05030c030a02010234030b010e090d0906080705071704060f0306030b0601 80
    0x3c85500b0000911240b5050000d98025885180c000c2118800c405005007500c080041c0c4484003070003030127403605030742e8001903d800083c002e00304040152060391980301007a922002c2d0428a40364280005500c1c1440030b081c6100f001149000c1095031103145083e4032500c9a80700d01000110a60420b01506468a0b6402d400070000d040c045040c0d0360b00c00105055404070030b0f0004210b0b5907a00d441010480c107101400c40c11038110b40030030840c40e0605024040340000f5102804000080c0f0b094403c10480203c014041e08009045845a5170b40c1d0704250072140312801254002e0085e00c0e41610107040010b10507070034584c140c0103483ca445160300f01605019181d40704c06401c045480d8000da05030021000311000c1c5008540b12001581440d1881c00102400f03401003003a5070003903001800455125440801741d9050f440d00040b50346070010110b4a50140070000340885a8480750301d86645007201c000d00458089448502c005410901c0c00d0307040300c5281c44003030b00b220503803000030304150700c1014524003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 556404964 1250 556403714 556403791
    0x4050604200d030f11060103051c090509041b0801140123010f0e0f040f02040e06061606021615060302130c1b080f1204060b060703020a030c08091005091206 69
    0x200c141035800170740307026801c0c0d00030340d030326040042c0607081c116003004a07a444600078100f001c142031902000c50b0000100610150100f803030481c000070407070304500100c801800e0300c4000b4488015000c0c000d98000a003031040c619101c001345824107841000784e48081c41101c0c161a445003d60442c0415980c600c960120907a100d443c0e14080d400c42e03a40d84c81001320f601800351b401a02e407810010703100400400904450311826062080e10f0000840488415065603c1030000d03882d044040340d4400130200005c00205404021940c020001c26240d1240003103900859160003a2101003502c2d0f000c4411818801c80014100740809240b0641c4044040301c541c4510011407510200200c400601e40118030840c00321100d00381130005000d002d0043c06e44d00705084513414a440403903a0040d5076421a91001400c0c0304c00f41d40500107004044c400d072400500e000d0f100c1240300030001d0340100258412407845124142c0c2400384c2001400019041d44500b50340d003802c140c0181c07160030301b5011645028281d074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 556406214 1250 556404964 556404977
    0x10140d050627390901020705040525030c0e040510170d02280b18030309030d11040e0105211203160311041e08030304050604200d030f 59
    0x919100b07a0040c50700e004000c2403080c10241006201c82c1020745441a2004080801c416400905100800c1c612004003040404540d103500100050341002c0c01035026640c81032400d01005180c43c2c20744821581815000044103440b01241c60a13070440e58000000c1c0c002900000c140042c50409501c00303131f0054416400c1c200d11943d50081c0124482c0703407107008005500aa0b0421000301d80400442c103c5110205140d40c0d9505800018840050701c0000506881e0300c204c00b280310700301546200c400c1381801206695981c0381100030141c3c0d81d84000401c0700c51519080240326038034a00c034162001d442d42d001012009910307101c100403194050404401c1d580b0010043ca108032102000341c9444403405950322a124640014103200c0362103c0044a001d15040540c0580b000b900c5000700c3d000d8401c0b0000140320010074094940e401e9080360404885444000306100601800051040c03045100c5c0a01e400e102c0410749078260034500c0c010407181c01001e8403d880f00024010b401c1500445001d01e40342 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 556407464 1250 556406214 556406239
    0xd0906090b0a0e0d020a0f080906090d08191b0f1502180a09091208190204030f02040b0d0b072d0c12020f0a02040216150b10140d0506 59
    0x107800c403280c1511070301d072455500c2a00ea903016074244000c08042207240054030403402c5a803658906025005c00007092907400107828412035849400340c40c1108405044819260a6850003030400e5100a541500d04002810a4140103101c1d15400100341d030078080200c1c56650607a504107041d480c40000301e45030906401c140203410352a201404a00c444d00032031000002c3c540d810b211003d07030545c00c8607807401d0030301860801050445500c008640294940010542d50358098000301d400c000c142443d88500021f00042030290315590080024003c440800c00d0f20100c4040000079407130b03050000c0c0642d1106001a11031401120196045074048c4040714101014110250303c041d85442003101182a0313001200502022108010f03194085000921205480300142ca581c2c01c1030900092080e9000200409041136202c1c00c429141e61000d0442c4402d03000002034009007125410003802038129100143d10710384105014080100c0b00c0000790b140400b0078000700d000d007030001c180540200005591 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 556408714 1250 556407464 556407473
    0x603030e1c141f140609060102120711090108011806090c03120f0e04020306010e0f12030a020f0c04050c0a0e1f0e130b060a0c1a10140409080d090609 66
    0x4114881d88a40b000d800701040565a01030038200803442101c205181500884103542c1d030140c0540c020710122418180b6a450f500100c6c40c0aa0100504008840200b440790800042861504003d581221540305a0ba20742d43c00c5070803240f03503151003c0852010701c60480841c0069100c03116203402603030b00c2e00ca026100d850b19a00e1200d000c040c3c00004460105040401c0ea200c100d910b207448003110150714604001000030421000c0041640c400d00c071942484140341e03280e5146000c640e10301070580391515050f00700a502d07026800c03d10881409a01410080e501e0b042c85854031a000f079511007070030030090880440c0c4003103030000da09030002031030f121002c10140d80b102181605001551009210040e00301031040110001c661004030a041040750700031983c80c08180ca0121815140401010410741040b48450600810b10307540140c0080034003c0c15103281030954242ca289500c0700c120140d08105000843d48118400341030004244582c2040143d69086480b0480c050000454044140d13140c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 556409964 1250 556408714 556408733
    0xf11070308040605031603060f0603020c032808070305100b0304030509150d060b0903070501050901050d0e0606040c0206060d02190b030c09040b010504030803040b041707030c060f0603030e1c 84
    0x4168040f500102c1000750880003e110110b0100447c40c040c800c0c50714140c7c00c88400d5002d80500c1045c19008140c1c003100e03110410907030366010a000c035040e10031342c0110021a90020710303151a41c002040000000d441900901030309000c4e03100901c4442c1045d280c40801340407500301800445c00c00904201d103040503681c54080400c000c40c1102c0361650f0715010f101c2c4504a0f49286e2100070a64418021200c0a83d400300355003080714820f003085d41c0d80d280c00c5801203566110300180d8801803072410342d070303446095400101d0070f1149409440810016054400c1030fa510a4200d40103544034503c2d168440060910f10103d98281140f80119003201e0f484044400f038039081225010448480821804800e1070103004101c2d40c1002030808516050441d2146002e5203c001c1c40a0002c07400e01010030108000c4000101507002d040f01c03081e8840245d0710700100501c48500080e00c0450a01501c845000c100c4e200d5041240d0f41910391040d0740dc0000c0030b10006544282c050141910b84106203408246080d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 556411214 1250 556409964 556409969
    0xc16081b06010e0114061c02070c0b1809040f12030f02120a0b01050903060703090f021503040b0109051003061a19060210050727090c1119030f1107030804 68
    0x40c0908459810045800d040001c140e0149402002500c0301c901681ca400c0211104d198801d105003102e020292031900103480b4040f070040441c1008070000480c011880d01406a0342c1b040060090400c1c0390030300300300d0b41302e030151005045401540784281c00144082d4101e52110064200031500e016800700400c05c80c1c0002c4142100d00b12500e080020340c16139803040124280090800740d042c030400001180da140c600501050a240ea190741c044240118560643d4029074000d00350f0740c100100e44d011039a5a0811ba50840341d00d0004ca0001c117109842c1e014151152813071400313140015140d601c0b98005010390350402c03030101700990b15202c12038681c6104007a0b150343c2c09605031509403601600034034011104061583c00c510381800c1c0107c05521501d0940510403005200710b550740380c11416220318450364070054843d80b5100560559540013040e03190f03044010001d82d016500c0b60781c80c24142c8a135403440200051800075144038864000c42c1c1618000d03101c6002c6614403900e980d1142c6966000e134 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 556412464 1250 556411214 556411267
    0x50c040f050918100b030c1014030c040f06120506030d02030a0302131e03020108153d180801140402040513140715020102071106030604090f0f1a0c1608 67
    0x45c03049050b542010008041032010aa407000c0d07a0a01c000c0c4024060320b1480005100110b0000200300c0400a0905450203401e40c4078030251059920307a0007406021a9100c2c81407110300304000140b452402180c1c542c4500174a4000d18030b043c2d66070030224001d5010854440410156407808104603171840390309003200314070f144000c40c1d90382503000151040800802d400d40402d0302080900d01078460000c2002c00e8510300c044180301070000680e10a0b2035250025001000710b1085140c2c159661041800043d1652400c05194584d01d0b545424240c400c004c0313a4400c00c420344d0b004200103051030350065501c0341078440002c0b8154007950f1810b440c10380c1c00380c4140700340c0d0200c0001d104004207407140318410b03081c6000840c0381060780d0703842804000120030b50a10411021000900d151681e81141900343e600540140910325646030001039240200c600f036907200005c0440c1000c2c0b4400c0041e5600a0491b80f41c62820810f2003804120340000140b000c988031982807002c00f00340c0440d820900f0b042c0c41c0d031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 556413714 1250 556412464 556412471
    0x9120a0605071b0c0519090e0a031404080a02271602100b030d0f09090e030d0606030605090f04050111030c09030f190b06120a05030c01050c040f05091810 68
    0xb00c4010600200303140700f01d1020076104600d80024400c2c03035800c4122001074450341145114480003174504500d03075200c0d005550030400312018104004c0b5407403030014429100c0c00704031041800c02d0b00e00c0340114041c2941e40d9208041600c05860320000c401c0d040e0180200d00454440e801c2200055031905903651440d8403803081550364001d80502020b5405500b80c24100101c0d582100000c1d9245041500c450510000081d82c1611a21400710440901700e0000c05105209011000950f40d5015058a5480c0c07440c108020481c14442d00519085400013000c40b821030b01c540004e07100803103000d0000c036810766940180050405401e0059417180044c089010340329034030f4105260030324840340111203141c3c00c4030a581d280110040c242200383c2d90451507500041e500c00340402c08148003d0340c45222032080880780010010000020070300d00380008020f003c81d803a810f100d100d150040303000341d50342902d90580a01060510b0085603900460074030320252090491509141002038174a6541e0480e0385 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 556414964 1250 556413714 556413721
    0xc0304050a0308071a07080a090614090a23070605160b270703150f0e070906150c0201020a0f06020904060e01092a080405030c01020408071502030705070b09120a0605 73
    0x1114003070340c00c0b40540f05c44a40301854040401003950200501241802d50341d0f4814009001c4140d0100c0b1300c04013072070040049800c050300f140390341d41400501200c0511100204480b40c0a0a40007000d904006000400303140d41819000c1e10b29400c00c8041d04190581c4003800c00120700c1c42c0070102d028802602e501d50000e208440402c005070481342e50131105900c4030004000041d403100303000a010020507000a03621700480900006031020b02d0352030104d4852800082111001c41d0700030022142190f81c5d000c0e07140c1c54a070041d9840c1c80e034903201a015802403c2500045043c04080301e10062040800514101c40c0c280000c0803100540c0102841d541d0040051003105403034800e01074407941d100c502c034100040c0030321140070a07520801103004109220010900300031041054404000c01c1c480255221615122903a41c1c44030b407403094044d043c80340090744101d10300120882d0489a0040040c090712810210240d10551003008040d0304134990301c6009014560034030169a00e18424a0701050600303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 556416214 1250 556414964 556414973
    0xf0207020a05040b010801091112040809030712110105030c0d0e0f01060f2d0b0c0a0303051305030a0f020304090608010905010f0527011b020c1503011a0c0304050a030807 75
    0x20340390b04854000c0e8136042c20400c09a8120400d2411070f5201c0c0e5010031450111100e070f9440d40980098148288138410a000c10800402701070110310790242c04640005503940044609004504006000b0071001020b07940c042d44990010351744010380e440510710f410441d040c8041241d214407003001c0641c00500c042c0407504020b0092074010076441c1c103180b403590300b0310038402c100007290110750550310042401d01c040c017501c00d61240018050201455203a00c1020005c070346901500b401100001c0c5000000703105102c8420040240c1500705009500341010100c041d150146000c410b0400c0d88030074440064242284c2c060301340030b00a2a0004101c0a00901d45903080d10750041c1c0030002c0c542004c040010101806609003044928080f800180f90443d500c46070040000c040301c3d0300300c152007040d120300c0a5000142c001030317003600381e42d0341e20302c1000305840c0c590500082c0105095007400c4114240600980c0e405014114070440540340b034035565000082c0500c00940c02110b4554002c5812014070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 556417464 1250 556416214 556416229
    0x81303031107150e010e030a0f031e0f080c07050a0836010c0b0a020f0403120f1119050709090c1802090108061003140408030118060509040b190f020702 67
    0x52141d400007980006103401e015000c139241d420301504215100c50f4034032242c1d50802031309400c5600b241149804036580d00303004241008038590010352034680412102103030312410303860180349801c0d0780b81c80386504c035044044240c2d40103c0c41078816105841415000c111808000c10700b0314a0040f080c03003c600400711081040c1c90350502e20721110740816a040c0130b6604525842103440d8088858485680d401520800034000c0074041314a0301c0d004940031003008040c5182811210036911481070f20b290b039000c00c0350702c0d08110491080d00e030011070001c10b031080300314040390072940301d4001e94107c1502e61405400f180d1039030a0640d844044002c00304000560598040c2180c1104101540350194140c00a003c90f0009408203000740d03044468a24114803e5010300d60309a82444840312030b00b040c1c101001103800a000d98052000414240840c031440c0748144012210042d114904907699603d81004031a40100580100240179070036425260b4248900c5010408142005803509a03500511890 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 556418714 1250 556417464 556417469
    0x6050703050711010e03030403081b071203050a0b0d110303250218090a240c0c0302010b0a030519020301020906040e1005220506190303090e090a1a04081303031107 72
    0x46905d4905091035000d030200c21030380d0003901403c205000d07480b040300546e01039100d207894103491000445c0c408204000a81801c05d614220366080c01242c403101c01c20303c00c4408080c1d5042e0b100482c06070110024101c5503943e03900140c020141d0327041c2210040c111115142550341c85110b0b06200c0080c80441c80c01120b6140c00940d2040594014034001700703c00c1d51340c6504807024101010384400400103003880c64031000c40f484400d030b041c481c000a000c80a0600b0f959414114055400c00148080c1402e0040522080341d0700b080c0208804209a094016041d10602c403d0741c255400b008101d5181d19050014001090300c5101ea00103403070400c420b0300c84020203801c01c911800e9180444401c0d4040c42401c00f420540749140007c1a848040028032110000500201684c40302c00002040c5a0012582800c44079507040c4100e5035951070890640343c040201d4028001c9403041d40401c028a074082480340d02502c5051801d04d801c1c0c3d2240717408100c45440c2c0c41100020b0034505100070600050011200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 556419964 1250 556418714 556418747
    0xc052508061e04080d060b07051606032f0f03011203020d05090609011d090117010b0a0515070c030f06020315030c010806151b2107020d0618060507030507 68
    0x200c41070344080e00301149001030006401c0113800300c0d02c0000c0014650012009110408689545540c1071411a841c0c03481c0010076040e56240d0705000800d00d000b801144120780952001c401150068104140506d0a200c20700040f08800d10204003006081030042d4040c20080c000307004261054a0000c0c6003034054800c030800c00c201031207051819100c0c003040c3d81e078160090030404800701501c10504a00001031079200d41c401e00100000034214070304442003440c00038040003402000a00c9040c855800c14503c2090b401c2080200c4480b5410084070143c60f00ca071051881103442a660b8031081c42d404d2034900151100e0340c1c00070501c0075150501e8034549007610154064041186405d0002e0000c07003008000340d0060480d030510003001d9030081d003229100b20452460424090418690507500c55810704820191800d0707070840381c03441013480251b400305503004020a00c1800c441e0340d401c0140a40d00080da40702c51540d0340f007000040c111f00a183c490b101c1c940d4001450f240200d00103101e4508122041ea = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 556421214 1250 556419964 556419991
    0x307081b19020f0f030d081501050f070b06130606020705040513020a0b030a1508010c02070503030c061b071e030801090603031713020d0b0108060c0c0d0c05250806 72
    0x2401c500c42114100c1e25030b01120f400703000c4080300000c1102a9100c1c0340859160140329400c01d020f0b0b03007221a0f6030147da034030012484e19102000048d175440c8120041c0d9890100b040c8266130000c0c43c9044401da00000241015a4405038131411005071481c6403c001c0142c1c0024009012500b00b610407181d0000a00d20000262001038001c40c40003811801041440380000001a003000c0d030603001b004a40ca0f002e26541440c90362011514000d040f158030100040c09011400219031400006552740703030941da03001d03200719142c5500c0001e901e10ac040c2c9811074840c003409620007050341d250703418000c4000c0c250300450f100880e00d4002c141400c160000c9800e645400014808242d02501701c004030480c00d035400615885036605008001c00d0075000941c481000c1e080b28003045104848030b8122801441180c040e07440c2e0442400c11703402200040305480c1c0c0103240501c5642e05c00c908a060240c01107003a00d4040001010800114600203c8a40110741380441048600003c01c10145d11914217240c2a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 556422464 1250 556421214 556421233
    0x1302070b0709121b0b13090501121203051e07050c06010807210206071b091103070c080a030f0203010f0503150c0702090903090d06140711120d0e0307081b 68
    0x15a1050700c2401030f2450281501d6a40004daa100c00340002d80040b500301626002101da0480b6803d2680c041c3c40c0000f820040001000c4400040c0e41010715400142000300d0f0090140460080030020003044009a9114a180b111164078500074001c51942d030b00c5036070b904810064070340313481410b9010790302a034000c0e4403c014001041401c44e803060b0301211408070035200d40c0009070007170042c82c0c006083c2c13441c0c1c004003003100354000d14881c080f0340c0c40210500140d2446015407420b400300315040390225030343c81c04a4001402c4900180204e100905000490a482812907803c81e0402d1300005904503558405004a00d4108019100127070003a40c000090700d04046a0340c524044d05000900656400300800c0d0342ca0003e20a0b0303024000041d003c1c010004d030909290f00540300261581c6400d00e040c001003031843c1d1203030601c908451070308401840da041d0400705413041c2d9440510380b106031950ba8820400070f501e00740004d20f0018080d030b003035030703100d221802038200014042c1101066541c0803240c40d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 556423714 1250 556422464 556422479
    0x70b01051e010503191e050f0709050604050607030210050a0509070b0f0f1b0a05012007020f1302041707050117070f0e0f0913060608010209090c0a0e1302070b0709 72
    0x2166172100035000140380c1c0030744520084014100208480b10054424050600140b030650f000621610701d4580c00940b42d01c41c1c280075602c150301d5014180c0c110400708030600c42400d00400402046210b481161141404004001e0032194243c514501036a00d80040c060006410848480a000310b1011240b910072001380d840b403070384a0301c0106410941d000c04d0385170761001d0460b54102c150145000391005074005180c010300030b05c103c07080f081107002035506101041c03100c441620400d035800743c40d6000c200c8000c3c00308001d00b1966081f5518040e0200001f10761000048403e900e160603c0c0d004000e03503030400c00054012265403050580110302d280801c4003150b80800c4100b0780090500f058850385654030041104804503044264000c1d12640038440e202d1000325019207424003030407080081945402a40342030381310740c42110358090703900000320710030070344038001890021090b0810526082c1c1030f402080c6c0d21504400961100c44d40400d0710000d00c04000e0b6450360100d86450030540a0341848603 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 556424964 1250 556423714 556423717
    0x3020a1403090105060f101b031707080a061203051210080a06020414030a0317072a060c0201020901120e0a060c170610050d0f061e0f120305030f130206070b01051e0105 74
    0x9203100c818503290052341414080c0e103244601d20551027540359036142c2107402806125054034110360f81480c1840000d41d48403100d503050803007945641c4042c07500320b00780701000c2548409001d49880c10348612002520800030021078070110310824015171540d1400c461010140302e0140624020382185481800196000307030380501050000c0700c00115a11030010840d0f1001c5c181c081c21495607a01900304441542040c0048041440344070706000001c00000e00b24240d00032403024601044c3c1c00b105005200c1c1c41600130347c071201c10b207104807091003015450303400542c1c1300150301c00081010207000b0060304504204556100741c05442d081c04c005451040141148264136811244e6582d9015115844920350041c10040c2104044810700c056444013030b00700102c00d8400d07080b14102031600000c0c0060b11031140400700b40c05407100307811a0380714501000d4a141c002c0200b914041e00d901801e0061381c80102400b2454006c840c0c2d0300442d0b04200900000c0154a80c060040095969221503680e92080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 556426214 1250 556424964 556424987
    0x61b02061603180608160309050303070c060212070503061804150b0102010914100e06060a0b0702011704210c02030a06150b030109150f0602030a03020a1403090105060f10 75
    0x22009901c1169800c08880075403050112141070303010703410000364480c0d000c04054090340d68032090030401c1c1c0c5d40d0842170b0201c40a030503004007160018800941d400f0302503a041c40981c0d000b64005482c000034080030000b40761086030131030007184000c0b0500045042800c040364060b510101241c41d54109500c541d424040b4104180461070f8a40004000591003904010001c0e41e0180c0d45101031440041c156840300c1940c5032182d02c3c0d0f458032500540d034501c00103074103000e510003402d100015400d062800c4c40a6004a0f416814881400f03209540540301603138481c0300301d014480402c405542c0095030005440c1001081041220407211000980d80219a80481c4c0e80d2200c0c1c0000c103a850400d1140c10140e041d0310406850401200008102c4c0b0b03540c00009074803c0078401500066120300340010140b0942c0100780c0142d1080c407240a80600079401400f00803203c2c00c00c40c80d20b04020400c403826501c1119040242c0e5140c00030f00880342410044c0a43c0035100326103025044000b10300042c17003640700c0c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 556427464 1250 556426214 556426237
    0x61806080a0b010e030109030c0b070f170711030301081609020f120405100e0a020406090501380c030a031103070e060f281404120303051008070f061b0206 68
    0x5510b0408941e0060802e0b0b01c902002070700a002d51740d420b003805004489002c0c016501c516050000031184c92051030810903200b13882c1c030b99496032030402c1810880c4000c0144980144105010b414461407000c20296000b03040d080002c12501c0140907a030b245161281d070090800900600000c01c911031f00e42c00ba1400d007114910901c0980c0d07290b0620b9480d0600001c558420703a441c001c004005e030400804d6008a05000381c0341405005c1d91041c51008440d02441102084110480c181c04241901920900200c12214180b4800071148604075101d41c009507050000340e000007041505160140106106c01c0c0002c4031003825864007620103010802e514203031510440d0b000510940d0031011400341c48000c110080c0c3e40b0068001b5640c5ea541c1d46229042c80408110440e0358802c5400c140001c0b64191049170300302c1d41c040c000f940d8050740a00710103400d03000c580520001c0441c0c092010044540108050411914407070314002c4058410004012000f000640e1170b00040003503143c20080fa600481139 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 556428714 1250 556427464 556427471
    0x5040509070315060e0901080a21120c0801061205010f1203020307080a050306031603230f0f011b0201020f1e1204080d0c020102070c1712070606061806080a 69
    0x80000440040609462038050702903201804280a5401000c2052080c4241d5150703401c0c2e601d48c90520354407002003a00810b440714200080303410782c0e5184d018030f0b042000741c101458040785050241c0305030b031080050302c0000f65283c0010440117520038480f0450302c0d5040310410117941452078842d03900c580c1d4040d80420482c44c0d102142014400c0044880d402d4101d00d81c5520b032082c5150003001d82d4003e603043ca02c684a1108040c4684104112400440c0e6100f0041840d20404003d89140b4912800c2211500d00860808480a20702400030018a001290000411100c42c606d0303040c0301c0030b484e41c180c000c681c414080c0051101030304003101c100c0d00c1e507078507201d01a4210051001c403911658800c0a981026201031100308070202c4060515034407500e00512203410402422800c038000c4c004050060412000100801e0310400004400c220049007602c902c500340322160940c907480544100ca0003a51020b08100305c030703070000e80243c6820a652450500614003107000f0000b01d0003030009060070343d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 556429964 1250 556428714 556428721
    0x80702060f06061b0a0c080d051c14070c03030513030206180715020109050105060d11040b01020705030a080c0d02160b0a020703200a090e0a0305070f0f0b1501030203040305040509 79
    0x1e0700800d0384c280b507944021030091150540344035915590442403c4a0ba407140740c5000c0781440c030100342501c24920660300c60f03082c0081c4068081c0c668840821000c41181c1c1d4100340b101c402000004584514a551240200380d0342d1454001e04890005048a250509102ca590002031b400f044040c1c2080b02188680a05a14101e41c20704280091b030200310b480303000d030409070a4103030190000d82c2043c0c0114000c0110b6950203051001643c0e105000030300701c0c0320303280071005a131600d0b80c0704070304e075240601c1141c1d240e13030b00c82011034175203100107030107980901021400d040400f00030010840c0c0b0440910207404c11b505a044548940255030046450100011644c020014401c200d003400560300301d04c1116408880b840705024a05200020602901c401e50022400364070a028048001c16040020941c00c011a201100c0c0c3c4d0308207a00072100140e841003544040b400c0b0072456091075010350071540c1e150418110300b002150182032050b0501d401402040086038016080c2e40440d1402d8405d8102540d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 556431214 1250 556429964 556429969
    0x601121509050c0c0a14100c081801090203030d09020906060906090d170d020a1b2103090c03120f170f15040c1229041107060c020c0907080702060f06 66
    0xe21000c281c924882e8100050174005022489024001c0010a03640401c42c407c100900347d0700340340000e101194141c00420442490303503441c002c03040001c4000051030401b56001a0440d800103585d03216580c2c55144030415440c10a41d807079004003080fa41c05162464003400300d2070394050f007817070305100f40c0c400500320b030034031410b02d8450247c11080703051155210503400d41103000b03400054560300064455051074246404214100009680008442289288607175000418115800d058001c241d26413000d00005040d11a42d0b90286105008124a03100c40c01c00c001d2103098502e00c200e0421003404c245000524800c0c5045802c140802ea030090349945103103207250040042035469030040d240604820501e0392102c4120f84800d104841844165845918100c81100c90054011900d038404101c000390314207a40b1025078032000c04000d03420080c0da41c80310011240e621a001015070401401080c20385000d0b60754562007101814280040e040020380296108401051990504134060100d11141d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 556432464 1250 556431214 556431217
    0x30203060d0b010e040c12051203090f0604060b011106012414120403020c220203070c14010f060608040831170c04021e0f0904060801050601121509050c 67
    0x303a820140228880d41c1d2a000307a0032a140444064461500401001c41c2202940f6066030750590032100421031000d600711014031a500140032f80500b8441d9a00c1116010800e03c9058030460151030005100a4010005440c005000794102c40940200005010113600c0c02c03172034020050419032808200c00001030980c0d002d46020440c0031100c00125105d54400f101003143d07441a4443e6091b2000355284005220480e59122000254042c0300600c11940c1e180c668040c66101c0c9840c03420407034924054842450300c4031f088a0303685060351103c900402808542c01003000078901840d00c2c0c040c0e4038054440c0d0240f4010400b400d01c8484407030056581d5491000d022540c00010300b030121000d6691002c00c0c8000c10110440c080c1103000d903207404425440d192003a244031500e11a4803041e941e5101c10924510780c804039480d00182818400309829459038803444001c1c281d4480001018140030002408000c0505082c0c200181040240034001060002c0601181d00c4120041010384505221007000e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 556433714 1250 556432464 556432489
    0x1131020f0706092001030b0f121905030717030c0405040c0201090b01230315070f0224090105060a0f140105121003030809010b0a15020f0f011a03030306030d03020306 73
    0x4940c241035943c030601403e40d059051004050003032660006402006405036400005e8266100d00004c805d03d01c0f0b41003400144a0044400c0242e400440e03000000102160b6014001d403002c0c0c1c030100303141c4100040e400c0307020300076901c1c1ca0006040d072034038001c0e517a1144038a0092500941e1500e20100506000750041039007158029021002d0390703110090b00300400c0c0c50359414149038071400302c0710f0032505001ca010710705840c2d210030800c4165a0210306481c001142c1004404500c202c40c00c00c9210301c090f030704040391440041c40c000725a0030300c01c00d45400e40b400642914460074000604005010203010510200c0300c80b000000380150b00000141c0d00d0340a80c0103245080c4080e00200605c02106c040440f0550f0710a84504c0825100c10304414204c40c1c1d0024526003106900c040bd00c1120141208040078980d18412114142200b4000310b041c41c88500240030160b440d2032220641089000c00441e5a282c1503004500307602d42500001d640d614a80c1c060790a2540c00000711304d40b9261070030103120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 556434964 1250 556433714 556433723
    0x40311010b13020a030c0e1f05120a020301050907110d03240f030c0608010807050d0f020310060501080714030c070f02060c0c0103060b0a0203071b080a1131020f07 72
    0x41e90945036400c0c003e9408600701000080c640088201128004c62000041c0d40d0044c11f9050807400e14480c140400080f045a075040c001e0a00003002000011080107105408859015844e945440c0501c650307600045d20910900501ea42920010040080c1d0319000290074900840c00d0040601990410350400d8220707a174144403404040780c60342140b00c0030b804881c440c4403804941941c41ca0215006102801030348880e0b00402020407051500585411106002c0e151083d1300020075030000e46800c90a4800c900f00340d407100d60410a56820503071890307200c0758230705051080d000e015240c1c0003244001024400c0d000e40100d551414030811002d006080b9902401c0c00ba0341d28900d10b2860b6030740d580180018002070a00c4c2010401000c00010341d100f50400380c000b98100b0410f543d41007000208582e80701f44079603042c980002c100100700154a00c5a0180071b45000d600b4118051025460032141808002d6000d00c0907100100d4403142d0482e298508d100780142c840b06034172084070003445030a00281 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 556436214 1250 556434964 556434979
    0xa05060a0206190c050a11031201091505010302160b04110a08030d0513020108060f0d060609020c0c04090b0601050703021606120b10080726010b030f0703090803040311010b 76
    0xd0180c00007035490040c2100c2185001c5880b410b203410064070601c0b156400051800d01011820750b0243c10050b0301c0c011100d05880c00c200b0080d0010740e0424007640280d50b01c40e1101d055001d41c1500151850180c1800e10f42507181c9941c0c141c07280c0d69803460b10380c010900e4950f50005424088101000c000c2c0c0300004101240c425a01c0c107641c7d550390400b201c0d000442e45410003140054021840060a9580c1a103402c42c1594901c0c04001c8541b811980c00703900b003071140903030800081c03c0c1c2c031480c400b800d0742e0314006032a050340110043c58a410140e0440c0140e140c1558040440d10002031150f001e01c0c00d182ca2662600b252a0490502e1742400c14424407026444000c20b40c0c5801c4030900040d904608800c022070013812081212000d01100312101188080001c241c115110346903031148148040c590310042d10b40c8603890070701440243e11844c40d880000c014024841c0c020813030303203801c003030103250900c030551b40391301d130b1150a103c003410003800c3c4250094000c9802030300b90480302405400400381c3c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 556437464 1250 556436214 556436227
    0x60603020415031403040e07080a0207050a03080702011112040803071421250323190e0601031119082e0608070b0702040216060f1401230a0506 63
    0x1488105043c04112240c0e41d003240c90062010001007070b0340c200e070040d0140f10f2054880300e005403400600a03100303a0685030200f040c04082041005241003051007940c40451502d0041030007421929000d503440303001c03d4108280409120140110782d001a00b009e20350b070b90380c0c5556500344c03480c150180d5142c038882004501c0c50002125180700d1420b90860700106002959480030002c1d1020f2030503000d000000c0100c0da4118854070982c405100030152403c41c00081610500c00c0090301c10482c3c04e81c06000380260b054510100a00911000b0000c00005103015410b564850845070100c44240c0d005d803040443e03003640550250141001813080d001580d4080c560000c451107040403841b002e002c0100d5070440c03e86414610b01c00d210444000742c000c0c2c102075082c02803040c9141e01415050780e010b0380a20560042c1d80100d03884400c0c06124500c0098200301c041e4201c0c081e81d0f940d03c0000c0100800e500104207070440640c1401c40c040c0200401c20701e0408000c00075a00c5400ca4000c55080480815607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 556438714 1250 556437464 556437491
    0x80304090509160f090b0d0b0703090c0b040b0309010609090507140105040b03071e080615070c0b0307020303040606090908120405070b0c0c0a080f0c060a02011e0c0f0305010509130606030204 84
    0x512042d501101c5d0103000318105442404204051920002c200d166243c0c001042c0c144240d1100030b204d803140c4200d10b2641c3d6120030150a42d042600240485540003092003508042441440d004044a050602460400e034a460342c82e6601d6109401e1200c40c590507000281c4e102c2c1e000c48001d040d2200440d40c490400c1100101111000c02d040c0030b903118400712030202c003030003030091501c56100103280c0008a40c04072407405941e00505012070b104c1886003004100fa401d42c0c0043c40c410a03c0f540299145e01d00390418400f81d41c0745a10130031a840c50040f070400491300c03040446501e24201000e45034503480350719042c0d03e4000d240c1e10003170410b1030204401800160108a401c81c28a0032503041207032070340710028030341c44e840c1140c1402407650103a04500c50506045000e00301ea0480350000041c114a5260300c4d9280d0500d01903482082503a0f0700c1103401040d00092040392807842c0746400c2001d9810b04011445550002e4048844002e290b0001c1041012680000021310744c0544140800c42c10b5045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 556439964 1250 556438714 556438739
    0xa02010e0106090e1b0306071407051c080708070206010b091c0b010f08122a0105010b0304021008070f031d33130201050d2417030408030409050916 65
    0x9403041c5004e07501e010400031007080200c3d04001c0d0018058900c4c2c1d152100d0070394010701e9010581021900500008002c9101400300c0400c4d24405100024040030700c010037021020018081006d11551005020403a07a000520390b064420880295950f1030500c0000390340401502c00e4400350a070003c1c207100402c003850090b0303812500302080c00015030383c41c0c0d0091034075001d165500381c820040901c2072654250609103143d0f001280ca010703500c100c0c41418029801e507503003608404020000042031000314107011031149441c0d00d580c92b2014240c2404400101002c00500688040680300c1000a00c0c0402032003804c04a101400c0449041000c50040c079002ca000d10b60402600da01104040d07103610b00b04000b114840c00d14040c80d641180444e500541c2c2030341104004141443c3d841d80c0030005005201c0d00300350a19008a800c4550b5803505410007200400d07011010441d0f00305110410036201c0000a0340d0666404110106560307840c4143c043c505000e66508000400c011080010035201911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 556441214 1250 556439964 556439981
    0x71b02010f0c020d240b01020a15060b07050105011d010e06091009240e0601020a0b1009020d24080a031409040c0f120b01170601111605181003080a02010e010609 71
    0x1006180886445c0720244219142c155503140540c1000716500001000b07042000401000f100c03000984a46a009008864008100c00c640703984d980c05c0180591002417440742d9210800c06440205581484650424664090250340c0141c0301040800c48003034444000c0d00162549070744c100000c0800e45101e00500102d4a01201c0c080c114510204084950800280c400e0b8410b800414085000355500c0d10707640d100404005603200035110100d0380c0f85070f42c002820244032890000c148428401b4569000d601c0000441c0031001d140c0d601003000f4100401c00180558250921194030341e440e5108580350301c1801845503025250082054070782e904908003a585010030354a4007423240c2400c41d000129071140c000c040c08280c02c6000e03081c3c0a00905034841d882030041c902a20404144000781c0c0c80c0001400c800e5031412410304003842170b0b0503d103060700c0c00303403ea050b48540a070410030385c14140d180701400003401c50540004c00f840c54038001d400c042440a0114000c02c50a40d4503c0310500402100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 556442464 1250 556441214 556441253
    0x30e030c0d1b052104091a0906030d020c190f03032001020a0e210601140f0406141c0503030106020a11010507020109140112060b12071b02010f0c020d 66
    0x6510781800181081030320702da800d82c000b00a1a510215030720480003103c4003a206442e441c0204400710f01c04980c0c0c0a4002d40c0c0d14894a42d503404605001080055480206024040c6c1c1c0545050507500d0b070300003090454142d05584c0b58055190014540007071166030b030400e0401c4036400d0340000405a20410403071a81580380c000503204140b511150f404e038412001c400d0300103441c000880c00c075032800001000b41e850440c4019001b1500c0000414140b590980c00700c0740c0b045142c15007900d6810a403000b08441401200c0400540d0309095168200da46001140713070148000896400e100c800403000c2030a1a504401104d45940c0e480d00020b40c1d0b1800c6040c1111400084592402d03103501400640d803003203a050310b4880c400c03818001c0c0850030b01100f515003410042d80329000411000b035846001c024004a61074181e4503008249039003800007000e0681c10400034509a1490004010880c110085074246802c1c14104042c107012101e41d25032240295010308441c503841c0420146645088888200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 556443714 1250 556442464 556442477
    0x50408030103020312070c0b0a0909150302030f070501021218090a09030e1e011409040c0c0c0e041a060f09070309060b01182907050d030609050c090907030e030c0d 72
    0x44060045c654018650000d02142d51a2414462000c1150140c0030341805840d1490035107540d00120815250340d4042c0642d0041c0500083c070540c1014001c10805241c44c0000707110b0b5518100001303542c0c1c603c811910380034040c003040c1388220350700b2103546801100008040c0d41240c00d09000002c02801540da0803008940c03252500e410343c1c14a0700f00f219a204581e22584c556648440044d078000040d050f00086107a0100680001541e03148030b0a407500809698480d8000b005241c4400d420050343c101c00e400460310410400021800140400240e40ca80a100415240c2e50045011440d000702e5a561048803003040116041d4150b00601883d406010305010f03c0300300500540345c243c10a020b401c26151000e4060040c1030f81700701d032841200c42d1000c09910901819a00e1003040d00a2074080310a50401c480c64000d6903858040d020107082106020045400c1012042c9580d2142d4000e1078000c48040c4002410280079900000c0b448084000350390303030380740c400d02103507126020008203401050f00d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 556444964 1250 556443714 556443733
    0x5010509031216050304110d0c0b07030201050f060303030115090909062415030903020f03040b0c061008100e0a020d0506190209030c01030b060d021c0b033d0504080301030203 77
    0x108043c148098009a80f160780ca50380740e81d102c00640d005d00702101170b040004101e2a100140084850000400480c84c00fa51100e4182c50000d082d144060403c00703d280e24036050000035500030045904513040030705441e848460140702683d00d07241e60f0f40290b520074602240c1c01d090004e5508a8030303194400410745c40310f6001c0280165840c500c2c82c05500443d0103031076802c05200e8080d901c41031615009004130f9458440200d4001d19503440342c1c100a0745103102003010000d8003401c0010b0b41e00a646001c800f0000742c10312540c95541d40e041c0540514203511000020351180003405524045074025100880c4452142041c5a8940c8280c892825590b00c1c40ea07580c40445c0c9510070f5a9040c8002005024500e9404004502400c800c0349203a81c000d1041180b8190302c8446c4c4000e220f215030310340c075189110b150030700140304071083d03600c110f402508803a00c04090300210207804079880158118220b15100755442441004481c00c030b03d0030301741e0705e40803e100902001e24041c60481c0d20890480d100002c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 556446214 1250 556444964 556444981
    0x609180304080309270a110f07050a030305160206040b070905030a0311060c07020117101512110f0304030f180e01030b0717010e060613120510060b041809050105090312 74
    0x20620105c01502211200124200e11541c0c0c004080002c007030a01242002600e0321201c58540c41003504031050740c4152031100800da0503001c0e440e40a0480b02e241000d400500c20082d40383c0700010001014031103820b00060703200d405014000003030300d07000d002c07100400054075016104600c240400c0e0803d120340c000203201c08810345d08a402c0903034183d6a558032041d20000208507090f000d80350361600d1000078004034125080c24904d205039809507565404100aa502c103004484c19044e544200007002c00c1544a4a407405044a40155040c604502c510461074411a007811081c8801501241000000070350304812600d00c9058900400700035809803207040f4103440d81c02c04240102d044c03546070030040060001c0c1c1c080c0d055201f6400340c480c41c41c100341000c000c20704688030b812001e12206440022018800200040121040c00013805c10100342011009401402a8490307800641c0040461080d102040d030865006035900400900003424401030450300c03504018545030380000c0c088000384991 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 556447464 1250 556446214 556446259
    0x3010624030e0705011d0a0e040b1b070f0803100807120b0c0a170a02090616051b0f0d05030705030d0b120a021305071b060e0d080f0609180304080309 66
    0x1a0f130161154140e2030040c034400080500030200540d880450100c001541407450074036603205510400a01c0e0940c540503c80d0f034030103a042c80a1031b60805040c420b203c0010070036800701003520742286490352256142c854207010072130540c001d03040354010404009205001c2c5400b0045c090312640b00504242c0c0da800c0024154000c1d1036090001031600c03181400b0820110407856001030705140f002d4500407290000c01c20551049a407840603100c40903024081c840b0031b2048a46d440c1700d4540c021060070a0100291020b90030843d07041c03281c0050214413040040c00c000b02c80205a101050f1303511115075155010003404c01408040c082d0720608180811001d0114540b0300155004003032804071995101c2ca4402040010044000c2c018410b2840c2411101d502c121081e851254001041582c420580e0341c0c2800c525440c050248482e120501c1051031285044a5112038261503920180d9124205800c403c0400000f11801d4040010f0102d03800310080002c050403507082c0c0c1d841c0082c2d400b40b504c00410 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 556448714 1250 556447464 556447469
    0x1103070e060603010521010905100e0118020906010219110f010206010e01090b0f0607110418020609130209100206011a0a1d04020d060b070c09050c030c0903010624030e07 75
    0x4020200f005210500c1c0c03050345030502c10341c410000107400703403105d420310300311000e0480c15103140e401005451241b0f10365020340541e558018000b03114030078001042d030324106d2148030300030f12540040d800503a469100700024030341c051072034051280510441c10720340100003109817014080c4420b55105c030115400040c91504988403100c0499981e0320b0898008024000403038001d92110740700d42d400c42e0a60742d101c060f118213405442e9142d05450000100001c80b0316110301640b010340f0603a149000b59072246c007a5520983c00742c0b40180654400400d02c002841070b992600d9100301200000c1c04203a900050080c180c4080031400001c03c0d280a43d42010750140c503500d8030000b40302c5490b001003d0011100201c00c501e001c0c00c05400c007460f201703032071099400c1030700b0168a158020036000140704449006000403d03201004105c10b00300146060351501c802040010381110024400c0c1d0a0b072403d41c01100185a10703800011100b00c2584e20b80d0701644003007a5500007a041c1150000d1020000c03400104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 556449964 1250 556448714 556448719
    0x60e1b0a020d0503040302011404030203120906060609011803080c0f0d0516140f12120c04030506070c0c0308030a09120e2803080a030e15060a0905040501020c0a1103070e06 76
    0x51042e07420421541c0c0e500c010000c0b030865496484900d4103000c2216407030b00861181d0065601c0e00700400c0e410001c66401800710000d0b5101e001400b84a44a40c01101e45e581c80a10389900f0464403403000c0c824802003075200510f0441c001a40d64402c1c440440c0d04005c540e550b4041c0d503d44050a0b02c1100c1c03e0052a5084000c0000b5611032000103a41038030311500791070040292814811110016802c04051012180c40030800003001c3c0c5104041188180e070200085141506040c1162030b00d9035070310b200038140d0050101c580d0010003807082c4540900d00560b44a04d0590b80e91a1003902000509140e08080b500c4d80841111070100700e00400f483c8016800c054890761101507013045954194000400d03201c40070060110102c0402c14000c014143d400c0c0d0750720302050710055400754602e040300410b580d1011392100c40c2440104d64502d00d04c02c0840702c2ca00e030081015190360907c14024403c01c6c00c0c858980c45040c1031903080000603410702c0441c600032410380302030581d2440c04007070b0030700120360069 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 556451214 1250 556449964 556449973
    0x322050a0909020d0203010e0f0c1906080907090e0102070c12020906010f120f09140d050a0810180614041103010e0901021909081018020409060f060e1b0a02 69
    0xc086003072a40a80392260000340007030700121140c0c0100e42150188002980c0340e41203907140e042c116404001c41900d40d001521140b24801c0800c1820303c14205a020b80701c02c01803c000428802d45042002202620801c4410011307100041000340c000d40c00300408440400005500040405400381c81c1e441d032076000342070390a15540740740c0115401c2d61110038a0302800031803100a0340070b0075244900244c68000e2000001e071400181083d107040c2040c0da110004d45d902c00c00d540c0b9206039001d41550030601003030a10041a440c3d182e00540c961583e600104000300c0804030b0f0344600c1200f0b1b0022002c03180c010900b5000b1504500c03e01064849440703d14009480400040240110136032007035900108502c001410019905c40c07100c150340101e00402c1c00595441c0c1c052040010601c01d5400e120400c00080091240741809440d040c9122100a0720035507a54480c007062260a82007402c0008021004201e40342e141c40010651500c1982c000c2c4540102c40c41c6146c003001c181e41184c5c081c0401750001d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 556452464 1250 556451214 556451219
    0xf0c0f060b0303040b211819020f0d0510110405030703020d020a080a031106090307021e01090f090204240206180307050a112d010f031d0322050a 64
    0x40301401e1001e41042e01440308010024050000c000030b45076560721901039060300341040b8169500068080c0024005c001a0102d04a00d01c5002032088520105094200701c0d45038940002064019900c0d241d540203001d04041c1010000042072200300081a0b482c00c000301c03100645940340b0790141e400b800380c040c0c0c480c22061001d460501e25444480d4030083c1780c11010740d1100038850a1001d000011000302c0e124402c50f0b111100c0600c030813507012544000550911190f60002200365203070080f6220029030700d6541c1d41d1164807805a04010b8007040d0700e401c946a0f43c50010310001d51191181700301840e501134078185008000301031a1400180c0740e00510160b21850141d14511000c00400e82c0c0c2888200188030006406009002d10703a8043c22000e400b0b0808002800004000300000038814078110a501420007072007801c3d40c078000401e18080340740410403142a4003d240d40d810706034641308054400954000008014880c0b071034200500d03a50011050070302d60099200d401501d5206520880a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 556453714 1250 556452464 556452473
    0x21206100e01091e0b1206100c15020a030209030106030323070b01090e071502100b0603070206010306051003020405090604030201140f040314040e040b061c0b040b0a06080d0305070f0c0f 82
    0x4400b441c004c3d0b1000c203145a07260820251980124540500013107680104420b9141c400c43c0d842c0705d50f05c02e00706806000790030f5442c00d0100d115841083c04c929404103111400d28820b50590320203060150003007045540ba810f001c0e0101c040805000c200c0010700c1c40b00d10b85a80500d059446d60383d407021014180d42d0030941c01d44040c1c071080105161030311407400d000604541b15100300210f4032568010f8106010051b1440e4145c0f184030234864041c0d54100140032503da40020442d04580e04941c001441c1c1d210500701000070265503002039400303800d150078401074810100c2c403240920b1280c1c001b00520610289140140c007002c480d0030700e19005171400a0040f90103221083e02d00b645103514185015100c5100720720058040d50f00341e4044854004000d15420140d64111491802c525040c604261a603601429a480140004c05028030200442c0c01a043d541010300648803140030746e030003c40a05001070046c0011128800020103030042030030454064214603030580d42000d400d0b60f4002403500d9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 556454964 1250 556453714 556453739
    0x6110c040914071d0105040b010f031d01020c10050901060501020d0c050102040e15130506130b030a0c06020d08060913201903150c0e0d08090301021206100e0109 71
    0x301594100190800ba00103054280010006000c02c030560f00d2000d44c0c0304404031a02401604401d000d5442d021811040740c0e00800000d03e4906640360202d608551202d40d041b08101c040302d5104076600101f2280d080d80301c0440c01181444e0003a030100b000d662950b2402e8283c0c1c0b1180f1580740582c000800e500340044c4100300b203202c0240644000b605d815540c4401c5111203600311030100034030003618140f407140e1070f01e124004251006000d0500c9141400d8000484040002400c03c1c812540c2e07180c002d1300c6840502c40032065940195003031680c95580c00d800383d00c0d00010a06100000d02040c0099154644121803c2c0103035014090040007290075a269250450840004054440500304003826584d86100312190780c18550110f021192441c50070903626190031494101385410b10403da00d006620403031044280394215950619034101c0d04003c13056105100071950103500000d001c0c1340700c1200141180c091081a0b92001405081e44000c41d66420f98088103030000b014101c04000341280c505 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 556456214 1250 556454964 556454981
    0x3050c0a05090c1e0a0c03081003030f0f030b1302040509010905310605040c15090b091c060f0219030b010e090721090618030f0305100506071b06110c04 67
    0x2400034020011100d484c0054003e60400400545100c0a010800d0f500c548056001070860103507611040c19035401620b010f442036001c601300071022a40e1140076209070071201600d18050469202c4c113180400c440040d601c00d0240358020035051000207001b880c0d41c0b1034076110340c407009924000020018001c22089807804006a400c4540c1510000410040d216050090f0f105007050441d0903d02684803240c5480c2801c40e000307008000ca0f04000110342c0e0021142001002c4400c080c190001d0a0030344078660303d02c580900b010f490888001441210340d401081c590840c1d01c90100a05044e49044050300c9a14466500040c141480d000090800b000030513080445400e0004440c103401e50507421605409040c5030900c0d03101e0005c0b60070b1200c00d100311250759651007022107502c511614050605c00c850114a0100760f5241c00042d0002c6405041d0b8000e040000d01c40340c2e407400c450805000c640c21900001368040400003000940c0d5014803601c2d40b1105d80c8034042c02c0d20311144020040103041c0e20 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 556457464 1250 556456214 556456237
    0x10020d0e04051b03070306080c0307120f1403220b04080a02090406180501090b06090115050703050d0e0d02010b100c060b06040302040c081e0f040605090c1903050c0a05090c 76
    0x150703c40354405640240d40300b9403060b900060550b15010b125850400042c00850207900080c0c014400112400f14944529070403d0b244807034845240341c20350381c0c40030b514610075140c00081200d09065001080c0d07040840489801c46000e00c3d103075032a00a99105521660b020780d404922000e0060911010141c1d03c42d0044100003800c2141203034814020380d117040c08440307a0b5503410001c0300304001000c01640007001961035503a40c3d818802d0920b0345141c61800c0c0f01c14010082010401c0500c2402100c608509100d414040c1d50410400e181c0d0b1859580d5001c030140d420020004118100203200c803c403001c55550342401a0056142d2400401d81d0100007078005004010101c0941c44074000d09924501c281d903041014a0181ca003040116000a400c08852010f03c05104d400345c1c0c40c8080d10f0304141c10003c0000d0395141c04800c10b180a11285c5560340089210640c0c0220440007690502124050000d46d400a0403800800540d100c0034020181d02064190205180328005005000c3ca18000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 556458714 1250 556457464 556457491
    0x1504050a0e01020f13121e050c1503010914060307060e0a2112020f0a0201031a10080a06080a05120a0c14070f0806060109060f0c0b01090b10020d0e0405 67
    0x425551600f60f80c0008071040841400144400014000907046001840703a08000c1c1c0a00441d50ba461604804003410300741045032104000d01480010f1014980845008200c18080031121078030306010707002449142d440524114001e40300c3e4001c594554031501005000c0c2900707e007030040942c2e03020600340350307280c00c031125000106849001c1b0178103a82c050014803e2072030449440c60205144c00c1c0c4501200115008400380d00b04106001800c2078600d542402c011408401c07a92044030706040e030749007a035800310780350500d2181c113600801240c0c0070301a100d40903c9613940f61030603180d83d4055040000c0455010501c101c1c055950b400c046c1064810924026000c0e4805440c1d200120b83c00b19078424044e0083c40341040f110002006040040c1000c0015200380d141c40302c00601211854420f8405000d2080e58084582c0c1c407c4030701070802070344041e8000042d40c40704000300040001c001014000c0c03a540407100d200d05d0001440d546510030355036600400c0a240414400030700005414203001e07090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 556459964 1250 556458714 556458731
    0x30705060c07380a0c080906070f03081012170706020c030c07091a090f0402060c0a1a0f0f0c0a0903020d030309020f01140729042303031504050a 64
    0xe00d41802c0821201618060580f02c0c5514a981080511845048810002e040380d01e9004003007001003e4100b540c903074451300000041440d41c819804018000ca6040001204045d004035105025a540c500311087c90307510b03081603680700195460054407500d0b003141c044a403100c6100080024910401026091a02d48002ca528541240042c0e480640042c0320030700844c140740c0701e004e80620071503000da4001d0719140c2c04240492005813030208401c0640c0c001a0075503d5420807900312615040442d050207106042000da103410412901e0508080240070440d0b003644c528200b0300490b003412035045151221030300440ea07980111445828030540074400405699a1841c20307900078003e45021030001c00707610400040d1101480c110741070041c04280086110540f10a840205502c039030741d180030074551041e07440016000e141000d0052481c074100010406000f4600940e04c45080d00c40012044500e00705131640812500d80150a002250203c941d241a80040c4c1c2c12541070400014403a2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 556461214 1250 556459964 556459979
    0x40f020d0c081005060109050d0215030705070501050a1a0904031b080408010509072306071403270d0209070e0d03091502030c0304030615080f150f06030705060c07 72
    0x50300c28819035441c880a28100b146000c00d011642c0d1110800000300a20b251140020f01124038a005460144452007500402c54440c96684880d030303080e00d01c4042d101d141c51000109103a004001c119010b508110204500740741c50b00585900d4108038517425214030f10308080c480c5481c0c000700241c7c10482c89031402d045001d00c0d107411141150280c42020356450404045a00703480b0082c00214060b40240c1b010410095021003e0b00300c0f0000e6072513508421543c1000601600480c500901100092802050940b800000030110a925540402c0c4601011b00c0420b4071a11902642ca07080522161458018a806180c40c0c1d030121031802c06c0c060a25108005c0b0f001d03040b260324100e0206041c0c0e80d052180340a10030045548a44500c004c42c5000c1c981c0c40104e49a0007030348001811152601401c10000c011040310902802e070550446008a1544070940e03600c500001c0488a244400d1000c921010150b90300c141c030032800a002446443d15140c24840c0a510480304c0d90302500a0041c00329100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 556462464 1250 556461214 556461229
    0xe0417070609030306081c11010b0303030117070e04081c0f0e01050709050a24051e120a180b061f020c0306070507050d03020d020d0906020d060807081005040f02 71
    0x90040341e00040d80055841c0c050202e460301e40000d6403da0201181d9052602d6000c4500b4140807a4034004500c030064044c603c1c09440e451030071070392601012002050b240840550710100d24101030844601e81d548156012882a042d1005002000c00301300306100030814219004c0c465101c4000080c000d000c0a4500d0704807404014a03c1d45a5102e00c10300010944c03225003800545811900301e08802c1c0b52814059407040d0512035503400706034a10720340c1c41c0e4502550a46220540a44141c140c1d507010020440c0c01c1d522000741c21655680c1c11001c21201007070b611402e1720708072040c00c08640d800043e858815408000030f00c0d15602840340500c21811411b01800c01542090303030380007001c10400320800c141c1000001007181c0200802442070313201051000482001c0300d10306080041e07942100e4a2070b50068400c0d8009054154201502c1e00b007084a168014100c0625000007004095103408034103450740700c24030034070840e075012003690042e19074298815508076110b40100512010150b022a850 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 556463714 1250 556462464 556462477
    0x40305090d0c0e0a0f11090f030115150f02030406210f06080c010801091b0c031806050c1009052a03070303111b010f1b05011b0e010302030c03010e0417 67
    0x1420000c8051002c03880c0b20b40202d2081405d040c1003400075050030750090b901030166014040c810113000140c142261000c1d4061441080031407920b20323405458005070002d010201400b000020888103403441224400310584080d107030a941c1c0d01e105024146000340160300b1909650a85540e1406c41001c401440e216042c010010302d80505808035001c0d0014001c028164454030031103092058a404407003000c0d200c08211002c03403c2800b8460440d003012100c2d4040065894240c13086003101255280d0414050015040318001710703a0480d000c0c0003040140c5001400040031584a0b8143d5500300d510742d1074139256480d029100080a110440019117000c10961050300455943c44d1340000200d01441009115968425500d1824422200091460740d00b603c00c181045031034940c1c1414404c0d03200300c0000d110341280080c4086410341c2d054003944840b030880080401c01010160701d43e5402070003030347d2007407080280d05400c6a280200540715481c6c0100215500c00c140703402030481811287c085c041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 556464964 1250 556463714 556463729
    0xc03020f010c09080c01181a070b04110f06070b01150c0c1401021501080c04020a050d1d061006080a020703020c060406030c03140c0a1d10081e070206040305090d0c 72
    0x1401071611106a04205da80c4628904110241c03c03d0480c4482000050b011207651942c90029080c000150040c2c6018101000b00100030b0007050200f0f03c144075460508003541110007441d00032030003082191511488200801d202c03515001002013800c80c22001c903242e10343c1e052404500e6180d41e100d42c80c2004a40044002070b203800341d850303c1940d04100302c40b421020240c813184a94102081e007503031070a01d142103902c0741ea00001d0143c2d03102d1094041e9080d490450000340708400c00442c0303204540d65100c240c080a482283d0020700c0c10600111110111109911040001e4960481e10390180d489000c0980c107500c643e0300b440c00e50351581c03002003004000e07e07500060240807050004003541c00542c0c0d03202c0d18039502c100303100e1103603101012645800300c1c0e03041c51944100080b005403400d104a80c00d055110714101503114285030030186451003070202082c805000b082401c0030340d001c3d2009590403070041c1e12190010340001d0041c0002c0c23084a00081090b03001420960703c403140004139410070301 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 556466214 1250 556464964 556464977
    0xc0a06080a0e12160602041a09010e0303030c0a0c0507050904050303010e0c04060e010e13021314100813030207030c06201f15080f06070909110306010c03020f010c 72
    0x21030581540b144120303401c0c50001400d060765200600c05418003c1e401c450000600c494009801c1040030340c100e170014031000400a1100401d07a110901680116505a0105800103009400d902d004400c40e845041f00740c00003802e282228404846089003204104d5291040c004045600d07954140f080f4031648c480c0300103583d25810030180c0031000c0c40181a00412100c10b000c1401656000028070b001110b003807a05003202c8880000245a049816250411180c8005644006441c41702c0c0400c060301c0c81a55223025070765964080c0424510700c02c00c190001502c44012a94442180c10784030011402407040f03605480c0c072a2120542c8002561120000c5541d990840e107020b40c00c6841d003449901c84070302a000c14544902e021800c1c1364208801e10f40165509054907c40950201103405005040100c0307556079612016035980c2d06050340c44001082c13511400080010540c090b03403503110010940c25081d92580310040d60000442e0f00101d0a500440d100041c1718002441480d00c1d00c101c66540e003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 556467464 1250 556466214 556466221
    0x115091a041b1b050d03020a0c021e030c060403080f03090a080a090f0b0a02070b030a09060e030a2304030b04060207050f100c030c0801121e0b0f07051204140c0a0608 73
    0x1034030b8003c002241d440c201900d40303e1503000c51004115402c20301c42608016a1701c0780b4a076400c49038a0404e010080d4014251030040142c60200310349018030407800c1d400c545405d1507500c01c00105025912005164500811132040304000e1000a140c0101c800c1040300c010100c01c0e6581c48142d000350020b58001415004100610708811411000800b00b0041c7c1c141303044485500251100654084c0141c85c070000002f00d118401d041d8042801a50030450410029400f0b4144940300e510010108000420080c0710241402c13810014003100c0d00e40101c054503161070740c0c3e207408940000034420f4644550034400903021a0041c00051400c040882c05418070700031b416600021038411111140030540307440303000070645810200039415102040c441004011440c9081c45004445040341640c0a030f403e515401080800103945000e48080c5640560683e00c02d00c089626028480010070729100b64008900840c2801c018401020100003e5a01c1c1171401030109055812031b50040000500b0031080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 556468714 1250 556467464 556467467
    0x3060301050106110a12050c0a05030409060b09100305040215030103060c020f0d02070e0631060801020304020f01050705010609020a020309090108060f0105012d0f030e0115091a041b 80
    0x1810b02401c8242851002c903c03500001c00e98075136200d54018441000b40042c000024014415942c00b1060481180e21042e00c3e884d00c03603140d030440c1c41814007081c03c1600126a00c64844107903140c083e4083c00342c411000d180300d000c030040c04002c0c1050741c010960540c030700c461101a4000718083c40c0650b034085410840502c00902d0103c0246c1e00c4400e9401c900800a259540846c1c400100e6480c141c1140d0b00380c07180000501e0034843c5860b800011501c01a07110f8213004030349140c1100c0044031004104569403040c0c1d540c01d0380b108907002984000704d10188500d56000f603014206c01c0740500c000041d0360b07850760f0008040381d10081546c07015900201e0808518500fa0803040e01421200d8041e080600308892520917002040c01514144280c2100480382e001c0a103044034400a6140000e6031284088000500118401078007000064140101e0b00d03e0382c88140110301e0780d403048a40c007130700191500c00048010110602c19800056054a03800c1c180d940318018441d14541320000110b07600201c070030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 556469964 1250 556468714 556468721
    0x303020a0206073f0e0a2109051e04050108062d060d031701030f031103030f1902040509041b05120c060d0615233408070803060301 58
    0xc004101c0c3c08050382e2200c0c40d031084a101d4201441861301d60400b0303042c102e5440003900756502d04e00c942c80c26101014aa20000e40c900055010b01d200000c0e880419281d4240c0c60300b601030b505c021480d015030422540c204000b50b040c00c505c451400b0045030341010000307000e81d4001e0f400140654804000e200302e210800c8944040310054070074004000a01449030302038440d004103540e100b0180c451615040c1030203050300c0031703170000d0010150f030f6990385910704101c0e0302c040d103401a0b00007007440d03a20111255000045901407800442c8100c0181d8600203401d40110002e00e030440250303002c0c080080d0315201c40003503d002e01c0c82580307000880d820365400407440d908140c0c8a184143e0002c030784c2011541020a4401804d28140c500641d5a0b030301c4140b51020300040d601c60354550942100d4482180d500441c400028458208400f02c3c2840104240300c0c540514100e00070b04903140c00e40343c0f403944004010083c0980d2200035103071242141b61104203140e0400981a40d903230714000304004c036a203400e20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 556471214 1250 556469964 556469971
    0x21131202061b1c051b07260408060423010c030b0f0405070c0b130b01090b01080114010e042003130c09110306040506040e030a02010207020301150308071209050a030303020a0206 78
    0x500c480e0400c60300c42040c99120020030850420f495480c4046103d140903008912600602c0307a203480d5403180700f49410b440750240f4004030024002d44800d0010070a100b00119011141200c0c0207013030b9510740d40c40e4501200d1402d0038850207403003011001609480c0a0141510400140d140041c150304200240304c40000c0d00000240304601d0b00c804c01c41082e40101c60b401800c5d070080c600d419242d40304c0009000680300d50401a0007100ca5000000b449101d81d0080c490848007a070f20501c0711b0740d032803c0720036011044c0c01402d8007080c807031101c815060030507500414513a500f1001e259614442d240c01ea450a0b44191060700410035100804c1090042c28207044000b448600d82c10007000072030340b604075094003002d004c0c1c1d4496502c03040810420386e1181c0208040804580a40b580c902070203101038000d502000080b4025400d2606804142080401400440b90451241c514049066458100344c1d8001444601402162031000c02c05403200c00940c4003852081e00c0060380d0300009403010740b5200008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 556472464 1250 556471214 556471261
    0x60619201b1813060905031309150e1b1603050423240c061503010b040b1003090c030b040804061d180603120319112113120206 56
    0x400c034000d50310401d1140340d40d00072403c15554482c00304500c0c22801074500c3c00f802620300d11000c9046a11040380052410032140e00d500f040240703020b103640030115075001c2d110704594000c0702000a01130300c41414441c000000c0e851052032410310320340304032801020400c0e400e40014002040503c03119035004a2801140e080c143d224004041010004d41001da1a920343c0c0080100f0329428004080e0101c00c2da4000400e5400740e42041c68a904503260451420b1602c83c801d41c00c0c041c64a180d07040c01d10502c505180e014040c5000344c403a0050a80161058a00844441d04d28a1001003c128130401080c040c510520324240e4403071810300700400d00461001c00d1075500308080c1003860195074045100b071341d40043c0303208602e41c0d03510000040d0030080c20b2180384d000c88200008103e0080d14141c0120900807020400304114200800d03001880e000f004c20420b44100c2c10400180b402180b07101440d888031841c0d01e41c5041d8101c5603a09040032248038204400f6038003403420701101c103a04420303c941c0b15090303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 556473714 1250 556472464 556472479
    0x50601091413020d050a05071218081e040b07030806010e010206040b07090f0f150201110d15030f0311010b150d0e0703060e070e0609060619201b 64
    0x80051618075115144202446458038185058821046405030360600440e650f0800036480d241410102030a0110303005030000320400d40001c0c44661600c240c40143d030003202400c510340c0999840004a07404141e640c140a0b903422125a605031009000340301402c800e41c3c10720f458003018a0090001e090180002c4c1c10b00401c03507110003850343e000501541c80381d00204d5098203a10340d00c405072400042e80e04059002100701d000420305501d0281d40300100c030119400103458008102d030407800c0307030b21203440030314540350030014011449845d4010078800884010100c5040c2e5a070f659040014200d41c0045010500766402c4515020007841240d1a4400c1592180128448003100d0030750751040d0391290034641c4d512602c0840720b020400c000c2d0301841e4800402c1180e508100140c07503441010b80310340400008050300041c814240b01d40d4050040702c014044904050201005070286680c4c2d0180030200220b1141e010000c000305900500500d5810014001c41075031080345c500071881c541030700c9015181 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 556474820 1106 556473714 556473719
    0x30604140709060801230d11040c030617010618091410091401060b0f0d140f01060f111e0313080304180903020c0f011b0f02030105060109 61
    0x29034413015690b80c0c4c0c50700c20070411914000801c00107810020b284040d8100300d0060041c480c0b140c00307101c0040d091000407a040303d9002244000007034070b03488104448040d07154480201030280d8000d00c190760428031010050401005514801540c0f99503203010705c50f1101080011880d02001e60300035248101c0c0c2d50000d00f0302010280d84070880040d0b1410b101105100310012110401d0b80f4500300740d035a030007100082e000003c40000440e2504441d00740e602c201c40340c240c42840014115041541014001042e0098600281c8240100f01e1240729050000061482c001c00400d00c40036001240c0311082da0070344c02000450300143c0030030b4102060400c004006401078601207007501100052a45040050b51200100500580c02c1008141002e05050740610390b00300e018103010506c130b5a491040f144071296090141c84119081c1016021440d00f8091690030010900c2d01842260 = true := by decide +kernel

theorem cover : BRFrame.Cov 556294964 556474820 := by
  have h0 := BRFrame.cov_init 556294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 556294964 ≤ n) (h2 : n < 556474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
