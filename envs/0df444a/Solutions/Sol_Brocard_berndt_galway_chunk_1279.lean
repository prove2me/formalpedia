-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1279
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:08:26.844896+00:00
-- url     : https://prove2.me/submissions/9ed8b39a-0a9e-4843-a16a-cee3f9950599

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 229856115 ≤ n < 230035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 229857365 1250 229856115 229856141
    0x6062227021801050f1e060a0c0308010806070e010c05120c070311040513140312190c0f02100b06120405010c1103030f130f120306080d080c180a080304090b04 70
    0xc120f51401000403820001a64a03070700030446020004410b610240034aa469a005002940c1c0d580c05410000d20b10b0143c0a0b045010605000c0040380050000581c0780c80740d44d40c0d440320194581c0d1383c401511040001141100c040c4605203c0784015880800034000e0800300350000c12003107003540340c001000d4451115030390140340b0b04820040091300041c44100303041e41042d01000741d1603048003980c1c194403902c245480d40e41d80700d01c140421300d02c0c0517106c00400246045c0800c150600303020221806801015074400580c4008000c000348032041e444071010383d10041c41c4916100d0308128541e0940c0040790192000d035910724611080c5500131400e0000124604080d40c0307145030000c511256402c018003200c240e030817056a201c0800400181c0c1c41d15954110b40c60070001944614020040c10b000c0c061940c8500480900078a068010040c1a01a01c0301d116110b040041c0744074030741409501001c4072a4003a403e4000021218810701c02000903054604003c00d9420f503000600050f1082510310303403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 229858615 1250 229857365 229857409
    0x6060812120105040b13050c0301090b060909070f03020d090b060307060c051005040201030b0d060515060f0d020f040f0905101202060a0c140f0a0c06020606222702 72
    0x844507481450030300341074502c1201c0020705c05103034a021584400110101c42e00c8586410144425420b145010314129600005d00380030003c0c440c018032086000b0003000642246035540400c603d14002d06903110426150b10703006084c01c0c050351044c02592a4560300b681c01d5040c0d40148083c0d4241400740b080981700f1801c0c1708060301c049544442c1e0f909130011542054541c0e410200d81107a00c41c1e00003603500341000300820200815410200000d220688190315a901c00c111002030034103006007520591406030101c0c90402e803d401c85000694046210071110020411010401a00008000000c1e060f45980040c8030f107840300b010965040e00d0b0700440c410740c00345003003640180e03241022502446d40350b01d081010030400b850f08400c661402ca69186641c068414040030079030340020740410140c000c00018003000d548100030f03610f920040d2030f8150840d5000743c2c60007141b9200b5422081040c4010300000c1c044030510400b04041013075074410140c180402c1649004d6141010180d0070404000d02c0e4070f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 229859865 1250 229858615 229858627
    0xa0c0c0f06050406050904090c03120e0f1c0c0e160e041a0118080613061a01021207050a08120105040e010b2103040302100507030906110304090509031606060812 71
    0x2500c0780c020f600c249400c200c0c0002d0060f205403110b40204a800d640880750f00100e513143c0c50102140b1141d84007503030005024540c1044645031040038015100400341a220381031341101481441c10002c2802030740d2401080200003401c2c1d4448a0307492254081242c551064641d4080003414440700b0314405214038144001055820140c554004214100342080a400b14405d80d80340301c0e04041342d0050380c281c0550320400c818a1401d02a9903001c0d44907081c1000007000010b0303042c1e8002240000240180c0c0a4494080e00c0c14a20b40289a0309000310100c49690f03c1682c1c5000b42c40e0302c101822b40303000750f85c14010030181c241402096010400000203106400220b004a212000b02804044442010030300300000214144101c0e00a55000303020304c20400300455014000d42e01c900e0084002030402c440006034140705604403007110422038007a42c9458a40302410028100191000e105130104008100082030340d801c1040046124110100e40c061610f41800c0c2000501241c20388000420006 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 229861115 1250 229859865 229859867
    0xb010b0406020622020a080d230405240a1709010903021209010e06041202190602071824080609031c2703170604020c100515060a0c0c0f06 61
    0x1074940d01503603104c06074070700000110f850b68004040c0c6001039006250f403407003c0340e03008021807072a001c1002034a440d21140319100c41c048900050a01101101c1001e00040c40f01c0c1c038002145900c40521030b8400980c40c8406107050080c1e90052600b940440c28850004d8188042c20310308940c0b001080b4001c024141d0151006902c400e403007808020f014100103824a03060b03004908032200c0b10030103010a51201d403203070841246040384030300580c810049400030402d050804a603070b04c01d40304294080c00140c0e1506240f14191117020384682c105603141d003943c0c014040100001380e0704810880c101c007003651810650a007011005031142ca242d41041006038080301003078038540200314008100103061700c55692003065007001100c0d4101c180401d00b1240090692140c41e500718644095460381054592804000807441940c400d444030b5000b80d0312900c2103501c0b030f40c011503004003603800e01101e4155242c005860ad0f8400c401420110b969407004c103050102c1a03580e40050310034000812180350520300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 229862365 1250 229861115 229861123
    0xe040504080d051f0306020c060a0c020a0f02130504060c0807050c1203090307050f0303040c09060e01051201060306050702150f07091e0b030a02040503010c0309020604052106040506040b010b040602 87
    0x51900d0b96281c4900106011a40d10303480801c1c0540701c689404070641d02c0e803800b03402030b6100844002080c8113000110f0700f0000c052180109591310350300108420102c41c1c0d2410a134040c82101668407203868003a400120103540161031280703104550009001b0a0354801802258018280d20708001060020b020b9460700026910a007403a00003105d901c82da00d1074503261071441a0b940003045405031a54042d001c2c0e07000005140031703a20401d2000c0c602e40d101c3e014181100c030588203180803941a0f030b00401282c2881b800a01c50480c0c52000803544540340e880b004243c480a860900040e80002c400c0892001c0f1503620303980102841c004040b1a0a2213800200301c4019409403086500c280201041c080010b4081ca100604100f2000d50302c91230281311080094205100709400303942001c114040c1144a4420054060390013092141440d0615013842501e40e5210743d030f404840800141404000820001c442c4120301c6030005160300c0c5454501080c0d0301d8010f0b03201c0b103100d1105000900003550089 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 229863615 1250 229862365 229862377
    0x50a050120030a110d14030708062106181b040b01051908180d0f0e031609021305010504081911060705100e1b04090606240e04050408 59
    0x101c0c144466803803485003588403425124119900c0c0c8400514189555000145140708000d6041500e0b104144030005503402429040030404d00782d010400100300700e00521041d50000809061710040014040d03402c0034088910b10301902541c0000d080102c03c100c0480c0701110745031914080c007448855046001c2080b128100d00c2445141c59845a0b107190344501c0c00c0e103d51614203601542840208003003d0308024040d0341565070501c0344080401e0071400040d104009540560700d01109414500045800032500d44246925005403819904090b00c5912841c02820101e00016960304491100e15802400c035402141440002c1c00200008031004c10b000404032032690307810350750410302d240048022451240781c6602082c08140e00041c8840041c800d441d040da111000c01c1400c10303c02c0c41c0b60342c0c1c013031000f00100b0080050306854060b0409401c10303507095100e420302140060300c0c0c0c2d184c2d041001140d45100401e103601d1044a1a541d401956003002031001e80d010401400c0540310400548114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 229864865 1250 229863615 229863617
    0x70c0506060d030311030703020c1608060402090a061a0306130504080a051809040f0c060905030c01141b210f04121104150317030c19110a08040915050a0501 69
    0x129002c014035010b60800b496a04411505959901d44458050003c0d04084c00d6030005105100346401c2d0350400c00180d5064031140f0005101d265155802c0144003031008206802c425200d800016092022424144511440000007612403034440d06104184107220352181c0201e04120a000129902f042201c09000280c0741c85507541c1e080c40d0114248103003030000e19800c030309813304110510040c400700d030a8891064040070005580c3d4802140d608566000c1d01c0d6240e049200040c0d160b60280808400a054004c80d507401c101011940d24a849903407900b0300820f03086100b61081d1140020300c100400c480a11507241030406400c0c1a2845018034041c0e10200003030500a4020300826142107500428001e0081c046209098040c94003081c132803100712038802c2c031100300a0644961405403072003480c45990090400d0010358410200020241d45032050210011b8510b55004083c4400c0e55414059840242d803a85401800422520702451070f103a04444000d0034011981c40b420340a00b140d40c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 229866115 1250 229864865 229864879
    0x20609010507051b160b04050f030a0507091a031c11070b16020d0b040c180e1513050d05130504090309030623041b150e0d0f050f06090105070c050606 66
    0x780000092030205c0442034072454100c11100001c006a00c2001402500c105841c5403007003004078014169070f000b040d000185660485441071107820b91603441140b600030344130102d19110014001090901604848040f51018220240b00c01d09801640d83c9000c400303080e0081812902e0000080942e018841c40c0e08080c2158014074000d41d40c1350105860481d030041000001800d0520f480d450410107440b0f0105030688080850202d24403038400c40e5401c14401001d000c0c54040010f11681002c001000903000c02c40040000000c03d078100000c100b0008240c590554504482200c010030030b01e05d501c00d61249007085c03c40d00010380e000100b1011a0360012011403414010407000d941649006110400000008200002c1c492000048081d2240e03c2030b0001081e41c482c004810b151308841c4044c808111020310940503414207007400c07a85a401100b42030103182c5c1c1035445038240140d02140710820b0340b003035091100d101c000f842144d0700642c860414400d6881c0a54445403240002404980b00d104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 229867365 1250 229866115 229866157
    0xc070506070c08071407060e01020712021c08040303030b010207330207081b1002061e0702070b0a0804031e090911040902040e04030311031902090f1e0102060901050705 74
    0x154025103100720b070710205d40038085d02d58200040e5101e8040c0701d56000940e040034503501e19400402c010003074804d0326103030035014080b613020b1002d40d85820070303001d016840d0040e030f14000c2075809010348069803190b500400c9030303886480020724181d95a007048444503101c1003c4201003d5144031454941c0003040794403003149507040240e0500100340d20000e45030107032155902c4024461030188101d900308607041d4100c0c11007001e00302c0c0d50b040c003200d01d21021202880d494141c810700035440d0354043c0851040b625a940c5410526107a40c006480301c0011550100902080640007241003182400c810b130000c000c00d10207200103102d0a89446004101a507500308101010380e0304044401034074980c81c040d03598541e5440c0e43c0b0b1000000701d4068001030300d8220100101003c000c1141c2c011440380210001301e40a4412140c02503200c1404240d000b0f04003034120a55032140040c0140041e1411114425a20100000fa0402c9402081070856914000812102c01d030000165064140701e4428065491 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 229868615 1250 229867365 229867373
    0x6050402041410050306010f1202010c11060708030a140403120b0409020a0609170109030f12021b0d090b310914060a060203090d02190b030f09060c070506070c 70
    0x114071048035107140d103900b00c104080b00c040030760388a040b00d00030b504680d550381e620340281c80c00030b45900502d400107101c02d8000025620504c0a40011802813490302c003950420400200b10b680504011a03030103034040708002d440d4103144100d0040f00440e02d4005450710b010b81d0010304001c1c51004e5101c515079100c520001a0b02c07180d00510049034040e091080403515407802510052583c460303a0742092201c3c8402030741c5034040c00b80c0c0407500d41c55110900e024812580c20345080e0443c40840441030f9003070011406c1c0141d540080d8078600410070243c103441158000c01800380aa40d000385204207401c00210702c1c0e21707407111183c9100c2403180c05001080c850003140c043c01442a80c2c007030b9100784e090a180d0030400c00c10324101070082c2001c43d540340802e0b560307100030707031b224021a02c50036807010f0050401005400c3c61a00c040c100c0810f0000c1c080383c030762aa140e034001a0010303a044112020240708101940c081000402e400a08004000d800c10b0303081e6480f41e50b2900024140001c01c410080c40034104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 229869865 1250 229868615 229868621
    0x7030f050c010b0d11030c030d090e04110d11090603031204110f090a020405030d080606030424060305010b0f0402070b010b0d02071a0f061906031a06041e0509130605040204 76
    0xb0f18402001c60040382c0d210304041e028162004200c611038090484d404c0070600d00021118452905501d0b03171207038245840000111207000074003c0d44e24603a036030344980d403980d01d042c42084054880d041304007810103603000340f00c10281d0040c101802070303100700320f4140c0e294045214642e02c5940000380c0da02603a5104041861480750740712040c0c02c032005030b0500103112903540140007690760030307030449040180c010801c6415400503a540c175040142000814045454815002c0350b1840f00c0b1641071300880c60b411b446044070159402624140d40d00c0c0e84540aa150800d18003815010071141941040300c562182c001940041c030850715004000030f0300107040034103a015641c6154024500001e400300034042892200b80440e07820721080d005c5000100b036032038643e000a0000f580290400c020f5410300b04181c0c010031810b41c0a403042c0025040500c3c050769880c00800140c0350152000c142269007040c0300400c3c0034550003c41c401c52045081120b07900d40c051120740055082400401d10740c0f59800842c000b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 229871115 1250 229869865 229869881
    0xa0302060706022a0c0108010e07180b0a03020a03150503030a050a120f0c020c0909030d150f06170919020108130f0804150216050d050304090204080106060f020307030f050c01 77
    0x2003038050004c0d90282d002e40c9030400f2406040341c25034444003084001160221424000c608a100150001c60302042c4130b00010452000041c86180c40b5503105c00b40d07050160020255200040d400180a800c07095060181c00100a101140022500e0800d0b00290320b03030080e20b80010070840c003c151661180d01c82c1007820b0110540d444104401d030450130030f01c03000d40003200305d0038054800e000118042e800c01110f814442c8801e88051400d0143d000d40840150581c110b1904401c200140301041551032116094002c14164882511600051010b031100040007442e59003c0c1c3c1000d60101d480789400e86488144541c24a880340315941c8082c500d070100300e0141405000c01e00b00075481800c1103078030300c002c2060fa06103060014506016590480c2e032802c2c000c031000c00045101a04000500300100000129071050702944c2c01d040e210314954040381c000e5030181c007440e91918001c0200741c0c4c0022150449110f00c0c40a140b501010751000b424031840300c0105c40c1040000151500201420752000b41 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 229872365 1250 229871115 229871137
    0xa0215010906030b0705130e070c0b1801050915011401140703030c08010f0302030a02090c090d0605040c0b0c0d2102070c0311060304021f090f03080304200a030206070602 75
    0x11580d6100c200e40001050240411141880307041c0c00309281d140640141c0d50490260584140241c0c00c102841c144400040c19074000c0c8040e80e00c020380041c0b510008140314010441c11110fa200c5a40341c11420740f035029000c4c01194000406640c00110203481540c151808000042c0c10045481c0048408005254228030301c2100452032104041d071540000d0045803c81d6a14900c5988441d041000402d15100007507155010082102c01402c00007056607202c1190b02000303041c01c2c032080c046030b1807203071524040f00c207556500c0410003002130182101c405080000c00d40b6040040c80314226030385803841031001c4180149603580f40280520302c00b211890402c5020b0941d141c440c03500c0e10944000c0c0500080b14601060b1000000c42d061110549228940040004190020300d10140003088402600d407010000444808a09203200e100b08000441c4190029a500e207050b0500c0700e001511280d090304600415000884c903030303447d02c079500240e94045a115a4840272890100b0082c07048400030740f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 229873615 1250 229872365 229872403
    0x711090901020c0c01020606030a03080a020f04030c0611060c0301031112030406121b08060108150a03030801090b01080f0c13031703070f0c0201120509150108011b03060f05060a02 79
    0x11840c1064002d400800d041900325240c28115800590700c601c0b00300d445681548c088009200030074420784030705801100307840700186000a01810680554050341058032903070001801000083d5002c41070518840c01c02018000c40d080598a0107411311041c480a064040700203881103172940e5603000b540030410000c0841c0c2d5500ea44c0c04001e40041c0801411000c075910b031415808504440e0480c801c240c4d041c0d9a140600350340c6504c01500e1030070029210075081d8801e51100c01043d01d441c48990040c1d8020b0311008030940c500b039407000a6811200c040c074100044041804110001c84185a0700080140105511507280301c2168090182e5940301800c002000002c2600380e50350355008601a016030b90b504600a040b01c1c50942c0d040320b0944009000600043c4014090030866105d6a000000207065405002155242c45491030b02038100c50300596540340918084400024444030340c54040c2001d2015a14000e6400190f5810780319a41c045c5d040020b005042a10034000d411651440381d02c41c03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 229874865 1250 229873615 229873621
    0xb04060212100501090515041a070501060807030b010b0c07061d06180918030a050307050f0705010b041505010203030a050c04030b18010f0b06160809041d0c091308071109 75
    0x101610555500c14a40407446010006c141d906210580210210302500402e00e8245810301154058000300b07013032803142400b40022000581e080c0504e2004010510092440c42d0460034402e1040710181d220240400301000104a4240042951000c940c42428060511090000040691015034404039800b1000040c504e0354401e008820121000c01980d8410003690f480144d8817080c0081000341000780d1082c031840126602c10801540d0003205460660f0601040c420714020540000300d0031522070351503850500d564140f500c80c9003032130300100360000101890400041e45903c0080c010341c4040d42c0304e60000d11020344640c1150000e541c0f03c003500e0b800c1e2402c0e440b00c1c1d2081015015004c615424241c4010100150b03004100c04440000e04040c54840c1d0340030415103800c1041011078141600f80603d600030341d124821202c6800c0491400109040241c0c3c00c542061850020544140041800e002400444031201c42101d64452045070355007010307041040c6a94401d10280358072103511810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 229876115 1250 229874865 229874881
    0x180f01050f1e0103021303050f0f0c03150c04090e151005060d050a090c03030f02010c090509010b0c0709290a0e06090c040905070509180c09130e0d090608070309020d0b04060212 78
    0x40b003900540080640700da25558000582d10b4030041000720307034960301c01e1018104037140705071804d0700981ca0250b620710b80740e61042d00200b03071303070b02440a49026082605005076900c003529456501c1111600c2e00754105017081c0c0090b4090088805044407541d640d400507004d0303819a4401708040da002003101c0d4440750381786402400a020032030003400550801c81840b042d180a0304d803060035110014550381003030707003054000040b80e0420300000e0a14400c0c0c0000042d02a514810741c0108500303042c8580300401c80c450040142c003a4140043e00409512800b00203284440401541142d02102c0c144055215042d80e0781d8640280d800c6a8200740c03410b003e102000c0c9c2c000c0000c210008050700c03c8a160511141d809109500440b0b15054018003000024030030700e41f2085c3c10883d0190a100003547c60000c0e1185407502100000300004584802014480c09402c0306145911440c1440c0500c50390010f80d010403822148050010044081c580c00304080000b41c4e01070b6020f560407200056002e26011034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 229877365 1250 229876115 229876123
    0xd0b0a050303042408040f060903030b18220b070f050f0d0203070306090b090606160c1202010201200a0f121a1908190c05180f01050f1e010302130305 66
    0xa41d00c0629130003021102880f43c01581c002e803190f504400380161a0105844080140020480c100e08259032594551081c3e1b540842d80c07100c8400030540c07642d05142a031040d114119107940d84084407108a003800002440300e030640c503409201d615000c5006c1a40f298281e43c035010701d000c1260140404603407007141380d816a01852081560342d03800d2111556078100b040480d451820681c0c0c00c40e0b04d5000182c038a040c108010700f0315541d14040803885800d00e031150501001140c00258400e00601ca4a000703548c4e09000312002103001042644c2699007104d9481258480c2103149803d110a078500c00c503665010f0342c0e401410001255007070003003c00321110202c0600400c04140d21421044410040c03503a000f10300351051b240c45070010f1850700710b80401e81880d410202c00c111601c1d001e41c4000701c2d46803a80030303030040310071f115402620310743c00e06040c5d8582411058000b00d001e41400e0100d1141503442c4058078003400704520050b90781003000001200030303204902a440a402242c0d00c00810800300007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 229878615 1250 229877365 229877399
    0x2030903010b060a021903050904090f02130e21190c03020f010c1b020d1712011d0106081f060e0102060f0f1801062309150102030d0b0a05030304 64
    0x14000c0150091400400203e0f01401e00702030016030041d80c81c000300c5a10300c85a070101a0090900605041070000020709a4004c440c0032508900d4010301c60045052000070314408080e08034040c03014900d031451540e9900403600c880744881001c1041001900d420301c0890741c548039001c00c04100d0025100c8080c01c1405100c0d4120f00500c1200000801d029040c450210980c02d035640d48460300a405885940541414a00f6039008240019580000d106103401015603400e2159007074840c130b41e4801100c44001c05904c10304841d01c40c982c40d012114100d40319507040d15558145040c0d1911411161303801e44405c0070448800000034600401d000c1d41054480b80081c1c2d09a080300e8080c1d464440d034115003102a204a14652014008100661651556899414021000040d140750b407207662342c95500d06100052403604503044280114102007501e103030b0001441d00240240821000001d40da07124440d101d1100e180e940c03466081603600c01340d0000c014480102140c3d2203d894141810040980c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 229879865 1250 229878615 229878619
    0x603060c020f0a05071e09090308040c0f0b0a0c0501090605073501060302070f060614040c0e030c0906240d0b09090a06020a0c0807060e0d02030708031303180303020309 74
    0x304518682e1200b0000da2600002e43c054068808a0f203000e0b0311142c40711128204483c1024001c1000c60000c0c4548109170b40036000755103481650070182024800300b0b25a0300305030070080c4030080a02c110301d4440115000b40c800d0389802401d5443c14140580102803615005200034100343c180030f580c6502403020101b020b011f40241018111841c05450009190f0138655150036141c40104141c6009a003e41011401800401c002400c1c60791000100c8400d60070001c0e582d0310a414842450405100e034030380302d0030241030201030030b50302c1c900087d5203030000310f00e043c0715500010000e260385d0dc075021114000e00d801c4a0700501040394089082c41500402080c00035645050300c8448640340094006000b82e8603a8007403c000220340d00c07100081c0d40003d0140e8142710710907207008006120900142035460203000005400071000303148504100310f4408a0003150300a102d030001007120403049a8100c0b041203540350300d000c4c0071b2609a44a20301c842c400d0382652410b100c0041803540100080504200c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 229881115 1250 229879865 229879873
    0xa020a060c050702010912031701060306060306062f0708010e0303060f010206010e0f0c160809010908070f0e04021f110d020303010b0d021b0f07060e180705030c0d0603060c02 77
    0xc0075404680500034460080d0004840010400441c40c004540c5600301e03000c2d28004040c582e040c0b1070721500303003400c3e03000c100001c0d80d07418204070440d4944a200c1c06840a1318000d809039071700041510b643c0c4081e14580070001c06001140e64001340030071003000106100030082c0800c0b1450200386451b0b820440303d0b40e02840502051145561011402c2c0f0f0680700303140c2802800b61101030105207088002030020100d03510402440d50000321035401818900d00c01c80c0d11315034401030480010314900ca079900445036584481000d01c071301d8203050040000da0781c11103c6002c1640d0759000051a0b0320100c02000d144d141c00e00700044c3c1040e40703c4100b00e41c10400c00d003110500030040c0c01c100c2e41e900c424070844849170014004041d09a4480d00103040000591021050300e121159000707041c11440c4031034000729448403504001040d00495000d01001d0100c1e51300c44420758900b18090b00d407100903c004100b08001000503000880a02610002e5070500d40801c242c0391240b40450040400c02c48650141c8a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 229882365 1250 229881115 229881131
    0x5090a0b01141e03071803080702010f0905091602030409150e090304030308070e01020f1c0e062106031e011a120a0b060607060e070504050105011b0b0403140a020a06 73
    0x82c80724215451103050161030f08011002d01c04094180d04050088410040c2481c2086010301310f010b142401f80d4020034119507600c0701440098010080b42d90f4900c28401d135040c080000703658281039690300075141c42d01c0800b0b1185505040741540f04580280e41410329000219464501d940811001d075424414030451031745440d0074880d030b02c0c080c5201c0180000c407114001245c40703100d0241a504441e06004540100100c000310710304104075685240405035070007038000000c2c1e80c8103120303a074180b5054038000c1c604044141d18071130014200c900b140012483c44049149a00c0c01c110300b4442071940141801b8442e507201c480d40c0079100c1141140c0b55000a480041c10302c1c0380080201d86414402e42c014043d4030b103a540d17201182ca200a115651026040c4822808140036000b020f045444100c0a0b007095030400c0104003c6031010380110341001040c03048040300320381010a01840a800507100b031142d54462074102e0340c00d0300030140624140808a131205e1070580002d0020395040c400c90302400400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 229883615 1250 229882365 229882397
    0x4112812020127030305070609140a02100f0804080c2b0e040605060717041d0a0c080106080403030b060729010e09031206121c022a10030605090a0b01 66
    0x19034049101401a4080003003000060b0240e0024074030648981070119009d0b00a407075041c440300c0e0309481410190802c3c542e400840c64045040c1080341c0c194140200b1020224100800a21004000410559000440d84a290f50800140f9080418001707014880c00c041650444450920f10303403100810108240074080e850240100d2055507400f8246504051403070716840d83c041480c030101003040d40100300100b205158524010550801140000b5681c1004909003049688500045007000a080c0052044035408400d042d00181c142c030b00454410155030000e41c403031068003002000b544a990b4210308180404001c1034082084031600c05050781e03514054221114100c07800789254108103c015860000150b24603080030340980900c0d03c03013101c001298a040003840d13038203036800c507401c00946480750304014800e440d007800b07411200c0792641c1200408506800054a6204020030310040d280c9900c03d510140040030028400031060504911b83e42c01006070300c01c0d241c002a4111407000001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 229884865 1250 229883615 229883657
    0x160311040e0406020d110d0603050f01111b070b0307120b01030501030809060d06050402030c0c0601170d0f020a020d031d0d0c050409080403060e03120609041128120201 74
    0x907051001c81c0c490a980365a1024004e43c032141c0c107204125641d400620350ba80d50400a0580c4042407031001801c00d0660400da0f141003a1800403041d981e043c9110403070390b0042c03403003035a281614030180c810054001b4841d8074140326050f00b005100200c0801004649940902800303281c012900040120821950045055034424000904412400c000080e6141804e5005116002c1c15500001d074040d04c40000400b643d0040d1018000e4403c0400c417110140c0c0c06000e21401011420006203485026608036038445444560110a0104002c0b04170803290003403060984060740207103940250ba1300d03840c01130512441320340310812000d103000200c4581c1c1401d451003008150480d203e1a1100e2600c4100000707002078400454038944d06100000010b0346a0144200c00240c0101458070307804e441e410100000c0000780914420340d2000240f00c0814024020003c04000568441c40459100580b01201201803902505884403644002030780c0303140915030030000ca200344c0e0381c4015400507245034114 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 229886115 1250 229884865 229884869
    0xf0e01020703021512090a1101050a14161e120221030a0902120705090f040b06240d09050d02010c02070e040302120a020c090a051509130b16031104 65
    0x169001810034809072804284c403c1300c0090341214289031640d4141d840342c200d00d041e5240e1078603a2100021000300034030803680c1048041e081c030b412810081070400042c160724035501d40b102070000009450860103114101074007050307046004983c5182010308140140481c040080e10003024000140c55400c6c40416000000c2c080714203280b04603550458503503640d60018040c885495070b00d140b03801c0181c0f105000181228500d002404e282d40c0780c14140200e40c00c3c01070980740802445400c120000d4a41a41550000e105070346c41a0000862032000c07040c44040e01c60000b0b0368402299091078503c00d0b800c00c1c41a0fa1240b01510900364088805a090b03038145d22807600560040c0701c0500400201822070f07035000c0d020744100c4251089041c000103980d404520401c005030044c403212038907414a544580c2d040f0110760307030400c00c03840c2000e141c0c41000c1c42d440c0400d208e42050b4010944046140ba001c60b0000d400107441c140c1c50924039494004100d500102002190a220b010719240e1101c10940e02 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 229887365 1250 229886115 229886117
    0x90207080735131509090c0c1a06190b04050114070c0302011107031203021b0a0201051603180801290306010620010509030913020c07120212030a020d0f0e01 69
    0x2c0b0401845030041c69802101550408010031140003500112040c891514456641c0304d800c2124200906074060700c860150131014030110f0242c400010314101050400402035043d100410f0712884009071601d2203502d41c880c001d41503164046520400b00c00108101c0700240c841501000510004850318040c0800180c5a50070005040007d940500443c004140e407460503a01440d0312542e07003804000d280e0080800090740824014039560405012408660004009100c04207041e40002c04910580c26450202c030001540a403c0602030741b20144085243c01030114601c0e21030030801d0003440c0036622000c03100761940a002c450f000b5020b00005c007401c05400342c94580c0c01e000e0141d4031500040c030143c99410040881c01e02845080c030070f190042241c10701860780c0710a41c00c100191060070580102c002481005a400750301000074407001105c0c20304e12030007244091400000c664020085c806d408500000030850401c640c0441c000303c4034010f070380762001c1c47d850080c1d0440e000d500058081e4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 229888615 1250 229887365 229887443
    0xd0f080c0d0b01051611090108061003110f0307090b0a12120302090609030604060e1c021504030306080d09090510060c0b0612010903110f0d081602070902070807 71
    0x500c90700d2954026805049041c18801d10780307031038102c54071582203102d0704c1541e0f440c203001d07410400e07850034881103401001e8a2000740307001c1c01c040c1241404c1e42c074140300c000c10301c400b1a880d0403416102c0146081c103a41008082e5524560b540d0002006400d44060a61048614441c00305041844c80c0b501001a6003000b4081012554040c3c254000d5001110490b840755051258100550701040076502c1144146808100644505041490b04803080c0600d00040a100703000c2424550004944488602c50200b0300080e031602e0509800078a2180c00000c0e8600419004400e01d0750005041c0040355124001002a0f581303100e2030300c203e5035039030144600050b04900c0c000c02082444030340d81e80211006284001c40f01c1c4d2206403900311542d5a00032400700d071030190010000c0340300740980040307a0040c030081c140c0c11802040c02451650001c100da007800b20075135510905a442001224060140c0f68800c540d150214280186160040030b8126441e0a079200c6080c008182c3c45d10b00c0064a81104001c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 229889865 1250 229888615 229888627
    0x70906050a051305040f02090909010b061608070602040803180f0f06180a170c0a080a03080901021309061707030201080c1809011203110105060f120c0907020d0f080c 73
    0x40310076a0103c0c00e070b20381c001d081181c04220740c0c2d243d02c07a44580d1013444800682e0340c0780c42424000e0940c8018a09c944507450b1846240c0c003034607220115441c800741024292400c1c0103d180035441c40c0075444018103190301c00302d8080f1760040008010b00f0308464454140860741295420041c40100001d02a40c001d03281c0c1001c4001e07800c04001034400041100d250311001d0350701401140d90a80598001400c110158203c1001003006101e68403100c1402e50b074007202d540c24529403d595142d400b000408022141e030001352101021740c1918542c04403407492044c21607031445500702400b154015003141c14a114000d0050000008000707040340d0b41a1120000b65503001e141290582291171515849185d0840c05000c0e541c510340310502a01d1840040550703102c16003001041081c1c4403100d041d5682c034000a000319555124542d4190200841d08955100306881696090008503800c1e0764021004500780100540c0101d00c1d0084c0c3e18080e90f4000b06c0450340a0115031940040d1a401981c51042242c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 229891115 1250 229889865 229889867
    0x117040c090507050706090b100e1b031801050a09110102060709061b0c080d0e0a030314090a0905040f02010f02120f0702010e06040b030a0f0516110111130905070906050a 75
    0x40e50f400726180c14510708029980e15680142c98003007004580d103000140030440c212071f508005802821440c80101400d2501d481c230804111190340c2620750007040480021000f0804c0c0c8240e03202c41038410000c8c469820108410b10140c90182011200380310b40c1304003090554070005955108103099603030100f01a14015040d109002c0c081446c121004030380c40c092001c9841c03074581000070101a0014004d151718120700034000350b030b80d41106d0701c06c1007421000c10110782d210340301c0203483c14800c25083d51031780f000c000103005102581c0045001400c1c0010001171018142c4500881e90007a259444040c8502208a03103c80514030b0b003110400041c00048181348180002d0448544181403100041e910200060b440350032035445000c4c80c0f10000304000d400e100e10b02074003c1891031004180518101900700c41000d1070030070001002c2010545d079000c0400425040510681c59552401d0350310000052a0817024181d4040e10000f507040101050f0410f20a07907102089552036620340c2cac10b11a0750a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 229892365 1250 229891115 229891121
    0x20a0813051c1e090305030a030203060a030b0108010c02010b060a0906050c01062d080613060504060603150b19050a15020708030f07030315140402070302120a020c0117040c09 77
    0x409071080d10400c401101c82c260410071514070070400340c031103040741c021401000d20740d564003091a40070031882c04400c1002850010682d0000b00c494200940c4998810003c10100e495580c40648a50840c000000e007000041d8003030303c00c0e140c0aa000303104c048403501c24010300303200c0e01d0402e00000745c0003d000c200c1280309402030b10359421a0000421904d954040d9549151400c2c140585200f241544040d40c4d02e0050049500410010004d00303c1c902e0481c0501901032082c14002c0c203241e0b19400000c0030018139500901c007960f44070340c8110344124500e14a500900da02e011690140841040e014000a0035840800c04c43d04001c00c13803150981400142d486000e1070b0194507040d031007030340d40108034440148081d24203400d111032816103c2540c3c3c01c0c001c0a69001c40d83d0100585400fa1061204014580d09022200b01c00e940250f034440c041c0c907040740b5117542c1820340d01e62070b01c1c00319500548503804103a00b9800c580036079071856a1140a0740180043c4400d9030018080f404e206070070003201745150 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 229893615 1250 229892365 229892401
    0x41115040b09060d0903020705090a050106020303010e06040f0c021b030a051b01050c010c1815020d03111e03011a0c030d09020a03241d1b0f061b10020a08 68
    0x1a0009080c141002d804d03d0a40d25901011000744e003010405209504142d59515800411740c441407044c0e516048020352a1b10041c090340a040f0040c04c0040d0321a1240d8000c44036500c3d4803001000404c0c1028002502e0b0114000f45000701c02060451116520300025226031081d081005415100300c6944200c090b120b50141d03080c103000003408151040746081c03042001106180d01d880c9032002d0310340b0318040841d03000c0e040605070305140c0e4800c1c204507074000b50350b6440010038100040e03c100070010941c2d1a000d0f1a42502d103415405007030342d1003042080091812107860401034a02030740e111100351818080c11100c40a01d610911030307a03c903c5441d8001144503070000c3d01d1006c8481c5c4940301d03101d601484601100c2a51341074010140000c09920030914074807009481c03142a00d10380c0c1100d948542c03120311715815982d1892102d28880c0c4c1c42c0c00f115140b000b8000d00c00790355240d040404e01d5a804106044030220302601c110480c41040034000c4a60818641d85d40f105a6998180d1983c100c050b01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 229894865 1250 229893615 229893619
    0x706210b01030b060f0403110402071e08040b04060c17070305310801050403110105060a06081012051005130b0c0c0a140c19080706081815041115040b09 67
    0x401c0f0b107101d951520310042003d4491000030907a61400c3d03040031000c02102415543c02184100328520200e8100705404000c0440d403c100103540c0300c582080303180340c0540e07080082c51020000b000240d01341c003d0342040516100704000b00a01c0d000280c0800d03103005503000580843d804110448041c0b40c0e804988045105070108408400c3c20058944016800c41d040b02840d80e640c0c40c00d010615420070071800d120100320340240b00c2803400102040c1c905c0d8162065005000c0818040303110844540403d2010707103204200c0e48684c00147c00c0c215518184101940025840c10740032400718076180c5400c40005821081c6802540c9a6001642c010740c48036010b02241d0250400b00c4000413052030031000c801c0104070013031043c03514020400441140341c5290001091078140f04001450021032010b045400601f007040f4036540d810b00030b0700703554501c81d0141818021050301d80110400103961310302980c0203c880d114104504028080244900141076181000c140800c20815801c100200032541c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 229896115 1250 229894865 229894871
    0x309061303080d0c110a0305180315070206180303060f010f121e0e01050108060406090c030b13030909050603070b03061816020609190219050d030305090706210b0103 73
    0x149884064a60704501c994601d51038846000b690220751141700415592042400b40c4194500c0d550301070110301c60209094040300040a401195640a0200d54100442049000030500d03103020000c1d00e40c6812100c0c00d140c01ca002844008650001080e06d110300f001400b4201c80410000054038160280208401000303c084140c100410050207801501010300c00d90501803118a100c40f000d4504968100c5811f031301d018010042610001086c0b81c016400c084000348074015400c098000e41c20b1038002801034021002032040709080100181c440d18041d5071034541c42030302c0300c04460944100380c3c2c6084d859484110140404910140110b800c02e00080c0380e4900d41140c0d07444014000012510107800046095900700e0712601801955440402c03000600228031010394442c880001c9450007a000c0c807103080180051030052003484c0d028150003014011840c40610700280900f1040351140c0c414050100001907a900072505407440d089070706020cc009030000c000710710080c84c011840c6410141c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 229897365 1250 229896115 229896119
    0xf130b0103030e122b051c0e0f1f060603180b07030e0a0302011b02010203061804080d0e030307030b12150c0d14010f061409010e010e030708070f09050103030203090613 74
    0x808110814055010703d40340c8450345d1176120f1000c015111a5092020b00604004090926070080d1203096005a5404000750f04400110b6061410080c0d019000480c415200407031244442000002c1a003801400f0600c00c81d52a21130441c00d035512918072504180c80c0203044c0c800a1103001140381c0c00a4540b50003d241d030403110302107142c440d80b240b00b9005170759151145e0080c24054a40c01410310001d0000703501e0341c140a404500c2c0c80000180308108002e6001c007145c100040e400860304c00f4401c0840c1440311b40d007081d0100b42c40e6070040d15444c01281c0f40030700b111110b08005800200303e0391900040d141c0c6a1000844040b456030041c501020f40c00100150100205148500c0c25204003095840d0400e40c100004049645400d40220050140310440d00c081c010010084030300a50082c41c00c061000141c0300185c2d000b0100c26516589402184d5020562590005200c01244c0301c107032000c8400344e43d81030b4960480308280405001600100121a10307404c050f4028400410401c044a0b807240d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 229898615 1250 229897365 229897399
    0x150403031110060b0a080c09101202090301050c090f0f060901030f06170706090608010f031205070204050a0b150705060601031e050403020303160e130f0905030c01050f130b0103030e 80
    0x90740f54020007041c44010174400801e59000d000329920005410b401132500d100e0300009030303020101c0010700040040070404480c010980f0b406503200110083c000f4880d0b8200b000310364680b6046408940e0181c140c5000c00215442d20ac2c240420392640900b01c2441c00c9a540700440c040c1c0283c5864604c0b568030b0340b00c00103c81d4000ca030131403044003000014200b5642403210040c558500e5610186c06c0120b00c10042c01500078410164044942c000c1c1c80c0c54044540500c140c1e1035009a54010f50300a00d018200891464907411802c0740d40002c440065000c80580454905c03805441c102400c581e010b81c0004525502039405050040c8007644d200041e410084032020a8030001c403011401a0008070500c0303d018490304c034101c500040d030308041c0d0b40042244046840c0c0000b21884417002611170f41b0f46d944109565108645041e00700c019641e44180c1c80900328080d08040d5002c80d071818107003000940c01c1d600d8800c1d100c2000d90100120007140d1841d2021101a49003042495001c6a000a04e629030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 229899865 1250 229898615 229898621
    0x70803030a05070306080d02030406031a030f0a050708120909070917030a0f0c050a15110708041409010503060a020901020129030705031f02030421080411150403031110 74
    0x40ea8030390401007898a0b0001c00113042e0350312a409601c05070b01c810481c2aa4580100c117480c1502d03510301c1c000500055160a81c14030b6100c00c920a60180542c1d4000500d410021134807001c940d005804689880b680d5000c070079944c02d09110100404a0b0902c0441c90134a0804825078101400d8034100c0440d0751a03c850200c040d5400c1e02a03e0154800124542140e4011000351000d4401d400c000601c3c50306912000e407500307001d0800270130b6003801d9a1072111180d92a40100241c4110310310003903e5440c01d29244041da80513018220401c140084219142e2415844d038505071140030340034001e03035181c03441004c01030b41150740d00c207040d03540b161021028903800c1025a151749282448400044140760140350403c202500a03d00175080807101001d00f4101055454020b4070320031f00107036643d4503810244d4440d684480010900703030110f280840e01130b5010000b13a000d60700131241c030036013100c05c4000c0044032201582901c0b5110014001040801e00076414070a041041a081e00c101c41e20000b00364040f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 229901115 1250 229899865 229899871
    0x213090602040e10050906101112030702010207170c070513140c040501111c1b02090903091203041212030e0604080d0e031305061303060218040b040b010c031107080303 74
    0x1400c3c00c000c00403800c4505441c40028841514070b4901c40c140240031680341000054950180810744840c13a01140d020008030305652080301e1100c1d22400c1801c4000d02030b62000b40c040e0f82d050724602e900d1135046200700840300e50583d2403005144070b5240005000031280074580d0920315540c0c440b8051740b491072000e01c4038814070f000040565a2418a000502a1161064114250344c0700120940c121081d401c01e040303003171009080c1415030240d20540d0480403035001c1c0000307400c03a5001d030030301452020000180000d070604840c030362106e104042c85a42d4038003c510807084050004203146001c9214805a042420880c0c90017088515890103050314026003a901100c005000003a01c049401f8175204614a80c0300c8800a5442e04c21940100308608105000b400e110340800107505620225000b9004000c0d9030084081d5210a04002580d40c541440c59186024504015038040d0320728191085440040c0161074003481031103161001c40e400605101d00010510030440c000ca03101d001000550301c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 229902365 1250 229901115 229901129
    0x30216030f060f1503320604031103120115030207020409050a110d020a0506091207080d0f0305010e16020705030f071a0a05040603051f060210050709080a021309060204 74
    0xc070105103882801c03540e0880443e0b40407443d242c1c4282c03c40a80030194800ca0f5000078521844810014034010402c1d444407184402d19002404600410000b055940c403940c003035280ca200340d016520005499110b0002100302404800d401072062000c00381e01200240c0c16450300504110341607010030100d80c00c10000b03072460340c40140b494040102101d011407030810242c82d1000c111655030f002c034030340040718020701d4410704000c00c1720951515050036600d60340c0b00503812900d03501e40d0744820a4442074184c01c1d1200041e0030111883c2c1a42c000d004450494400b10111852a0703a03070701020f25000d0360806038800f18002ca0000041c3c076541001051b01c0103000402070b00d6640d00c0d180c07207054101d090005072031445006100106d23480e03400406131400c490383c504000ca019543c0042001c06140340c025581c800100c01c0101041c00d9600144581d5103500704d00c810403107603c2e100425980d400140c4907400d039035031140514000500740b415001c60180c1c0c20705008900043d156a5103401c4c1d80050708051 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 229903615 1250 229902365 229902383
    0x3170c03090c010e0102031206040f090f06050105040b09011e08060106120e01270309080a0804080129010c0503070501060b191b06020c0c0a03050c010e120303060d03021603 76
    0xd030709200303020204600009003000c0c000c0440010010b501c070300510039a1222503d9041c000341458507650008a030211003408200507a1340303a46440415209801d00c00e0342c40300d15050010855050510807d9400740000344041a641c2c07a06950103070741c105c110380700c04106015040010306040c0030419a030181c03141c2d44409034400d10391806a0200c03158200070642c3d03681001d480e005103400c100f02c1e01161101684c0c3c00e80a802103401c064600c6003140d4800883c512400c0501024419094003030000e4500380c00003403100c0d1740c0f900e01c4c944200800040c1e03100b60b0100c003500b0001941c0504d0384411110300c10801d50341012001e40303405084403960b80c00528070b6000003c41028407201218040230303c03819400d29561b9107100140314144075001038401083c00c0d07400030b10602500740410200d003c84c032000740329200541d00c900e0030f1070f111072001d280c041c0820b95400490764a8544500302844440c20440290b0642c1c0e81c2004110f000c0c070319400e056003540100c4510500c0311320381d1480200514000c035015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 229904865 1250 229903615 229903621
    0x30c1224030316080c0a0804090b10030e100b0f060c07050307050a06020706080601050408030a09050415080312070c0b0f1905060303090d0305090a03140c01020f06070c03170c03 78
    0x20509031800300308014481d4108102010b03041c050000e0031005140c00240031919051803040c0c10b4500308900c403010708400f102043c00150480c450304250b941318815907481c03080310620711050742510840d1403c135000d0307000300e1b001c601200500c2e404150322003802411003802e450a40c003c83c032142c0c0224041c1840c0d4104840612081c2800c00260001700400e1760740f20441c40c60150025210680c50085204020500d000f240c2c030b583c0300d4000e440203414a030007520303a24003011074040e04020a87c415940a1030a1105c2c0c0010000d44e4080c0c8411140c100300954a003e01140a91420a40050145040c40060340350480400d15541a040c8188a1140441c5040c18212010ba6034505410b03078184500d400d11040140b10340b40403090b108109130a80d440701c20381d8118031703040d0303124000c648a41e50401d104200000500601d80b0702d0f00d0800910806541c05a89501d004980721088074011b441c02d6406600810721852041202c40b40c00740c060319004401203124050400d0f02242074480400c606008414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229906115 1250 229904865 229904911
    0x3051606050f070c050312060f04060b0306030d0e010e0d02040e060910111e0901030e06161107060801061202072405060d030234031217130206030c12 66
    0x10035500f00505041c00826040103558940d6a8441c1e1058001210b00c0e5102048c013a49608201ca0000c000040003440320644800c1140c450b600b08441c2d680c443e1082682d151025405400500c11424040c1d641d001c54900070828411010080e040803038220741d0b940c01c07404090606200c1640155415005002c400e1640a00c1d10300385c1d1901c24a0140e500c40400c822a10000e1401090721003421000310251920740f100e0058005010f03019440c001170003800c08001140d408020540c010214035100c801c41c0d040203101582d03585400317001d0103000c60400c100500c405806491130580b902c2030343c00003601c1e01c4940d980305034541170319143c03030b00040c1901c01e1111148a400d0003299413255040c0e5060f0f500c4d04407502d009580f20418000354283c18020504403c40c107004818140107000380a5514402030354a103005030891034080307800c5c4009101e080540c0030322080c0d034010718081c850500e0301e191082510740130080c01c1c0e40003900140615034100a9800e00584139200e403071250421610901d844204402 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 229907365 1250 229906115 229906141
    0x307030215010806060103050c480309190807091d010903020a02040e010905060c0301080610060c060c050d1a03012007260c0f07050405070512040305160605 69
    0x9000c10007488400041c000000c00084855024400b46000300d030745e46402046001a00ca08035190b1566000f002c80c500c2c0559032104140c0318103500c0a00c0d042148030019456110700341007200c0941c10380080089041134038140d0141c07406006c0d050002000c00360b5035181a4a410b0701944000c038031907115103003850800103050519088200032402070009060f1650000e480ea0844400284610f648400c40c040506096100c1440726601908641250a107100b120034290024440c0321124030640d80040c0551040000040444601e81c69840940b825540d03a80044c007640c4411100f08032040c82108100b003080d009507006035402c10300c078202c1c52500800345420b482c4100c28054800300e000740b444418560b00021a0700340c2e500721051010b2004010006407100710030400400300030700d001c10300491020700882c491031090049411291942d40d00c1d018001902c0e805c44040000c903c007804050002500007600a51051003032500b83d142109103036940681080300101500e96546d1003080110007040c2c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 229908615 1250 229907365 229907383
    0x30d1110060303081308090a03062007030f0509040908220f050105041707050409200f090c0a020114010b040f081621020603040b06100806010212090d080a0203070302 73
    0x40d005011460a5440181c40841c0107041c400c9060346012002c003d0021000681c1c0780188003c1c042203030381d5034900f40000582002d55541d1101c010302494803d40003c4001190384140d0b00da1604020054400c1080c0c40c40d4111640071900a5251100c0e03000280e00d0b1401001c0407040e0003020302d202e2000c4000e060040255401ca0181c09010980c02e0221340c2e0443e0594084450a0101e11b00c01c001030a4690f040115690109410904000c1ca000801501c2440304940d051003d400d2a002881c40003040001e078030f11030450f40c101526901103190440030b0310061084640350700010940c001c040b031402d02819403d03400b003c0c0490000c00d042c0190802d40501e07a00030640d0b6001045584500035605d4058580740c440d0109661100407550b400c0f4a41d071202074603050300180280c1d1240b0309800c1c2840340d00011500c00d880b941d400303813200c0c3e0b0080c021070380f20b8011b050607070003004101803a1160a5240e440004070f140d000384a00000000100d9202c001d089010841d03000d9915140c1d00d14001c1c0c0360144407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 229909865 1250 229908615 229908643
    0x270604290103060f0e0711011104030f080705070308030723040501030b1302030103030302090a050111060f1308030a061d0c0904020a03060b0c0d0f02011a0904030509030d11 76
    0x103280314440c1a5511280d60a010014040c005810038001038000b0606940052184200c0710b500103030b40361205003144d100d9131207070302c801c2042900c030b502c420b00f00d8641e00d01400d020780d81444184041401d203044200400c1c81228405d28058060721000e1070412907034412250244000100001164072100c91282001008400341c151032041c8000740150103507010b40c604243c1d84d41844030041d6540344804d545030400e00811540ca50b100d0800130007035807040800034012011000c0001e41c651003070841d0000d084a802c064049915407920801400001406458500041c455001c000c030700c0c1c1400650241d100013800140d0300740b0b483c030f0360b0f654882c0c55290391034040298401c0041800111046486440d002c90703005907180c4031100190014840c503004200d03040c0c1d012030450340d0b26900181d0f9281a5100351582884507944100c220301b80d42102c1103c0702c0c0c40303504c0c004008050a0401340c0e140c01610a0070124102000c002c042031401380c03a500f00d6400248620302e1801200428401042e886606e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 229911115 1250 229909865 229909871
    0x10e0102070309030b04062003090c0a08100e03040906170f0a05100522060c110102131403070816030308151806040603021203130b031005010f02010902270604 70
    0x74544000e0b01004282c4405031808981c2000a4200600d5a1000b00f402d11011340399401c000e56101032081c244c100715042c244501c18000075201a10782074407007904480c007400007011909040345840d0040c10901111003003920007808089030801d03290053701c025140031001c0d001c011a06000d002c2c54110000c0c4818115002058030201054001c903101c01e940422040101d2a520782400340d41c02c004102080b41103e0990498900030001a07410100c00250142c0c0d95550050158401900b01e10468800351b42d01e014100c000c1007045400d0f08400c1d00746c00c0080566610b25078410070315040003c10f42c40d00080203070300e440500c10550003210058210381461079101d16400701c0400700c3c04100860948000c1600392030009a0241e031181c11000180d50701904441c00003400380c0d41c1e99580c0d001036a45d20900c40d200040031580351071040c2a00d03c40e010300c80c030044c0c44515010040d112040010b00c440c08554942c072202d005030f1600581780707180542c0e42170041d02c3e02560295102d201003024001d203214a007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 229912365 1250 229911115 229911127
    0x2090103140709031407080d050d1a0109181e0e0f15040b22080414011409040207022706040c030c08040b071215081606050421050a14010e0102 63
    0xa8410410703000c4d2a4080000701840d401070904615000300f0307620010861207010f5140001503401406400c07100078425060114085a200c26815140f12a10103400200d00d103c00308900b00040a540c0340c208a0f4180000e00e02c5500c00d112000c00e6070440d2400c1181e91205940d0300540703410445ca900d00c10100303001c0d080d0700d102101e45400758640604054034200490b00403500d140e2041c0d002014900f4521200d1032905603c1c41d0541c1a500a48115105030030798040090055001c0d1440c0300034600907078941c0c0d2800c03a011080000a4000c220260b81140d04030291142d44080d105000180b113400b07a84e90f920a00c0d00104100590344500400c0e020142403444c0c0d100306503004500f26821a0384103035030403160f5481d178030300b10754000314031525040b898103000304c84056000c00c42114081c0c3e5121010345601e01d40450001c4091403062140d90000741d4100010409007035000c0c0300300724606509184c40140340350f903107a0910300280305000783c3e802c0180e04800502d4500902c17484604007100802542002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 229913615 1250 229912365 229912367
    0x12091e0530030c090306090a0308100815090106080d0c0c1203050d050a1113090606080613051005280501081303050c0a0204050f01080708070b0a030209040609060801020901031407 79
    0x11007811030034500030200210700400810015507500c5200030703003154190b24019101940d81c45684109401150b4054041034800b03d50081120603100410020310950043c1501070580042c01485140595a9090007041113001400341560300d0100d503448050100490070841003980007503000f4202d690762824180d00003600304058882005202030000b8195803600544006858104d480d400c90800024680050f40103100b0308809a030081c02040005d1a11501c041d51b440009648881d801440d4040c220f0250070345420085d84400c1c036101000c102a980c10105071904d1000f03124112249000440c1c40485600e01500d1000b04024030f4014120300300b041c400c09250f55081c81c040c2c1045000640b00714055020801da540c1c05901800410842c030788261018141c1c0f9003802110194000d2080003d9002c00010342c900540d04e0307008a05281038075000055000f5801042429041519010001103120035845018010000302d000965117a8441000500311a1f0034000300c1c44103011902446141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 229914865 1250 229913615 229913683
    0x50d030807083102120304060c14010507050304080703170709060e1e0607050705090907060207060302190305040f0b040501020a09090e0a0305130305010f060e09010209090712091e05 80
    0x95010000c1e20002c01443d030020501c000081050007040e4400000d000400c29484500d880149015403a0381c402a4414000703c0d098600c01d03124000080d01c18800320f0b000c070781c0c0303800202411482414103020000d0514014020000110303821004141d42c00000c00c8074a4010214042000e000c4540d00e007502c3c03e03005201c038120610000c181c0a180003044200c10480100580000340000420004203842e2506820b59942580e02609005026440380043c3ca94001d00a45881d403002c6054001c0184543c1002c0300240f00041098994113260120080841d2a80e41d205005074055000507a58142e961005800c41c0c400e980100308040c50214003462012010541442550f45440d0050b80d03500342809035840c80200e504081d0440d441c041f400340407680e03d644241304456107540c038036003d5901c070340d18a0700b06d0190802c5160826010b8000440c490720428601540003d4004005a10f02082e102e244651507000d1021202506800c06101801800c104e0032081d100e40605205614403e111250700c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 229916115 1250 229914865 229914931
    0x105041b03021b01090507061806091505040306050a0c02010c0c080d200f0403060605010905030c010f12090b0105031527011803020303040b01050f0325050d03080708 73
    0x4042c0d01181600710140b51003012005400e8203070082c08114981d084c17458031842e0741e10480001c26402e40c00c0100310f14550102d0300c216400c540320414240d1034000e0120354400203500b03881c10031508100210000308039204160042040420000d000c500942c4040d007151507030130318042481100155a0300045100d0120b82e82118111804a5100e982e0b0390401c0329011002c144154003803010840048511002003d001281d003d00c6003030010607500e6006480741140ca01440780c01d9080440c400c1c09a500401040c0307015159860004214224200d03001c0c2150032035403089924281074001008a890708100807180c00b000c0a0240000d8205942d0300c0c03100742c418000c0c01d04030301c98000104c40e202c00290f0054041001c03800d180040002240340c02522680103ca0485481035402e00101d41d60034110802d817141c00002d0700a010040f80100941603035002d4295000108030402c2d008107803515200c1c0a023400d14400d0316000a03034140740780d0283c00c441e8010b000401a00600a1001881d0207010700010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 229917365 1250 229916115 229916117
    0x302071101020708031b0106050904030c051501030804060309030e0406080102270a030f08090303030f01060201230c090a051806011101050403020c01210c020618030c152503090b0105041b 82
    0x28940d00c0d446d4124054101540280c0e840352281041105068102c07042550103071040042d0b60640d807414041003022070003808058541902444140401c074000e80c0b0000d42175000f42081144900102e00040c00d44400303030880302c51a5008904807001025107040203030165000d611070626003940b50042100d80255101c0034190329030041c0706030248882e8008440d0340090207019696603140009000035140002c5c407a2000542c1303410100c00038a000a484441c510103410341140460721480d40c3c107641e0340c10106180d0790054184200081c81e0b51024071444840760b02c101e075104c4d0f52509230009012201c03150f001c2c4207164146420000041e03404145080540c3c800d0a00d0b10507520a60040c241d140c0a01a1b2100000c3c60007100004068001940701e1084d0040b40021810540b038146040c1c0341d00401c2042c42459100460703400b004101080c04940c001c540240014120240782c0310340c02e1100c1ca03880041d010aa03119244014018103440482c007602054409000040d00c2c6178240600a00300030100b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 229918615 1250 229917365 229917397
    0x4080304080408061f0803120103120212070b0702010c05070f080711060307181a0f0a1b0803151005090d11120c04151a0a0507020a06030207110102070803 68
    0x400704120301c000e0314040d0803084111006403600c2c0341c103200702290868000d041c0f541c00c2c82000900c5d0b003000048030440d205000d43c42040b80d00e15501c0198000700d21007858150b00175a02c01190004514001c1e01149014950124003400c0c071220103401c44131240104820090204074200104000c00c680e5640103500500c0d91743d407850203080c03070702080000d5200a50f0000d000002d020302039a0007482e0a582242620010b9012907071400f5201510700d841c01d5607078106205109000c2c40d4041c0f030018244800c5241401481034048200c0c00d01a42595101100c0046002c800e020038404a103221481c0e074181550703068a50041c03500054540d004007400144100310111400c4108a80c4450000551a000e070104844016000d103107a02c650340c030603107079010700d00e801113404003e900c2802001c100c03002e94001d41c4614180400101003544089110018807108020000050b21101c196600512513541e0042e15004c4624103036126509034061a4115400b016061090340000b008807028a04042e00071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 229919865 1250 229918615 229918621
    0x1b0c060b0d0c0312022d150601090303030b0604082b0203120609060d0210020c040f090f020607050115060c1101030605030c0f031c0201150603050f010b0307020c0a0f0f09020304020603040803 84
    0x2c910303042841031802201c2241010400c075143c501809102c0c4006c8200c00e0340c00c035005000311200050000c0b0790807070000380002b40800100780a80c0c820140b40001500c036624140e1529030300d5140181c50f004c0c22028141101510701d089858280030801114a44059464030702c4400e000320b140754024282c03d200b031001001182e01e580e00c4490001c0c07225070144c400904050392880c060740b1181485030090086061141c000c0045065210301c50220b54000400a20800d640d000d201c01a0440b900c12280c43d940d4040c0b41ca55804501181d00060445542d000c1c003c04241c5000e0064006000900f814542082c40600a40c2d5000c2016050f503902654044c642e4200c240000745081d40350800500390840306010840081d90640000091030380030319000250715681c500c210120b400c100c038030800c40b241c808014005480f507100156003103444c51040318024081480020014942175025603242d9040d034104001d6001c820b11a04000d0212078011030445c50241c011030014030000380001c0c0340361400000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 229921115 1250 229919865 229919867
    0x80f010501050712032a031805070306200c070303110f0c09090307021e04140c07081809090c03060108030c070512030705060a0902090a0e1f1b0c060b0d0c0312 70
    0x101c203120003908140e00101442407030444120450b00d80700c00c0d00103820301c140c01e080d1440078000e00894035805070003810000d0bc0c540361000200b00b03030451445100c0034800c03c00704143c1c0400160142c100c081c4050b207262031440c030300501040300703140304c2481070f4000c500300b00c454102c00700b4920805401598045020340d581000d0314194410880c00942c0308800e510800c44884800c0c000e0343c82c5840036030b010800444010311071940c500084039802030500b01001850002a08035000d0901600002c1003012103c41440002d0301e030080440e4141c9003684047d0300300b042032504114140c0185000d20141d13140800301000e190301c40c580c9014190203030301c1d091400100f02e007042046807030ba1500320054411505020f500384020b03007100d4000342e1240400b24003103116803c3c14403804c80c85030300b1000140f200030010860000510350039050040e0980d903441c201c11165455018080038002c0f0341d03071808039941c00c81c41e10100f112182c040c0e0703c0c020021a000c40000500c501c3c9042e06894200d20211511101c0b00c0e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 229922365 1250 229921115 229921121
    0xa0c020a1a0c0105070c0b2404050103120f0302040602120903162303010605060d1a03190201030609060506031317040b04241b051213030201080f01050105071203 71
    0x484800d030110180101c500304a2000090300108044070000d100b6078980b603000320740c04c12005c1005040f4001c1000403440300b9180c0c10928111000070789485000150000000302240c400b40d2041c1c42c3c04081441400d295640030407120344031171450900b18245401d00030025035070b05020f461400710310b50002d68050030369400c0102890145540c609081d240707460f1400284501c50404510803c041c5802d4070380050300d41070107a001503800142c029400c1100700741e040400741206000d000f500695a4403808101d8805110004909608814854201c1e1251000504640d8141e100010085c5400300500150b41c401c030449030000c407560014185a45981001040d45004100e03000041200240002c2c01d0a110005803044403040d492519488404480c003001d4510169003041c0000c0301107c03000e51342e03000541d8285201e0302410031142403c0c00c030b030b6545415038001d5200341c01428007078004108640c0e012110315402002041840b58952406001800c140508a80107214100d100f0704010468482c0d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 229923615 1250 229922365 229922369
    0x3040b0d020f0301080106030515012103110604060501050a050603010b0711190e060a08150c0a0e0d060b0f01020a050c0402030406091e050d02010603051b0102120d0b010206010e04080a0c020a 84
    0x441c10b40c0c0c1d01e580da111441d00901013403104503218011055507840865850310b070307d8122070340d1159504904010340103400e40c01d0b10104045091001c0c0a800241e090000c01c60380b40f10360312850000807a5414030b4100f04007050140d000b140708460030401403140c420940241d44800b0b40c8190548408c0411400050000e441c070380780c0840407840d11701c000405000107086280618416140802001d80303c8010a44450503e44d1210308203a8010120300c0c0c9800060042040540c2c1d4941702c1882100440080c00541e001801a142c641d22014500308a1034118094141c0280c24001084195020741d1101e859081c1c080c4d84a20941e0b011000a00b030011a80008952940c401c020081c3c4916558003029503904200e0283c95501c10b888610100ca8014801c050550f81c00c0002443c0c042e0b000e00e0540ea0380385c1c8103180203045005401c00702c0c1c2200350311009042c0f24029a0b20114551407050002490000140c0c00007105204200501010401c01c00881760128980e00d8031000e640a98000300300d01012079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 229924865 1250 229923615 229923637
    0x609150903030d02190903050a030e060d02040b130509010810051b0d0906050a18080d0e0d020f0607020c13021813060e090a0c06120b04020a17060a030503040b0d02 72
    0x1401510f8080c00d030700600c0c48001c0c107600620503207030b090b508644c02e840c00e000080855203c2c45900740401e0241d00794560141c0010030291420800745161020790f00301da407102d4080780d408600c00045614081401c00034140941d03d800c00c561610207010395400110a054021955a00209400300810014070600d102d45440c0c907a03444c0101d50500000380b0010000b511820f152401040e1102800d011b41d0088000000c145588401c3d541c440e198264091401807600c01c1d03841e015104441014000343e040380707581d50040c1403c60205a071580c28410014500d2085400c000000e0b035a6079202c0302400c00ca4002d0100c01a2207008110b0800041160880c641d6406622030341c44241c0c2000c1a0464420303544042ca41c1c0215488540c60559501d1006100400c4409040010b06c9200d200f01c607040d110646900300840c072105120042001c9903c40e82080c3c0001c0da404103640090392020304010342100341500c4a04c0b950385140c4480d0388034003890054100b85080024426042e20150301600c0814081e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 229926115 1250 229924865 229924867
    0x5010303090509091f0c0302040905130506280c030b0a0b030a06060206131103070b070f0308131511070c08070302040b0907050313030c0b0906071b02060915090303 72
    0x59003400303081c949951049500c1021a00005419000c010600c2c240d9800c80003815180c90101c40588000f921029188400305a802c4c000040d0301015805141d001b002c009400442030324540c280f29090a20050500710803202141c00950001c11803140010209044c0c040040d0060010f0012405410f4011480303900c81c000607400302e20303080502d00075401507880c28010054169208000d0740c50351f00c02c84000d071503440c0969802c0e02140d6004480000d000004051700d413090b4495074001041d4210070010b482509903662039608140d0032804641d0002c0d0102c862504001d1941d482d01c00250b10440503844164a60200d80e41d222450010303902110340c0280034212407604c505195aaa03413092005a10072070410002098500b00340803e280604403544c1c5492869540e00308903102803514400c21402c1003140300012010480781d040e00307070061540c1c102a2000c2e04144000520303024031051160285201d102c0e4030702c0140e50f900102c0390706c080140c41000c11a046610060f0407070255004075501800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 229927365 1250 229926115 229926119
    0xb071403150406050a080705040504021f020303070e0f0d230304060e0a090c120b0a12030e040c020616030b0d05070806010305120304020f01230a020106030b06030307051c0309060501 80
    0x6840e000e0309100304140c508100d078941c0e803010040e00070810f108260b1b254001040a00603400c0640200740e00a0028001003a0781591000043c0700503101d52805c801030b00080300b441201c551050340c3c010050022511255000d0400740042c496144540c40100384503842c1e204160800141d0904802c0b10400340700b030701d0301c039503540c0001341440d44100b886030f216070324415001c0350740d41c05072140b00c848040a0344c502c0d4019401c481c0b09002048090800c0e0341c8a200c1b10000a50401031641c14000c1074881e41c3c0d180400f0320b980040c0000d5502a24211095410000400a0580c03940440842d00320030382c031f8085045412800031440420400d00060190701a40c0d101094403480054030303904a80c424011038207010002010088140000c0d140294000b525101030312641d8440d4400c90307110b5110002504410480c6066402e0070b501062060700541d441301020414421a41c0c4c00c550701401c1900990315200081c0e070359544812001880540c241c03845940c00780e100c0d01c2a0f2200c02c00725071100c42081107503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 229928615 1250 229927365 229927381
    0x90f06090303023a0c08070804031101031b0c06090b0906190606050a030c050d14160216090e07090903020102040e06060a1d060c1005070f17040b071403 67
    0x1442800158050710501e640c42d03101d2a55070b1100201314518004d2034035150107130404a0913102c1003015080401080903000c1010503035050040c001e0380e20800206582d1451031038031124841012990038189071416206110020380c034150120002550b1408103003128803440d04000400b0130304405040200764808000c60710744005043d41c0a480440840100e108102482d03000751007080c010180082c00c24070204580034082c1d00502903001042c1461801c0944a0905100f110707400b2412a04265206040c0030090360780e1a01c40da11981c0c07034030240004103180300c40c0041185540c46110300f04c1d5561300c45010703290401c0c01008003600450b0000d00c1402c44030f090007400b079046402508104602074011550a2420000300c640c2c44a03544c03100704a4407a0380140b020400b040c5440380b9040002008000481d100911204001d440d0b0140d0024450a000c040100325100e040040d80c02d0000394590021401c502d10315084d406503104800e8180e5a980301d004841680c5c01d0340b005070a1303c1020050000318 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 229929865 1250 229928615 229928627
    0xf09120d0c0e120d030522030e011101150e04030c0f03081b07020315060f040c0302040801150803070b090a0218061005040f05090c0403050a030f2303070f090f06 71
    0x1244841d5201100c00704940c0c200308101e40c8607505942a41e020280104600c0d00903046140d104002d801f40030010340f02603581011451042008a0016000d90621000e544c1c200b2410510741191070005c1101000d200300d03022100103540103c1035884a01000034082621804800c610f072580010043c0011398503260190044405854281410f168030b02001500601d03d07041da10840d80081c002c04d440b075070b6103126100b0844007400f141c1e0007410800d50901551a280200860034245603401640c9520b440e40b00d07400c507010b803280c00444841100c8100001040001521303a2b040d005491180c003901c0c2c202d402494070240000c02508030728418101e00222024044035417041100f40c400316100070884104560754822805031701c5002040301c2042c011402c007800302a5000b90a507001c64917044e200d854070740c80c003000070038100c000030300a10b2901c80c03503540040c083d80c070b01064034940c0901c0d45201140c0341e5140030082c000e070104101c4610811a0502c03c081c21001401d0b9031751090149038032007030300070f0070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 229931115 1250 229929865 229929881
    0xb0a032703111005070503061908070f1d0411100314130b0603060601080106030c02030702040905010204050111010b130903180305033121060c05190201090b0f09120d 73
    0x2d40d000c2c2d4015580c00000701e0180511400c00d5540705841c69450104100c0c01401041c4d100c408a00c0c03041c804162210200f150740c0c003a102c50045800d0a0346880700d030180d111a02c030401030f0140301040070710000950700d200746010090b08a43c219104640315808500a0000d1030a481410b10080c0c10b1040302e4030700f080000840350082801c408a9606c0006041c1d0310181a11036a0004800200400c10240300b07501a100004291054030324141c80c07a0001025602c080f20150380710b035400902003040c1d60304082c0d00b00300c090162009000186404c0000b40c2031045c00d520091a45031100122001c141c41000c41041c8000c000f00e00e0b01005849060039039403078100d10321544066040d5600810810400c444043c4000d0501a0394030285080c0180440080704c1c00840a510170b001c0e00c4880c00207403050140a1416034555a050348403210340010281c406203900d01003041d03905d0140038a01250b5502c48999200300b4010307440e4201c2d141d03464003600c5c0c501038980b4103180c0c480104484048005a40240318 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 229932365 1250 229931115 229931147
    0x3031b0d02042402031e0d0b060304080c0724030c2606040c03020c030f07020301020903030c061501080106020606150d091b090b2d041803020d03060b0a032703 70
    0xb400c0754001c1c3c0242c1e0759100300d81c00d1a040924601185180c0340d41100100301804402c0d1001c64400d008070003261098001351000c07980c3d00340108018080c0c0000704203000080c1208a42c07200c0c1111910a044400c1c20f9148050080648800504009030f004a074210180084403040c0315401d0040c24030001400c0c0259285446a8100f159201d1071610a00a80750031480c410083c501c0d02c4c480403003005650f0700c0341c8000c0f078041d5002e002c00d1141e96402d00281884801d2a0060301c25850100511003107051040d1065041c0b00c3c500005100148e80003c10641c0000203030307854205401840500036060082c1d030210002142486201d81c10080d50656492180c052030106a01300d6454030301400590b8003400000340c001e002d895210b662480c0300c0a44855500e0311141e41c1030000d0602d404030b42a80c801c014204410b000381440b4070101503042000304446025440c04004c50760401c4034040691046141d00310406403200000194520b0078140c545100347d04140d010a6100c403407070302400252110303840344 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 229933615 1250 229932365 229932419
    0x12080a0f0305061c0614040b010806011a0703030b0315070504050f04090503090d0f050115230102070626150a060302040803030c030a0b28050d0503031b0d0204 70
    0x21600502a010b01e40c080c0300b00514441d01011034500c4901403440d004003e861890f101c0209013150310010780c03102d000f1030052803c0a025030500c040c0c1c9207002010790020000d903250504c0300c60000100b1040d9116582d0500d00810480c0000d00000e2803e030501c800d084184980300705014840b6003040c005d000316982036406d001214200c07410001190038800015013030360010000f03868146080494600c2d0184508240f0886900340e80b101d50840341e039030b085501000c82018051200c200c10b00c4224002c4500c42000001e510701143c0004d441d100709128040070b0000c5400c04a01404100c070200c04c03800d0340c4200b0354102e46403c0350143c040318100d2440f1400781c5c0c0103140c0411014440c0c0219000c2d0341c00d0390021851350b01d664000c01c1e110ba00c028a0200c90700e9030382d0100b194aa460344c0340d02320418202401000303110b040003100010221654085481415290f02100010781c0210079203034000e41441035104c84040301042905e151240d104102c0350503100250110b0343c010100c0d2000441c1e2007040307543e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 229934865 1250 229933615 229933637
    0x9120201020c0705011b03030510031b030b0c0717090102100213170609190c1e170d02070302040b061e0a020105010f121401060906090603020f0409081204050712080a 73
    0x46d41c0081c0180c10b0600301d41e803003041460100c1d0180c2c201680210400018003113456594641e45842504561400c0d070400c00382c4800c00c14041400c1c1c0c216048240400201e103800711581d00c10080100ca40c10300c1c003141c0303404144a40560f00070b03c4a4043c003000d050b0f09565804848450400050301030040c200340d2142281d0090081c1c900190461182c2141c400400191010409002c03469041900032640004010300204202c48902101c44164002a5802c2c3c882400c0102c106c02007016294004110340c172551a048400b075001810304c0407290199070000700ca04850020030014460020540c11400c0004030b29500d5241200040c119011305900070099070b41c13900f60781031104002c0d21444c05d00042200b120400328038880000624161000d000140c890342d506084801c1daa000d61181c01402e40d1000c0400030350920300300240d80311034216810440f05019542c2d55017a40150032640f611030401e00d00003010488100150f402070900b403d03000d441c10001e80340c2407100c0c1d80601550300003d030600d010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 229936115 1250 229934865 229934867
    0x406030602030901060b36060a03050601030c11030405040504060e190308100509040803090a06060b090411360418030215010302060406030906061203050c160e0609040609120201020c070501 83
    0x15903207104107400501090100915440e9140440c5201f41100b80814500445d40e9944410081c07444880301d403008101440d040f8009022114640c5104003807141d03001e000c04040102000316070686800f2140022151a0b5050120007000c03034000d940101d02c1144c164401c0c81c9600401e07140100c0c401c3e91480416541c44c0544810b640c0300e40315042d00306038075078085000517002001131540040510b0440e0b100aa05480301e03400d692059021700606080004c0d960101d05081c05030349070b60880c8070009480e1208188242c2440c007017000030540e0751116200c00004450114403d100c06503401013050200b03040c550040030810185000c00c5025110b81030110f1168058008506e0403a42c0080c140c41c00c140c903000d42580038050b0802c0480d08207517598030201d0100200c02c1c09080050090783c82c5603c420100b12418030305502c10880501006e1041c00800c40d02401141055100505407051029a1141d2500304041c1000d914000c08404640084844959055010f00fa21002c80310484e51140d5460300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 229937365 1250 229936115 229936117
    0x3060703110a0e03030702090a1e060e07030b03030d020c03030a180209061201060f030b040c08060c0301090b040b100c0c060306080a02091b04060504061403160c02010207050406030602030901060b 86
    0xc40c030010007030034411154410b00030700c400b22079000d01070300f074a2801d942d0750f001a2042d08212054a69942d40341c82c2107180802c0314800c0411001480d03010001d5900300307100341d515144003d003030204164071803800101c107032001d0056030052020306000351745501021402ca0b0f240e40040390760102c0d07285000c01001082c1540c3c4130b48600c083c2c002e06490401c0d01d4003410b00984855260b113941e515901e400d070000c0c0041740300802d40000c5006410002d142e0405181c003141034842580044d05580c03102d018441100d003084200c0b4112002004002403000329280400c2c00f42c0614180c29074410302e520f940c4081142c000c0c09000c8818410070314458030b0b43e283c50f4190104c50142c0101c00c6e00ea8031421003000142403500f200c94110003009001040182c8004811b211076016421540025001180410036903810003640483ca0380940c4052303007140340c840003141c40040c0e00c01c0350000300301c0c03024043d07000d69000703001c904084c0c44003a00900c01d0303d8580c02e10a01a40c02681c0b802d60540c40d040700041e0f800f070004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 229938615 1250 229937365 229937381
    0x5010e0402040308030a0b0105090d0606030b0a0c140c12040602060618090a0b130c031202070e070f03020319020d0204170c0a05060c031c0b030c03060609180a1b0503060703 76
    0x11001130564a4402c6d001c0e0050010300c1c2c9881c18014200454420f036500d0722000c0154510450380460205d0852810003600600070b480441c0e020b0401d40041469608a100403040c0d04070310707072002d4a034208480ca0343d1825050300c4040c50384110000340440c0040e40400c10900c1001d0558100025071f40d4290b02145410080b1201000c90300107514403000100740100352908001004049242c244c05a180c04400c078005074401c4400c10b0101400c8102150144a10700082c0b421000050072843d1103280a002d041c1200c001d1800c140d400800186800000741c02100400d00180b411501c1c0c81007041700303200940c4a4003900300ba03448039108941c04e01100055004040102901c1504820314150a201d4a9007040b0744d083c24a000500031002500068901681d510b28014008140034001c0c40c103040c201303082c11511070f000e60030000420006e0745841c0c8490317401c05100401d0f42c1c420940110000e080584950b8020103580f044521600120090706100003a11011000c0d0b42d410346803544158100c43c041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 229939865 1250 229938615 229938623
    0x120601080d0507030e030715090b0307050412020409050a03110f1c050a090e0708010306050606030421090308040b120f0103050a0f0c0512010f0608010221061c08030105010e04020403 80
    0x10340c0c541e40704940b255000e080c0c080c2c4a4103010103000600e800080c20400503030001c20300d20100741100146164858030b031000500c1c20302c001c2071440c1480c40c4000c00384c0c42680690741000030340e03510460444d2110f51000c1101504107040c0c0e04c0100d40703480c1c003c090704001070b40100248144403036040e00d0440414000400c05c070001c41410345441106050740c86810002d02c150601042140c00504480b44402d0544600895510380d459581145400812588064500c0740188418800c2200060b81800da030901800001d8041c2416103807400110780440254200628114010030300082c1408400003504440e141c9600b40641695480d50084012809200150039513000c083d012021400070402c480c9054000c111815405494001142103824140c410307400c90781d0745882c0492050340703e02c101c102070700000e0025894040c0040c1340022107034500600c1801614240c2c013081031959444100034a004100072507640303071035907030a049a880c0c100744605400b080e110700442d00145018802c44007a2940 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 229941115 1250 229939865 229939873
    0x20f01110a0e09070507140303070909020406020607110c1201050906090f0a140c04020c0c090a0b2101140903030103050c010c0b010620010618110c0d1b0609030e12060108 75
    0xb203000300500c070000604410107100040050001280c8600040100c1c0c04d43d010086640b400c21250050800c041c0f6072260302014410b00c024402140e0108000b6000000c51505803040740340b4087c0103040000f402d03521540483c580001c080034031019001588108001026100c1d20b43d2594461511102200c06010464101c0b00c009800961072019890000f4880e200b198002003500d0b010030100e03400311045100d61780c443c0c1c103942e0252130001c0340a540445003400c184658000d2074082010075500a05545140820b10003c2404140962007204a5071035018048110304000307020387e45039842800241c81c1ca000f007000d81a0194000d106d041c12459000c1c2c010706246e8030b06102140d50113454042040440081c415180488509024120140600d240700000307528030307448140d080720a050050b100c00380c01417108050a04000ca003800c540b008a0a0112181440340e0521028407104074000f032460b0710300342801c0c05241c1e000c820562108070549110f1610075001000542c0d4007824401d401140e80 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 229942365 1250 229941115 229941137
    0x30a11100201140c0d0f15091a09100509160503071d0901090c0906020a0510020a18090c030605030102070f030e010908060117071d07030b0d12020f01110a 68
    0x1002202148050380314400011108080e1901c0c3c50442000e0f03e0b240c210700c0021a03041c0080406200d04900000d4103035080000d0340c480154010100c0e41780c0f1420031603940d40d41e07045645111a4124042e080340003000403585181814011141021030300032140100341c1180000c1c1c80e81106c190039248401d044e11001d00f95a50311100f11110129006940c9000807009040031590700ca030034109000c0c01e1b050f00081500440c05000402000c11075110b0703000c65004119400c04283c0106002e20380185601025135100c418500903190300808200f107a0301c0b020310000c006a1403045034044a001c91065405000860341c4600b01030a038003030700501808000c01d00300c42a0000740a05032501c642d20044c142101c0250390b990680d410a00c09a222043c0c8160101c25114206400c1c0210300c06404c101c08d00d442c1008151980709030300c283c000c01a00605580b44801801c070341d6000c641c51040c40c1d1100300c2802089540c0e400940300e030181701c02c0040e190b0a0101ca03c02028180003a1a5402415640c0d010244 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 229943615 1250 229942365 229942369
    0xc0608070c020d1e120320070b0414030c0a0b0606040311090402042706060602060405030f0a0e10110129010e04020c15070e0904150b010e10020a060506030a11 70
    0x105410004c0300c009000c80161980e0351500d910000e4100e0040060304079402c2c14140150a60700035104101c0f01074910945140c420b00d00784250340310107400006c00d440990f2a0318104200c2c0321188060003140c4404510b003009000d00103400d00049104158009181e25128140070b45401607001c01000c034204242c9800c1241002402c6960160005201081c44420010921100150503414821412803880c17404140049802400c0080a403480101264a417039200c09480b8050b42e41510307400c401c00101d294823a8890350f00c0964900c001410340300d040990340000307401404641146241c6508240d8005082820b001510b208941c019079243c3c2e4504a00c001150130801034000c1c647d202d58207010000781200d00b08444050365a207080592540d061482d0060242004003940a2151981e038040100260501c41040e801d00100d01c80891345040e05401608e4010a021040303800640e802404228241d00165000d250780c0102c00070002a20b810090607121118164050320381003246000c04998 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 229944865 1250 229943615 229943629
    0xa0c0602070f0c0b1803060f0c1602100807030c11031b07030c080102121303020c0f0d06090b010f0605041518090510140f09040b0604020f0c010204030c0608070c02 72
    0x500c0b0300c90510b045a9140d44904512000390031a15a80728040303401e01440318400580c0105903030840042560345040c0440e403001b41c100a01e607114030718003c542150b68807520010070100c41d41c01401c007412080c451400801c030000032914039000070b0500c1e445030b003010301845030300d0074455009010b10b141c03444c98007031b51001c2115490302944d184148034000001ca00002c42d07501c0a820500000b41e5100111951340e29004c0b4080c201010405200c26414000798001840200035101611030345003a1002e04006030101c0c0d00e00c5006040345050140080401040040040c140c0c4c2d400d40006111580314901200d0601580c011142d0351160701c40d80c226441e00403201d411003001c480314208007040c2c48010142c10745500b44ca881c0007101030f13004c00b07000f000d002094000205a007503450b0b00c1002d0410000070418000500301a03c810b000754081440783e100d0b030f0116165188081601a990752980011a00030340c0f0078442a42c00340404d00010070034920030141240200541d96800c00c2c488a190200200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 229946115 1250 229944865 229944877
    0xe01020a030f170a06090c0807120902010c05011d06150a09020d1503050307060b0f090403030b040e030403030903050f0f0d030b06070c03060209010305090c1e040b0d0c0f0b0a0c0602 80
    0x34480b8004104071039264030b140c070300d03c9203034040b13400f003842031074086c10200313455100c40501d080c040c2010811201603488481c84031401e1206902040c86c031007500041c0d84420300b4480141c0075500304018041c84550401080d082c103400305040f61102e50f00c012900c011106a28981e56100328500c50400405c0380c1900584205c3c1140320000800f440b0421040c5882d0207540e0080380d55410224140302445001d22130300074081d03410b4032940314000407207001078200da2000b07000409165981030b030b40226444680c0b01819024020f411259119141e0802400e05c0c0b966200c1201c1d6482a40c000300c0f0062804070703107400e0580143e8010b010721450710509401a15200782d40d241c000e9010300540000c0390541d40104025401540010b0350365030104001010348800401851050703018903503003000c80d11aa0030701110042c010540c4088139a41c0800a00500a043c80d825400044400d4500500403500d1161044806406c010328245903a5404152030340640c0000f040071030078501040010510980003068 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 229947365 1250 229946115 229946117
    0x50f06010501051c0b0907120c0309030504051314090c03010e160302101206090e0613050619060308040f060f08010f060c140f03040f0b1e09190801020702100e01020a030f 75
    0x2c0d500703803000c011400b580422610000001c0448200c82500b5138070703100d5001300c071155180c01d202f1890582c402614920403131194074000e034000c1d80c800c1d039041c0880e0300030000b05c012043d142190782080c0d0b0310707280e41d4040c081d1250700c03039480c1c285043c0d03500d40000f0f2006a8000c60340782c0040c40c03501d1a004c20140c0406498040240704032503280040344942803044e040a03042201c0c0005090250f50521481c20900821900c80044c042c940c1501040000404560101240c40c002e4901c400e80318401000e003e450b4001814200080f8010a007120000c000030300780d0b24580e442c064640e140701c100300c1d19a8030078031540da244980350740c040c0702403841510000382c4a8041c209840c411110090341d0b511b00403500031001d036241c2010400f445107001070821103001b40740481c400b6003007030b964803040385410b5008195416034035070010711052180c0364400c540021082c58101221850b80d1081103a01035803018804078855010700441c40c0040e4000d01c2d050454520680c02071407a4001541e0a658004007a50040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 229948615 1250 229947365 229947371
    0x10603021c15020c0303040b07262a030103060b0d0c060f2006090708010e030d0e250e0f010e040303270c0906080f060412031404030804050f06010501051c 68
    0x80000b2014001010704101150007103035a8602410401000d9034090029130412001c0203401100046038080c003030b051051660340122503141d0091240d10040c404c150450605a480b146091101000001d141202c0c011042070000300c1d0b1240400c0001821010000c24140482c00b050148602c075401044030b226082c03e0070018954a603a401b044010784103e0a112980300c90104082d00f03405012403c020b000c000000d210a88040c6d5201c2e48a014140d003001e5966070703908410842407010024107086030700008015103250b10700c0415205541c5540515543c40411002051074070842c143d07540d04850340c0040030799181d280c0e99401c8000e40501c5840c00c64480314005102075840c084483c4220081c450240c2e5081646000045004e84003503500100d0150810144070b8400c038400300307001c1e03401a8003010f200c01c401c040040607002410045039445481d001d24cc00c0200b010340000c80303e0f0003140034404542204040c15861940c4070000d0142c00d000603018048a400d190018219044802e2b80c04004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 229949865 1250 229948615 229948643
    0xc02030d0209180c1306020c01020c010c08135f06190809150402010503090703050105100302131116020f0d030c140105060a060c0302031309020c0106050102010603021c 74
    0xc1d984001041d03815920404c40090840b2a8400b140501c6000b04824006000b804214000107174461400c84201414440c030382d0000c2d003c03c0203e0048070400c5010700b4a41c5042da460f0445c640e91841f0703442c0003608503448403203622020220901c6480d0001210900701c04403208014410804004640107040c002006001c0a803495131044040c0000801d0b06240c0600c0e420807020060942c10007500c0300d000c540104103000c5211310b481e0111b9030f005d40c0a08000f075a9445143d04d041c07a101031684090481c0d468041801005c410243c3e092003101d00031280b403004843d2070030014044604c3c032958a201407004000c801203000039070108850041c00141103c100070b0741540400c4c42000440811400614115003410420203d03500540740384400c84e000304568039118021407804003580c002e060500501108860400d4820030461301958045032060a402d55617216440294000c104142055420b145000c0b94651052160b00100c9070020703e4a0000101c8040c1c880c001000210161180078000c031300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 229951115 1250 229949865 229949899
    0x30b120a051b040e0307020d0807061a0f10091701020c03070b010611030f030403053414010b010c02060d150b0903010f020711280611010e010c02030d0209 68
    0xe091003401000a88024030b035004042c1500d450b039841040c495441c102ca07006031103000005541040e5410382d1043d198401d141081141c40c0a8088002d005504210340c94004540100e80a46c4070700040d140700c6d603182010800c1003042220340e0718890004001050803c007500041d00440301800c0f01400051904000254940c2154010101640c2030011040104225580045641d2403101c00c0c202039030038584103013058100d17032202501c041d040200114010001941516050441c0d89000040d082e0f40200b8800652000300050f1041d01c054001500f401c010b0714041c00b0b04400703441e05964400c8119115420800aa04005000030810b941c8040c0c150105040303080e014042c0003802202c584400d41d503010142035078090b00c6090040d40c014451000000c0c415100303211002d1003150b0480b410f1880ca0981c191544015039414424a00c0400014019811020074100c0d00c40342c800070f014407048441018203070340004210301c005038070030040600100b001d070340900004000240303010901007603c90 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 229952365 1250 229951115 229951123
    0xf01050412032d050708030c0f03090f010e07060c170c03031003110a030309030b04050f120c0c030d050306150c1605040c08060a050d0203010b0418021e0a0303030b12 73
    0x141100410f50210340340d01c0702c20a00e084280c4481c411082c000b144499010000d1050140740720007840ca203400710110301c020800134240c2e01c02a0529041e15180c0c50040304180d1340e6444240c02201700d500c1c0a41c00d480045000c80c11000b0340f1925101c2c03602007d0b69586440c203000b40a518400d403800306016620092005100650062404400aa515908505001da807819031481c00e52f100303003058041000006d0704889c002c002c03280c01110703040340c0d9900c1d0b05180f424074940d659460214001c840c120800c400410300070300300c3e400906003203075203003000d51051585e540c450340c566070b020803003d00006040303140c112407014400e11203c00e81800c12200509040c41c0c28202c1c12401030084e002e200031b0000b0700701485115018040c03407a01c420765042000116240c01040e0003210300404c290f1400200b55142501f1046a440014008000350a1000c07050a85040c9030070342240700e18a4040c0c2111580c19149160b41e1141000740611829440d65400b50010a410008030b03070400e040d80303c41d95900030184 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 229953615 1250 229952365 229952399
    0x1b0d0903021509030403150905030c06010801020a09050603011a0c030408060702101a0916050c060f0f01080703050607050a0905060c0d090902160f0c03140a0201020d0c0506060f010504 81
    0xe0014501040c00368803010002c00000e280310200d80c4248020008640a50500d2840c000091400114442141800b60030b52040c2021f8061b6841604000554410158001d11454116548500000b500c943c20047c4502c003c0c85000c07908201803020556070704801004183c0404100201d030700c0c241d035031101341d401d0000c02c91f40040582c2141d4031441040440740110301c2c5000b400e031200c81c03c100d154000a5106180500002c19403100c0041443c1014055011201d81e42c4120702223900600e0190f1030311400c240111410324800689500010b00c05200151090039294848041c00e99130341da90b90125516004a4100d6003005442840081e250b154030004146d200740e000060402400036150240c40260a5070061171810300c1000315038007000c1403540c041c50f0158004043c108031011070500309a028141d8001615a0440d0b82e607028201500055041d042407007038003600d492583c0c0e003200b9900c0d031a195001904d6900504000303901c40ca080e140c1c0ca018007205050141c11f142e00e4201d500c484107480 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 229954865 1250 229953615 229953617
    0x10b03060d020d1101021e0616020f03160c0e0601020d05070c09060306090203010b0a140103021b01020310080f011a09040201120507030207141615030b0d0b0604231b0d0903 76
    0x49004c001055905112040551607240d40c641c140280d5200f80c5541c07904000c00d200345030403581414040380c1e4030034415168800b01b50313421280c589444070151217100500c44c404541c2c8001c14840000e10508015a45108200c1600075006866401406554942c080081281d081040c1c03000420441401e00c00c0202940c00350400107000905032042c10b00312000c00350a503200301d402c40010884614404400d110019082c0b03000b50f2120327007021040340c038a020082d2640349540040200191040c0d2407400c00308640807d01242d01c4050b62040d038508030340c8001c15240c132541541e05503c20030b09100c1c540641252041c540f00d07030800070b69038107c0c046030b800366140b40000740c0000b4040300384070381c00308510818004200502201c910200250070b4000384ca21440b40301906806400740c035903000750f010525644000c0c10391166030300103180400c1031030070481d0001c3c230131071034442d9044001014801c0b10340985c924501440341e94480c0d1101d407003108240709a01660755020400e40c0c02044413405100003c5110b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 229956115 1250 229954865 229954883
    0x303070801030b060405190b03070e070807020d0516020d050f12040914010e060d14030309030a1413060305062206060306060f020303150604120b0703050709060503010b03060d020d 79
    0x1149020803c690020780307881c1c403660610091054900900d10101c510b55400a400a5148005800b0909121250b8000c2680496040070054010b8000e10b13881d100310b01c0c43c0e00340c42d41c0410040d0181c695008000101d1700014210b5a01001400d0400070040054000d01c02c4840b090b8002401c5850f02e610b010b403501c03004502003820480301c040c50060350424503240c50385181030f40c100044e022880a005041d2407203112032030050001d00c906a002444140c103298141d81c0e6034a4003090301a60f03540b00b00940000240003002c0c080b0028a01e40589000300580403078000351500d881070403000703004040d005c10740c01146c03070360540c02c1c03006000310803100c1c84800c14000c01d40c5440c0c50000707800c607105a800b6400f800032000f04800e010390301204a81d80702440e0303901d25185481c0c00300801e10a0040b07070040b4104c00031030181c040603c1901045c8a200341c3e10759409100f155a20f440480351b0030540e20450300410f40510043c031406071a07401860b0300c0304020701440120041c64001500802d03400400742d800c0a5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 229957365 1250 229956115 229956119
    0x6030402010c2f0a06121109090717070e06270a090902040c05131e05090a02030a060501020c0d1103030c010c0906121b0e03010b040203010f06021608150403110303070801 75
    0x708019003c0e01d00c43c0c122007401450b45480400b81c02107400c0c07040c224051340d5604200c407110403400261035840f000500700d0301c160325140502408400c082c4100c1d240e10100c000001d4a414400ca400306884603018000303070b06004502841800050178251079041084142402c6401521510008001004155004924426980144001c94040135101c10400004000c008900981e8461a004842c0d684c0f520036055034000c0d03030844404080b500100d034441c1030b410600a1a80842d00950301a1480c0e030002c02c1080e43c4d50006a0351a00e5804866410030300150300000400d1401da00c0c402c3c41c0d940581600c1ca0124030b203100c0b6085a01c1501c0303040104104060034840e240d0710003020401000401c004100070b01c10001d622031400d051700449810080d00040c5d550494400f074000582411029100f55160b584847c0401c00b0031078140200001842011900d15001d00001ea1440485400a018142a0700f40048898444100900075814880340358205001208100002d40c4600720306e9645c0f80040d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 229958615 1250 229957365 229957433
    0x414060c120a0b010503012102100c060e0715121404030206040c080105040c031106120406020c1009150b0109080708060105010305092103191409010b030304031106030402010c 77
    0x100001c0c00c0c09184a107070522140c3c3e50798100c011a415620960703107484054903041d884c0603041904400c002d405c142c071001507820701e5030012207488140c1e12402c414072003070341d9540020740c1c2d0b40550701c03c500200242d0741060000900032483caa11031043c02001080d103035482c55020150076001d1310101d0040e1701c503c5c10481805841d054020140500c803000b4000d46c103003916010b8a00b8880d00001e08482c1d480c286000450b0745100891300140459000104c03a45024102403009401c102000074803070180c035507080305804891203040e04a9a004a001c0f00f40c0e00e411813004000c0002c4141075060002c01d00300861030410800540000b46040c4000303182d01e40c1020001001d0310f10281003122280e0000101d101000b001c03408400c804241d41000075200c0c1d554005a402d10007001500c040c200b0310700041403804080750f645562050070850003d00410b0b5031308081c0342c1d8a104038400a0719080300410aa5058900700000303603001401490400805181030700c520031035210800043e80710b1110004041184 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 229959865 1250 229958615 229958647
    0xc0307081005101802031008061311100c110303040308030a02030901062103120b1c0501060b0306030a0b04050307120809060603030a05180607120503010905010801060f09050414060c 80
    0x84842c200110490b03524200040e03604445400b41c500c04c0c0740d0003000207107603c00600c0007180181404000c0304c00710b0400090207210b00300800c4007512110806510341865041c81c200ca025410310b950303074240da0f101031915040c5000340180100e503414041040000003094228004e107000e02c400354001661390a082098608546007684944665840e40c5031345981e0003600c1c0034a00c070290705400c03c403145c0520440c03040003c101c5891f050b50b014031a4078041c99120000c40103088000d10800003040025203d400328112400111580d0740e1540c40503102000103405404030700d0b00a40708008aa0800a040c0d4854282000002505000074445001c00240b1441040201e0f0800b0b400d9010f50300d071810b00d440041c07a0348100b81100744d400381905400904c6845032012181c0070340d000b000b00b078004071048400602d20b501c02c0c4038410025083c00000714015006100d100101d503000c50400703404614041880d00640401002655203044d04950801300c00010f001441c81070400015640d42c0b01c030941061001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 229961115 1250 229959865 229959871
    0xc0301061e090b0d0618080a031a040509030a11150c0304030201050612061506040518010e0907060203090409020f040c200105040f141e0715030506030c01050c0c0307081005 76
    0x51410122900f0103074036125450481680c0100010400558a00100300d01400000f07000b010404002016290039034581c2c400380b020311180c1c4080c4c0400e1000e82c108001d03102c7c20384081805030010080b00a21074010164028000720400c1a294a03c020400c1c07404520021291031048020000070001010350a100c0c036940480115100000c26013090291561014020144020180540030421059071048140d9000b403500810402c4010500c011500c4103c00038400d400c034061003180030482030600425007206803090350703008505144101c0304002c0a081060000e0360020507041c008440341c1c845000d0305040c110103440e54104c08000d9048414120440a012803803649404180f00000700d00c61480030000b5040324040c800b220b00da04a181c10b1010340e0a02d0201140130240b0002818400304d13407501181c200d0680d5040b41046410194161201119aa541504401c85001e0300358040d40c0504a00301940041395007803140c0d540030034a410540d410654066101c8a00e8404420140c094564 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 229962365 1250 229961115 229961129
    0x1a130906120614070e060a050405090405010c0e030d0f0305060a051809120c0303041103120408060106020d090605030a0906150303021b0d020120030702180708010e06030d110c0301061e 81
    0x2c203032034140c00052040ca030f81e05c0000e11071200001d5624496114605580103400020180e8405082914140d0700070300e80c20110f01d001c294425101c12541c07070082481081d410303194668000360308050504030003c102c010030340ca070311086840000c40c183d1100c0c0d1010307030744020101400016040030f049841c170340240c001c82000004820000304034680c8021080c0d94001d54080c201c041040140800613060424050520710501400700700019031140005085040310302c0740e000d5503000b01e804035045808a4041c06540040f91040000c545402115802020100d020f441d0028403607106403440c0c5011416684281c00592140841c2c046c1c1c6010300079903204050f4100c1303607424100c001c0e50020b01804c403d41164070101c20309451540310918144111031040d6401001d03030350240740e0005201081442900ca450000c3c6010300040b40b000f94502019000d25002001800c2c5440365075001c03220b0030300d41c03800c00d0380c1d0740103201124a0540b024017406015080e40005c142040035259291a0b1015031940491 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 229963615 1250 229962365 229962401
    0xf0b070e0a050303070209130602191e08011502070510030f050c071101080a0e0a0b040b160e190b40060c0204022803151a1309061206 59
    0x10840d0343c004222056030b64159601060b507950810301c40b2a2106903d80507100c203000060006503442e000141c1600300c0c12a8603455090580060480a41c0d8804010700022038040310040c0180c160700c00c41040b0300c45d954030459004980340d0011030003401301110024080794403052410b100380007a00031241c0c0989002d10313581c10070b0103070348610b0103030703030712100414103001c0101c001c52400141500608003504008003200d00070069403801d4001501c0840b800c0e610114288042011211020001240e5807101e03510803030500214800c0119108040e600480314600055000072000b003014090003080132a00301c0c0c4030050800380a1808501c05101100b13030703942c00e00a0712000400c10002d181041c0c906a00d0146044070503480460000e1003038024800503100861500e642c01e0310b8480148090351511b030341c00e1000d0300f000d112070a44802d0700d00812580c001c003c25400e0f544000000509010022403a8030800540d43e02d011303500715005a00103a09a03e5540300c500c0a10416000e02040056924001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 229964865 1250 229963615 229963619
    0xe100203070c1712040308090a050906030715030213080f07120305030c0f070602120a0f0204080c06130e101d25110d08150a0e070c030207030f0b070e0a 67
    0x418424198002c054180603480e541c9010000208130144c407603c40d03280c0380c569441d120b040880c407c0e008016024440c00040d400490309040c419820f40c0070360b0014004001841c18078a41c402410600381080301059428000d140104030780408540041000401503c4d00c6000ba000302420122682c2040766000c88400c003000010b0703131060440750710011034a2050745901034550000c0040c450b080d8060305003800410244403d0540d044464000e070009041004030080d000109000d03800fc1d0302c80c451140d0131461640c40103013000e0008107001c904881550f003400c2c1e01c58401c454422001e40b0120b401404040090080e558486807200c4a1aa912420007062400703601181d43c0342d6030944c03080007102034590582400c0d1300030f4800414450311035041d101d201d201d512008184200480d051150358881c0054140309081005116058900200185c18581d0307540c0029150802016012800c41c07140b40c3d80000800c41d039040d4100e2141c49503080f41550b04044a006181c9105100c0e0076101b030000b04c0d01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 229966115 1250 229964865 229964873
    0x903070e070504060c020a0f03050d0210060609050d0f06050408070b060d0215090a091a0301200306220911131413060605030123070801061d0303190e10020307 70
    0x40d43d007214018a014080d40100c1c3c40480d926943c56803000c400903d207682d0201c1000004924003401003a181c2c01c4680c00c0e001010101c06071881880361801190102c101803101d0f00b40072103c0744010b401458588020f010a96a1404442086500781e800307c00100c0d080d02003102c82440d4540025084038084011201600059082c0c1c112841c00f99000ba000285015162292116000200b8545004001008032401038445100441a0291182d4a410300d030030500001920342168241081d00d5407803c5550340c8050040c041c48031412030300075180700a0627003050070840c051109203510a01e503166485441e48207202d41080742c0e0810052490030140c108450f4003200d40c0c056800152001c00c50308501c15801c0900042c41c06421554140d402d01c42404020726a5041e003101c100ca124107107800c2992030305022070b01d080c028015000001c3c4644000040780082d045242d0f4411b40040035603140080365440030310350041484a40d0040b40070000040a01d2406080c0d408250070075001843c503106456903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 229967365 1250 229966115 229966117
    0x60305070f150e03100903110c04110307030504050a0f030c02121f020a0c020a030b0105090c0309060109090303060504090303050f10180504141f0501050d050a03030e0316080903070e0705 82
    0x5182c4100036005802c0081030342c0801c00d07010150000c8034100050007003800c0062481c6040540303246144140024401a41044d1161201180c0c1e01d210f544e06644070501c1c114041d201c0504103558511642c403044d804510102525043c00e8800e40740c05d16001030301d2040c17100d0701c0380040035490250030a03581040748490000142489007602031006966910740c45040d00c1c7c400800d0310103500040c0ba0140070003008009200503050700c0c0e007140d03552010356818400f00e40383d20044800c0c40094104200403c00285a40c2052075154843c1c01d001c01c5a64031800800e0442d03901340c0d4258000313620361050040c4c0114078800c1d2030b04a140080c50600c400c1c144018030040c01d810700c8103c805070741c0e1040098144120000c543e949c10043c40107a504a59051600024a140d0000e41041c00361a06000080034030708000c864501981c03020160a5480070b0f52002c0d0000d103051060840c09010400c24030b100d400390364040d1a188c502c00e80b00c05071240c0c00034040c103143c03540503041202e8901060f01400715180d0410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 229968615 1250 229967365 229967399
    0x50a1512020d140f03030603010f061d070215071809020309031e0708030108030705070503010b130e0705090106200601031a0705090303030c03160804080a03020a020a15060305070f 79
    0x1480442ca0b0101d585032803001500c4402d03110a4601615904011414001c00110300441c0124001e112401e1107401c05400c551061180c1400100c8005800c5403c582c501c2c02c980d0f0018580c01903800b10302c40c03080071200c8940308581d090001100c5100640b424151401c010000e804194003c5056261a44d4046d0781c9115282104080034400100c20300d0f282c85110440701100c1d4050100c075102e5035210b030860368070f030060101201d40b40908400880c5500301441441000c0070010170b40800d00d601000103000a06200030716407024010182c02052a071582c8103c540200301ca541c41e05040000c5c80c4144180c00d10240c0b0880060b04030100400106148c032500c03840c0d0110009880c20552201381c400c0d41c42d4400d800d0125050300001c0300300400000c2c20805180308425800090141c00d178201d4080b2144c2c5412a40144000c80c14003148080d28865400f91088161900480f203c010740c6440d2040210320000c00266596210403041c030401805200940c020301c1141503042c46141880c0500840d84030031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 229969865 1250 229968615 229968619
    0x1f0225030f021f021e040b030106080a36020301060e060a060212030601050a051201030c051002010c0f0e0415030606090605060f2b0911010807020a23071503050a151202 74
    0x801d6000e241400c00203142c90105d846285540d40b55901c402e002c3d011741092060101160a0000003031100c09035010705003441018400c0c0e6001e100c0d0300a54a8036140c2d0407c5200c106038005000c500050f2000d10a500181c0002400c02c90245001f008000e41c0c40307241c1c1c01a00854100309034040a019045041d241c105800342055a100c04000c0340c11102d6018113807200845200c40d0b0000000c1c4408400c902c02503910545800e0f01101e84403130b00b239080c0c2d004c821aa600050000e0305941c1c50b80e00c21500c40a60000040021a9800c80d60b0500700c0101c43c260025140300d42c1d101820440841c45115240041c202036450504007014420151841c0c051401070744164400c58105085488158020004912001d00d080104901c01d00740485150340400e2002e0108000c0c001003004a4000101c0b840e185900000c9c100b07129a02c18113540d2070303c94145982005101d03c24010481c070707082c841113941c40900daa0b000510b901e0314101d414140c910360f400704540095051002d020701410040c0030f601980d01 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 229971115 1250 229969865 229969867
    0x605100f08150301240602070e06090f04060e0109060212010501110703030809030f040612050901200c070803120702010506060f04090b010e041a03070b0c1f0225030f021f02 76
    0x30b62404680035010000004065100e007450f55225468000d540b0415510607500301e07007840d51a00300400c081403042d10b8803548001d103100000c035854441c079100b0b40c0c4544a11070120702008030030002803c1d501212030444030b0340e4000c102001599010301c040d5004013001d00c6c1544901000b40961501d0346007900001e002c00809400291200e42c0c200200e6241620220341a0782d210b5807100d005083e80d402e9001d81c01c209040c08080b903c004014000c01c09168501202c003003c07506450040203207130b404034441e800e413030041210003d101002403014000b00c460744c00d035004503442c10322002421242e0081a091054105101d1282040b120400b610140c50f0540e00008426211a00507952800c1c5030542c0f0307131310906001c8815003440f21540303840e0490300b09070211064130391281028290f50041c1000c0c000181c0c080011a17443c1406540d9140c049200000014030340f1203040103a11aa5503061443d501440500890204240e801031003c1070800540c80541500f0841c00925003030700185885441d046a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 229972365 1250 229971115 229971151
    0x727050f1302070f0f06050f0f0105060d090203011a10020303071707170702010e01140c07111804210804020108180708030316020c01050c030d0504170304060605100f08 74
    0x109a0460707041607001484c80d00c500003681380400c3d0300000c020080300e81508003030220781e00b410500100d5008100c4000d618405a08080905ca4503070001d58041318000c3c0c8415038400540c800784100f6021140410307060564210003814003180705165080d48046620410401c2000380d8401c2a1102d480d0850424035419101e809088071521920611540c1060404040c05800d41d015031014001c0d410352402400020011008682d00260403900040c00c1c080c1001103400181d0992100340c0003081c024260031100010801c5281c020108407000c50f1002c440039440d014045051840303940b46072440c03801e17030180e00d01030380001d01204020300400022005d4041001035008140000406801e2010440391a8a03040c8040408040d0000c402005401485400600c07940300750704842c02c00c500c0400075480c02049108a0004240c010300036150b5101c417486005003030700700000071405a070042c0e00100d1000e0515041200da0301c0754000c408244071488199000389900b0140d15a4170000809491903418 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 229973615 1250 229972365 229972399
    0x130501080c04090f0b03060717010b03041a010605040f090c0c020409080d0e0c090702060112030e1f033608032d1006032003060d0b0727050f 62
    0x100030350f08a0b440343da0401c104950001ca0640c00818090000c90444a290300c0c1c00c4015200c0c1c4032280c80107060207281800601440301040001d5800031700c9880003031a91000401c52468000c02a08030100040000900b041401c1400c1800001380200030410007510340e10807805044c0502543c4c00030b0040e80c45106400034405820250380c101d20b8642d9003130015104500116440d91508408a4411220440403900c5180b0010b44d45042c0d43c40c03086000711840d050707141919202401c100840c0d00a20030b4a646400105050b00010405001d450200f240100840341452a1201c021100001c20035161090401d40001c0d200d6003840ba0481c01091740c07525035139821035241d100d4955420140d42c0d2145e01500d1025620101d51080b60400c2c46500b410b502c88008509480c0e0b1140f01000704204140035041081880380110380008005180441c0c0000300c1e40c4580c03004008903801004101080396003030f0100644810f0002d20f151000814603000d04020001e5006004038200900421003d011449a5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 229974865 1250 229973615 229973617
    0xa11031503160b1b030408190606031b0303080a09081b0a080316022e0b0111011104050f03240717150103140f040b19050a0e070b130501080c 62
    0x105246810206485403509101110344e4458a9100c910003100d82200342c426402006840030340710303584054401d80b8404800c010840d00c00700c074191502c03541c400c070020020300b8940a03034200e07840b030310040142e55255081c098070310381000b84000c2402d402c01224100043c40316040700c018813045590074000b501f0000210749440301200e0010100d820000c107000c10958007801d0075803060150360895402004412960a0001441c071095a003c104031003049a4070754150010300402c2018907000d200c800c0c0340c004290964003e0a41501e00c5a0001070511140c28254030940000f00298004e089159a104591126032040004564200d44081c0072540140c0700301255104030307142e0801c01d0030358142280c403048200014100b041c003180c81c00034290401c9400014180c818414044501c900d59542e03183c0909840d001040c1080d0007980202010261004d403007444e0040048507000101e0390f260013140343c0b50103050740000084010600880103028200c00038041560400c1c0380c0000300f501c4441c0c00c1013032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 229976115 1250 229974865 229974883
    0x90b04120203040807142b0204050c0702030a0b0103120507020102150601090302030d03020a0305070c02090402010f020f07120c0608010b042304050403020606040b04050106020d050304080706060303170a11031503 93
    0xc1400750301c5d030000300800c034450500c041e0f4004590000019107104c01001d041640b4007400783c41020a001d2181c0507290582c0b01c01d0340010703800c5642c0d244c044140c3c0004d0400d1031008007100c0800034440184140881c194101c46e00f0091810401c3c5804050b8001030340d1a5210b080c4508084002000146164402c02000c001158082c040ba0300c04d0141e89000b130040d4025a0303040c1d0010340b8090000303000d14407a916076401c25802034410a401e481d075800441e07141c0151703050365055202d8080140650103041007500014069214050801301c42843d0580c50754403030340e01030020032004c000140318000200040302c0131600c885c18021812403031510000076060540001f160b0284c81c0208000505802140846c4600d008960401120728409c1c1044210741c020b0041e000180c0c8114050003c09000764000c40e086030064003c0c505050841e541d138010703a421900110000703040c0928100150716008400303034100c5280d01050041d038001c0300c2c01482d2400010a10200c5400000c0c0e01010b42d2024400802c1c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 229977365 1250 229976115 229976129
    0x120203060415031a0603010501060c03050919091d0a02031c020c0303070303020d150f120309030c06030e0f07030b0f040f0506010906050f09090307020105071e0308040b010504090b0412020304 84
    0x2160581d43e06110284080034940c011030900b9a10018845c2d14040c890f4038103071001500c072021000b41503101220240c1100004680101881c841c10380071003101150000244021039022540718203018201c0703c2402c12070702540d01c41e400f1400c000d0040e0344c04200001d204403040340c4000400003081e000c03440c204400005581500000580c90285039060300100081b0200b420240400c2022030400c0300c0c50011442081350701400d00100f0b11402e9140038540003458000d1a00310620b81c1c0701e4032142d4240c14241d0003003000c01d99403000406600c2050019481505010001c1c00000c0d1860b00c5181d0400001000c03464140340c25000a810404081c41180c010354000017107408968580e00a030006000501030a4030a0101e542e03c90385c5032410782c10440c0708040001c05113003440d0380d5070700556081d0400b0404a42c202540114800000e2283c0e16004000d40607980d5440c05081a09184040081c180c1006010344e003007a8885000c00d90b500015504158060300d55627030500d901c80d00302d04500554100d90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 229978615 1250 229977365 229977401
    0x190507050f130504110304050d050a050c12070204060b0c060601030903030e010c0903030e0402280905220531060f0905070f1d0705090109030b07080907090b011202030604 75
    0x212901c00c0c650040c03401d85500742d501700319044003810072114502080760003c0541c0e1040c42039030942c0c5d102d034021f41090031650402504281000c1c07501400e007a02c1c4612005c1d50a804201c0c0c00540ca010300400006107041c10302a031808141001d243e854050081655050540342d601003020140300b80d100c4009007948500800912180c144c00811200351440282d0028402d1048401b45160610840d01e4000040280c140b2008540b44010040a03000c0c5401c01070241c22500010607031603803030403101d0001c0c0000009540040116016089860181280003a030710402e200ea115203034020104040340744d5040d1040200c001c03503d0004082c1008841891500c0e080c90380c00d4040040018a1314286c3e5803c0321440000c40c4c5607a80007503003039500c0000030504040240070590b00c034050001002404410324103494000c1e100c0d19a0000d011041d940b100c00100914200440040d06019441c080c0c046000181300422141c000200101290340c02d511070540d002000c1023203681d855000e850380c0f0740016616 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 229979865 1250 229978615 229978627
    0x120e07050d1101020d0f050405040e0307060509070806070212031f0b0d06090b090702070b1e120108011a2b05010c0f0917120f0d0f0b030d0305190507050f 68
    0x280070b110740e12000140c05840394078a00c00089000384051803401c20f40d84c0c1c0f45414249400100070182c0044468091075000421410003c65054025244280060710003429010320703200c1c2ca20300d8488020300784801c540262440b02c3d0040754440449800039a2840c0c081c04250700666241c0c18000b499102d00134000e00016404070410b00f680240080300d1000340204020031034402840896001120001c0c010b80001e1400e11000b10b03030b4000303000111290820002010b24003030034803100b40c0c07080907103030360301960480104002d990901411550051400d01d00355440050710104090840741017030288006040301d0040d505a00081680c61640e401800034880e07501500400381c01a071166078503900203130151101190094038101801e242c0c0c0c1c0d2035001080c604d0254110800350f078100c7c641c18200810100254a02e242c080d000702e02d4032400320000003032710000340001c140c076000d41030400109140c1080200f00c1404036450708860811504013000c2410382d9250004c4030507108a038000d500b0814081384e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 229981115 1250 229979865 229979873
    0x906200f010c030c031b030c021f05100503160902031e01030c03031403040f06020d0209030d080109051b030a020a05040302130204030501060b070f030f180806090c040903120e07050d 80
    0x1c030300d40c0c0c080b4949041080101500089050341d850710702101403100706102c4849494801e50105202014900c1910034504102481e40c11200c2c055500310032041d150030500283d207162f80c3c182001420210000c000245a2000ca40001240c40c45289040c0c0c5e40440041c100d107040c25500203506115240c0003586603140c0c50304011010b4140410b5000801c4407107540300b0310341c01500f124041c80c0c001401920728a82aa0b03840c0c060743c00074034190b020310740038806c0d4400c6880810081010286540b501c0400b50f0410f003d400445500030141100c84c0c1c00d58501ca44420413007402c8a40060124002503602c910901e03050365039218582c4001d4002c0c280d0070340400f43c55801e50151055030f00c01c5000307000541d0b0312061038900d03020307041007e8104908001c0d031400180c041e41c444040350800b0b040810400a0003000740c0324000300c641c88904980c00100800c51954802d0291746070340380d0101d0f8104164200d94400800c00e000c28905403810b981ea4200c00340b4005010403610700100f00081c2000240c280c0c91034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 229982365 1250 229981115 229981121
    0xa0f060302041e050603011509090207050307050c0603130b1b0f1b060c0f0d0e1c0e030d0f0804060e0a030f0f020c06030a020904110f1b0606010906200f01 68
    0x2003210000e01048205018003c801c03050181282c40040030207046900704110104550030b100c0183d03040c0040aa80022041c68900207000f5560140c6c001c1c5448400d50700b8018240b10401500e140700318010820803110300d07114a4602d07030b02c542000180744686c2d100070460340c00f203c00102203e0703040340c08540c0000d05002c000060500010560a01c0b41d445064150a6a43e54050381e900711091070510440031440110b502034822080840c001203040d500406a4908100325a001d0007408000b51740f400c00515000342c0c203c840c0c410194010504880a550020646100c0f0f021010030003641e40049424044140c00c04100e085202003507038500c00903840c002e8046050303000508041003e40a81d048040d0000c140981040d0010305646d01d1580c17040c0701003000790b00c015405507101c0d0b9124030b551321082036070020345610115108000e0ba5160070322145010301c2d1590446551a911900c01c000d06030364000901006c59844d030520103105140541c8440c1d800103e41c04001842c410708070f0740c2c103144078150 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 229983615 1250 229982365 229982369
    0x812161a090f030a05040b030402031906200c0606100207091407080f15040c020102070501060e010e010b030408160c050303070302010f11040f030209040303090215031611100b0a0f06030204 83
    0x1202c1d00014003007070080d103034010740c401c0d04041007043c0400c01144d6192001542d0052000341a2070f406003d01a803114115418041901d004d40d4885041300e101c2c0301c1c0600309212a00042d00241440d100d20b656558401005000c03c2c0105610350b40440300c01d000700b00c0d500143c0f0031035409100b0390701088a0b84026400c110340800000c0d0340ba201060780c1d00040c1070014000c01d0b901812100b081009030a02c0050700d9507401e000110344d82000b108010400c28801c007400341200c0c021940041d4502a851500e41006030090386054408100340f00015038100d0441d511800d6424548201d806d46040c20b170244011640b0a64150000040150030582d0640c8010107810800904000302002d0340c0c0701d03806500803802101c50500c0d16400a10140ca46000d506a0140c4649004240b110050340840c00e854494100d18501800100038003542d0345207149441c003000101e04e0156070342d010081c0d00c20b03901c41030200c1d1011030640e074921003031584e1105002040600b16017120310068a6440900800942c480c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 229984865 1250 229983615 229983631
    0x302011b0801060f0f11030c0a05011d0601092003070309020a08120a0503150d050f060609151309080a0203071a010303140a03061203030c1205010812161a 68
    0x11503019103018001c01100d81a02c00d942d0b104c50041c0c021100c2174030b020300010006030900004085c01815075000f00300030b0807013034018005014511000e01e095429614041c840c41e078801d2201800101210340014000e0460380100f00c04503182414071302101d05121024140e141103040001040519901904504007042c400d54014500700d95a00c092070703d03440b8110300c0402030081048004e81e11881080603540001c030142501d07000f0ba4403a00018140d0720040c40880b51508002500c010b048000e00119900001c2600e08071039a19081d0300001d041456010b41911410740d4074070b44070000b61681c1c00141c5103039001158959410310048041e50f25001404102e0b04400c800588a0540d04400c0326141200c0e41521085040c049601400c40e154000729005401c05076205000188000c02d11281c8140902175200041c150201840040800c070094211038049800c00c0c0040100c8540011665100c2c0c9142108a840f0f0110a5001000c6c4151040140c04a074506a040380f041508241d054002d5000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 229986115 1250 229984865 229984901
    0x9120803150414060409020402040801090c05100305070e011b0b010b131205150702160e16030504020d02010302093d0f02030306010c0f08030a0606020d09080307060f021204030201 79
    0x1c990030802030b524440d50024109004a011070010304294002e0901107100402c09410301d500d03410441d00b101e02014094501c040084003c0010341401100e260004806103420300070352516040181c0740d4042c480c280340c100a41d240400c240c101d41c012070900038a502440014495035a200c9034219904039540a5071050240303400081c1038060000d446016940c084003420314004600041040018000d2a2000790b00500604a1403408618540009030900400c591440d003011107103030501102601c00941450701d000140400750b41c0314401454210313424a00503a9a44d000b10100384000c03020741001c0a103000d502c8060000303d0b00c00a240010640180741c2da658a030b0000d604944030400c1071595005600b042000c01d01d44d501c2003a050000b58080c0501145492041c0e444605980c000c88038100b240755600c02c00c0c0049a81801803000c10202461309915181c104040786407070303200c0d000c0018003456440320b241d508060150107590300030030000036151081c5450f0030042d0103060003400b18495508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 229987365 1250 229986115 229986151
    0x140d081c0e0d0206151807021b040b030a15061703040e09070f03060b041805030307090e09072102060a0809120304150e1005010906050a12050c060a09120803 69
    0x100c0010440c07000c1440368010000742c0c0368005c00c0016800c203000304a4019a0f00702e2030300007010981c903000c0e000d4000382e0b000b48240560803040030101888080f00e10701c07a505102103522a5500020003480803900b0401c1c0701460850404210010300c00c1d0340c003400310285c1c40540d0b01d000d10008801b91040714150000300f0000c0c0c1d180c8030b14686440b454003c880e0600040c20702031000c203216034411000d0940146c00010340780703034189502101101f0154100c0d18ad900020801903619401541203004022034041070405060010318941c0710f003600d00511940491003840495158401c000d00003001d6000380c10240c1d1000c00c0c1000411403a022688091984564800c118a4402400417a441a034002408040280d040707100a03010303084d0b4103900355081c1b003808060601d07241188500340c024003110000003280da00d00300034000456550703032100c080c042c0f140300813034007045001c0f554241607042111840d64941405078140c0e540c9003203402503c981651080d149080101160040d800b401040036807105d031030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 229988615 1250 229987365 229987391
    0x18081c020114010b0304030f0905360601140706090b130506090d090b03060301021201140f01020a020f0f03070e161d10050904020c0604060f14040c140d081c 69
    0x102e000c2c404c0e13450314442000041d010900c104d02440e00041d00345803078440682d5030000580454588024502080b02990030402803000780c800424850252440b001d2032803502e400060943c43c01c4d02070845611000284c40e00410540303034020b4025a60091040c191070400011040d80c11110705400c84849c456080071454444000405a4481250755115038405082100d8900f483c0c0000c0c1075542c040d034090000001018001c100603010306030322084000c0300d00c030540c1040a442c1e50f811000b41550085846c110151710340c03a508190169040d65094010303030242c1c5c0030030f1801d1441d520a03421180558207024104104283c86580b80c03209a0f0b5210b170040d5041041f5285442d4040d00d160700c00d908548804070382c0c0c02031020706050703d0001c0006080420040f107050030454210b9013100d40d940e0300c0307186030300d40e4216104210304d00021054041c0e4a04d030607a590044141c035070180301030852014503050602e503030340040d600703626610040d071179201c3e000f00c0452010a10240c00c1000e0f0f0a00340b21881d2101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 229989865 1250 229988615 229988651
    0x40f0b0c010e0604051f2d0c0c0215071e0b04060c09062c0a030308040b010b09031504051e161a0d110c01140403030b03030a0503010618081c0201 64
    0x7207401c0409085006d503419164600c96a09a07060b101d80383e1034a6084a03180528007100c40000b0300701602c01c00700960844900115120502140300784206088040b001d030f181c800086884000c52146c1683c0c4035424204200d400c000c24040c06800e454403074000c0108046144824000d600c00c82c818882440e2911090760310107800d009000000f0b56000c44407401900f550380d500b020140300f82c0d840b04100700850100d1059804c9401c260003084086050204101c02500c0603401002c2c40901130781403a86840000b034441c41c440c01c0120204440c80c3c081030600000b40a410314a072980004e44020920400440f03480d08104038100c00030100100e80010240c03810300058100b2260b0200c0203280c001c0c002c2c0410000e1110744441d6200c0c18042c4480111035609220f070b03540558407460103e0080c9058500203013660500b900d640d000c0c4e00f0a02c400c441854100f41540e054600c2401c048030091481520600c0d001e11503840207220344210b051501881420000c1082c850100340c4c0244211140c42e004100340c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 229991115 1250 229989865 229989871
    0x1203010302180403031d0703140601061e02160906060806030d230702090718060903020108040803060d061b0e041802100908031225080403080c040f0b0c010e06 70
    0x4190700d80c558220001100c1400b590044c402c1c1400514002d4601d990241e2100100c0117541a502202c018020b02c181e80100f44101c8000400621503503041040c002d0154540c0d003816600581400e42c281442030081c021010818030b00500484215a03480d41803024001520881022a0400300810b02505001c146582d6510440c1ca03248107540e0582c603034100f41503a6803060410f1100034009040143c0d5182c0a407405100913030384424040c4900e1004c0c43c0c0202c0b1650000c8203001c50820100010703604100f00a620941240b801500c03680c40001040c41c81c050301400400d01c40c079060080c000407104014001d0791070080e0b039401100108036401d00044031900f00c038859013140c5129039200149030110b035080904549161044601c1e41d103105075442d54021147d010204403c1e6001c102c0318030240c0c44040c010180510300c2c04171280b0444000b07000e03082d0260026040044010004110880e44022540280003100e02951450b5548000d50a550019404400c0e07d5082c40803a00d01540c1c00151340380 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 229992365 1250 229991115 229991119
    0x120506091302090907030f11040501050a0e011503020c0f0a050706180b03070302090a08070518070f03050604020f04090501030c0506042d1a030912160206090f1507051203010302 78
    0x1e00155035020001d042c0c2004000a03101c1c41000404030004d05884c0c2c0d49000c8a2148010000c0712000da8208402e0b124140c114502942c0d12110030441c80c00c2d50281c142c1141c08041c1400c032080c0849004401911802d130340340f4071138450168440c69407000098120441e80c01003040c2c40c5565151001212805245840c1c480b0300c580000c810b120894200c03004640006c410700300185400c5030100800d494040f1980800c1c2543c00504080000d4104058070b030100240c1058541030900d0416000b80041451002d00703010550f40f440010903a45070ba504a640c002ca14a240ca44c540ea41d854101000e0301013400103e410340c6841100007800c0c00d020302030ba016101112030780c3c00100d0084848064070140d81c0d0890342c2c0465440d000103440903070700014451303503001c40712050381e02c1c41c180c0c0700b542c9007038503201c5a4200e1106c02c004c4414408882240b510701c0c640c0c111840d07566252584002140c140c400d0400591100c0341c08002c80301500017400505400d0b02c540d0954a900c0303c0c001c0080303e580006d2001039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 229993615 1250 229992365 229992391
    0x71b15062315090a0b0307030606020105060109120c030501050108010b01110f06011e031203020421050712210203040f06110307080c011404061d0c0307060f050d0c12050609 76
    0x32200380740021816030b40030700c0d0716803540c1810742c440000340003c1441d80c041c9170300c10300020900c0841540740c01b0300005070405000034000d60401c807000804d0300c2c0891080810104c103100350b000c00c018035100b62a00640c3c000c402480721b56150708013140280200302200f400314188a00c0c0a5003000d02250340d014440f00f07175020348217a0b032900403d0300800c000d40703c0702c0a10481018021001503107002c60710400b108966001602c50b4100100300c038400c9120002d02c8200c20340e406420000034130000d9084151550021450852426464035a241c110307030700340c1c692241810501840d0380d164000058411030300c9048000a41c15541c8105480241d0340c5124a401604100822804116000028201c2b44506400040d884011020b0b4000480050f5001c40d00c0c2d41c1c4482e001a41204800320008250724424050880550390a000a80e280c003103200328000c0c401554110005c0701d002d8416649a020741000500110001c580010b1918890001c800704003131404010800078102004d13250300c90020602a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 229994865 1250 229993615 229993679
    0x504111c0203060a05070c2a120209010603020c03090a0905060906060304030914010909050f0a0e0304080703111c0305070605070e28080a03050405100f1403071b1506 73
    0x3950140c40020030306021b1003400c7d904000001c16002c000802c010302d0082e07800f220f04070340358800c0e481840c5034801144d28258440640141c1c1e5030305d050504440c007900703006a0380d1407030a6150b804c40c09484469a8000111074000500e031549402c094420402210940540d07611041048502d00007500c000d0006480f220041c00000d0003880540d4050b00141081c0139099540d8400409131002102e620441c441c00c0010f005c844183c030700800c0351204024010318140360030711303100550b641e0203884040c00b0240b11a440c1055929031710300905207038006076113207540c50100d810050300c00d03403010808581c0f5174a040c000990341407250314583d00b295001001e4620f201c2c0d46400320740261801c45040b940d050100440014911030030805210014030136112035807260b00d4001003280c03041e90fa0701608103200c2c03148c00d0441d40e9503000c00c0e100707020f1203044841c0d5103075190307040c08480044040b0002105a030b030041110003030003030340000c4040700f4500316070501c0201d40b2132001d400c40f0046401070745010581c13410a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 229996115 1250 229994865 229994881
    0x15010e040c031403040315020d0608030a121a19061404150c060609051f080304050a0e04080f030103230c0f060a11100c02120708120405100504111c020306 68
    0x4a0041c1d0070a00003102d0074941c1b40d4840300001540340706521003442c1e0002d100b0131403d4240c040d003402828410051420703d50702600141c00b000b0250303404240d050303035292100050103c90104130858074003d4040b80c80d4181404d0110b9648401d40607030b5003c40e0811400c03441015946080b034081d10544003841d461003212900a64503110400022540a521f40401040ca4807281c82003900c02d4591a00110100380741c100c5100b8029881d810001c1c0c40d404c01c204c148420b0302c030048103d0441d03c030306041c40c000f0769550800e01014007584c10340800720340d0000000000d102160703008098200c0b1060418200000d8850790070fa0707500001e20515007004880084131014074001c1f001e401c13414a103003030001d0740c0d980885055040c0906642421201d9030b950031080c2d4655410460610488804040a49009000e80350941e1501030440c3ca00b07460406880090204103080c803850034084403502e404d2055042c50303e000c10412a040c1c0c070441c000c01a0400c40c0140126225120300c010742c000e4050007040e124040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 229997365 1250 229996115 229996133
    0x12080403020109120e1503010e0106140c010515130203100302100c0b0f041202030301060903080a03090807030c1106040308030c0a09080f03030a05060d03170a0f020c15010e040c03 79
    0x82642035560f1110301c000420b181c0b03c0420b4031084c45950300d040301d41901e070401c01d4900e1013100c250490442440188072841502840d80d06407003103070405814101416404c9407440c42117800d8100c0a5080006020880e201034504602d1201c0481d900000b00c2c60300b00d5900202d000c2122000701c10a4100b4042000d410726032000035402409162100c008103803500c51140040c8c041c1c03112501d0050039030800044c020440a410b13198101071000d1031541d450500d00501c0600e6600001c0d219110001e41c0c64690741c029444001d06aa20110f40c40d140c030b040b42800780180301c00360030503142c5070350400000f507403494858100c5058940c089040b60454440d0032035070030300340c105508080c2801905c0b5008107a0810400840580c0109040110780c1ca1408a20b00001e442c00a46420b004001d18184040001d0304803115003e1507180342e014524a550b0300c000d08000e010b50203006c0411610010390780740110303000b1800405080340110600b2459a0342e80440484c00000c4401802c0f486c081003082c030000788900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 229998615 1250 229997365 229997371
    0x212070f0c0308060a08160905060f0306071b0b01090e070504020a05041404020c0f0307051005070903020603100e0108010212090a0f0f060605061305091005130c02010207060c0c020a121208 83
    0x500101003c0340c41b00a518680000902815041c50300d00400304000d07a0342d4010300b6844142a150030802c05111004681d48110207403a0400340030140854068102d003260b184090250000c1c43e41040e540d4402891004003c0b10600c003640d8000c41034085550b003000c0c02100d1001341a0740d52036241526010211240e510a910341036807090f001c000c8210301c204100012420030401c4409566074507841d1a1040c034004003400b641414904000030030100715041104201103d4040d601650340366a0008045805040d0740c00454612403c040041170600301540031b45844000759404100689035440e0160b980c00101d900200180304640d0280001210030205454261203001c011078001d44400010310541c024203001c038178030410319000700181c0c64200030050308101030303c0180607000d0405001c102582850300d034003111700340ca8508500c17070036200350f0444060540007601008114a0074400500d10304015000741e120311803c10340400c0074581c02c09a5250346601c00c041c43c29000e910907055440030402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 229999865 1250 229998615 229998619
    0xf0b0604060602120d0b09090d0809060f0601030911040c091a0306060a031d060c07060c031406120a051f14010810090201090b1801200a06050c130303030212070f0c030806 75
    0x15200039406d6417550b926807800b43c0880e5010382907001d21100000e142d0784009000c08100d50003501070002c660445885030760406000c0c6004500f1100d039052841d4031403296200103400034079092481c860968804034800665010b490a080509403803130452600b03000a840c0e02d81e1001e001c1003150503141c040e510031586031142241c000c07415010b201e41f09080100c12a1032001d851800079081d01000010300c00d91001e000c2c10300b0308000616680705e101850f180c00509081c028125210101c0020100f040992807171540001258105440c100104180700c840b2720928122509100142603808144100340d81030f25004401401030040131005040a0400f4083c01c1c2e062001b001c501144403020035000300840c000c00790801c00860340840004100e030414124a4042c604190a000359800300440c886408940109010986444000165940388100031000260307850b1058000101900b54018002d00c819040c0a2811070352103010070707a4803110b400d005400050100f2550800030780a080310700c2d040800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 230001115 1250 229999865 229999871
    0x120d060b0309010207030210060e0411030f100b0f0406030201020307030c030509090411030d1407140709051608060307060804200613050f0d121d0d0f0b0604060602120d 74
    0x18a0144103510350080c1ca0b81801c0c1d13500011030b50103142d010008a90b0a8112401c01c02c0017910b0314030340701051003000c1c1004020708011407600807580e801300b03c0d98204c0c0c101203040d00c200d40801005503004004581c80303c2d004000e0060440003616140c4903610480342c041e00554070386035595030212940d00102000700c0074081c09000503e416103910050138415440303031134405440782c0d040040600d4034020390080402c01072407281d8610070400000540716080c2c1d000c102082415101213101341800810342007040840e00d000f00704080c80b1024810084081c001e42c80b5600300f515208181a10f0b088180207074400305180c01d000c9000900044100364401215180580003140103200143c0c60303500c035180316400c040c4142828091443d0140c50301c110300504a4070200000d20b6541c8034005545000c07001d0003803043c086503041451410101c12501210020208a281001d5141110364603000c12800c2c0d07007d0f280100020182d04140c490035040d00d407550000c182014020f8070744600c41c0d208103003824410b51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 230002365 1250 230001115 230001119
    0x50d0804082101080f0105160f02030d0908040e010b0a0807050306220203071103250525090506030114160c0b0c031602032d070b090f06060a030203120d06 68
    0xc0521000100b65000005282c1d50b5458410510700c1c0412041181100b81d00d00400e010502c002c0642c080c070014a1400c00e010300b0301740564140c1c25401250158201d0b070f400c12071130004000809000300195042d1804100e10340e6203c0c03a84642c18004e080c001d4000ca101c00d0003181100c0e010710301541e8040e0000302540310441042c107542203040c900d681d4140d00543c001c010f00003143d4011460321000600c00000318101090792038800b90362441c0344000010350484141400a00500740400300c8803618900960304111544841c150402e05035224030041a0314100c0480d0072840d060140703d180c61311030142411541c440360194600c3c0c0e1807188420040c4410340310b59400244070912114840c0c0140c10b0aa510780c0b42260f008401d500c450300c4520110341041054500884554010041901030410340c4100d08030103d0441445206100b8090f102c1105441080041540065481c0110012034251140c41d10750106006040701240002941a0001d5903213081030700030400030344404103900b100803910913 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 230003615 1250 230002365 230002387
    0xd02040306020c0a03030e12030408030403030b03060c04140a06080a0b010207080d180f0f0608090a061e0f060f030b040f0c030c14060301061b061e090605090307050d080408 76
    0xf0b4440d0348200c025070003d201c907005058141c03040800d920816000b9040c49180e0010680b0b5600c802070000303207200b001202003401d261082d0f00c00d00494002900f1980141460158404203400911a840f407071101c892400640d41002d403104130864106403900c031100c1c0c50b842c59441c0601001c504060440c4103419002668500c04c028044c0100015162181c0100b944000d03040085c615820840c4a10320b9013108000020180a10308201e540a2034481029102c0502d0142440d00958001d00500d08061005040b0100c0c0001c09080c3c3c0c0a0740ca04006034458000d039082a194103116500780810358003402c10114103c4941244d105204804000e002c8689130381d0080d9032041500150350100d02d964050011030901d2070301c10581ca10440302e49040d580341100c010000c18401014210800c2d18002e00b204100c9644c00c91a600e00050100030300c0154039052800080a010005a0300103042502092104401200b103039801500a03000e0106a2418501a10140f8000d0021200d80c0030410160b6981 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 230004865 1250 230003615 230003617
    0xd090b0301060c060b04020f120a0c020d2003040b03090606240d020706050108010213120206160206070605090303060a0902040b070308070908030301092a170714040e0615130b0d0204030602 83
    0x1c009a080289c8580d42c1c11488200e441c1d0043c6040301d40f503d0b1100c504012030700003d118101e803285103000f4694440e229803c0100c0c008086c8005181d10001c500490746c00702a00240d48210554400c0701d8803642d50104109240c0045141c5444460039100b0880503401048001c0900c854800030140c82c186455584c081160000da0024580313942c0421130600d40411340703541c5002040b44080380c444810494000550b18460b00c0c12081034410307480c07140f40c00c5480300d0054540c0d0503000141000075207818503100b85c9a52045800034401c1208002c0031981d43c0244c030030791b0180c4e85285055400c000687e43d0560344020083c21800034840c00310703000240310754204015030190002c0c81c03010684030b8070900742c0203412061040717600d01703005034a09002c0182e50000d0050600400785110a07030544500c4001e503044034507a001c5c0032010500040110b41c00d1180e619450060b1000d69441c000b90349520210100d901604d0301100d548890a00c003081038008000140450802019006140c00c3e0360355106000c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 230006115 1250 230004865 230004877
    0x1509220624080a0b060d030e1003180b0103120203070c03060b04020c0f010204031b180c2f0c060f041206110c010c080105040614060f1303030903050d090b0301060c060b0402 76
    0xe03e9105035004020040341500140c0c0005041e101c041d16030502d650003030b21804600300c89038019000c80d0207a81e040d911a401c841800349428016080140c000d052613070703a00200740000c1c0c07992111074100420040c800000c440490340c02000040c00c45013903540e4040500103a0310a1a4020f400303000402c12072506104406081510384001a0f0f1586145841c107520100190010703821030341c1074030402c0000c41204240d00542079000d0f0010b00b080640c2400d541c544004a02002c48050007800d0b1032013213640d100c201540c4000141141c4013880b010040007072611844c03071a000c444006120801240081035460300286206040c0420440030b164403045490701700465250305d03030b9150041c100e091600004054050700c01a541448a5424260276444009158410138007454002031450313542d00c1035505982a51410300e004055140d42d80c18010305440d003500058829010340d500300d1952074004c201c03603070403030b400700d820a0308607840c018040e01c003032001c03003070a41d106501c0b4100c03a003140e5a94802016 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 230007365 1250 230006115 230006129
    0x106020303070f1e030203040c230a1505250503070803071209080301120201050c0111030702150402011d120105070f020c01080603061f08061509220624 67
    0x5128505000000e1600050700940c0003807045100c4448607404d038114804c03003131062500340036a03a07885074076000d400100d580c0c0c070064070760b503241200780c072002d00701e90182c5000381040340c0c90382d4000d03200d2016500d000c64403022000419010800c0d01480c01384045449100d4810020101d64100305807180390560f400520300b00c4410700c00008104006030061015119036120079410800c0e03c034255181c1840388018042c0031070501f40c070902800fc580c807800884401f151208024800c00884503038100890b0020341d14400580070b4074a130003064410500c65103108a070144e41d907101400c14444040c240c030b212840040c0e0401c85510074400340c1d1109019035800b440d6103a9540205001c4804000d0900d04103903880c81c1040861014403c2540d40060001e40000c0c60307001340c0792110040d440c1c5005484903a030206004d40580c0d0100004007282c03400c00e5144d100242d49100c92a80c1d185110029803507485d850701301c8000d40f2004000030070501d0f800001039610340d04000c02d00101c000d03482c0b807100510303070b1001c8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 230008615 1250 230007365 230007367
    0x260a0b040302031b0c0901030b060409060e070303082d060105190f110109050c0909030702030a1b0f050303310311042007080702010e0402030718052209060605060301060203 76
    0x71240442d03004c029aa00d5080f440600348252031903000645442c1c041c130000e0074011840c400325140380e685600200000d45e102004002d01a14402c0c07d5481c0c0c011480f041e00890301220020b0500014460b4035a017160f41071000002340324032035040300920712000d00204e04005051200840040040744001e042c0c00315921050360b01caa40400040c48460841010700e44c81e418100c103580088c0b00000d680c44a040100c1d400c403180d41ea800103041c07460042d1074000c0e40c54030400142d00c00f4400d440030800c8114115096800e20a600c800c20141207190900c0790b140c25030b100b0849482d10b2100d041c090711034010322030904e00d0346200e601c0960419180b260401d0b0b0380c0f803c0310b000841c0036141505c200c008105491010310300c003034504028443e00380503c58020b84264000129402107a104400c9003042950041c0f0842d01e0f030070240c80c001e000c4c07000c03d9640f400170410302c500450145850529801001c503400748100608801806000180c255000100d55540c0c48038000300d100c0da54240518060301055000b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 230009865 1250 230008615 230008627
    0xa150609022107030c020a030806030309061c0605010509010e0105090406030c060e0f0d1101080703061806260606041d03030a020a08011406040302010309030e03070602071d01260a0b04030203 84
    0x10700440300054200070a241ca01701080170a1500800c0110285400d403e0811140e5107210100e4114072400c007280341d010200144070f4030a00601600c0c1d21003904a010b04019050f00d600040d2201d201d0001202e0106100e440084c242d50b2146009080400000c0c102182071603481e507845940044903000310021820044041503541031503079402c1034100084880459040c100c0d11790381003443c0e003032181c10b0400c80b000001801050003500504014200715080c48200a00c0d030141100404180c0240501e01212100044000c051140242401c403880409000552200810003000300346d2002c1210720860600945900e01c0d0303060000c0c0d4410010001d0150341c80c11910801404464140c001c2000e0104a00001445880d1031003030354181d0740d0a00700003e0003070940c18162100b41c10203420355810300c1240c20205800794080754050865055100c0311008030010170800b00b44120034010b0341d08110240c001801c00035a141904208509614260b07842c0c1c00c0591140b1140e503501310303815405a4800206 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 230011115 1250 230009865 230009917
    0x120a080a0e0d0c05060304020d050a0309150c03080a051506040b030106090806040f150e0610030606090209060d18050304120506100b0711041d0109060507020307050a15060902 77
    0x3440321208402c60700c1403081411603544102e80400b0b8020306009110100001d011500c44034041800b03150071000300c2c2c0c848010340c900200300d9505805089a00070580c0001c4c0b0181d800f4503007244400d5030640b107401701a0303191410750b001010000c010708000030580c0e110746d20a0303c0d05002080600901c4205075900d6040c5840035008026940c031404959000004000c04902c450010107813407a07104182e4820700540c0d601c00c0c00a8419454a44414011001804079582c0c1840d80041264400d850900201341c0d2912a00100d00544100c1900400100466010240716601c030360021200b400d000a04c2070381030307200c0c20b05d181c0050700300c58501c1007480707074540078003c2c200310a543c00b40c01c1183c0d240c2d10034180324424655018080001b08031306181d085140039956a500082008501d100362028000200b03520315000e000c00300310a0f21410700e4440416406480802200d40ca982c0210051504040d00e41d10f01d40c0c084500b110020115540f200007007080a160300080050020041110003071190149c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 230012365 1250 230011115 230011127
    0x6020c030d0c032a0b07050304060e01051005060903150c0304151a0118180c17010303140c030f0403030302072f06070f0b100f080f06010e06120a080a 66
    0x1400205000031514070300c00180e0302442c0e00c81c8201a040712000910440710084040224881300203003281d50070300070400010307840000341d0f2040380585018032080450500130b80c02c848041e81c800311803a0541c0b00c00e1020b4100000204400b01024003142c0c4206c3c0480d1206400c82015074071140503040000a00061002100b01492443e0705261f0400460307040c0c04144415020085025040c06100c50703038442c44001d0700c41104001c10080010701250650028201d0003000290120030204030741e00316a2105070b01c40e03032000b0b050f82d5250300c0f00400d50302040c0c110f4500e5001100d03250a03522007040304024014000b070150005500c00d0b180036884602914100c149101c158041c813180c5003100301d841e410103141114950341c1c0507040e41e515a4030242d5003010488641100d50140c261000c103c144030131180310300c034000200d6015910b5201856101e014198803401c2c44520141682e119200501908080c0b40c03e054200b01d00401c01b003006d000007680a070804580610070343d81c200c4081000e50311190462 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 230013615 1250 230012365 230012383
    0x1060e0d02060d05091213061d1e04060e0c040306090f1208100603020a0804021302040b041d22031d09041a01050307030213110717070215090d020108040302070b0406020c03 76
    0x2031603c1d0424000307d8401100e80c1e240c0c420340e004c100c1114003458991104500071482c44202404244007460403040311640940501e4030745000d10310300100080d02c882c0c414582c0e4060411040d00c00c5c6880d02c0c40e15003601606052609803104162154507200044052040344160b4500b600c07030540501d40858180d00301d10059000005050041054403d2103a000f100300d54000c1e8100c9001060310b40d0800000003d020316081010311840014000c594ac0409a1500c100b2494540c603d010350750b608003a02404a109941e0341031404002c0c54440d0000e0300800b10000f482c0c200c40720040149aa403400980d0415007600c0a0701c6075403269108946000d80301d2007460151800f540282521490341d80401c10214030140d0500215aa49025540c45e0720717804102c49900d9041030300c2d81c540400c00381403522203a003c50780417842008814041060400f182080e074065001c01003212000b450b443c1c005540e0034800900071000c5009150b008107000c000303640a13201070b04841d0300078003444080c8028103140586007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 230014865 1250 230013615 230013643
    0x100f0203040515040c0f0e091002120a2708031e07020d0c0809150409200f090102070e0901020d0e150c0f042103020d08010e01060e0d02060d0509 64
    0x1042048003180000483c103540100714608650f4035911800c140d02c1d01c1d00c258002d082103902d03a03000011180c2d4921149030040d1400410345114444052180b4100c0c071890302e00152007405c80002030312030717052503216050354601904070034601b80d445c00d580784005c1e150301d4048501d4600802408002c1c2c0c9200c040c1009501090799801e242e00f04140003954031407060a00341e041003000100b803010042050250b80860801628640c115003c0110b00c0c160394100707018001c1d00510346160ba8040c00c0030395118030084856141d44500d000581c0a508800340e0060b1281419445030450002d61030207048140c2d403059840100041c2c460446400d03403402e550303001c2003000c0c0c0d6032301540307040003c2e0030035001941d040012904001e0349c510f640300103c1071501a550000c460543d214290500c080c0c1c0ca07000d41074000e03209509032038503611045801d4812600078060720205428130401030180301c2c0540c80441e45a00024040303c02d5407a030360b00289503a448400c141c0c01980e01e41d010301000ca0000c0252240950780 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 230016115 1250 230014865 230014867
    0x415181a010308090d0602040906030b0412050a0507060b011e120b0904080d090c0b0301080105160c03020714010302040f081e0607020c01030b0d05030a080906060f03030904020d020c0708100f02 85
    0x9503803211689400744809a510815424401718104034255048800910042c1c1043c0801ca07940c0c10b042007002c904850503039940c0c000e0f4100e581100d114500702c500c11039654540c58101340d415101c032001000000340080c14020460800f45841c140c407200888400f41580d51000c2c12588203543c8400d91319055000d40c050b40c410020b1100080c59a820b5408424600000040059050800e0010100ba0303902411180c0000000410869419008035105015200c00c1031064400c02208549458a1031030140050300180002d00a102215100da500c040052502509003034650804002140b001e07402600680d00102c05909101d52840c80c0000181da200c0207001d01c0d18004501a486418400c01c045c1015640e000c0e2040c140d460b600001d075100d80002c200e9071601030381800646600d00030345284405119010008481c2d2519188940c88840301802460404080500b4040a904000308d0450165000e01c0072214140e02042001d00a10403c401080301c0c55041d0300f00c10488010052882000340 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 230017365 1250 230016115 230016119
    0x2090a030605060414070f0e0a0308070204090c081f0f020a1e0314040515060f2803050a0305070b0106030203010506160201020f0f0114060a1d0415181a01 68
    0x284190080003100d401000c0891142d840b800050014082041080e80c003a181405000b00a039022402000344a665100c112003940c4020411010603000e00c030050803241e04020200050520790021515070348070300c4851240d00e44480e400381c10580d40742c62481c4d010480f803510949a00050240c10303c60008520f08514180c1e0004008000200040d0468000050104109c0500f8030a44c00355582d078900b18039011040c10309203000e54440d4543d18000300310278080340205000345092969680020401491010860801884802d42026150780015800b480d1007000021450600c01d10980700d20941c0e440c2d0303485146140c40c2a168030113801c030f0310806105000500c00d40d1034050407034880495800b4207108010136440101d290015144210304540521000c4205003101504100c0f07010004960b410f0440c1d4070002070200d007000607c9075075181c080010180304e810002d85c1255421600a503503001c29480c0e40d050850070b440c141000940319035a01401881886042c0c40e41d414002219075800041d94 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 230018615 1250 230017365 230017369
    0x1a04061707051207050d0602030108010e0d02030a1b1202010203070216060e0d110d0b0117010b030c21060424020a02060a02090f0307030c06030c0203070507060f12050a051503010209 80
    0x81c40c05a58020f00c02c1520740c24050303000308610300041000404c56880c02005290030000f940081c40317410190341c03c011500342a8032000c03445990800c4140e00950034440b140da01111b03100c942c4400030440c1c5041450200204502c4110700103040764a03000940e43c2e040004000346060301080d4007003404007120320180310446d0300824008000d0f0301100c140f0700018050500140c0d03aa40e15014a500200748403007801000a0000014125605801460301e10a0000002030a071203290b4402d03640350300031000b4041b00e450f00340889000f0458003002c611006507551000c0d4034102042d00d042c1c90602010781c1c0d0021641d0424207100d0440788071201035060010807640a50ba44401400300c48141b074000c80c5078400c4c0e840b0107440c0100c419000701181c1c5010303501e040543c0f10715851300601001034141000342c1c07078003400003007210303000c6500100030100c40e4602030003192800b41c01c4d161903040000b440c140ca103960206000307040c010700d058280014507040212540c84001061440c0601036401400b1030038643e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 230019865 1250 230018615 230018623
    0xa050108010f2709050a060b0d02060304120201020f160b0c0a0210050c090307172104030602071703092d0c01180b130e13080d020702131a040617 64
    0x12201d1041c0101e018040400840e8010307503080035100c642e8504241304090280c0014200d100c02e001303c008129800300f0a0511010901406d4040d400290800c0410002460040d000040280510005042c1001005c60700401c0d440608201300500341000000c06000020701a160030032030b2203000514101801c040039403a41c40401e0014411551070380001e4a0b10034600031200d0201000341610b900d240c1b81d82d9072000e04400b501e1141000c1c4101480e14a60101d61108003030b450341d101241c141824516510f05000e940607440c203c48082c0c074000208000441b00c9c0155000d101d96070007421206065102c2c486095440c00103460030004014540d10004034081104203080b8000c0c0b921401103403440e00030044580312540304d2801e0303000001d1107207a480503103801081a50101c01c40008140c031220f01e4044510044000508034200802411034510900d0b4010803c1c24406001e400c4003040030700c140e5044907022001400026140c6141d000a843c15114000140030204134200b421005082e180741c0e6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 230021115 1250 230019865 230019869
    0x3041202031215030a0c060f1106070207030213140a0204182f0403120203090102060a0e0706030504140f0606010e010318030c020d080a03020d0612030c030e120307050a020a050108010f 81
    0xd41d03040b40d260282d00d0b071024040c82c1d5000307401c0740c0744046461f80d815008020800c41c0f0790040026024000420f41d800002c0f43c850302580ba640c0c001c2140f5801c40d02046001034409140040d1540e441e03000b018200c01c0c0b11801072242e180e094005880d546803012b82404040010460b071515840c08004402400741240074214400c41e1052404602503a0008403009104681015003c200d04610302aa625800402000d454800ba402c1d00c01c81e0300c1342e0460b6000e8441801110300590480721042c80360340d10913800154064052900544115110a40a4103007030428610070451f4000c0c000b044002d50b000080001600d02c01c7c6000c0201d001d036103a0501140041070380007010010810710120542d91100e10951100741c0114030f190f0f8178881c0304400b07030080d800020000d00301c40c100341000404001120b00040c07140e815881c3e40b80121403e9504868070f031b4164a2590380800e03600d0288010394010009800018490740090002041d1401004915483d592109041000c0080140082e20502c0b4100007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 230022365 1250 230021115 230021131
    0xe03010504020a0b0f04090f0608070b0c031909050402070c050a1a070b060d080c210325090b040b07060605061e0c0a120203090405100b1b071a030412020312 69
    0xb4450348040d4040035180f04a81c0221140c030306004283ca00204235500c44011204080100d41c203603940d03050700030003034040c2c89921684d5030000c0c0843c1c2c4501c1c500040f00100c0c1c00d0310340360525006841d0350014040360004081512000280c0c1020300043c14a28100f4014051100c64100e030348140070030303c0e0b00a10450f4001080010034a000c03800b103460b90400d20032100ea0125401d6240d030300d1040460390720000c1e660f00d04104c0d0b4010104d400d55510030011240204001114680644154401d0004030302d00c03140399000300031042c0707400a041c800310806400a070103021a01e0340d41d143c05083c5501038401e540c1200348502810001003081800702800c4800c90196500b1071512034000008150a204c141c0310054403a030760303916601c0c0345c1079408401403002280444007003020782c49a4104107203640c0c0500440c42d801404209a080300341c155001003400f148001e046a401c55182c02d48038038600e5040b80c4442b5031000220502042141c5450f4109914082c1d100560a0140c42c00c103031f40001340058840c81c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 230023615 1250 230022365 230022367
    0x1b030b04020f040b0a02060f13030c0302150108070503010f020f031f03060f0501150305241f0c12140304081c060320010c05060a05070216060903030e03010504020a0b 73
    0x5649a00c90790150790707a540185500d42c0e210b0742d032109000800d600403c0e500c0018066080041c8030b2a8407410000c0c0680f0740003000c0314402c011a034064410400d140c0040d015032280c000c444600b000c02d03400b503502904107000039001d007a1409090600b9100d6801d001d088650060004a9000c5841c000b0b80c2e50001300c61044240341c52042e49940f07a603200c5500060951802d004141c820036017a5002641228001c3e54102e000e03003202c40e070450854805070b5030350800d5502c0c41ca480140d00ea490103540d01d0008010080e11034403502c40284081c048401d4400004200302c1491481030000c001380001410030300b0704001d0b588201104000b031841c480200010300c0b524000c04c0c9a000e50501c2c405480d201c1080d034404104d401e440e030a1120384d0117081d1505a042007018044c4000c503501c2380004262440e0b010000b400f036915016400300c0901401085002184036002045401d82214a01800146415203880d4039240c15802c2c010546050442024000e0f81481c05001c0141c503076020000888029030085 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 230024865 1250 230023615 230023631
    0x180306040b0f130602120403080601051602010518060d05040512030103050c0d030903060216020a082109010e0d03090e0a0509030a0c0501020408070303030b030601050111120d0b061c050603011b03 86
    0x8108801200c20f4041c0c4007504c0402c01004116500800c0c9019600a8031150036959031040111820310413a560303601070400c451900030055000d000601400d0b200940c081c1d201c107628034007040094210020303000c407841d02c0b2802d00091003000e00000d4400e58840d0000382c550760540e29101e9540b0030840c0001c0c010300781d00300c11800f4144074003c0b1501071035010300c096654554084c2c4008820702c0d42d00c0242d20607800c071207002808100c00646164005801160802e5003070070601400b105401041d84141485003509142e502691030780c840003801c52094031001c00150400307a25580030113000344142803241c071784000d1102001c800010307950039404038a4070444140703d6250a40c0a13000d80d41c417080c00c030720070440040100360300354001280c401426000c03103410341e0382c58004581c0350307407020404019608190340640804241200604c4100c804a00110b0010039000200d002c69001481c0c40f080a0042003142d14002c04501440d50011000c40080c0710844c0740b200e130741000958000d10942031554603214 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 230026115 1250 230024865 230024881
    0x7120e010207150e0306070e030d08100302120f0111040f0506031b13061407030806090411030a0807050d09060806061c15050307060914120f060c180306040b0f 70
    0x34003c0c00110b155540080804400a0124115400d00394885d000d440001040544980807031f80303640d4001401041d14400003103003074410300005032240040d181d103044080003603203c0c1c144030110422000014242c0b186489040340c00c6407081140e99608010400041207010303a4041c5103019114215170040d901d4407030003c840f480010a01f1444140c034000b10300000c178050904c4240701199072688034100c800070100c590180720712a000c1c0040103e04440089100380c1005c40c04240d005200d2003038143c0700c582d15000645481403100302180c1010300000c1c201d0030410180849040d081042c20070b0681d05007000c0c400703000c1a01c020300c228040c140c0400c0805101814011b05180b1a0403464100f080030203c4810b8240c0044600400f0700074450904005021803044203030300c0482d04110b0015a99504d42070410500314940f1000101074464202042c0d80d8007024405a806541c4802d0b00540d0b414200c03650307410b660001d00080e4482d070411300402001c180e02e102a6603001e4016804020710f55a0760365 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 230027365 1250 230026115 230026123
    0x30b0303070213060501020c0105130e0403210903170405071502030d060b040806010e010b18010302040506120109060b160605091603060608010b0a0302130b03032101030606080307120e0102 83
    0x1000e5400000900f22400c010030f594002c5055590a81c2507d981c1c41d00b02c0015078651280242000a00140321410411034000c02103160b0002d110b4940016400e40c401d1074011000300c0c195444c03002d10303a10b22582c0205a04004240761318100d041e28640c03140b41986400d92196160710480c00c584201207a40c0c0c203558824811200700c000068010048140c8815425145400500902125201c3e08001082c040f80391701c00c0a049894010880f4986480e898078190740b043c13403d034100c0c18903400784008111961050003811a1380100510300105d50f140400c5030041d0342459000400208080001611103410703030400451440d009500822a9190aa1010310b0322084120b40040c410803c1004420040302d60401011280349400034800900301c03504201d030160440c440254008280440030031403031120780044003075031320040c1170703034240b104440d8506c4c03040007085051041c0800c00c00062042051511550000d000010015420488655189886904e50f0350b0440d0a20800c41703044a07050788208 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 230028615 1250 230027365 230027377
    0xc03021b03030f060105030424090c08060601030f0c020a03030207020a0b0a080a0e1603030f0e060a090e100b040b030a09060f0e0c011e0302161211061b0901030b0303 73
    0x1a1444680400425240d469400c240c81c0f00d0b501e02d4030071011801561241007543d000750307001039410180b0000141e000005d0400010b1514005440d90788160100703059071100e2008144000c007510345850000c0004003116840819540030902d450644424130b9400100f900a050b450304006a585407640001001c40925500c40740c0003420004202c0030080e401039882e0f0182a0156090041420040070f0340d40b0340c14141400801c40d45000c00800209100300d07030846095085080858a1107000d001081c160f901503001080825a5081c00b04020900d114101c2da100410100c00c4102d2820406c45209030f116030301ca03a13a82100040003013500900e00758842840d490b8402e8042100c144207042c44400340000d48402601402102c10544c0d0550103060016a500a800c07040d0140010030f2109800079002200c0d82d0300c8402c0c0420b241c0c40000c40c0032584600c54985a202d81da03412024078611890500c008084224488901420380c60500c03054081e1200c0b5a0242030104002c03841c0d6010911b140154 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 230029865 1250 230028615 230028637
    0x70803010b0901080109090308040201050a051b16140307091d0a03080a06060512040602160203160e090d05070305090d020d110f03010207020105180f100306050f120606040c0302 78
    0x1000381c0210010075260760300380c03181c81150380da4002c4402141c145240107404120150001801588200000c1c80d0001c80d604000f420003407410b044820403194032000c180e00317610410500040c0e1055160007401011400000e9a100b060304020039140c503403621591940300e844550a44c00f417441d172044020404405000c0358035008460400030440034056034200b03009854034a01043d5244500c048401c0054989015070fa01d49807a921200298071046451200302440100c0c080141d40c02e0114030341c0c4000b012595000c1604101c03405000c00301c0581140103070ba1000545580d500d8011081d11b50480d010b00b0700e01d40b03c0320008040741031414a180002d500c200002108410003240d03d5501d060048186c130081c9184003c101070500300d1141d510040d0208034107100741d0706150400c081054070010050403085241c207560010559116029502e240826184e40c001d000c03e0800c4030740c0c592904001c44030980c0507d80c3c07201c210b84400d405400b40b4019501d8000d10481107002c0e0301114155600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 230031115 1250 230029865 230029867
    0x3030b042918070e04060e04030c0f02031c11070618030b0405100c170c040f09050402060c01092d03172a0d11030f010521060a061712090409080708 65
    0x3c5402c00030014031003028858031961074900003282c44607041c030200e44110741c903031074001010b9040e44813030124010283c0203d0b490300c600150354524200503409075162a0940e15802c0004803415012401c0400c1c9070008000c001030850000f080c0341260700c004045a4016a102c0c0c5103450f2400c14038103141207020b91180c1d05003882d842d0034481e42d20204840d00255100d414103800c1e186c0410140307182c85944102640c0d18603080040c800e40f107095004a4000d440200340034034105902e585542507864281d001c2e1414135014503212135400a14100d0b0f1300b00c451100d8600300e01a460741e005040d000d891142074403c00e840c840010000c2e6080c0c4040403411092000603a509050111150007540c09400200045410070302c0c042a0780400f641941c0c0101d0000020400f00e1303080a00b40104440203002945031098142030b0f48030301d41e906100301d9009030b083d10004a0503c0c1031003010f00340c041024501400c41d40c0121405207003807144200765a50f0351401c80d00410158130b80d00b0800e1130f0b80203005024100c0f0030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 230032365 1250 230031115 230031121
    0xc09170c1e031e0f01060602031905090901030b0f010b030106171e09070f05010201020310050418140105070806030604050a03080601141207021608060a0b12010e070303030b042918 79
    0x100c044000f030220350b010048034407001e4103800e980e091b00e4141c070403000960720030b01909080b8100c1e092050541c504514200d03040210041c00680c201100380c1c015070748030321b604080c000000200c59005006d013610501281c955450060010f00e103402002240030f030403814002040139039009501c0316001501a01d240495802c000e12083c1c2c0b909450300c140148000c10a500080d554010300940b8131804101c5441c803401c1d441c0100f03100c041c2441501420420808602c0071001071160084461501b0b1030030b000103a03516041760b0280003100040c100070700c6503002a04000000e075001804480190b89071922142da9202c040040e02d290071640304034481eaa8020502460351161521080c1c4100e88580c21980c9030304907003108100d11070141c02071641c05c1d002840000d403600000e401c84212107401501d40d181454070405071900f1144a02c00b018100c0d04491000c000b41541030060780e050301d400311030405c150b60300810450040c40c0344114035030748400112100911940d41070422400308408148250303041c9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 230033615 1250 230032365 230032393
    0x60f06030606010215010b0c01141303020111040b0d1d011805060f0403090b0f0405040f0f0b040e0a1509080304051e032a0a080a02010c09170c1e03 65
    0x1400854a940c000d21071000000c150358400520102150003100d214a626400d2452243c00c0390b00034503450b0f495640303c0c01030380600c016003042c080c800c80d900020798030500e90a24000b070a40c2d082f280101580707401400140900e061504c11100485880380e80002c4c03102c010388400c2142c4c3c0d1043c03541d0015500c3c1840002844203180c00080781e5502c50001c3e11380b20394443e0400c0d0324111042d10701078000b9407001000c4c80764040d4080100000c01c070796041c81e07040c1540d4400080503203a07988090564a07441d08201c10f0f00817140c0c081c10381c44500484d001d200e141040400d0301e946004c208409000780e080b49090907014005984480c01103904684911b9a0b0701e01402e009540304108260310002011011031f10b003c2c2140031055940d241d507520b4000d415460b030300d0510050700001998100540c000c04003481c0005d40100024812446c164001081192a0b8503015152034003075031140260094118030f980c001100421000e07001d1000302c0c1c070342803452100074241c0010300c0007404050b090320417039440d185070f4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 230034865 1250 230033615 230033641
    0x130f20070b0115210902060a11060601030b10050a14130312030b01050a0c141c0e0d050d03020714070e0a050c120f06041509090302210403081b06 64
    0x5203000c0d010000080c1d99501103140703c401d802e04200005440301e890060a62950070100600c40400040400c28030080e400241807030317110b10980d0001c990240b00700c0070424800d00103030381e04c05c0c000d00302004078159400210b9403140f80b114106040000c0004c01c0d9940342d001d009924190000509159102e44042c8901e44d0011020301061b1080a601e000c1a0a524820b000700a41c828040e9955420410b1207035003a41d02009401d000c40d1020800c40d20b005c5251010011a515250840b1446100e03c540003000761500c40e4480001e80030380900b020110200b0b80005104c5201c840383e10380140d07107000303d0500e2400f041c0c1c806090075140c00360200000f000c489203020280a1a0702d25020005a1100031564400f4899800c0e6104002c08510003e0030500d4140415640500050000701d001c44250000301e0380d03846039800484245070303182c844009045d4100000001c440031503804003040c103210a6403100d240221300c401042101c000911b001d170310401c00403100c1c080300c003402107640c28202801c414040f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 230035971 1106 230034865 230034877
    0x3090504050a0f0b010e0a21050a0b010305010f05010e0f0403020111130e0601050f0f0703050910081f050a30050d09060806130f20 58
    0x6951030301e009651040e10070510001d04050105010412200e07610100390401400054a62480e1039444241050b10b681c00b80d81d04541c402003521000c0c01003106070013059401114000420000f1f8004001d058030312401c001c3c40098a00b440c0b000c1120302c03d210703505150101201098100013400b2041d03070020300038800403d10355650100241c3d560303c800e40c205648202d01c4010481001c0d164003194010800746069071910134041110102d5004e90b1581c1260800c00048240815025400b2524518800750102980d8080c0c503401a122060444842c50413214000f040d1115080d019806800d80d00001c0ca02c0e04018101048680c1e1000b44d119201c620980605a0500b403001d81070301d0783d528901c500c00030445015450002400315680b680500280030142c003d005072a0707201c5079030402d140d030309500029020110240a038060000441d0b07100201c920202c001c00c041d4420401000 = true := by decide +kernel

theorem cover : BRFrame.Cov 229856115 230035971 := by
  have h0 := BRFrame.cov_init 229856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 229856115 ≤ n) (h2 : n < 230035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
