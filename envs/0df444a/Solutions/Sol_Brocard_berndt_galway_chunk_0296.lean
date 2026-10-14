-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0296
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:02:32.883417+00:00
-- url     : https://prove2.me/submissions/3119e58b-e5ee-4327-a824-969847218fd4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 53057557 ≤ n < 53237413 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 53058807 1250 53057557 53057581
    0x10b0a11011104030305031503030f07060b10082a030709031a0c180319060506030106270c110106090218120601140325050109050d0803150a090c0305 66
    0x1121a1a89002ca03100905024003050b03805680c0d0515046559480d12401022011084060a90305020000c0c180c07444280900080018a120f10401c0c02a00880010010401905206803011500c0d100009030301c00500100c0c0d0100c401601a03050265180e100aa50a85c1084500002140f2591014424070520005a200040003200351141900d0101a003900070b006804801800700e8016803a000155410300c5076180e03100401c800240300d28864242840070300000d8a07502c1c00b0354a010000300382407480c2e4116101c0340414404400d29403214140c5076000700400da280f601004004141c0b486d01d05e0080c00b031107000b0142c5500158076032210858460402403800d40452107480062f00326642c09101149844c1114070f850303502d5034103046800221381411406000b0503201000fa005036008120551141d4059613002c1c2c5e06c036030305103840b00306010724440b0300c40c0007802050b07042c80015201d04804c1c0d5a070381010310251011286640d16a000c401707689a111300d02c0080380d2510100040501c04c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 53060057 1250 53058807 53058827
    0x402030601170c010c08120f0a0b031b13091208070807110a020d061d060a0b0405100e0603100228020d0507030c060905030408100509030717070203070905010b0a 71
    0xb00c44404034604074400c1e46030ba02c03840c0d00540e50501000301061030a1189202c291440c007048a000c0c4a00f42c0b400d81e200c0400c040341102c2d10764040c0d103044081c050a040c0002c480c0f602004511800203120754440c10800c5040d04807a0405025844409180000c4d00301100320b0511001600c540c5050304212070054150140142000708110b00f1444070340225600140000700650150740b5500b02d0709250070704c01701a0055a039800f014100b400b0b850700ca90040020720500c180304007181041003040e148101f000f80c99050324032040241075030794113101508284c03890980184004084608140443d00b91405070382141309608050407a5040307040046200320b5100303255081c40c1c401781c410030155038000780640c06080006420800400c0140e800c201312940001450703034200080329281c0d551f41c0149035407901800d1000c00c12a05080103c0d00b541400010341310b0321039120b00c0c18440700c0a10280304260350041e00f002d036807601c40d00c2d40004051105c0c0c030039103001e01900d2500079a6214002c001a10f55000c0c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 53061307 1250 53060057 53060069
    0x609010c1202030901060b04080a0209090a020f10020a02030a0b0a15050112021605010f02030603150105150c19060c021203090c0f1305010f05041802030d03020d090506010e0402030601 81
    0x4140585a055512440760000071209100c0161207845042c00b450042480c0d401c2010b01100000340407031119030010305c5840242c403c0b181c621a90762801d01943c0c407007104200082d002810074004203031600e0601a0b40c2100281441141c101c0d0b8855000079140018082040d01e45111140a011054206009150300a0300c0c07070f07441c03d035803a00e00700000340f18005400046071815400310350102007261091600308103581000084c051400501c2610000354130a035125032003171141c000c880b110004070668280c1210801488203011001c112040c0240354845c02c4c1c0131580e40907110f040c407403050380102403021542c092034000401c0707140c8080281c90000711034410810071505004200c00c161002a10041200080da650008041900f02083d61420f0254000b0b2502c0d0070701002040204140003070104842044805005034101603481910300c1e682100d01a4064104411481085000750014210382481000c002032814064989505182c0c0a03004651500d1070315081c4019490108965805030071 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 53062557 1250 53061307 53061311
    0x30e090c07020d02060310080303011707060801030302070e0a020405130b2803021e06120601031104060518010908070603050405060907061b0218010905041709060a05030604090204020417060901 85
    0x840d00018030f9020441c20080c85000c0000005052004030142803008040e9102101c0d100c2d61514400320031081d030011040164843c0e107800146840c0310301d000038100d030740540244c0b1045090000440f156200100381c580381d55020003000034180c41c1c050854100120f00000051400400d20410030101d001c40681d0143c440d241044840025a854044003100d03411101115084880d082501300c00307100a003031980c0040f0125000080310084921603101c0c04099804000a00b0103000c131400c1805940a08000a10180000701c464503c04141c075101040506002c481c0507aa0341c4a2890000107402400010f41c03194107220820600700209900464104090040309061100013403100c05074111403550303000041c02803000d40d20354015861090700d02203401066580c40b510380c00e020b40310a850484040404031602012040101d0544080303802c020111403a100c50040101c5064101920041c0c0c0f0a65402c07000005a0300c40c80180014030b00c40400c9101c3d070904000a82c180030000784007114030b034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 53063807 1250 53062557 53062567
    0xa021e0313030314010b1c060e0f04030e03030412111212040302180103080a050a050906190f0305070203040510020705030604060c1106040203100c0c35130b0a1b030e090c 75
    0x180300240d0340364601d00d07200c14407241c400700c03003076005031400354400302d649045035044c42b11a09083c0206445140030713850b015016417007203040c16921f01c03840c41190b40c40d102244003040080c116541c601c1043c03000400c5054106e0ac6246054201000c40300d40c180341c0d49001404004604000d5181091100002c0700000d6a606d19182e09407644a003038030400c104200051a101458020400c3d80c80da550701600c140d44070101c42c611f4400c5064500110000b141500c080613003241c6c4a8014907215100c0b56029505161400c018001c180c8d801103245c6046d030199a101056a4804000c118481c44c003641c40480e8031043c06030007078461072505090403500d03000324042002580340011180400c1507a500b0005211140e40011101552506001005035100c00e000741d081d0781c100c182d5080d11003d0340214681c01210310f10700079901d10445520310300c0030003007880c1003080322100000b420092080d4185100c001d00000e50f030320309141d041c800803400705145408506080c01c0204a16a01222204101e4070303003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 53065057 1250 53063807 53063819
    0x609030a021006030215130e042006071101030b03030705160e061005030112061b09083304030c08030109061a030c090d1103120d05070201090b0a021e031303031401 72
    0x3441c8808005544404001480c817140103032040800000c11105055000a0a1920f00ac1e041c0d52004107003400382181105a651961030000b048508a60b4814032a12006040304019006480100403166245c0800d009090109105111120724803100b01c0f803461041303007002010005070344060041405a0b112004402500c2e406c0400c4905480b41811041d40707841180c601500940000300c0030307151044950401c014030342c1d00111100c0648059a05680642e584c0c165007100201d07520035540c6240b80c0000c132000c007410404421a401c680a8500059809401c1d01d0310341c3c03994420f80c000281c0640d15402040301c0c5003036440380c01160f80d88001051560400d00c6c0c1c0100315014502406104001e428039001c100100100c0100342e0b10805010341c0d180c0000800d1800070741e007162100d81030a0f820000014012841880b40c0701c032a81d0b004003044c0d86510340c00c4048000303400080c84000310014071010541002c01060145104248010000030000018a4020103449803804002c040030010030041c0aa = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 53066307 1250 53065057 53065069
    0xc0210050106051c020d060506040e09280b09030706050f01030b010503030301060f08101701020a0306080d0804080c0c1504170c011e050d1805120a050d02030403020c030609030a0210060302 83
    0x3211045840251300c500040d05044007c0155034420b0303601010020300003420350f0701210858803400d800c605460311642503080e01e4098004d483c800e410149103006907880000c64180015411076030034400c03a800d0104a65810f130450b0000d403400d101114030040108108a444c1d60781601411042e00a981154034000300540062164080c2d9000d10940b800001d8054070000c00a0340100703a501c680a9124020b209098001d5200e2194100024101600032680d40c0000070049030340c3d0050b23951a201903641d0340340c1075000e4001c2681740e0500d003c0e19080003219078a0b07401c4040c400812020cc1c0b0b5039035241c624980c180c110b4084104080e5004150011004e0b83c201c807451512080e151a0b00c0c001c10b10700310b02203803d4072132003d504440d1450146145270f402c0740b000c803002c1c0700c5106108480c0d500f460303040c4050360b0b070240c11800000a8010410030340000990740203550090303c41d00488119a0fa0b04002038144142260301a08907031020a4100c2c89a50401075410403070109403080040038210b80106203 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 53067557 1250 53066307 53066347
    0x306030d260705070c0b0301090e0102040b040614041205070603050601110a080d020c030c0102040303090f0e04030c0c180e0c120601052b030c020108012304090c090c021005010605 79
    0x30710884000040050340603908503401d01d544400c54600403a10342d0b80708802030b0000e01540f007200c1d01d8441c00f0b41102d2814402c5601f036841c031981490400749041c8003118201c0e41844110180d82c401e200c0060651030020801f51a1403154001d041180d04101000b01101c02c020102c50402c030288440c0722a282002c150741030b9040d00a890303947c0d90341c86400704501070710884201803403a05c070000300318182d0300c41903020748103a910076070360f408505556241c800e04110f030b5070203401010700642021800190180d1419000071f40725040d01029103582d1007401341c0321006490b90000d600e84940030181498020b10100140900460b044c0500d02d00c51280c0700d41c1c801050041d24003414046000d03181000800289084002003401c61118103610b916005086080750481240801c44c0080042003a442c0d09c2144480c00400c5451640c1b42c9000004000281200071002c0e1010344c80103a0108481076107010b009902007440d0010406585c3c10b000301001c94505902070401c0050a000c3e0990104045403552 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 53068807 1250 53067557 53067617
    0x1707050403231203011214240105130501030503160501180501020d110423040207050106120c060201060e0412090b031014120604080a02070b03070305010612063609080306030d 77
    0x9004414401c21f00b9241c404a465141048a041c2c1c42c5c100c803844055928030b058403829111f248105094049150039150203010040460f0002e00c41b084008074008800400380d0b02070300021079a0011412113083c202640d18094420b031f500083c0f03012a8004502528503084100e0105600d0035145c00c03050244c50504505401900c0300c446410301c1c499844e80c06807400941c00c10020000d4542c1c400600c00c0422084e0b0041755218103810001410a00612494080b500003d042d020760b6a5260384041003c1c5c5010342c00c1062203032007840815024452000b944c8980d20b0b5050064180e400c1c16010b18a0104612000c0c0c410741c1300c14010074040001054194009034032204c2e154583c208528182d0411095400c801400e110100401c0101913060308603134103c82283d00c40700e0304180c0c802e40340c0d0146d401c60b0144001c602c2c41c514400710902e51041d00c0919141403040785110307515004101e001560444070044d40c0c007440c0481407101e5031500740902d50a100440c1042c8281c42c0300361080800c0b401000c2d20700703 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 53070057 1250 53068807 53068823
    0x6020105060315060d020d0204050c21071b03200d11060402060a180b0a050a030e01231005090c0a0207270b060c01020304060e07050303040617070504032312030112 72
    0x30002c64442021f035100f81c1d0f03030090052150340b030268050296600031a00d0040240c01801e805100822440c800c10300603a0659114101c8200c508902c20441e50744060403070070002021160701208070041800f20300b80c000c00340940645071414500400641050415400d00d4000700c00707110040e40c51104680141c04d0700e05000350402c03c81810a0401c01c842c0d030202c503c501000030401102c640c40002005c003188292020071400000807500d80c202d4603400c070751511504002e164140702c1c0311451b40441c2d00c0f5100403440880940c0304d0700800c82d1110180c4003004135000100d481c0b0407a503014419200500f14218903250000d0b4503504015095100710081c807201681c424000c01c60f40c4541003114001146c4000030355a0342410b1410100070480c075055000e05024000000c202494048121421104241c0e903d580614980641101201c400350a0906000c0200000400196020a041c2d034400c43c0f03401c0c904042041c410014145034240f800074120040405c01484030303800c0c2d10420f041c107580000385 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 53071307 1250 53070057 53070079
    0x8030a0e090604180b0406050f091009020613030b010815100b070804050d080304020a0e01050303090402090325030303051302060a030e0109061104090f0c050313050c0411040602010506031506 84
    0x22400a01c4070300d1683c40c040c3c84c400c00900a12075090700300740c02684141d904118aa0f5040d4040b00c000400303032403200150700840c045080428040d08084000e0340001e004031319045680640d990603503075a90040b03d85031802c50040201d081d00f031001c4a208036400c40c18402624080f202500f40b504580107403e03c0d030102049107014000400b06450140a014261450040a50414050680044404034460101c2141c08a440c16103802001d0403500d02400860500d1440c20402c0003079000209141e42604c500604451114041c044c0101c40c4a00b42e07040700255030842c20010103a0300014204144440801005401038682d0700442e02c0c054070500d80020116105540c0034007400080d4030103408941460300f0942c0324800c6600030421605d43d103400b0032a40c1440c40c0b004003961410a01103010070f4050001038000140c0b000c0100d0b415104006480700003100b840054116480c8144140300b100d4007144c2070115640921400e80c00130f01c00c4004000d002e07009400740000010081ca0940640300d0001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 53072557 1250 53071307 53071309
    0x303070314130f0b09120f0709180c030f02010810060c020114091005040906051504090506010c080a0207050a081c11030f07060504020f0108040503180d05010207030806030708030a0e0906 82
    0x1030100a4000c00303e041416560f2100302a44a42180d00d050b440f4051092560b500848005060101c54a03402e014008140c070380007601d4010100340c0d18298000c0c401c00c0212001845119000000c2c512519070049407002c180001851450021305956250051000500000303402402c640540c50b424a050450a40300010110083c001d10300d03140d0f0800f0f00ba03107007444001c0e04400540107580f180032080100170341d9642007007103078101140030381803516040005008900c410b80080d68400d5060411400c40880c2c1c1d52011841e45c0500380c43d43c01038000c110280080d01d0311052002c02000181d005004050b01213110011045815400006011041054040c110b4050065a518a884103401034030342500c2d081500180800f101e0407845010300e58050403056005d070210a02a94101e401141845a07465130858601080b00314983e202210700c0f100c1001410900051141510a81c1e1320140d5007888418140b070004580c00c0350205400070300803132400c0c076400b4a4030400c0e400215001d9541c1c0d00c03404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 53073807 1250 53072557 53072587
    0x3080109090c0905040b1803040b030a0902040209030a0c05040c050a211506200d021002070611030408090a0503010c020c010c0804080a1208060604030209060607060e010510060e0303070314 83
    0x9448000c0e004c0c20102004140300580a226110f848030b50107416001d0a019001c40e00c07480b8038000c2028403002800844c444860f40e60221548510141006150050081c00a4500101c1050495444400c10030034012820a0300404400c011a1308242d030428130803440c090300003003500f0307440b01e031030480c150845100f442303680c1110019190401c5d156212544800300188030740008621490b15842e4064001c41e502800920100d842d1000e502a2458040051650000c1e6014420640340580c89514000c2e4116050000b50700861081040a81c0c0b54218814400d004c400c036403281d03210313901d80851b41928035008034075001d2506092030000603202492810110038051500008610702c94600c1000402c6104800508081700640318400380d5900d200400105100e2400300a400860207004503445090030400303014080d11880300464500d004070626800c440040b24050311018014404009403a00a40b00d00d00b03150040e8007551030001c00c0e0310040d1011700c0392500344290f21400039004032a20040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 53075057 1250 53073807 53073809
    0x5090f0901081e0c010c12120501060e190b031303140c010603021c030906050a031d0c0f0109050303030402091f0305010c0f0201050708010501031a03070905010f080303010303080109090c 82
    0x340020403658581c41030b140c1d903000e11062281104244414a0350a22001910b0810b20f04141c0d104541400c43c1c0c1c1d16900041041403055090141980340224560b6641c003645c0c0c081e1825070782d00049401103400b04510b1685003001410002400001403180e441e50030308407540040440713540c0007180050701c1c04582801040e4030b007101441c030104040f424440d06401080450340200c84210911210702d000400d00d03084181c00502140c00b80400b027208c07901a102800c81a025402c0c00108481081940f0103482c0f1581c2c0b0074050360704540f900b14400e240401101451304828a0050b441c2400e1502180c0d0f24840a040a4031410f415000180c01d541e0b1600e442c02e14818443c0044c141a07564038000c1d018000281421010545450301a045a4414401e581c45521a5544e00107103900c0c1000560042911150100440c3d041680c00c0801d074604010f4400200918940054071f03609d0b1103c100081400b6070400f6046400403c010000309034852040703070540311280d50005100e9540c3c45d01406800301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 53076307 1250 53075057 53075059
    0x10f021f02030a1103071e030e030a020a05060108010e03040b030405160806010e07080402100305250503010503210a0509010c06050c03090c040501050109030b06030a0b0f01030510020403030f05090f 87
    0x800300c00ca848014140e0080c5002d0702e0409014002e007400d805084a00740070403145500004c80c003003480c00c400c000f203020506126a2134140011201400c180c1103007940d01010344407015a10805079402000b1082101c1401854440000c0209038809035079581c5034401c1d032162001000002c000718050100521400920a10303400d010148103a4540c40e56866040034800d42d07542c480300100040c120781c0141c032901d12031540100443d00ca0001c184056008242c080d01c041d201c00b0b10401c2c070b040c0700001c550300c104d050b00365034890503100e40c9030400301882c0c0070040ba0307000e00880042c0740256000e10a07005441c0c1162050501503220b0083d040101c91900364100c1c050245400e0509000c01d60a100004600910746201582c0b00b40c0301020600081c3c400a210300c90028070014400c00c0030545007500c03d50003802c0182034505911342500d40800c0c20341c0c2640d000c0200c480446c01003081100070850a80040302c03004080d41860b142d500e010703080070101f14200051260008180f4510f0781ea0fa402c1c080c000760 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 53077557 1250 53076307 53076343
    0x1211040504050717060301050c220302060d060305060903070209010b0a0210180201030f200d0b27010602011514130501030809120703080403030c0c090504030c0204141302010f02 78
    0x50515001844944184c100b00814072901c030104a10b8201806800c0c49004a0b040441c035064007030140ca4407400d0f503500f02201c40690800c0200050740c0d030300010102d5828100d03001c2851400c5003060780c1031204c0540451019441000b445c80140c4544d2001411154451401da458400340c00041c1d0410240038600d41d500e500c1c0c19080f091182d01e00c850009094002c0ea000c210000c81e003030a07001194101c401d061510941c1c82800444c2072090001401c0c203190300400410f0400244010034488030309006c0000c205000604140803080f9548070950040c10184001d00c000600e02113078560820300e6000302d01c002c140104001c41141c5031078850440400c20607034100000d40e581d091140d080e8000090052240329481441c1166400010b01d00040d07030b400014882c58680f566406513544a19050b04a07002c07621000700068000b81c41c400c0c50301c210b001c1d0f252800d50300918810001140c404c0c0e0720344d0491200310018406070405641d020202030b54282800c0030300344481c0d40c0a80c581085c0e0f1200d0031400c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 53078807 1250 53077557 53077561
    0x1f0c02071701050a1d0a021c020909010203010603050708040b01030f0f081803070506040515070c03020a03030906030b01080f0711070b13080111030108060714070b010e04020f03070501121104050405 87
    0xc0c1c41540f040d0302c162254101080a008201c1c2090340b4905040210f42003a0b1041c2ca01c2c1d00541f0702500c00b4240c0d6403500c50307840000c400030340c0800c50039102140c010500da58040010004d180e0503001d202d0384204d851074411050f242603995030300c40001c10700000d4824001aa0000300b0002880704024480ea048407030700d078a8a100c240100b40107036803941010b01a0160b8140000c00d828190309036400c1d144000c1031200072070105460302074283c10000c030540e8100900400003000d41c0b90082c1c0880914000c3d5a41070300340c0d040ca000a01501c0c0d4520038141003081c1d540c200310080109501043c0c1211842c5000e04043c0114032005d854228a900007058104000988211031041100600110744442e00248000c8003250310b0356905020034403414003980c2200e40081d4032300b03219540720569909400b90803800c01c0d05c0c0e40c50340006c0003002d801449042c1110381c14041545001441040d510b0b004800600c0e10710706280c0020006122041603498480d11198092a0f001110080e01c000d4007002e00200300354 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 53080057 1250 53078807 53078849
    0x5100518040c080303010f0b0c1c02030307020c0f060304080304061b02070602060a09030912080c06040308010e090a080a0302090d1e0209090d090501051b0115171f0c0207 75
    0x40c60060303504030b03015221450000f507001004802d49040303d800c10b0024202c540760400008065000000c803640b50b00480c2441e44446082281d03144690415078021616444c1005001c0d140c003070120a00b40c815a084044649a540c4482c2181d5029900680c03035900c9844624080c0041d0000d600a01e084280d001e00b0704110302d07230010b101000c03110141e0131550030303031604803c0c041180c1443e94050b00103140580c050110585001e0b03031078207162045403483d180c4070076035500c0d505000041d47c08800085011004200c14201d031200c0e140c00c00701400140c5415141a55030640d140300f05e400315401e044d000b081c0e0024a82d03e043c80458005d41201c0012055034400d64202e80c80a59a0300891160f2603090215904103000288138040b501c054031514030450070940190340740d400844401c09031003040c920a14046c032080c0100d41e1422681210300440728140b950800270381d80074041c8102c1030790101120404804500b0490610a20041c40c00900710407509422070615400750458036688907002245040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 53081307 1250 53080057 53080099
    0x8030906071e06050a050613110d0e03040f181a03070e070e1c0605070203130b0d020408010c021b03031c0203101518060c020105090114130b1201050306040c09051005 73
    0x1140c0003c031501d5110748c000305440002c030f419100125a14a0781032041c11031580c0d49038041c9800101c00000c03203090070b035540744c58a2070608030b4001b001c00c01d15401038403410f40070601441ca20031514091041c588a014800310355208214420a841c04e8000c1000c960180d0080c80f4030000b00c103010b040c80084011a141d10400d0480d00441103540e145040f0020741480d00c044140c51444001c6500250410301d01100116950410226810200d81c01c0100203100f040900c0340c07810f4580c09401404540c4400050b400c610090200010f009810400c00b005145100704a5401041c06000c80181ca070744903c0e1681c005042543c03c41d04001941c00d100c40c039082d420440c48000c0391140c400b40600552916400c5481420301a8024042042070055504541c098a1000c5625491036103a6040607804120640c030048036034099546d0f03141c0010300e01c070b981114079051405400705a006200e5802e01d562140d8840d00d0500c01c04013025980c01c0407403030041c41c1d8007019005100007088030391810301c00d140c01f0f10303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 53082557 1250 53081307 53081311
    0x10c0306080712050706080403140c0a0510020406020c061e07051e150103020913060606050a0206090106060903120903080307030608010e0105281104060503070908030906071e06050a05 81
    0x10152241942c000388000d4200b07401602c0030f80c060f0207819003503d0100265100c15003d4411818016411505812254003030041c021081183d0018080031501e401c2a82c20407400700030703503424140100400d0041e9034000991030074502007516420303541c5000d00d0070b440c081c1d44488030700c1a140400040fa1014050001170041210005c200c985401d40840d07012660340d503607041070403500420701c0c400401c0980b0300040e030b145d40229a60b0701c02c046910140c0d0703108101c501d107401420220300080340b140000d0303604200680e4000c0c805002040660700342280600440d41c2440700400a038002003010168502c00c8043e040210f0b03001e4112a22801e040001030007a2905002d8103203a9840c00000408900050080e28006c0c160811020f01500124421010300f00c21600000d034442e4890300d1aa1070240520300600c0202055900c05450b41408800181245c2c60365000700180c2c0d00c18440d0485c5559103400703c07200283d10551400182500c203100e4154101c00e200090513851403c0c0070030a075204035030800340c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 53083807 1250 53082557 53082569
    0x90f0f0402180a090606020a0b06010e090106050301150c0b060609060c010216021c0f02010509120a060504020306100b1611030a0501060603150b1602030109020d05010603050d05040503150711010c0306 88
    0x31000f103071180c500f501214420b03c1207134010f901040c95030012030756494840340c100b00e040c50120a8601d000e008510065000c1e400720700001d000100421020354451182ca40a603d5840c151854101d140c60b140d40114014151610030000000c0c928890f83c0c8050851703110101620080d51105030034000c1307040900d00283d059000f41c170440c100122040707003030704164070441e408640c8091854694004580d1034100e854129013203030300e4400144200c281046074264061091074041035910342031040c142015406081c003100b0100d0070b281403001c113200300c090342c660b181c01056402c2202000c0c145140c1c04024607101e1505030240c0f006403800c0c06410740006090f10201e441c00c3c80310b075000101562100308188160708a14005000442642d00120a00b150260009001103181800c2d40c0000381d08030428582211169543e8204004020003270010b622018000c1c1001410689440c01203130701c45082c964000480c4252000040000380500e091155a00f000c80003004a903c00705c3c4043c0040c0850b00a82c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 53085057 1250 53083807 53083819
    0xc0c1a090c1c02091608130c05030714150a0909181208090714130b030c06030709030501150506030a051e07050a18051008070207120b010501030b1203090f0f040218 72
    0x30850191000f8a0704929200d9941b1080c070342d40e92200118100c81180c00311002080b402c5d00040d183c3e002c1080002503c1105070465102c20081c007000030703241448218001416007031240d10340a0f50085000c1086942c42000464901c90b6030b15015071a2122040040c04c50315514013080e0195404840d0130300c203a0000049a1071691252410301c4850403044050b0f6104a220001881da021a6040050200000b80441e06000000b400190b82a0000c840000014805e43d604205111090040110409140d00760141d9181440003003101448020b0003491903944a0303020401c400da00a0240b088a561401e0f8040a41050800100554807a00c80c40001911044044103520314419110f0300f1100700034454417070b01c40d2a040940e03149100800f04400d600a0400001d86100d81c414014803031446100202e01960600f800981220000c040043c082c20b420303180348034610000001c80b844240201c4100080c451800001a5007040030031040d6003050000c1032900800d0f5658800d070fa60240b00f1106 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 53086307 1250 53085057 53085061
    0xf09030809060a06030c0b0a0203070c0e100f0303080105060f0c01050106030f230a05071103030103081e07030c150b031207030e010206130809040603140a060c0c1a090c1c0209 77
    0x3e04030030f82c3c582e40800341107011071050400401071250002c05000d4170a00640c0e06001e0f09466550054101e50312441200805400b040901249141074a0180c00c00000b82103607141540c41c000d19222050107450b0003010300196500d14800400b00391454921840020320007136840300c2005001c1d00a980d0b0350b00909003840781c0400b05034150020790241610b006030691a66a809000202a000180c82041440588461007048142c144011030103540a43d1b5941d5460740c0042605454400d60f03051600e1940c030a0240e040003036030110100102582000d00050b0126041e0060b46c01811901c40c4103030305110348018601c40c000d9441c05040f580b0f003e501c50b07815284c9050010ba8458008440c405003e1006100b80d40020310500e014240c03d103005400021915100d03500c03003115024844070014581e01061800c0e04100807801001c0c100511072400b0761044000f9500c1c180c1c211002850f4444510300400001c5a8401c1009a4010170800414104000900d41190701301c03c1c005d181c061740105030103c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 53087557 1250 53086307 53086321
    0x30b01030b060a020312060109050d03090f0b090d11060c0109030306090b0105160b0702010b091f0503031903050417040b04080d0f05090904140607020f10090b0105010c060f0903080906 81
    0xb09480d2140b000f0b8000d14039001024415910070040200400d041c02180702011800340c41c0c082083c21030911944881d807255040c1000180d5056a9522800b584141008846100d80300d250800c1038055002800d40e071210001d400044890103100003a1515610b0811714800b411751581021086400420040002d20b565000441d80307442130070300d515020f9460a00c50000115480340d40d907840300d00c61000054003003195000032614001541c50b02c3e0740d0203401c15440e429064520031348004040c11001540340c10700483c054103007400c04039549810701d43d071070000038180700f2120420000f00984089144c0e4554582c1d034450b0541d0820b0040d524144107048000400d0343c084d84024841034000d442c0d050400090703c040050071500201f040310182e4041810942e100e000300702c040e00545258004d00f507890b0070781074041c1c500507c880c0d20310700036070524800801060b16801d900e8192003081c81c0c0718108003020308242c0040c11003904074404c05441c01040f00145a40a0070147c050580b210680303d140e12520 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 53088807 1250 53087557 53087569
    0x20a020f030d050f13030602031509060907140708040906080a03090602011a13090204050a0f0e0604020a210510060501080703150b09010e0603090d110706080c0306041b030b01030b 79
    0x4450203d101000381c4043d03e081c40c80a000100070079092004196181d07960b1500741e0f002941c482041925100b000e100c00d02c0c0c00e502859000d441038803401001d2a1254008044580c500e80e100140a40020f0a40074800c00c1d00444000c0c1124403818801160b554142310b1340d83c43c9806060700095400000403440d00d00c1030103a00104098040b903c2541340c07032b400070002d0303141800904604590792a000140161154002c4610a2814140c0001d0602d440000780f003e40d01800f8280c2c059805c00410000181e881c1020034040d900f441d03941c1c420390340d00380031800355000d50550301400c1c1d441200c2007880b0381505504030805550f000c0e078901c21180c48002080d0305462099803203489080c1e0b400c3c8180301100d005405401410030525000442080c0c9801280c02d81c1d206032002102c6d500408a4040300680010450384122040e0005011252500c14000d00c1010301810460f14240c000000c42c0003542e468004602600f0341c1d21006102d17622803400500140300d9401c45c0c50100b800c00c0700c02038052401c0c2c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 53090057 1250 53088807 53088823
    0x181502010c081303050f04031b030203010509070501020a1b120503132102190f03080904050c0705030a080606040f0602030d0c030204140f0a0909080a0206060f0f0d030c05010c020a020f03 82
    0x240f40309103c009000e1341c0c2503d0f10342106604c0030800b0014440000400d00c40c9100c02c0316a41c0041d802c0d0941800c50043c1400d56000a250000c82da000d408100b00903640007441c400c42c00c0c2c0101c000a583c1d809012051503414142d80601c00b070340482e085c10000e01401000401182c00c072075034414805a6600754114200ea41c4c0b04606141c0d40725001103c0c09410b00c00c5801300010311004160a505485000c40e6030301d005a5041654a030402003000e0000e030600d8860703c0e4000d811046410704100c225510f82c0e541e40f10782c1042c0702c01c110280e0040703180368a0744130a0310068401900ea8401094a0780002136580d0030294800420318200001e81c601c00707000e482102d00f038030082545625412080000c0c040f02c800d0310403101d40c110506060005400585104441a90388901c01d010740d01c02010381c1c000d1500001030411403080c1c8480d003c1ea06e2640c3d41d8082d0043c1740200742c0e030000b9034002074201542c40415040025240354201904079114a0b40440c0503d1014401c03141c0007031a02c18801850365a00c01 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 53091307 1250 53090057 53090071
    0xd020604031a060a120b18060a0605030105060d0c0b0705030408030706020324060d0b030c120c0a140d020907021009110a0b040b0d02090604030614040c05060307020703060c181502010c08 82
    0x10054074002c206c44071880d40d804400c0740325584c551910344501e6464080c0450380c590f10541c0e920014800c9140c00e0040700d4020302c0495802c02d200c85951038081c50035903d481548000c440024400d002c010092050f03500410071282a80c0c0c88241e030341480c002079413049401241c004192000000940382651300500760720b602500c0306e81032000784d114220041c6405010b06c1c0d03261040042010595840c0300031042000d00324000790108030455028013403030031340700c0d00310040480c000d0405441545502c00400009501222404007039140c4120030313414132041d100303c5501c55041800c41d209005c05226900304141c42507c0341c10981d03951303440700d03090f17230003a40502d80d43c0900c2080151901c4000e600500b80303803d80245200c1c540b5642e41d82d4602103803629039816400e07020680410003441b0342141032000070003003038516500d14641074400030740320042400300900c01303030b5504110700c9400c4c80743c001103500a8012a00c1c00070742c0e844581c0742c040c00d5240c2e1000700040d0300b4102000d0303c05110711400c1e801018 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 53092557 1250 53091307 53091329
    0x6060c020a09140f0604090b040c0609050108090c011d06210105030a03050702041113030c0f0506090f041508010204060302071101020d021507050d1803020d1103070308060d020604031a060a 83
    0x545504d65030f400d403005030029900507201c600704c1307012410080140c1d01840c031a0150030b8615140c0f20025000344410b60000303052040480410840c450042108038000c0400d2a091701e64920f081d004111040b003404059401040110b0030b011040304a90500724600062078100c4407503aa207408041d42c3e00402d000060000c1e00a10004005040c59000314034026a11011541001190600c26215500c0c0e5841580c1061900742d0412002c000c03c04a040589011746806e4942090503011800c044980681c2da8019a030b1950860302a507e500c40c41006001464000d65507595180030050103504410000e540c2032075160703400c10031513000241464442c00250042c21403a1410b0380c4507520b050000304600144401000481032040c440d100e502e1815285845205440c0007a040080c508028107070b0080c144560f41c1c841c4000d0400000940e0780c803503490b2501101030396600c00400c0343d8039000603000350800404140841000f4bd0740500c0b00802000c0d01c1128130070341e44e8408100e8141110310820340340c14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 53093807 1250 53092557 53092561
    0x108060613030f050703050f06011409010303210b1504050307090207023102030a0c020f070303020304050609010207030f0506040b0c0405090609040501021b1006091104060e011206060c020a0914 85
    0x115100e404120b903601500940c1c5001b6600e483d800c1c1003422010f40b5800396005000141f000c05071000c1c1c00348840d80700b991090900d604669024101c2d41e400741030340101c110000a401c0b0b014001d030300f04004a04001c0c2a088202d03803114a41300c03494126010b01c80c8213010703009011a21404c24401e440446800422031040700341e942e000140b10211b1001c1554042c0111403583e5030742c00080c00218013030b48c2901400180e4aa09140080c100151421414001d40101c0000c02c0426400000d48050356001c0310765660f0750741325800603883c0c600780780c0c1b000340300040400c00d28081c85000320f070080c404c5d0b004400c03a1081c0d42d554580803005202d076000b901e80c03010b02c21012038120704103c00655441071040b0300041c0b6040d20b5070001d0700d02c1f400e030300164000f9503c44c140b001c0c4e011005020301d0b0003c042c019001c2c0005420140303c0d013042c0c002d5000340f9042103c003406980d41d07070b817095056000c4d03d46241420080c2075101c080c0100170000e020303c268010812400005200311052243d081e00083da24003040e003036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 53095057 1250 53093807 53093813
    0x210d0909110c1002090a03060e030a030501060810060e1c0b09070501050a020a0f062301030302010f090c0e0702031b070302031603050c0d140d050d050610080a021c020711010806061303 81
    0xa405c0f10365195004018158007000192552042041d05000a4011901d68031401707001410f0303c2d13050b00f0200030000003005011a4507040e5421405071801420604a050b24610120760340d4000c4040640c0343c4035204039420103202c0d50445840c02261800266104140c543c070054496218820103c0c00582c01400071101007009000319003c2180f0880000c101e884403180c07488005a006035004010310b1003d00104101a024480d403414291480810700c0035401e00e07109c01600000c04c0c881d00709000348440c00034150b9442072080300c441d81340384018a030039000800c9000e5550f51060000b00d000e4860f01c1005542088174014450851f0751000c02030000d400c5100c00c1c011303d01180d980440d0820b194001c071088007041030080c4100d0000c00d0740e48588072082440a9416294040e00040c001d20060030700c80e0610754803015960340070103600b9004d6034901403e0714041d100d00d2070040002c492440461000c0030401c10501760309494100340d8603c00c0940760501002082e10507141b0a50b02441201020000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 53096307 1250 53095057 53095061
    0x103120210020a030b01030f0614130b030f06070e091005010c170307180f05010e060a050909010f050907020114011a0d020f03040b0c07050c210d0909110c10 69
    0x44552644161441c640068800200b40d07081a001c443c082a00c1c1c2030310302491b583c0b602c540300b54504003410901c450352411940f07000e041c00b070010040c010714228040020082c2c0c15004410840d601600b1119a4005060410303140d138010340705100024010400d200140c50003c4006010f0141074030b18031007143c40d250055452940c44541165080c00e07281083d034040305060003039441303400f10f5101d81c6002e01c0c100942e80b01c061800c3d0004a452041500d0900540c0d0388007002d044420002d0b03420350755881c0d0003881501d07103020340c8071000d5100402800101c0c4c03241e030b10b103064001ca90080c0c0300b8000365101c00343e0aa098560380d00c140381809800d071004001c2106181c2d144204d00d0742e04140a450413612286007824ae03442050351104148002003480104688414a6a4403030703140400642002c0c3d5035034580e504d0350b4040369501c0c41600100c1004401d60569022540c0c0081400d0850740c0e001904003000d0100d0012b4416038040624100c1c030550200603a000702c6584036a00320141c03a0b008260400360b00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 53097557 1250 53096307 53096333
    0xc040f0806040b061e030a0503030a060617070315031202030405120607080f0c0403060e01060303091205030d0213090507020d0210090f0605090f070b0403170703080415020c030a0302041508040206030103 89
    0xc56412a01d40100461b1424000a1141400749014599a1070f0406626040c1c3c0c10940c0702108000c85410540080c028085250b40c200c0c03804e103404520001385460148108040c3d0b0400741403e01d0169040f01d4160b0000000c0080310000e44090019260006442e5128040bc480e04000f01c0e07a40000210082c2d40c1c42601944000101f6000b8240b40d103139203c0317200720b60817200c00c01e800d40e5540310188245a0044000c0d802070801549910643c040e03591125128042c2d604400c0d4425000f0682c280072006050214000e044031810130407039441d004500a568038003c030311807000b500482c083c5881c0c2a1403802000c101c160041c00109242c01150f60300c2c2c00601e4002d000d80614000c50740e0810384034405014120082c0303041074500e0f03100ca0840c20002c4106810106038062018100400320000ba0040c04056001c0d400421040001e40c01d541028040d01c200c0f0b081300014000015601c0707540384c00d507004e0400e4804010000ca01580c044c202929400e178142c4001e9801007051004200103810410050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 53098807 1250 53097557 53097589
    0x30b0c03091c120207140708120a03021c05070201090215031e0603030c06131502030f041202070b0f120108010c27050a060f0f08041e02010203070b0c040f0806040b06 73
    0x440c0c4145a40d0359801281c00010085a11091025083e05200e00400c444005001b00d2303000b80001c5404c0d50102c1c0e9452048a04403420b15401040052081d40c083d401101e49206142d418885403a01500085c001c1c0a1020100e1244402c0081d8800e0000d5090a5a204001c64480c2e03030750032031000640da003954000402140c1d06100070000825540014010b10340503088007003460000c101c003486c03d444042c00000d081c14001d0310500c10440c0ca086100f510a4010b9005440c100003416201012820205141c020380700010000494082e4900640001c00407950104d4040c0300c1c590704c0740b151500342d4035004407001c000344191500541004070007494543c41d05184c00c80d0356596a654011030403042d8103911140106104008800d00c55801490624034864140b51000080c074050356103c40e0300054a001d0303d0361a980013065811a400bc100711030b0982d41198006440d80342c8a02c03400000e0b4858002c5000b913041d0281e00244c8544001030442c02036510244540440d40c61206004040032403c401d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 53100057 1250 53098807 53098817
    0x6080c0112090f03050a11160308070501150e06010906020105010315230703050601030c02010903171801020304050c0a06051e09060904020309010b090601090315020d0608030a020304030b0c03091c 86
    0x2c40700080d003101083e005a07101e81c41c0d103600c9403042500501060701e220700419030750304050f00f146041192101118240c1e41c3c403032905912110726003882c40c01841440100707030011029110110340550f898850a104213000d984031159262500d8049080e100b0a2000601e0b024010b210310b0b0405130780381c2101d0000d01400064007284d0312500d0490312640000c0d9020703004203507110180030265a040c02000c0b003900c0540024044116150740c0200900401103004941240140210706a40c40601408500a1003140290f4403070415062035510b51070440c6040c3c2c410072040c000080c009000310152030460290070203e0720601c054105600c541d61145038075560042040102c40c0d01503490b031016501400d4064000142d4445072014030101c071201505060501124400810004070f40e1101481180ea9161001d600c4040d110351003c090842c2d508000b03640c1c0004511080191b43c0000940100da0140003130404940340c890301c2681306d1000780d079a20000e80110280d001c0e00c021542e11300d9050109494a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 53101307 1250 53100057 53100071
    0x105130917030604060f06170402031006140306100810020c0304051c1203060b1803010b06040b1206040c0507030813060609140609060d0209040807020a09060509070306080c0112 78
    0x2840d0400c000c078103003900a01d9804030601025041510802e00070346113444000d655142829000341071182c00501e22100300012400003800c549081c01009489584003a050055645842000c2920300e0a28074a40c001d2040400040c071541c441c0c1d4041c4100c80003007014000103203c1403100c0c4082e50110500900500c810030000906071103004a00f400c50340325400f0403002c0740d072510701081101807142c27580c002c041c01c003070043c0204407000044460340c0c0e488010001401c018140402d01400c03003a03101c01c0d80100040340020340a1032440c01840400c9000041100c00da40d07200800045800c1c01d072811000640922200000134010011150450381900300c070800c42034299103072002d0720241c0d005550340d55215810107a548241803219500070f4400c031030344d020b03900c0c0c42400324160300c520010181c41103080001040501c02c0c614101d581490700940b0300b40e20161106134000c05860f40d4824140a44401000101c041e84217201d00810340e9403040144c941d8003e440c00444135845814115010300340d603081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 53102557 1250 53101307 53101313
    0x12060608060a06090c03052806080604030f09080f0606120c19090b030105130b0606070b040303050709150903170408070306090204060f030c05010c1401020a0801032901051309 77
    0x300701e204409446001c942039003865448000d5408210041050604207000c1c0151f8805409102c00100c84900c0b40110342814850440b01400556103c40818003030801071009043e800a8032482c134241d107464031680b183c0e0b5480c140f070365603c882565024540000c3c000c00e1243c980f001d0b4400944407110202c031030b4000c0c0c1c900010503581e4401e900c070a501282010030001803d980c007440125940c01c50003007090f80781c800d200810a46080c3c20080421030710900145842da929016541525000910807030180f401e4500030b4001d000540d40c103004070302030802c0050943e82c19640c04001c00d0140e03841d0b640f81c51460340c800d80f10001049124480c2c0b20148004941c0240030800d0748000c40c021840890b4014090041c17104460080d0050f1401c084204403c0c8041800e00e243e041c1120000e04c0d1003403c0c0711090500110074005c605900286500010f44842c081d503214210038181d07805000c40001b050520b0854940c03040903544a8100d40c06d10400400c01450701140c140011443d0f04408224078180e9a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 53103807 1250 53102557 53102563
    0x110901080c0108060d060c02060405010c0e0105030a18241404051b03070b160b06040605031b0f120f0c1e0d050a050604031805011b0b040c090501080c0f09070912060608 74
    0x982c1e01f00069002008010030b024003400758409180d0203003020000090444002005071000a2050040c10748a00c07a00c44600e40841c019050903401440101e00070760b0483c4009000b20504041c05202c60901064440c010704010750310380034641c860010800d1070602c540b001d00626980103026414000c0801c0001c52034544030003041d041507490f215418000d41490700070784402002c0c01d458013580c5002170a001c240c400140c103654080e0400d00004c1c811054200044080000569068004000070110003081000040702005500210140e130510030f0f2007024004030203106200c3c020724a44140c40f90700d00b400d081401c1400c05004600b520040c1c075503603c5452420000b91400c50000c4c80c00c1040702482c0d031400354000c0c0a0002440c203044800c0e0306901d422030001d1901c0e0041d02d24500880403e08100245007840011b0000003818455503948542498a602801280c03901800f0240948084c03407034450f9401303120750166107501c0c003501d0408540f0800131411348011100e0b40c5d6907040200c0c501e1020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 53105057 1250 53103807 53103821
    0x4061508010207020910030c050d050f0a03050a02061501080a09051e0f070b0a050315030c03120d0b0a0513090510050a09030927020a05070807080403110901080c0108060d06 76
    0x200c0300160740c8a141d07105000c0d03200401040702c40d400b1980c034800d200142003840c0180484004664581e040107039414198200b0107601345400032441109414020140c1020181010350b406400fa20010303941c48041500051081442500291401c400131b8110f164603071251051500400480741160090510303001521066030700c00c09558066540841800000c00108024058001d062030800800310806000b03808040d102c00c0035100c05d940c4040c0d0b280c50400c6091180c000090458000d0407144c0100c0d211a1302100740f4400d03242c1011a484158100b0f00105001c03a100030b0108400e504188091800410f000041100c00c2e01402241c9a4480707a280a43c60190117000b600003a0094203141c081c14000f5950300400038821042c4410200504003200702006824035200541d40d448268005c440910130b40d08008c000b81404910f10003400303200c1000d4400e981c40b8101400c1c5c0c004519040081c070a10074441c100d0117500c04c090610083d441110210b0f040400134203409001d000310b984007000e480030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 53106307 1250 53105057 53105069
    0x11010908040929040209150a09090509010b010c0f05012009030d0e0907080405070803130512010b0604230a03030c150b0d030c17030c0712020601050d0308040615 71
    0x10126050000258a00c40c2ca04140100c604070754600616091002100c0071400c80f15100341d5011130b400c0d006488102030355a201321340d03c913001e070b80351110a030113401c0700c555000e01310150346048000b81100d141441840e80209050b1907001400c00655103200e51129500c0c0c00721a0355485c0d0031103102e12403044190401700010005a1074580f4162810325203050400d21058081294281040a803922442041500820380f4a088032065849041003854480c0b2540f003540c4a100014040c03000340350345c0540e40203807034045a407850040e5640d00846e003070780c44040d42c0682c052410081080903c0c200e46158a010031500d0400403030244400001d4806072043d0300c2500400e81d0300d12074504006200200c02180810f880d800c1160f89a07510100e0400841c01c000202803106c03118800c0d05221000d10b1a40c102403800c00c54550b41e140109082e40c9a42004004990741c0307c0700142a04224008101d16068032005004401e0340c40305070302d08030350030900a401628465a00c10710b501941c03074080e001d2409405 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 53107557 1250 53106307 53106323
    0x2b0603030c1a010b120a0b061602150406020327040c030c0305100f170a0204020403060e0706020d0509100e0a0801020301061805030601090504140f150a020a080402040c110109 77
    0x40c5a040022000e5481c0403020b0160907140010700224200d8000e035400304c482d0180046a55031440601402032003a103000345c2d44a000031a05490400d00c1901190b00c0c2c0380700340c80b410b808090240c1e907400325024038010030015070828452040f51552280d441036a5907842101b0300410054440444d04a42542d000311000a444000d104d025640601480c1c0e0004199101c07152810b20785550600148054010541b81d84841c3c1c85069101e0010411640a5600184210369a65032842c14230014425541e404880b030042c040d000070303098000300c0d681c02c1c14007041d184c203460541240f0401241c852035070203c500340b103d480510012511041d4072040600fa40b84001641d95050040182c01902c180294110703442d901d02d0140441c0c0c078007084450444061280228107a110380c5404010300700d0000451001d8490500ca40c50340207000544a002c1240ca101e2600054941010a41c00c0c1d00c9081941008281011701140050900e0b034004282c1154500e81a02080144040319094034444030094400c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 53108807 1250 53107557 53107577
    0x30f0b04031e0c03030c120e0106080f031201050418051606030506040b010e0906061e030103110604060804032007080606030d05120703180204020d090c14062b060303 73
    0x254020860103110301003012001500810b004005200301400ca500030f0805803a80c3d6400701590052821031b9071842040b206010b40c01c03c05c20054020701c841c5c42030705101d1054840e04540700320040200d41d481002042c0c01e600c0f503030901c1c003840701800762007400031084403540c130fa00b101144d030a03ca26800c502d80030000341501840c00c000102510000381281e44628038005104580e680c00c803110a10324501520b204006541d87d0000038014051445000111030544048008882200740114180c038452158100035421354018801203005900817080030401a0700458003013800303903102c0e501140513199140d6401d02140c07001800e15040d0784c0305800c25404401440030301c1c9802d005903407604900b4549a410100d05808002414102a0005051554030284480c1103000802d1620045070060301c03d6544c0e03c850017840008081c05401610481c54510000c110920818048021900014103d5041100032800543c0c5a10781a0580a010348211482d86400586001e08001107000b911101070300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 53110057 1250 53108807 53108813
    0x8090301050c030112031413150f090f260d0903030e04020a020c0d050102121512010b03061f1703040e07050307020303150d02030a0b01230907050c07030f0b04 70
    0x525400307040b00c005890305100601c94a076180c1c0c02d8803055501460541017603480152025001c0c400e0b00450744007400000c0c0c001c2003a030000d0344000b0a4040c580e88051803502100710849031030082c0e01030440b401d00d09580802981060500840070100720b6602100c901c041c0c0103296145c840414144008542c6c10b88003001856001a9034901c0c20405541c15481d10780c05800003034075604609019441000013490700d0007448001d42c107030780300f610107000c0e049400e041c10707400300341241c0d44000c41d0351041119031011443c3c110706005220007200041c006241684580001000c4585103240702c0b20b0f40200c2e4000020038020b051186c01c282c90b41d09020f03655482c1030080d5080110001400c0c40207200c010414088015400000c8030b500002c0f400081070408400800581c2c400b4222038003a50600c9400c0c9441c0c00d00412400c1c545c104c51099141810b65189601e20f90031451044002e01e901066440000d051640146d00608c480e6482d02c040e900050740366985d100044440701c1d0259280404c2c58204020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 53111307 1250 53110057 53110061
    0x711090a0e0f01020f04061107090501083a0e040b04090b090c01180b0702120303070801092708030402030f0312070e04050c030a0f0e0d0c0203010605010801180507050d0908090301 79
    0x449507110000790320f0b05c0c4001840b44c08622440c820582001404c0349000708024040c80210080c00c0000d40c188078559641c80e5030f940c0c64104808180c070b1003609a42c920342c40603000c01400001034131007002880c143d50280c400c1c0c40c00e00e17100c6441d0340c205032142c1c0e6241c201c0c0c1d640c1c4650140c8502c104007600440c1440d80310709107004407a080160500400340242c0180146204402048a0090315215541c07019403001c03030203c0d0180e80010003144408402c1c00800d50b04000480d059801c2900200710141c240300c0c4116242840f00e40d80c540c054240d52a0001086c800001103600c640060100c031050341c411000e4902c1c43d440300c440e21144483d000180701540341d010303200081303001d000c0307070300703001c00d042030a48040d4600c40030345421201c2d40c7d128550605080d054001082d24140802a50074038441040003034805100884100d10a500c0c021b8041619130007900760034140c0300d00c1011407100c010354440c1711000f01009000705040c0b210a00490462598074024115600e100301c0800c0d4603440c3c0d11062600b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 53112557 1250 53111307 53111323
    0x30a0c15050402090f060301020d0c0c0209060402040f180b06070302030d140402010909020d0e0d090603061a031b04030203032701080c0a0c11090405070e070305010b07080711090a0e 80
    0x3860074200814000542e4424035030365000b441100f9252025100c02e00001d00a02c10188052401d5040456400c003268204100307800d0300c2d0007540d0014260b900e07041000200d00c00d40c058540301c041082014085014081d00c03200d4022035440c0c001034800d076800c1c009400390700050f800314010f900004482d504030b4000c1c01703108800c1c113075080b2160250600da40080c0c0b00351154001c4002e240c0d800b10300d80304101e2070354001e40560324800701983c4605014003c0201000420f00540c0b02180c10a400020380d4007a041162030076900007034116007140c9401d5203181c008800302c010064a12400c3c4004000750b0b030140024071500e1407041380200e4100590310503891404944802c141402034842c00c206040c10103d08880b118009885c003100e201d40e40f8902141c0200008041c1c0e0340110529081004020300014101c0541c0e00c1180d002909580301e50302181600c409000e81e00e031812082c456000004c604002a0a002e80728003140c90035041201c0200741006811101e800710030713403140065032030710b101400000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 53113807 1250 53112557 53112593
    0x10060306050901121b08030301061403160c020a270b0d020901050f040e01060b0a17010b040510050c0318040b0a0b03010b0a03140c0903010510050108040b0711030a0c 73
    0x404114580000522542c00511030798900c203180d1800ea804010550720f030a520f6202440d411040c07541c552015035503d42090140c1400b254201e482804052241c109480c895148400c070fa00360303084682c100f180c0300c184150040707801201040300401d04051004950140c5038500d2404200400c190030281c2c141c13240010031a0052100d8604040035841e40b655050660f4015203e48400341ea000c00031400a011600829003154680100400c0380c2408038002d01144034181c0d524200d10b241c01c1c4007480340e00307403e20561001e01420482000182000590340f45003007140e04250341081c010070a00740c00c680c0f1403480007485100d800c3c80841c00c0c2c90a03208144404905070b44000000c0c0c245200c1d0705c0031744030600407034030418000701d2100c1c40c00b0710a82004116180244a42040e8180300240001c41e0b0032103940c2c1440b81d400c000005142d45c50642c1800111101655a4070590710b85845a1070501c2c030161010301000b50703002c000000310030100300821041410741d4520168203054200141c1c80315288084da = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 53115057 1250 53113807 53113811
    0x70c030f030207030206150609120601030b0115020604030807020304030c0308031006031a010e040902100c0c0b030402210a050706020d08400611031503011515110601090203100603 79
    0x11000c282c3c0000c083da480005247e408019071000340002c0d410340246891f003984000151944000540302151150407a44504010041a621010440d060798200e01214005038444070005002c2071180580d560000c41500550f407901d0748946a05144465507003040e0341c408800400d102402c400310922600801482c07500b007080d0181a1042000e907c04206c0040c100309066004400a41e00d0b0360055030165030090150400b2001510003421010600c0d4059800b16001003000910410b158120380c452540200034070b04020201da03013905c0860f859010401103120b071154603800610200060341c040c2216400410382c0000c0b28a0003005240000c10400b07208204103000043d40c0709140081d008181c582c00d0020b0781d202e0b103020b41070240c100490040c0c1090b052541c40452240e1110040d03009040900510403020b5101b418507091300e140743c04da1002c21010280820100400410707a541241c0c0030b161140c2051040003180d89007444c20b03040314001d1a40041408481000c9400e039500902242c00d003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 53116307 1250 53115057 53115067
    0x8040b07030f110613020102011104091e0207050a030c06090b040b0603010608070305030f370e03060f060906060f0705030a080f040b07050906070812010e01060c0807020423070c030f0302 82
    0x40d444d12900d01800440d241d54540103a441160700031f412090301480214401034845a450800c8006400d5065507802c010041c0500940214030078000c0b51900d582000c014034808641340d40c2124003012401c400c0d03488a0b620120f0350000b4226842590042d80622001006407d2440c209800c41c2d40720760110b40d00340d000c102c0c20800510040107a4800c80c0d20114616164040003086c0304030711042803501c000801b10304400d8254243c644468102c00003099850341441035000081c160f03155020360310100c800c0391020000b041454408496540100c001d40058108040005907104076080322104440c280c002050069000e64030400f1582d000059001c842500c0c242030301c0c5c4408038000a00800200100080c00c1100c039203481080341c01c05544000721079a19114038042c0c0405032402c0c0031b014680d551030000080c0032485108044181a08103100c1460720105908010040420203102e542041e0455041d10040d440c040d00381740700780b0036500c1300404140300d454002d00460103c0e041506040c4103003c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 53117557 1250 53116307 53116337
    0x5010f03020901031205040e040b0403030c03050c2d0f04090c0206190203071709011b03020901120207020f0405010b0d060b0f070204090c0305060a0c020c040612080d020708040b07030f 81
    0x2d5101d04494001303036842d080f5555004211128400c903001070040312503078018401002440b0b102588181c0c02690200414240c425041781a1101640c2006071000c0070f001e800313042d0560544045420010100034151190b1070800855a41c02940f07603130417541c4020404000d080c895004040d4074401d280301034542031a015082e050f4054010003101e122641c04030019946134056402010207440c0d15494480c9880c0003d0194064218203179905040c1108c040d1a9010034004e00a032a41810161294a00000140582c00094109000070b0303070b0040d0030002d04411616a0310030320307000e081e581c464281c1e102104c8000300300303841081d030001c000120100300e001c0780310141d28261014268115400b0520f41c44500306905402c00640015145002d950244804d0700c0041e0b00030321240010340c0944a00041c900c0800003140c00c0f51080c84c0100100d1035810740081c1040c80203101c0c3c0f0a500c0c0005081410b07640742c034645500b1039000741c4400780000a00c1000d0582103130350052410390610f030010303454902d14 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 53118807 1250 53117557 53117569
    0xf01020a11071d09030705070b0702010f140a0c05070e0403030e061b0301030b0a090516050307050a0b03040602090604080115090b0d0c06050d140f1e010b032212030902010305010f0302 81
    0xe60f002c01501e0f1104045a22850705100301d580035500b041c1120b040c2a01c500083e045a400424100e01140040b02c400194500509003a0750080500e401903050050003071041d541c2412103141183e1031301071144c01007900c01c1c0d03c0f117040f4040c038000d942c0016040001b5400702e1500a024003811032045051400b200414881c03c00ca070706607a80403101e4002c1c2e889481c080d0001e82800d10300200f690051056040d14241030005000c01c80700c003101150140e5540700144180182c150289030703480601040080c002c210180c0050001cac140207044686001c1d5600d19440c2100c50048404a259481460400000c1d140380101c19031890220b5080002101942c3e074000f010119201d03007024840b01141281c04613990340d009040b603100030b2406030298901800400d241c00000c0301e00e00c011a040341c01000580c03416044060682c0c598090051460700c80b420705000e202c4280594861040c10341e24980001108040d60450303444641c0c0703002c9030500d241e00c0050305030340b4141c00a04078680300c0d55003000540c2e500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 53120057 1250 53118807 53118839
    0xb09091c0921030504030503030a0e0111040b0714070503150a0c0e0f0f040f09140105070201090f0f1502070501020d0e0c0a050f040b0d0309030b09150609060409050f01020a1107 78
    0x401469110b2984620f800e84290250354400340c124000402003020203515604244030f0504000020021b22948a000036554011800390041400080c88054009843c1d206c1d86200210500111802141c1d5080000e141c1440d42c408034202030454403c3c82100602c0f030240e080038880904144c000558148040f80030281e2003180b0300e101c0d4600c8006d480903a115a48405182110300500381b01d071071031030700307003001d1031400c0752415121903181c2030000d0311462040c0b207003098499005078140369100d0b2680725841d00303070010b80090303c2c0e8105c02080c0c168100d4841c4010700d10540304030005a00e0322880120402240d214135031080040d00700041d4405540e5809030554142c51003183c0c014500310a01020a005001c10300c270242e086800b81402d2428507410140b05000c40c3c1c07007585000107503590040c0441c0c94401c4510720090700c42c421004a03000b8a03208010b650301c001d006c0c00000e440c10403500d0311446c1108040b0b00c1d81d010f07540043d840307942c82c7d0300c000800e10040e40540280300413840c2c6031050440401d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 53121307 1250 53120057 53120099
    0xf120f040809220c03020715091109070306050303030f06040b1002030d1a040e160b090f0609030a052505010903051b190801020a09080a1a0a0b09091c09 67
    0x101c4620038030480f507040050b1007100000b0014040180000740082d07000140030f654200b041108400e460101d0b001d84261039a0045009203c0e0350001c0a00420140181a58080c5034a0318808149a2400c02c00780d40700b0214071401030030500f8200c09020484482c0c0807080e005403442448111040d40010442e041010096000203942c540d45040c001044008203040341d0050800c1c0d080c0036100030000d10b42e05107800c0e070651307005030507901e1140710340d28414088030680210907001c1c00010781c41e103140948104200541500c0f01025281d07079a030b0414812030414410000320b80c09074038504420700f2011010f00807c2c20515074290031503c60719603400b82400003083c0001c0d24408034603a81c95040c40c0703440c1250154901013480d61540407940c042d4200007010b41c00244640b4002a01100005a8013502508540303d440010a40360300740902d40801090010744d1a141c04914580ea2520000c4c0c034403845040d0041c003000c41500780c5240c96412500d0034001000340b0f4003020302006007826101085000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 53122557 1250 53121307 53121319
    0x40f020306010c1b1208030103060c08100311062101060e0103110d0504080405060f030a051302010e0f010513060903020f030d090e060a0905010b07150c0909090c08030f120f040809 79
    0x13662141001c403d6015040741d00c00c400300301d50502c20132403200c0c040c42c1030383d120f1002442200e683c464101c4a00b0000c0380c19030401c54942d241040421000301101e00103141c0a4030b1585840340004000310300d5103103402d080c0301c4140010010040c1c2c1e940b00240c10000042487d05000d190f031070300e004c2899401503085001c03100d503880000c1807c0024000c1214018000602115150304103941266030540007220a030148909140024810000c0b079442d00310320700d40c1611107508074201a41841240020340c00228140101040100000c03480c80a1000041000c0e56951100c10704500c1400040d9041d00c01c3d49019610049030703840200d0b00f2160490a444840b0100c1441d41e807010700080301106544c0c410003000c0c0c5130000100700003240348018802c050181811540d41c902110701c0c3c13000c032078a4100d0740780040c0c40700c00d091140c120703141c02c420001801418039000c00c070784175100300342560720800b0524402d000000318505141280742903558884c403048504140c40c039098440709100d1181f400d8162241c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 53123807 1250 53122557 53122583
    0xc0403020f030f0d0c050c09040b150102101e150e0f0406020f0a090e06030f03040b0d090606090504031d031b04150b0307021608070302121002030c09040f020306010c 73
    0x1403010400f181d2240400c500b1a4620782104c0d0000e8104400c000d001d44903405803030082102c50500c640b540e03000d142c1c032600c1b900003583d55000c0d10070503601d5080824118007030750001c00d144807031303c2c0212807040d01a810940c00034019070184108541921600c00313102d200030001002580c0300140302c6039010404040035403465031103242890091081c0d101410f0000c001142c46002142d00ca5201c805450300c0311002642c0d03490701d400309503440c01c40d00030f141c1507030f801040180702d0a00d04402521440d9281003021a011100c0d540c0d1000303403515a0000c0c0100e650301d80400051541c450004420711030b40c0b001010705001041e003c40d8a8091203400c20090181c0c60544560326251980a004213014404036080c80030740700d401240c500e5109451800c014821400d030800001c0b140390421007114810741c001c240403071469082c0000c1444122100d0340324091010000319005036070000310b21640c0c0031034602c2d41c1c0d04c1c02e5004000c1261500034506500901c10320800c1282d9030002460420180c00a0b0382041603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 53125057 1250 53123807 53123809
    0x3060b09010c02220203071d031e0a02130e0106050a030b0103020418060906050106020d05090f2107140a0e0402010507061e230a09030801060c170a0f020111030c0403020f 75
    0x11342c1160f031200e99030105500040168890740c045c5000e0200707a03031a03404069940350316464010b50003a590780d05400104403201c5103c08803421000340d1466030140c50f1603d0281d00000c14035051061041ca13110b17198004d02c126070354280728030300240104039181c00d461405c641f680d040031401400000d014a64520109000160008410007d15408400ad0040c01110303e444800341c0000e00c6003030050b100c0c4107030918400d802034003030307401c00140504a940340e44100c9081110f41d6101d008022800c014132150b2502009086c0110801f4011031045070100c003d48500703110098041e5803052404108041c24000140e900c50700f03c500d46a000900821418450305c2c1c110300044050810662413032511003000c1e031641d003090004100100c00543c05d0140e0341d03600c03000e00030b84100c03800050010382424011f000343c9020300e0001000c81d02450030a03000042304400c1c40501d502101282020a507003d07404180e4603070900403022201001f83c0590f046062019262403103014500000f4850031840000000e2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 53126307 1250 53125057 53125069
    0x50703020d060b090312040b090d060f091a0c04030b010909050c09010f090f020307080103080708091809010518070501050a140703030603020a150206060402030402011b050303011503060b09010c02 86
    0x65001003000800040782c3c1c0c2c9080d400e16900c001c810a0081c01000100300d102020541500c007111183e00c8414a002064820000c113490302a82c110f4060342d5800c400407a05229102d4401d60300e00c01c440e4849410b05902ca1441182001860309000c42002c01c003c1c00014544445207044550356070001c980414680340403030810303c4100e10650410b0743c0b0400091110a401e011004840149100300696030309031075090103a200840d80c0c0c0d0046043c5c03d0041000495510040480c40d004503000750400d400702e4002602c00080c542100915030103581440548002031050384e0708048242480c1e001424040b440a0701c902c07091080714107020022520301c0350300b1f02803140c0c0302c0000100d600160f07032039080b403601400618660009a00400082e58007140081d24184040d060801540040840b035440c042004087e620092080b410800869080d0b03008041e4200448400740c410005940c81c2d606011071104011181c40c082410542854002c00c0040340e0001215194502880d22403401002400402d42c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 53127557 1250 53126307 53126317
    0x30d0309030c0b071d060c07060f17040606090b01031811011202032412060c0d09050a050d030e0a0317070e030615040606030b18060102100c0e1804050a0605070302 72
    0x2040064080802c503c0740d030b00c003000c601c0b01c0441045c1101003400602c107001c40340c02400e107210340d43da00c01c480a20103240100d072000c01120481c075041e0040e640004100001400943c0c0032526542c840605000f500e00c5070068420028081c03904200c0301560200c1d02c04a41c440711005810340300700d809444a9640b02e00d4454000d000b01240540d540d00b0b0094100100c910542549021050b0780404150285012070703001d0354480b0840020880b81d20382004c000c0b40d6901c029035000000d9980c01500c00041c0040c400802c18500400c045c042c0d1446120700039081d20441c0340807400c00d8002201800000fa00120b0b0000e010350400d00c0c507112941c1f108000d44000b80d41e1019a507162003440100050120364001420b1035150030346083c4503c503134459050701510301c14074045910512021043c0342d044154500305034004014411602c0001d114280c040495036944140d00014980e5802c43d010303401c00444e50254200c030508407030340901c2d068640c1c070340740e1742807013401024581c40b40c0c0813070034540c0b0070b0301070319 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 53128807 1250 53127557 53127563
    0x219020319021c0b0f0a020307080c030c0d05010605031009020901050a05130302030f031c0204050109091e0c05040f120201020c190305070e010611010902030309040e03040e091515030d0309030c 85
    0xea080c1c1c02428642a00403040b560b06050840c602d00046c03103080d041c020343c1c0c0201c02546851a00741c950705088005038000a21481d4220340c2844332000421060103560700070304064039166924108028a6440440c0942009111742d004015054090742d01101319108104145800f07921144004000c2c0190007203644040d501d80b04000c7c1240910a0108c010114a1003100d103001288440800450130780c02588141c601041020104010704c0c640c03030b00000385a03070217420000081e1a09034074210440311819864000030b1030200d014420138480717448880c040d00088880c100039181031b600003550f801c030560314035000d0722074a902502000c01200107840130359842810b81d4140c0342c43d1141290000002d114600001301c01c0f020f9000d001d4818460720030741c10380103400b451800c40321a05100260200001840813440308000004129146001d803d000340300b50805000500b5401c040854041800380800c540007040038003c00c0c01d50790001e81806440050309021503a00480c0c141a24007081d001405 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 53130057 1250 53128807 53128849
    0x1020706020405180105030a03050c0a1b06110102040e04031b060c02010f060e160525050307031403100905040204060e0702010b01030c020c010c11040914060106021902031902 77
    0x8010442680c001d071050361015545040c004510822500020600b0311941d50541c020420450200f482600180042c100490845000411982d2190000c6030b2a481882919908a0042c4121035104c00c1c1c48030034038114002076043c542401c402c00610500074200400340002924040c00000c0074440714030811703411140030451024141c0340a80688840d156400e400d6191840c08280840070408550003604507030403108014458400544165200c017039084980d00803200c0140c403445003100c01c18419441000a0364441c0c4143c6000341c00140c08482405c2c400c5424030811190128030021130702150021140400e880c0c5031030010034000c100c0703a0802c80011814400700003d160b01500070740e10201003a43e0400420041c49030407030700c901c850142540002ca4080504001c104460144800424028030010341031500782c0d1069550143c80f0940d4105411070b40040285a4041c041d40c80310304010700c0b00288099107580080d80780d483c440703001c5841d0b002c000940700541d00e6010207051b6820348100b403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 53131307 1250 53130057 53130067
    0x51e070b0310050405010b03131b05030712050d02010204080a060f0209040c030911010207120201030e011506020706021006120f06060e0a06030b0a0b010801060f1202040b1803010902060d15080102 86
    0x312000082d040e002c0c15015034141400010401c4107802120710503005003100c54180a045c0e5504a40e0710020054040096401540403c596506201d00001070002d02c0c04242d4201041c90300906101c07201e292902907900c140300800440701d0111b07404141c1a80542c00161b080e135001442d2009004800b1900e411034a04440040601d41603800f2011040c020b00350800704030041c02c01240d49608034015040740100300c510510040d4029088064030046207000030800445901c495444200c1d40d40c0180010f901102c010405684c050100d6114000f03d80e4041c03261b1402d00c5194149859141c8006210340b120210b0308090003600c0e84558003510680348440c0080c00c200c421007001d44524001520b00c4820800810462003a9104603060b03041c040c0c50b10280c0da8604042503034202d401000c40f000f80044403000ea203804a90340f004001030030f1003402c00c03a10381c05002052102e441021040d01e00030380c074182818016035211000d03900c440555140c049004403454042404034503403517005584640c00031075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 53132557 1250 53131307 53131321
    0x7030203010611070503030405120f01112d03070815120c1002010203100e09120a0804060b01020a0b16030603080f04080c090c03060603070309230607020a051e070b03 73
    0x154101c030b5080c1e030b8a40c400c24000d9551510340c1c40e04d2191603450361080008100a00344044010807240090060b50422801c0034101403d44802e910284550715000541102d00103c8040304a4940c1c1004260700d00c1015016001619100c058042803e0103900b20008941c0e0840c90000c00c24100040c00360171880c1484446a5556135100300914854a50820030b13000c1c09105200b513a01c103606903940c8142c0c0f580b4201d046482460081e0500019000b900702400007503101c2402040c1c1080117540e00399007440d017414030b07004841402580340e045411141c61807000c61071a403c1d01e80c128159070036980c0c2d4082c54842c01c1d0000c1410764001001c114010400172a11820300010740300b100e6015044e50b0300342c3d60560402002440444106904030340500c0460282d0030a0009183c1c01407141c10b0018504045490704001c00c60003c01e0681c48140b424024250b40e00144041504100c0c0f500060403046e5103503171000c0c3c4450b03240e402288803601540004034080c104001c008018040b1281850340c0c0c1c10244 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 53133807 1250 53132557 53132561
    0x8152509050139020102010f020a1d030c03070b03060f10020a140c0a03030207031a04020d060b0f0d080316051c050402030328080702030a08060105090a1701090302010b04140417070501050703 84
    0x20f1401d0b0b0155190842c180c450f14101c0c001c42e0280300c0300fa59a510081039840590740301e041e4506840383c0500c5070700c810345000e031001c0000c0d82c080d00d8403140c1c45461340703000010850341b40408071100780034240140c503c44103203800044980d00941d20500505892080024251404c2011155503501240d40c010010a0603004100302050780d003c0c110300e81004440341c43c070b24448202541c009421007031414008000c1007959014180c07116005014090700e200380e0b000603070901e003460380a2b52440000414002c1102c0b4100d14103502c401c1c54186542410000c04811640400c44241ca80c03006413038100040456409004071448036058140e002c1d48044120300300130380c5c6032221000d04003083c001804034107000d0001003a0fa4000c12282e9941d101c40d45c5030001110281c01000304560080f103407603000b140b0103010113440b800c581c010000000d60541c0c4c82c00c0003420f40b4a0208464062890001c529100d0244180819070040d04440c9824011071071014455052140741e81c050169441c050601120325895 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 53135057 1250 53133807 53133917
    0x40203150f0a0302102a060204090c020c061603020a080a0504150203030f01230d03030b031006080304060503040201050c0102030103030207050907181509081525090501 74
    0x180c6918401e1100c05003071208101c054000a5801940c00020103042407203581c501c40c1180c112000a04505001c2074601215240044200d4425402250500512440c2d10884030742480920046c4040000c410104040d840740b035242d03020701d61300714600100781802000004003150380407a425581d903454401c02412034200b405045503a4030b841c00002c0000b4030000035640102003000c3d4030b00b0142d00e0710f810f03940d02e020070803140d00c80e401c50003180510555446403080c185030b020307481c0420b03400144170405040c4591000040e0b00d0b00c0c907000d0240a07030b450000c1610300765402400c0c0103959807214001038903280600d02e050042c56000100100c20940c1c0810b40700c088910665010b05c86480b12a4195410030080b1082c113040c041d5003030100440d03a0400626600f14105081c0320150700d1710755a000d42000020130400e000020080144540214080a860300d894140540000a040c00105c01440541c40b413140301c1c100f0900c0d80301800c00300b00411502c201e03201c0302c802190034180c00810002c144104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 53136307 1250 53135057 53135059
    0x3010605030f0309040506040e06040c03140106060c060507020304030c081b09090c0906010e0406060302031f03020d12030b04020a030905010b030f070e0414030a08040606150e01030f090204020315 86
    0x8105000540d42800650100100003000166003042c00000c140402000d008000540c801d8450300301d264103a80910610b4002c0e800360380340404d0789045042c000b4048052152140407685460010003030303070707a0000280b040d05038006008100e40e1241c10b0124070718040c2c0d400180440f44812000140740e10001139031102c041c800185190b860749540104048103d045404950b00d400501c0c0d604243d1815240303e980c050302c1414088107144980c0003140481c4c0ba241c01c04808694004288050540e440c40c0c080d8034000700c035054485007810341c3d0110310a041801002032045085040749134185000c3d8010f0107520901400440d190030390b02e48002c01802c046141958994030300101800103040c003203001c14600103088000c2c89158034021090051180050068443c09140b210350303424460103100800784081e9541d0b07003d86908260400e80101c440e550302400d800e41244034403e00d280e801100c028044082400e0020b001e08112000601800854030000d50103840041000b00b201e9031401207180c144c078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 53137557 1250 53136307 53136311
    0x90117010b0f0609060a120c1808060903040605030a020915030105100c0506011701020c070305010606110a1e0f060c080a0608160b070201050403050a030503240d0314040515090301 79
    0x21040074031a482d840003510580046007044110b9050424500800c1d0040c528a000c0740310030034040189003115944070320310340080d4500005440c100700c030300b80c1400031785031500141c4000e0801d01c03880d0707607288191700c1840144000400002c1c050401a4151400000301400740442d400c6440307940003042e4401d008040c4160041c08400c0c540e68031a0582c1100780760b0240c02014580d08010030661004c45c0340000c00002c0d9000c00217030b9080720045c800d61005500c6440085030b020704003500601080312032062109140c0c80b1645400102e810200d42d6010180903004202d1140040e0400340001100800080c1c89139080c160035100703d40d80107812a118030900c1c0383c01c02c1115242c0350410703100c95501406544d000d0840c2c205100810703130382000780702d014414101980740c01d95035902e460a10181000c02c3e0041030011040212a500000300b4003459071400a15078400f01d01080001c83d80301342c0c10406070030002002503510b1403c00b100100c4020700002026041000d041e011217211320b5004a10b03484c0294 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 53138807 1250 53137557 53137571
    0x15030c09021b0a0201140c0a080711040c0203120a05130204021210061d040b06041a040911040602060f0604020418020c070501020106080604030e03100609020a020706020c01141809011701 82
    0x100002c41c0700f4049039030503911041e0420130206003040c40e802240b0808080e0188004c0c103000150302d0801082d00700d121706120203505102c0002c00084990480039102550820008030015081c0310342400c1d400102c07010700050503207075420416564100100001d40081c400114206000c0959941a101c0d07150366400100c002e0302d0340c1c5c0c121a24580d00c80740c40c0c8151000710000701c003454560090030060401801c1d49041c0f0303903a0a0440e800f10007980b00403c0171000010240301c0315000e8050702e019242c104040c1071a1500e0400002e5540070300524035001c0014039008940c2c0c0e5615a01100c0080c00d10305140c0801912002c9800003e42c8076902481f0340e44181c050010360741d40180251811246100c010348115a90340d1416102c0241c6c00c2150b5900d40512086d89503080e900303104010142011010050700d83d210b2110291400025410900555014501070b85507a039100415034006102580030944401c0040902e5090082c10140c0c02d502c100790f8000400c44408200c00843c0c940e440343c0080c0300030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 53140057 1250 53138807 53138857
    0x6040e03040b070620040308070b0a090804090e1e071d07021c020a060f0515041505060a02070f14030d0504150e01120c0816111015030c0902 62
    0x80e1140c1d00c20b0420381c8500f44103200115400b948840e40701d4122000e0107205403010040c82040707a216800488401c50007050100512455500856101a00b410208108c881c1c3d51202c803068040ca12803500c0d0a0b840d00c00b40000668148840f5908000400707800f40a440398001194490016004408400e9150096103807400c07100c4102d540110040c1e00906144031440d02c82290f421400305954007988150040e40e000240700d40b00703080f90382079080070018070741c10329252074805200d41c20720880c8540e0030000460703000c0c200c21203843d00b140c0081768880d0341d50104000c00da00303000d0207a100014006e400302000a4100210f4443c00700c04008406440d4030040b42c880c10b4400d40101c0c010341c180c0150414001c01114001c01a150114805041210400a0070740146080c3c844140391140060811424040c1000300740c5807d105941290900480190890205907a1140100c08401303525455a08000342115520b0084003c1c50300320085169680d2264014400380d40401140100c1c14861180d034080c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 53141307 1250 53140057 53140063
    0x31902011811150406020d030609020901021005180303010b09040b01050703090b280e0301060609050f040207110a0b0a1704020f090a0b0d030315050301091e031b060506040e 76
    0x190300c8074420410741000c6181c840c150120001a22540c0055880d0402c8500e58015805400140032650050289901003a4024280c50507036100040c0103005001c0c990300c61783c021601030404851044002450381e144c80071300e41c1c00c403a41d0104182c603000000c00460385210080050411040039941805000800f038011502d5104504002e03001800c0002c0501042c4221001481327400b241f04050140502c820002c0082900400302c4140401c900c0b10100b00a41028051080109228109022018605808500c04c42e10b41d81e8020300c580d0b40056614100014540c8601032280041c1603c00441e1710752418803002c0c0c1c00b045020f00480c621081c64070700c00074403660b41e81c45141d02602d01c4518145040500c4803039100030b8200402c03280c07038041c0240c0f07a407900b1007150440c1d80640e0b4046040c40d00f20f070044c10b9403906030b04050f00136410f02e0651004282503081c03606010041949a02202501c3d007070880b42e00000d20b8411341c510810b41c40000502040d80c004074000c40c4c00310340401c01300d00803507030b4156 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 53142557 1250 53141307 53141321
    0x30a061a120a1d1605040501060509010305090a050604030801140a0b070807050c310b090403050706060e070305010305010e150a1a19030b010905040c0b21010803190201 74
    0x580a00700003204149500c15050340e00310030182404210860301c440b40900d01e000e021000007590f44481428400c104810104000410068a04001d15410a64000d1141c481e20146605140d1100082440c0d81030130401c0944054000c400d03191181410718004105950a03c5425850034010032040f425240c4814103004a8007000441c0d440d100017a0340f0540180c11204003a40c43d8003c0384000341032510f4002160f0321030300e5029600341003100b030209080f18618007a00c41e21642c1c0e103416150700d1320383c880d0385501c0c5d04180c16060081c0c4842c05071400c003010301007030b8000182080750701e404c1c400b85642540200d816a803041d0b00a0001d09540300c001c9036039600408500b91090381d070101240074980c05da4468600c800c0d90300d40c418211400b840128100102e000150300c601410181c04009005034160414054440c05109000a0406441c1c05407156114021010b00360800030f030300001e01086000388411030b00544000e4080d50380da46821500d03500082e100c582241c584011540d841441031140c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 53143807 1250 53142557 53142599
    0xa080303090f012304240615230705160906030c080a12110708030c0c030c010206040302070b0f1603030b03010b0d021503060406120606081501081b0a050607030302030a06 75
    0x8130311241441110705940500191442c41c07402c0142c5840c0c2420302c119000c08808400c0200b41103203040700402300305591001c2c1c402040300c1941d84416100103000145001e00c94440099103404c810305002e4103220f400c12220644c9068040001400c400680019044034060410008102c0c0e40d01c05090322044500390080c00444881c258845480c001d03121000e15680c1070b0f04850400742c6a0068030700c0c6502c0240e10005030b5200304540c3c407451900708074203a0502001e10103031603581482d40e0040d60380d1005001d030340d282d040082950029040c201c0d041d18200301043d8a01800f0603141d0a02600510740c0b202c0b01070082d420b1511160a9043c00403000c4044c1e94007502c1c8191182c01c40442105580000e01003a42c019112080040c0380c4440d88001940709000c1c1c2400514580340a600d82c0c40c00300f07000b505011440403000104950350380071805c0301e074108409617075207002030250f0005101c50b0005d40100350b101c50042400c03814550f06901540c41207810796020401c06440703d8183c42c4419081c9003070b07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 53145057 1250 53143807 53143841
    0x250309050c090a0b04020c01090212011e09020607020901030308040213110d0b06040308030705040f0501030902100302030405010e060c0d1415010c0303020d0504061a0904081603020a020a080303090f01 88
    0x5000c0504011500c81d5100e09100e8000450742d1038100040d044e87e11441c0c00500513034580c1c00700382c19403800f41103860403da40000200000f2428115900c40300540c1c047c0c0d61041b5a941488a0541d02d40c1000c840c51030b54010140c0c960340d03860b8034001e424010240c4090340903000f88151041200818858111105a140d882c0c50a15031449007000180c10f03c111425000081404000000b9a44102441c00780383c00d92a00ba49660500450242ea13060b2988410704050400303a2807009a1980d841d003650200582c680540c3e80d0780c40b810214003400000c08030295610403c0104020460140060003902c4c8505000340540c6145041184240009548801580d01031820b4120258020502c260b2094403d00703015050004482c1d1801c00c4500c00c0b40d096408644a6010244c828072065a0401c0e5540844d0141c2d4141000d44070482540941d503080501c6081d4545c4101c00d044c000c0102c00ca00d40d50040c10030304a2a00c80002c0c4d512500140c03101e1a05200c2c1c4a0b80464142041c001d000c6000807504d68 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 53146307 1250 53145057 53145073
    0x30703240614070309080609030714030301030c0308070813030b0709060207031205030405072c07030c0c08090a030203060406021e07210e060c06070206010504090206040306110f0325030905 83
    0x84050294819071080301406500440042d1b4854140010f91040c1080d1000c1c5480700e903070b428010006148010144c941d6001040140001503102c2060003d89801c007501d00d440b5051071070b00320014412650000146400b5400c0001040385d00030364140b02c0d1030669150030307425541d100180c1c1c0e0f2b219103001c0101041b40c480790780f01005200d00b000c2c55106002e01c1c22215000e5603110141000b121140c0c03000d48000080340059845440901500e4000343c6615042001a4100074000d11134128410f00410700040080c3c03a181d581d60300242400550f800400307451440c00c00c2d282a000a40c8034044032074a460584041c0c203072100c01001903414860300b28030041450518001400403911030140d0360030611050109130b0041ea02c414000d000c900004100404c0d007400c0404001c0d2410303105a10440c421424601240c0043e1211425141107030303440040401d1900c80d503594510f95004032103c040b10f0040201c2003100094002c0000424000104d00c04803034628445800c900381d07004610044c00540c4980d02d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 53147557 1250 53146307 53146337
    0x1d010509090402011e05090102120406020613050304080d030b040b030309181e040f03030b060c070302040b0301060e090a1a0c0702010c050a0c0801021c06080a03050318030307032406 80
    0x141e0540c0705205240c8044441030490744c0740c5004402480300c04c00104041410200d1b0358041050000300030b0190104c5d42004e15140000b56104001404001030305500310303101081000405c20f640c0a015520180d90070785940c07420040c0102512011544a1800c04040607100e0601000b100c4610304090a800800400b00c500000c120001502c40c2c107a0121505840c034180d45108901d03030046110302d5600700040d0782410300400b5150492420340c0f05410420502803442c4002a0460849a042e60f0200e0030381c01c00300000c1e0050001e948415081c03007400e0100008103c0102c1d000d54907030300c079a40d400141c041c250f041e002d00310b43c00c803080c0740b40b6201000f00c04050340c012004224038a10401c112401c001040da20080e194200d076104a5040c1e4010071904000b41e10101d02c3c1041c480c02850800500d842c18002658074102040c3c00790500c40000007041c1c0c80c10010f40513905501c038543c2126580d09108500500506c16040b0310180190b40c00300d0304101512510140c0c040755010b640701505400540 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 53148807 1250 53147557 53147569
    0xa0302190302030324030a0f020102060f0606030721020d1b0201110d0b0303280201110c030406081b0703080105041103161116090507110303010e01060c1a100302011d010509 76
    0x17003103004d00d0215010b02402d1795081112044581c0b1034101d0018a1020b440068a0042d002e000d04141d19960800c21030a5243d00003540d40c0802d292400c4001098400c00c0e4420355420076176400308560000403010580100c0d5001f10b0800e69101101145020301030308200d003240d004881008079450300b0802c15940e005560405100504010240c0e460075031044075a02c00c0324140e107821000c000c150f08032111403e4080c0714810544080c4c11100380390180100302241c481c40385010780c605104140c004a520150010f800e03200c030303101101032680da0b0305a5040c050050b110134800c26100d00d0400c044800d0328003100c0107030b80c028040c28980c5c00e0031802c110f0b8266106e480407989004030f8416183d2100e1054880c9a02d58028901c82400040d80e06081c003004182e4940350700403c0c00c1b82c3c000c00040041c0c00038030f04140e045070b40304d10f0a244468210702d03240391902030300c80c8802e00c040054418050751305d000c3e03203a0740110b0303200342c0741c10000c194507a801080c601082900c2c1d074081a428020750201e41040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 53150057 1250 53148807 53148841
    0x601090c030204050310060509010906050906090405070803030106030510050a03030c0b070e0d080903070504020703082a0c03031005030f030904090f060213060305090102130302101206080a03021903020303 90
    0x1d0902600b01038403840441c0c544041d0104c001050340c0c0790036040245040030384500340980403040040c0031982c00c0801013065900f01a1156020322400340002e0148401030100030080d007031440a607030f0b407540d4840009000d000c0680d00c2c192241c1c004400010b85107000c142c13040c04c40364580c80304848850b9a440c1c1220b42e5000814100500c0301d0035010380200c0e62104e6607505418403542c2c0d600c0d120038101080c549004c46940017140118810001e00d008286c01c52081c540c031031090348419503403201000c0540d0741503140342c0150400f01c902050f040c01c81c180100103075118482406883d001c403075840040681e0b8581c0c1e00131241c0b949d0010081070b003550a050704040c1015028110188806003a940d5400490340030b40074801c1c01d429104014800164180100c40d00014034100940c2041980c803140c464100292000902c0780c40b40c0001d00040a0041150710740c00e0a10300030400406075614030440d00c51042020480c0140210b03401c6529147c6400103420219805034011410341d03551f54410154a803807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 53151307 1250 53150057 53150081
    0x3020603041506080a060b0607080f0d09060f0e06360a17040602190503040608090a02040603060606090f0b09100c0501020c01021213050607050310080601120b0106050309060109 78
    0x110165000b116040390081c1c1000302003a10080c082088582000d60032140740c24103052040000b0040000031407406000d84030b4420045988665a02000e092240103008410000308aa0700f0002c0070448640386a02003400901c0d62025640241e5600b4aa074101420b88071021100d01c2d04030b0040241c00d0000c1862015116850080324424816512605034201c01c9540f003190300303030b8002002e0020550500c1111203070342800200001000040d52401d0300c0b0700540c000c80f0100016800050a83c1e00b00300103d150a98001d80b080102a440b400c1c00805000d1900442c00452000f000015210313400d03000420881e50350303000007802d00c0c0c4d0b070004000c03000e04c401e40e1207010800c01302c4001000c10000e02c002d00702c2c40f507014001a43d8000352610703140104001080d07207080c410751542c4e0034042180440ea040d880612480c00644c3ca0b940c0d0303003a80a81c0e0700380e07412040041c82410004034102d018058500d0710213000301d520041d0b42e82e132000204c80c40c2c40708a41010aa4006400400000300182c204c00d5075010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 53152557 1250 53151307 53151323
    0x10c110a030209010f0311010f0c0201083106050c090901170a0b09030a0810050315040611070609020301050a0207020d030513030b0f0a0606021b090c0d0203040302060907051008010302060304 84
    0x181d250001225000283c1214642c2100000c0030810007a22a14000c0040400c1c20194940707960800050400c02c550355001e414400000002101c3d1407604403030181e00780c20725640d13580614181d103030b070210754003070b048125146883c281c00714092003200e10548800807001041002c8980c00c1500711000240c0c5074681c03241c0b51061442d0b01c00000c01a0042901c2100040011034a4901d10080200b03941c40c00f90440300d5601c0c1d05c0106210507140400c0c043c8032482d22a403955490f840c0c900c1c0c244010f000b01e190711881610041001c1c02044015044503803014001c80c000c0c400d035103c00541104030310400d14000e5012448407031040c0080d000d5009000015244a180c0c040d40c0e07500d858040340c04c0c1085403562060a038440420045840c1c520901002d821280300405d038265855400540c1490b0f00400c0620840704000007945098000313045401000c1e00b41c1d419502c90509140183d60381600307680b2080343d40583c1001090908002c9440c60a82e1220354a000701a40b840d000d000c0d0750790002e80140d507204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 53153807 1250 53152557 53152559
    0x1902060d020d020703050c070608010501050a030b010c170913110a11121207020d020105090714120a0602031905044e020706031e0209010c0501110304060507030b010c110a 75
    0x400070f201920340395002c1c5c1c0742c0b16501e0350312400290030a01603401c07074402e1000c40001400266440815a103e09426080005c0c4081801e001a1400c0500b0b4200030301d01e91018080c00c40c44c6a0320700181c2804101500c00391200300c3c410003288141c51007039182d172015110520501e640148610502c6039048841c1040d6124510109e0082d00568002c10207038061540c89010f101c041941080b4100160041c2d100030843e508180b164140c4038561403260502032041c0726085a9240e98010b041030014007a0380c100c41071311010f0311303019000e50002c950500f4ad01c4074034a603071040341a640c01101d1080750702100030001e00100100402c6944010195440c8044e8504d8402c0c2c0140407802c0d5909054145d40c1056201d40e41020000707180540b184c00550030142800c01429507415442c01b1042c40481d114005a1079081e0000101c54103e50164090015802c00c036032010704101101c0110f016500a2005201507a140c0c07030250700355444544010b000500c841c40d8000480c5450301401180e48001305403000751 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 53155057 1250 53153807 53153827
    0x7050a080a090909050607140a0f030b0f0603010305010c08010b040e04060f0603020409150f14060904030c05060c0901020d030b0303090f03070b0c0c1e010c080c0304151806021902060d02 82
    0x1164044d03011110f5512203404d00c22042d8201c04980c070407e8600c2d10940c5410b200c1c040042102030b0540001d01410f031900c800d403801d40e45008414401c0340000d001c4130340301d41e03603800d10601070000c24a641d400705070844000304070712107480200c40c25a951030300c44021540356135441c00006c01c0300035600445130303954003408001a9154020804041e01600c11030070407441390b1510400302c602160b01c6c025424070f0700c0025103141c2003008026900440442da641050703613440c00c094500c2d0742c102600509501400081004450104d009071810f4034080c1d0807552180761000c0140c084485025506a040c1d0040c40720715a41d01e003444d00b5003240700e80601900d820541e00c900340c01c03481e044141d0124490704600c14003403203810441540e030100b250180e1200c2103040000300280050260090107084000005158003a01e4000c00880d0700402e90034618600c09141100000c0880d04090410540c03180710035400a0310030310004103421150240018518066903e60801106e540301c9108180855024041a004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 53156307 1250 53155057 53155061
    0xc04090207050c0907081003060f090203010e0a1106030c12071403070309020909060c03060108070e0306010b0408010e06070206070c1a07030902030d08070807050901031506030e0f0307050a080a0909 87
    0x71062240303000340900c00b02d800030003808200c020040c0080000756006c019040012071021000c498020900007018405500408040c00000402030b41542c01c242d0041d0074610006070300020b0034020b2715819492100c60b000c0010b540701c155400c869003a01444440100c18440f0000d0350050041d0900b111000d10143c41c140140d0000ca80e01404079a640d02080107508118226680c4101400050b11991030140c20b401d0840c000a0700043c100a04800010405030082500c100c1c6010003c0403aa0b8540e5220703540e103510740c85802014869428035100220440e4001b403168000c84030b64002d0040d80d950080304990b0300310300740030503190490060130307071031004261801d0f15000358207964020a9a40090040c1460300d2445981e01041051407410012800e1740b007021a50010480d03c1d01c540c1d103891800040f00640342d101c506115161004800198042d00341c1c0c8104413034598541640e05040e1409480c2d43c6070b005141c00600150420486040021603000041008181c0ea0a005a6080d120354103082 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 53157557 1250 53156307 53156317
    0x1206040309081006051003021e0f071e0201020d0e06070b01150f09150806210609060702010603020a090504081207030902010e090c0d090501180809100906170c040902 73
    0x30100d0340c1d407a41844010010303c01c00c18003140d0498144140c0703103400d0110760b4405101074401c0404d0350201b424100d0020103c5c20546800000c40c0c405d4503060300e824594407a42c402403080302d20043c40440b0703000000003140080039842c1c0507009000e0301c48013100d040e00c12419662580d035002100300194400180c010b96181d000e04000041da2403584684140500f60001d00940401482010702d01044101c4200c0d090f0401241249803d8070b4948900d80854290010340a403002d29942c600d01044071050700040c42c1d0310030030030b0380c040700d6a90321940b06c2a400c0380e840380006900001200703020f208070025600b120f41c11074810308102d40b43c030754a19117282d010b42043da0403000207a152103a00341503607803204504200da0f000f11201511824070307051400d4944030355080d543d80301d41c07035060020a1060030b601015100c8104114200c9441c028070f090b000f00c0d404905094410091404164186889070401c07005a07206611416036500c00c0740700147c45140e00a04a0780d1507801000045107840080c0080c1c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 53158807 1250 53157557 53157563
    0x515040e030c161403160902090103020409090305090103060e06030c0904140610030314030f130204090c0b04080f0102041d2d0106030f1505010c0204020d02070b0103020108090109050601060e120604 87
    0xe0a40f5042402c04022401c400c88420302c83d07072002403001e551000700301c0c1d004102d4440000050b40c499901005030f002c0d0041d03600c040d603242d140c5016070003455007101c010311503c503091380c0801080752102e00b4088000010ba440a800d0b074000b400340d5400b81480380d460794100340110a401800703400120440c0c680788049542e40d814240d034181c04c204058214000343e4104603030001d824203614108044c40f40404000b0150300320007222210344019034a40350700035644c0039001103801d602c0c03c2d21501c4041aa50252090040341d01c1080b03015403e59806209403015204020f0001c8100f50b61595101c14404001c0c007107580241842c0300c20388004800610b44030300c0d070120b440d00f4010b42d0715250025044803102c0203644622401c110000b000b20141500303450550314242000b4048101c0c42c00840c000b40238194081c0045440011b894083c0315031080360328101c07403007640d942000c1d550700c0c08203500f6140d0703040004115500810051150500900c0d44500203040030f03045c80c64010070948418030f0104159025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 53160057 1250 53158807 53158843
    0x3050313030e040e1e2e020c15010501090501020303060d020103020f0c01050a0f1d0a030809010209121c02030403170a050d0c0306170309030a15091b0602100515040e030c 75
    0x349880a0419144ca80e00f0440f04014040c0c0744986d07a45490700990f002e40a10900d031207015414071481c40c030350680340c02c490800201d55140d400103994615481080c01190f000c58040800012990710000850340700b003101410117508401182e0040d40650040960b282e140082400b0340b08135030800340701d040e10032094a1300c04a0800a111000c0044030820610b01682d2401c004131640c40c00c40000c0c1c580b05260341454803080c2a0350b8030350b020f070080c02054007080e405421903a854094013000141c10401d40a1101500321074009824242c2c4c0e80d10641c0b100a08280c6400d07400100d05114001402446855080041c50404020f006c0c00440b4401c400c06800319130340f15170034040e000c2c0c403c6001c04941410402149006480e80000740e4540d41c5120041ca0480e001e02a0078004502d60030400665900ca401b9803a4098000210380d05521a402400014814284114580056805824010101c5602d0f82c82d5003400c00c8244000741a950600070036070b110422141c00d80e86010020800e543c85030740300c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 53161307 1250 53160057 53160073
    0x40b0f130204061b0302060613060f060203070219050a030318090501030f05010f0c17040203010e0601151b030e0d03020106030212010207030e0f030303011e0f0f05040c0201060303050313030e040e 86
    0x1c082c4c00040030b400080781039140c031504140042c1d000501c0c9a0881c2c003c0313961403803400c040d0958030043c1034190020011344541042c000340c0303c0d8001004d41001ca01c00c61300015000004012440751030528410303694003104a94007040401d0040c4c2d1071140926918400d000d070309448441c00c40c103880007030b8070480310031200300140e00c2445000c2c0b08203d085070542c481070000b2011107500511a50045400f211103140c4a00454115a002d6100c18002d91205064408540c0e403042d420424850881805011a1070300e0400140091161080c182d41c81e4103071200c000b86142e07032042c03003122000c6080071000d5668550700800543d8890f41c071203106001c008000750b40c40d0007a1800400890440c4a214003c110107102880c4503a00401924195068035605042c03002d82d2100181030b414607980004c142004655010031140c10341640326080c0c48041d6418403940c0d010310300881c00c840081c84050000f032002d02c041441c0220541414450a000340740c965011425100050210b61112042100c0b55101000b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 53162557 1250 53161307 53161319
    0xc0f070506160215070e01051c0c0e1912030305070320041403030301120f0f0f0305090108090a120813050312040204110301030b010311220c11011a040b0f130204 71
    0x101c4c0d51018008038000003824102003c01038404100503604905008022486089103078021544074121410300500f4096030000b02005000002e1041c031490203640882e02c0340f030005200d140034034101da014001d013900d002c0041e1070441c02400042d090408060303c0703001c00c40340e00fa107060002480608026015030350780d14207908032030212035211090340245c10030303c01003007105103101c5880e901c20740221106070442c0751f44c0362001c0510702d91071000342600b130602c0d01c0c2001c0c0b5601102400c0d6048003a00c6142c110b4644065640d0341c0c4100c400e0041c0520828060107100901c140c2c0400d800c5002e05441a0680f00700703035078050a64219490f0310340200d07d550200003c0d45090300507100d5049041014074519411625858040c1c0014040505500e0a500d20302e4803d403039000044410880010303203111110116540c10001e014030302c55040001c0c41e64a6180f1039400188a00b44180407000303503640b175001020303061001403e8141744955004041454114468075025038460b807180141c0c60040e541c0c0d061134 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 53163807 1250 53162557 53162563
    0xf02090f0604230105060a0302040302180405100b0603180712050102030a0b04020412110312040b0711040507020307030806130c0206010819020a09150503010204060201020714060f0c0f0705061602 86
    0xc2c0d00b0210801e411000c4000c3c0c1c2c0011001d01d03064840a80746195a070720304c4030080c4d0182c42103a0000b0340110b28125810040007540404500a602c01e030155465600d0204d440170540e0b1100300a1a4132085c20004a41c005980703119401c0d0300c81c80d01c0d0944800a55803c02c08a640088075401e9a246e50004108100180d84d0311a010310100200d80440c141400c00c0844500940810801000b031031801c0070300f07481a1f4080205012003a0248800c581c2c07151129a500440d42050404039a809000020300301940303454001c0c1885841d030b59000310304181e41902c04440c2c40d08068482504005020500720b01d00c2c425001d1481d00506940082c0b2040d450301460518081c60104c0307180310001010351140c01030b91005038120450780c2c920300204040841090700700d100f01c0660303c40340d850f600c000f50000f0299011740189c100140070780500721005001311165030312880d040301c181d0140b40f04900060342444005d0040d0034182ca40c103000034140112556190300c0e1080a035000f001d2020310712600b4013115810 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 53165057 1250 53163807 53163821
    0x3060c0201020903011b0903030c0512030c1207020706120b040204150302070b010f050a1406130e161b060908070b0108071a0a0905010e0d020301020f070b0609040b0a090f02090f0604 80
    0x540e8001d0013100c1c6c459005000c500a03000040811041c444941c041c00340802051910041090380c007581c07403c0401030441c1c154410740086002c60108000210220700108101d0203e43c20b903262510710947d609a620020a03c0b10070749036010340d0900020444008140c019800080252030060b80d40041d0308241c0c09046050388660341c944100300c01030110f9207a201c0c1400441760004007140004100f00001440d0340030f060382940c4081980f0380005007204860f11802d02500ea40002c0500d0300e0500e070811100c4050098018030b01100800c900d0000450591152048e140544001418212181c0d00c03856080ca0031fa0114850340d02c40700d4248059400d0841101d13804460004151800d0500d85018082052900ca150f05000e40c0e085a05205c2c0c8600d4840c45040f94001c0007159203c115041c0c01d405504a02020741c0c814008000044141c1004c50140d8011034020100000c1c0c1da0352814008082d006003c811100301e60060707151401a255030b160030f405010043c058000c0351401c1001d10040b0b07410 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 53166307 1250 53165057 53165081
    0x270d051b090c1e03060103090b1e060103090203070b0c010603150203010602010501090b0315041509080d050105061e0306010e060a02010b030f010506010e010c05030c030f0c0c041a091003060c020102090301 90
    0x10014403800801168400700202d8520f19641c2d00c95840400580c020604032a000c0c109010900800800c00120341c128000508007018160454480d600110100c0f400520001d4040d40b0209040c06100306074000384c505000c0340b03400407070703019200d90f10360000c9418002ca48218139000310050100540a0103a60b014080080d002c02000c0d01c4080000d5481d4188481c1322110984003000c01c0030310000c140c2410101780b802e44240140d240c54503141c1c0c0541e01481420f4400ca180c10700126261a10f4030495402d14001d00501450601da002d460460768000303031925040c00151030805006403115009010800510b0300001480d4030729805060604402c1843e1810710b92400041100c180c1e004460018031030000c0c81c00f880d054440d8903000c0e20754410401110541c0c070000c101103802c040321a00801a203050003066907413021a0000f0b110503502c100a01d40ac104a070044888824244007403100e50000203050281d21035030361398507400304a07100b4600520050350000b074401d040b41401d010b101d0600032 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 53167557 1250 53166307 53166331
    0x1d030a051b0f160e150913061a0103060b07080f18040606050702030d0c02130c0512040c031505160f0c0c0602030d1401030803040f020a1502060a11270d051b09 70
    0x140040e520504400c5a0417158031a1044002041d01c1441106040c000d141d032040c1d04000060302c2c03407d400a00700c1d90b48101ea002908100380440d0801e42103051719030069200712041d04000f10940d0300040381e08408a03004100c0c1c05980c5040f5075950f03900810b8010041034581036601c0d4081d00501d07091050700040c00043c0030001c8220001621102c61070600c81d090750710000b9000410301e408481c28491001c0341002c0614280c14401401035004462040724415030916411003c0456440e099420464000d0701d91078110900350f4669018660b21400c12aa9190070608043c49a482510b8400b268100b080180d0000c5041c4013224034510401030800c1400c003c40400e585550f5030a0460b1000800c007c111803d000f46050441d12000b41d41005403400703102c0a040c184210800942c1e0b03445c221036103c1040d080550510711442420100c5500583c5181648002062088007000003c2c001c034000f60400c3c01c6a10800110b1801e0000308070510109030000e000c41c05840070400f81000143c1907100400e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 53168807 1250 53167557 53167561
    0x1b030c02190c0f091b03020c030405090f090f0a0b01030b041109040308060109090e030405041d03070609020f0d030818120f0301031106030907030323030702010509011d030a051b0f160e 81
    0x174203150b440c1c03104100c141c0350141c1d54103c15050141180203a52100e900455450140100d02001d012084d1003805464110b641c0b01240c1d40c0c3c202d586404206010704540340032001400440c80300c0c0d960b654882d01840b03078515080f56183c0815902a821a416800914500c050007001c0d03034403205c480d00408218506001c0c0e9490082203d46a101b14800c10707220f6681d4444100d0b1440b06040600c02d0341c103400068948824080c140203018040400c02280300c0e1402030084140d80c81c20454800915415540d441c01e1980c1f090083c4142103204200c04810784500c2e0100300c070400f402c000528140c0c00e45902d1039101e502d54a00702c0e50040c10076140512070a0103004000540785e001070843c0441e0381500d840c101d20403a490000d281c20114031110b20002c08000200200d940d01500030034090071380a4020003200603551840d0040d11541d071a0617815400c10490568401d108502818800c420000c043e0268168040b55070b140c03011540c5c100c0c61035007000460440342c80d2003540010003818020350341030082c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 53170057 1250 53168807 53168831
    0x10306030b04030e010914150904110c030a020c1c0308040204091b03030909230c0405030601090203011404050c0f0c030405040e0706090e1303050a030902090c030a0608011b030c02190c0f09 83
    0x2000420040e920083e808509d505043d070703842d0002c00003154159501a62504012003140e00ca91041700f050b005407140302c10001c040e00341030ba072045c0040400441c44561003000d40c0d04540c5444043c02c180c0e401907c0d86079540115100d00b203544240044461841801032030341c5000381030300031641d020800d154903185820740100e01c40541e110703c007411102e0f035507407965580d04141c099000d40d03008640c01d48142c90000c250010726500031816240c0c0a11907540483c6420100016179800b210350b8075400c00700f44541118101c0d00c070041d00401845605490078141c840d0045812540701011291003640300010400c085a088440000905101404140c01d80f070030700a070750301c2050100c400400700403000610030b000c1d42c4a50b12000700c0c254000c4c031450280c1094600882a9081030340c00070303421b0341f524400044c804814401c1049a81c261540304c2d00b8100740365402d81c0102102e0054100b5070181607070704504a03108010b0300020501c1031200b00b0000f42805401303032001116400508507103240c94484440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 53171307 1250 53170057 53170069
    0x1201090b041112060901050f01050319060b01030608010203240607120c08040b0318010e0a02150304020303091503040c05040e0309040914010f0603060507050901120b010306030b04030e010914 84
    0x4070540021808558030080c00110f4a80c0340300800a00540c01902c0c244031500350107400c403031300482074080c00841c02c3c1d88550805817981e109400d0302810014a1a10302f000a030550494a204030301410006203503540c23417010130b003681c1c0111a001c80701349117894580e146011901a0302e407481d8040d41c01d64201210b80c1e481403801134170701005000f4081c030655210100850310341207401505400c04203d0b101e090a8814218a0020361108510341d406c1c0404030400c3c5100240801e00260020301024000b00701c030006406c00d520184c42642c150004200f80c00c059101c03940605108036146100541ea440c050078110b6a400c6143c010503c907500f0103d0080103168004161151811701f20f03800140204689400c0c9040a0716411002d819403d0200381900d44d1031070351000c02203c0c00f4500134002a0b07210304045410b072240e920300714007040b02c084104008a43c1035116094003081030400141541d2241c80e800100201214101d00044080c0038000c50380d41d0080c0c0840c018440c90302420044402c13200001c407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 53172557 1250 53171307 53171311
    0x30206041b0e010b0f07060f0e0f1b0909210417010603020901030201030e1606020d03051008060415020f072f0603060609040b0603090114010f050303070803040305120a0b1201090b 79
    0x800c4c0c0001040904600d0744407421140241d52004003040015200c000d0400509810b1043c0181401500e0a08400507400b00c0d03441c002060880c4481b480800c800c0c2000403d42000e04003060600c030b07505101a402805da594260b4581803050142c0c0ca03185004101d4007034504202c080c004c41d074149041017005071511000a0f043d00da0909010401404983c051440c100007403aa9080030070315440d00160b1550080703140e0341d024282d03940030700c41d5079108454600301c00b806101d101002c1d8040360004d0b01250b40c41c0144100b011003488003520b0a034581581a00c0741c0c2040b1001d0300d0411a010300c841000c12003030034a0103d20b011000f002500c1007280005415800000c141902a000005a9240b0b503621a404500c0400000b0300d0541c4074101540298000c142c58842c10340660780740301c008204016011000011540024000c615100440ea200c00c07041e000900201c080c003605000c0c0c000340c00c00e00c03a0001c3c810816810002040781c410410031851450341c0d6a00805070349812040c030080b51000162507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 53173807 1250 53172557 53172569
    0x603140402090c0c06070306080c0108040b04030c080706020309010b01120b01020726070311040c110606060a050f031303030516120b010203090d05030406020606010906210b030109030206041b0e01 86
    0x44030b5590b4110340300d0030921429000341c07540e004030420403000070b40681c028810b0b6400781c1d044920100907500103480c13454081c2c4010701900460400100003070312500d44c0905a51060820354102502e5603201d10a982050310140703016511400703a59055648075080d1415140507540a00170000c6550010b901c07000d00f8010105141e6010724441135100701020303045050047c0e40129a10340b580da003402240b80c080003c0031880b650514950904040c0310b040781202c5904800054032181c0c80708410840310ba44175007604024400c0501452103c00080c0c0c02840c03041034a00c2c40550b08090303d1400800702d4400400d240300290a920f095444550701c0310744122803400f041c500003800c040800c0143e00d18060710002d01c0e407008040012008006002c400742c0229100c60702119900c0d103a450040d81e1750081750084a0008041501d0481c80ca40106080c00c2603203174191001521100c100042800e480c00c2c41410340140e0305c624144010401e4000c41001c90341d00d20f03201c00c1c20361820040c00c0300e65400184601 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 53175057 1250 53173807 53173819
    0x10b0906041e051b0a020c09092109180c0a08010602030c0c0607020a05031207050c0402040e0f180d09060e060a050901050c0111070b0406180302030316050705070611070603140402 79
    0x42c130010080d200c41c03071881014514080e250240c801c0c00958803d42c40d41c0381400344141c20003192018000042c04181d0f00e10400042ca112040304034505015044803110710340c400841008080700b5902035007207600400bc0c01460640d90381c0e82a5000d008034406034002c0c4119441003256a14482c0041109141e102040711002d80e40e540d41d000050403280c0c143c00c0150300d80034200d10340c08140c1a400c0140f1429108070280c628541c4220104012805288624048903034004001a20b08201e040d079a41d208055a244120300c14003001c0e00c618103885041c4c40320218220710414400d00b0b401100000b0360b80412642107141c25400c001c000c3c41c5010359022941800760100700b05014000a4014080c00c1d007000c510f052319604c19040c151114a025102514207500e4410074840d00d04814007111030441e0550000d61841d112501c0c40210309250410003801c00c43d041c002d01001070024052000101070503507451440e558400c600c0b03400c107070003a40b10300281840c00f40d65003958240c0d6012244d0290b011140 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 53176307 1250 53175057 53175061
    0x108130213020310050102071a07060b030a060606030507090905040c03031404080a080a080f0f01140301020d020f03010f050a03051015210c090608030702060706110705010b0906041e05 81
    0x490080c0c0001c0c0d4509071114000f104001090707001001400c1164000d80c02c4079800c90781c940d403142d01c09a02040c02c6020784800c00155003c120b15030040c0c420880c02078115603401000361904030480d42c1d160094000a40c0f51403d0045096022980380b01030714043c0320801031400c15540700031007035549200007410700c1500d40e640d1169181401c180c400821201c0c0581d103202c012460103401a90011080d0008030300c2d080c010424034101c0783e04240c800c90394803a100d500359091105c9036070085600d40d400c3e54150340030080c420350701d2039900181044200707841c2065202e5041c00341500600c0d1a40c2c100c5409401118803c1020900004006922200118002400415481d4040c0c1103a0040c0c10814402e0410903020480d401001100e109850181d1a0001d005031698a14001e8415030310880605078414483d09025140c080002d206481c86880001401c0341c458031b070702d8890341081c4420342da01d940d115003540b0315040824286620120489003001444104188903282c0c54000c41e060303078030b5940c1e800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 53177557 1250 53176307 53176309
    0x9020303040e100f090c02060a090c080102070b0103170306031002030403090b040303050705010c02034f0602010501050117010e06030a200a08030412170904020301030605061e01081302 81
    0x1080324041d00c03030702c01d55a09034075101850710303005401d500ca4041c01d01500140061a031030b07640b0030300380c01440d03642c05449140c84155960024012991080c0ca02441101001a620000b480203040682c4030340c003603100e2076145060500b4890a801403521817094200104901507401040d5842d84008080005850303840e1070a080310007901f0b60b00544109400003802009140e041000391801a00c190000e108004501c08102e0b200e00643c400c110131901d1410500041402110141c004c140284000d008080c646512000da171700c00d0b44101d00001c28100e101030000b15428080c2501410080c2016101c4036a22102c03002a160144520700d04444864003084d040c0c0c1d41070000340d8000703030824a00740b20941c60406140040c5d5151341c10318429511440300044008020060b42c08840090011601d044100d480310031609401c01c419003101c0000300200071075551144091070217140110b10025081c07800c6020710084c1000052905802c5080c0502d51000e0380c0c0c8901c099038000c2152103006d0305002248 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 53178807 1250 53177557 53177563
    0x60504120c0302090403080411010c0b19020f07060606020d030b01050403020607020f043803060f0c0d0c0e0a05040207020310020a0c0812070206011514031503030304060b1918090203 80
    0x7400084d400f49010081c0710601d41e003c90207601a5015a6460a484505400665802d105040003d06510002e000035000d51080107003c0d0300c9100c000300151600c84a01c02d0425550700403079040792613070f540707400c00e000095040010b2004e407081d40c2810850120b0050018090b4012444000c4c810703100080c05c00c08541f40c5a5405000001c00b40040c080301c4040f501c05ea4540b02000710b07200001c500905480d081c0244415520103008018014001c80d4885250400d2180402012a105080100500311a0401520a16074450010307a5120384114070f010810440407002d43c40a842140184103404c05a9400326a0380a1030032003950050380e4503c1030601703540d225104a0040d200740d0010030503211503039400702e5803407107003c0d1642501c0d21681c95509001c00c0b0750104456000103040240c06d4507400d128440195080340c1c855140c141c0000308440001c2c03865104480440390142c68031120003045c208010300e0701c0c500c592260111100d5080c46190710481300902c045603060b40d100c0c516002552028 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 53180057 1250 53178807 53178809
    0x40f0506010b3c1602040b010507030e06280215010905041113110f250f06090206120901020c060c0c0d05160b010605030117010204050d1b150306061206060504120c 72
    0x4410549030000c030030b16107900501d10402170b4041c90602c0c1e6200415841002102c1e6020392684540da207203403001088c4001a00544108860390210b481450443d083c0d500d465084018668010000441c02412a030750300c450691000340081e0804081c04001076000c00101aa28000c1d19100b21030480700d810240a062100c4180d400707c1d500089640101c81020000c0209054407010420000007440701d48950600c2401c0c0035142c100d215003460f000a440390441d42d05280000c080d5400c4c01c440580780c008120098032400026076000484d1018604c0c217208041e8002e00700300702c581c10000d076000b586072555901401c2c00204440000d6241c0d400f08400300c24484660050003001d440e684880002d00a94020b020340509200405455501340005000300d80544a02900d41e501e4030465664141c0e600d10784194541c0d071906120310210313200a501a444100880c01c1e6070204a2501c0c002300501001d454513800c20109007401018800d26030803108503821900003440601c40f002c001d04142c0001082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 53181307 1250 53180057 53180167
    0x40903090b0f090117060105030610030908191106010302011e09080f010618060f05120f250501181e0803180f03030a090302010815030105040f0506010b 67
    0x220701c40c00b01c0269480540740d95a000c1e222204ea07070514029845010170700710f56803400113400b00002001418a01070130744500040d030030003003800980f580c0d0300d12003034100754115652948880c2c0b91403031203a030150200260b1001d0001524103941540c0000b0041c4980b032401004400445450740b01440c800e880ba04001d1405500362500c0c0844512158081e10042c45124000001494510740c00a1917210b8034040fa00004105c240161401083c03000318100203000b9800e50184400c1c6201c0c1c807606104494400e180503660304200c4c1c49041c44205030a5107a0000c5040020841c460040d81c041041030300103682250048001340040868401c01c400340a800c00b0403540804602e145414174542c428405650007103640c9812000d40b41d0906d0b540f801142e81d0000011b503182030070800b5502407010741d500081070a10305d05060200001007820f42d80c05803401c480500507440042c05110b000d200030390140400009213031410940180100c2d4555251203034035405209000d8680100603407030b41d02d003c403040f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 53182557 1250 53181307 53181329
    0x7030803010305030c0c01140412150f0504050613080405040b030703080a0801240816110102040b0d0507030c0816030f050a1e1104060503130c121e030503040204090309 74
    0xb85a00d011926900b00300b5603803102c2c2c41480d1081120390b0181014050054003070303044500f480e24042c65845000d072a84003d540560300b1030440c003900315140c01501013071400c45101003034906252070103915102c0700130941d60074060300300d200b04006072035441190202d4a0480d8041351007980ca02c0000e00304100d41e4001400b19000082080400c1c0d080034045040b40c018080d02e03c124007410041c6c0c0c500b074079500d880a001075581d1000854400703a0000c0e62410500b9880c1c0f40245c411212641400c90780b0a801c100d0142c000030480e0040b02c0e956000f400d6001c9801d26083c4520102170074040e00c0884060001d80044c0810805003000d81e01c01ea000030a0702860b040d0500584c28000c0c2d04100522400d1120307908150080101c41003100700303001e040040302403110494509443c1400840306908080d010300d0142140842940100c1c210b000d000c2c0141a041c2c030883c000840900c3d041c1c1c101c1051131043c400800d060518200801c1e00401501c2d44642c05540102e2805194a0115840c440603001458245 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 53183807 1250 53182557 53182559
    0x20d08161227030c03030b010503061003021806040b072009040f03020a0b1003020123031305010b03121b060705040603051302030a0b0901150b0301060e0303070b0f0412110a03030b030703080301 85
    0x1d5803001141c444d45001e524100103032024000115002d200440b0803940007180d220708501064803d500802c000d00d05040d03001c0c1500103800c0081c410340d02545c4040e081950100b0300c2400c0c0010a0395000100050810314042030200c01c0124001ca10010400340c1407002d16403025080c140280720040c1465401a0f81401910300743e10200e0f40c1400030301090340060170f499142c03440301d40000c031000b0a1190325181d282c02d40c0e50351a202051146010003c40308d81d52501100080c94504100d1ba80c10403000d0b0580f2601d58124421340c800f12403010b00d6150040d802031050018854000c01150181c4000e89004181030f42d440301a030409a00c01d20009405104011160042c0500307048514021140700380203100c9810072000d13007030b400d505c0341c000c40701d0b952010001005014002d201104952101405480c1043c0031070f1210b40c41d20000702c5240ca03050007008104020811402d6081c17014075114140010240b03c0c0c0541e082d075030030895100600381a43e45805211a40d400c000d0035008582c0300d9500d80c0d6075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 53185057 1250 53183807 53183813
    0xf030405061603020702031515040e060106140f090103020a0306170f0d0f350c04030201090b0f030711070b070f0b0703050121081603020d08161227 65
    0x2840c0304981e5105514000d0800c0d504083c46802211322140d0010010000060444001089464050899032407044a200b0200b1280c40780c1c0504158400b012001c0e10b2203626104004e401400c03094007403e031000003000400c0040d0a50070940e0a1070340f013843e0041c3c85588a650603070080809030030008400540c03a1660410081c0000c0c00802c0c14180c0080d00e226003280741d810f4030080d0a8514400c080303a01504182c42c04144000c050180000c06d0a400088010004043c00e0201d0280c546078000c120000f018015540c00c5905080140066008289040654400400a4003001e0400c604100501c0b052800110040010300d002e88061030f0300325500d2210703141000c2c05c8406507100f110040603000000341640d000f486018104c0300480d802aa0340c0c103270b44407a84d02c288207415080381d4180c6e090100251801c4440105140d0511a40040851140500c03000d01803102c02041413410354040c4101c140c40c0360380701c96241c0280c4d4810901003030000e801200c1c00380d1021500c411001d400d844803040344c14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 53186307 1250 53185057 53185063
    0x30f0f0203010b12073005070f05090403080f18010c020705090105040c020a0b0405101517010501260f0105040f0212030c1902120a0605011403010902150307050f030405 74
    0x4854401c5008105125900c018424603080340300c602d400681244508000c1c150984180318998240a0083c0f094588038994554040c80700040545980d405400c040c80b002c0c0e240440e0101812080712040d00500d066540100040d00003410304510141d5a030218403041001d0a8940703c0f041070074004d015460b0350007402969501035216562248101000028850510348102d00c81100c00d90702402d184145c6450700c60750854080c1044806100b04107840280014a2040040159200c18a11021894542040d041c509103c19083c450791424004200e0001208504c40810303164400c5d001858148010a0b810010700120590441d42000c2c1004104030030400302850b11032084582064200d4012504c40e607901501545202c144d002011061880300c0301e20301c1031070480c801898a0001c000000c00c0318200250300004403803094172980107210104004004050110040e00200024482500003480f480c042d208070250300c8000002089445219000305c1e01800d60901003541d0300c0c203091030a0360fa = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 53187557 1250 53186307 53186333
    0x3030b030f0f060a060501030b030d050f0d050406020403020f091003030e03120c071e060e13090203030d05040506160504050d060b0303130807060c080304020405061f020309030c060406050301030318030f 89
    0x1e0f54038030708174000c5141c0d03009105a1305202e00c041c0c0105022690700c0c0050b24194045a1405410602440302d529000114011903108d140b05070000350700c2c0c510b50320600810613811aa035034814119801000440584002c400c03003103d400d4940212002640030210303040030b189e503081c0c0c40d881e8800a02c00a030034800203200d501300d8a0401940d55030716185001aa101247c0d401600c00051b11401f00402c2450900e001c07040c40740d0003260000d519000c6130300092440e401081c100d82e586407210104000d00c48107110203a400f88261144651603444598014200c1c0304600400c0d02c00c1800340c80f070909000032a8403650a03604040c040700e0342d80b80b500301c44518289141c4100d880910445a010569512030162060641d60010300d00b425610340e07038208005040002c140c036400a02010b600e10007040225107140201c81940c029590300c0900c4414182021a1065014044d20040004110056001c81141e046075050702d000f00030340504402c020418070f83c0340c4c4040c200030641000101800021000701c6 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 53188807 1250 53187557 53187571
    0xc060411040903080c07061407020d030605091603050405030c01090516090b010804080d0902030102030c0d060b03130b09010b062b0506101107050a031a070305060d03030b030f0f06 79
    0x2625200d00100704000c0ea80c816900400050301400030030b41c2003440d000640341e92845414041510340ba1003684403c44041250b8a4006030720400c12039140b690144650380241400b6100c1382030901e00751f503444c010380500070b40d484205a034910000301402800d000349c0b56886010b4000b4441c6003528148980e49002d4610b10191508074500002000c02c40b500c60982d02c490180c4a1040a0396541c031085940c2c2c2001084401c6d00b070300e032081c103401170358203100a40c070038214011000c1d160781d00c20281108581d1a60400230318854104144640c1d4501200c00c2c108440e40302c0603519040e0780d011032850140c40c481c1c0c041c0f0b4018401180e6400010400d4500348220740f12458032800c150303013421210082d2501a180c0a400425142e070620b580c61283d06807001d00e080b10750440b520f45980c1c0c80411942e070001d03801912203a50140364030340344a0040c1d207e190400140e16080c0b01c83e09003040090201d0000c260024245960b5038140c1e0143d890a0210041d441d032440150346445011604590719007808954038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 53190057 1250 53188807 53188823
    0x60702121303080705011b08100605040509040206031003050616080601230c1908070c0506030f06040b04060503060a0609110708120a0e07080d091a1207050c030c0604 73
    0x3220351046440c0998000000c01031805140502d9a140d07030b00907500510081c0d45a540f2240c581d041d510080d14807005500c150381c1c600b03019241c881c544a00380c2001f1b8000000b000340810041010380c0d1260800d6811580494407a5520b4542e6403c0c0c01c880d070348542c0001c3c01402110704000301c02c45020142d812002440c2c540030034076910300e0011203c0e4002805040c4098001c054070418110382400540700e1920b140b03007214000c4140318000001034001d81401c5900280004d24001040070020f0f4480003403005440590442c1004c0c56418800c03800101042c0c05155a0460503046607519080319009001c09000c1d00c0140c02c0055048000c0d08850061084aa080c032202c4803401000004442c0559000240c0c0b03820100713001c0c003100000b00302a200c201c2554840ca001503092100384520401403c428002302504044a0005400103040c0c0d400f003071031400018840d80c04808500c0466048010120001100303554000c0181d070603016482d07941070b0611010608500e80640011007030f00580c014581 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 53191307 1250 53190057 53190073
    0x2001050412292202010e030f07090c020313090c09091404063c140106110607020318010f03110c0a02030705041112070207180606080601030e0c1c0b0108060702 70
    0x240861000003912030b0103007582c1c00c5001c1594a1002c0c0030150001d48140360400406c03101d400081e1820070070300e0f03c086003500014070030440f5690610034580007903041c1c005103087c00c65101ca04194546948901c282c29501c0f4042140310a00c2421914003400781120200002040c1c030540c911690ba007100c0c2116400d107061384aa182d00e90101f8982801d0070341c2c2d844103155441e078401c0c416240c01c0c07007840e4924041e11001e03200c0d03400d260009101d0207400c0684e20780740c10707014230001d039481d249000c0d122405640040002550a2019081c1e800000f042801c05e034414005200381180104207401c1582c1704620041203405101c9004240302e00c41a000b10100c90605860300701700000c680401090450020081000c401d40c2408600041e171b00070000e0050b21a42c2d680c6140541a0a070b4a07007248042c507a03951000d0240799042240701d1741140b401e01e000c204d03e822400c0d140340c0c1c48045266051141c03800201000014004c020f0701d60140341c0c000d6843c135003075943d0098584d54440681e250070142c018100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 53192557 1250 53191307 53191373
    0x9041a010921061b02150f01050f1503040803071709070e09030c0703081801021504020f01020f01050a0603020a0605090a09020c01021b03130b070507210b070804050610032001050412 80
    0x744150141c2c1410244814592800080020902b002c40c40c06030025a944181c254840d0883c000d148030300c4c003604000e90b0f00d00d4086002803148494a41c0500034080e80801d11004240c0014420152800d40c1900e010130340b01e87c01c0b094998022359140c0803040c8152980841040401c0020701900f810030f00720541502d4408006903200c0c040c2e1800058403000d50000a0007520304a51812505203044c01034401800c80b0143c201c1c00c1da1b0040307e40c28195501c1e90010421030130440000f0340200882d10f00942010700440024400208a200781c1503550b402080211909100b07504407070f1040207015001c0c51408201d1070880c4c90340c200c0c0c00200051441c03400b0014040c507400b0125101c0d1b55200015200c1c01d4108003081c0740582d070103205808280ea0a50900001414900c410303409100e0a4441c11303421701d014508249450030041080d509804c0d001400c100061034a5540c00041c0480e481041c0d982e1521001203600d8081e6a002c1448114081c0c0e01109020003202c580351030301c149513140c01010080c0c0b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 53193807 1250 53192557 53192593
    0x30f0e150c0a020a08092b0209160507031d1207030507050f03250f12020901060e13050c070602041d010b0f070b0a061a09041a010921061b02 62
    0x24030800251300005150304c00a084a401480d244038010849240011b150344401940754240c0314048a0451042000d015031400203806540558400a0300301449402c3c840180f40c0e0150300402018000c0740c10b041e05846011880e00c0c4180d44020304039590040b050342c403a560741c2840e80702c2528a0700419170081113a042c0003c04080500010f0020110b803100203002c070080c0401e621815045901445002c00c000543e50002d0005203042820071302140400d0040001010301a8808807d00c1840d4400303070307903903240c0582d080c00d01845544006000e82d50507905041c188141100140b01d41d01c00a404144548034820702180010380d100f110020703030b0302d45100d00c500344903d0458141d550003d00444002a0340f00304a0350740f144041c14045a0b00d6502e8462080d00c985031100c20f404010003281c5251513040501c2808100b407140030580c01e420350782c1030018102a04038080d00d44904104030342d494480d01c016800e008034039403042040003000000545900840b60301454000180500505801c44270440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 53195057 1250 53193807 53193817
    0xc08070302061b01060503061014010201060509130c1502010c021203191e0606030b1503060604090b030f0a050a0c0b180f0102250603050f01060e0907030f0e150c 71
    0x940b080d450102c0280e00d403900a182180c0c100125034941001281945007800464000d40b040d60f00303000d201d402d00035205002941d9420090442e071411008002030703038a480901d0703003100c00400b042c154182c039401d00a50b100c16641095060b508c48148980032198158482a0841142e900f607849a40300003410111500c81610307a410521140c00d2002c081402561051501d0301c804450310303e8080001c11600300340d46599000c82c001c20340d1a410035000d42001c02c03100c1c5040070052042c51842c680354002501034000c0d40251540e0300da54101102940e28104190707510170411340c0440d808c002c02440c0c09569a110100c049034019201c10000035904c6017a0182d54030f2500ca0010490313250000018402d402d089080c0d20346c11885000076a840070004e00d5101c83c0481d0204684002c028100880642a2a405000d0150320f040c40001000403030350190030f6800c00081190b01001d991100003088001e040f64400905603070307140c8405030704003640c002800c880480d000c022141c502d41d03424583e21110300071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 53196307 1250 53195057 53195059
    0xf0e0c070f0b130b07020d02010609020408030d091703010b030601030b1005030f07020c1e031204180203060a090501150e04271704170c04060f03030e0a1802070c08070302 75
    0x1041c46100009101140c01d01e502c21405500703540700140750b864400903007100341c0321038025030092505c00d02001d5080c0600320103000d0000c800d62800d49040c001982d03a20a080e010303100c03070303130345246240801c140a20111802c00d800d080250301c175611017541c10740319841618864046894140742c4c485904010015160321003080e1900e81c15640c1d680e01307502c0042c400070f116404500540440840903030700d04c43c08060100c0c402555085859030b0b0b009040c900103012568450b0340c08280410007500500a402241044c0064005a142e0300c440c1d01040c881e542c15002201c8250500d000811464541d5080b2119006a81e5413682c0421002e401d04c422107004030704403070201792114106100c040d20381c121030340410711600150149a490010301805900185c0058070340c290070f51903400468404212800007114200c0b410130525241810303101c02000603100007424400d230680d42c000c0d41e5451000c800000c01040d07400d2190030980c070b0488402507100000440d00c0594800d00441c6245001500d9030550354 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 53197557 1250 53196307 53196323
    0x5010f1d04080f071104021c0509060c072d060b040f0e060703090f020612040309080106080606090604020705010603050c011101060302030d080c0d09050303101d0402011d09010f0e0c07 81
    0xf0008009a07074403000c025036034061111701c00c1803240c0781c82c4020080c504d080f805040c45805c0702102c14090342e902800200041e0b010340b0511040501c4d8100315000b803540581601c04103001412030041c111507045240301087d9201d04000e05010321a04807558141084030100106c0c0c096818403400c41f40a00246c04803540402c0010340c0503402a880741c00d00764050003007130310801c3e566400591564812810585034025078000d000030160481d2044001c0e10b8003030003d2204c54240141a603540e00000e2446102d40b031400040382c110380703640e41118000e5810000904c50552242000da54510446002c030303000510280b41039002c09018464042681d42c024082c0a0908200c8004c54031898058a8003904050400c84040c1c0c0d00000d204400c03a1034810400795441e4a040741e044680503085a0040c0d100300c1188840714480403040720034960103582400d0085480004182c07010b04035000e0070805410080d01c1c00040b880c0500400050111f5007503084443c0c041c0e0350411514142e00039003e000744090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 53198807 1250 53197557 53197567
    0xe010207120305130f0c030b01080615011805030f1c11060a0b0a0e07120f020c0c190902120405010b03010c020307062a0f030b0328110405010f1d0408 66
    0xc2e100b600501c0e0092031500300e45090120075200c0068920704110100c03040c45d02e1400401c208407644120600510b0190050510340c6048440320380c890280041060400040060140b1040440c81c103c1e40030701405005c5418103030041090710b694403070b01880c090101101e800f582c04501e201f085d81c4400025000042d080079181c1d0860382c2c000c2d000280c5a650b22940f00c2e078010600003105119584903030060381d2101004a066514613084800c0c034441004114010000318920f190006072010840390141d9000c1c0418a038900a00e910390240c2d00100105800040c80d01082040c0748402c0340505e0044000b0400d500380e6400701422204801c5004025130820701aa41c049013556001002880f0041003d584d110040368040144c841255010780100d4840080049413507810b100321400f01e40d050700106284a4218040107406841c080f001030384c1032041d1441c10402100961240c04010050300910095854610f0415025420f005e80c000c068a10612422100d1050302000c1c0929007001c0100d140c1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 53200057 1250 53198807 53198843
    0x106020d080604090206070503040e1005060909090c0603011205070e0411101101020409020a1205010803161a1015020105010b03042910090c0203040810200a030507030e010207 77
    0x2448000c02e150351040d0354045440c096181ca000030411140f2540107160b403642404215030740644042c3c00d00100c40d1140c00180484c0d1a200e04855920100b20b5103881d4640c0d130036201610341002c0156080c2c02113008000024140040c03207180c02c8042c0310b482a40c0030942c0f03035911803001c40012100501a544081055002c41c1031181d4052203c0c40c0030701e404907070541c41c440060b0070f80e40140e120170380f0742d9030020300400761550082d522181c520089500340080c0d4507001009544c0c0c041c49100c1c505203004181c440007042102e4603c001c0042880d2046046071800e030809100c03801952040314114448440e0800300b40e131040c8203150503180b03007428150a50302c440e10b4280e807101e460441e405c40040c460558103425060034000900c03440c1e0f1100f0305010f5034100041c090a8540c2941c2c00015940184010300403081d0200300300100d0b000b841000075030007030408138150f2441003940c914005284000b5107040e400c1c7d8035410861280707050380c07014004a402100c07200c0c00c074450000b003c3c01c1c0341d1079444001c441d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 53201307 1250 53200057 53200067
    0x105030c0910270606080117010c0e0108070903150203071103160f0f050f010914010c0e0f0414070203070201031a01080610020708010609060503060108070608010b070203030708030903130e0106020d 87
    0x18000a00070b0f109202d042c00640c820441d0142d8000102085500d0010041d400d02e00c0484040064004001d22814482040151030040702022040c10b0021041c00101e000348038658000c0116040001c500c17803580c80a4104001b0741c01070340d40c1c00000340c0c65400340955200000440d00040c0221540c00d03c015099140c40c0141180b40900302c0701254968040e8002c26030030000c8440d0840c4182c00041c00320441c1c81d010100b20281c148448199040c02024504c0c80e8000340c441003000e80940700e005e59402950002001400e0036000407035520804420310101507400005408218401c2e00c0c1001426600302546c00141d05000202e0b0024000600180190520301001805a46a801155040c544400c501420b480ca0b64001c84d0a1a654000030031081c6410020f281c010460b41025003521401c0c80d40c000d080640c14000c008190700c0000b21402151070400440f00e090350040b00381f03034a03410300f41c009035125408005040e4107011408030208515003080e030218100d41c1280c000780b078a07510003007082c0c403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 53202557 1250 53201307 53201339
    0x609090a080a1e02010c0e090910050402030c060a0f030501050d02150702040f050c0a08010f050619210f0b030f0606040b150d020a091401050f030c0d060e0105030c0910 74
    0x421100c429a03e1200a00b03003450001200d150300003144091203d00018034500360501c644e07201c0c02d15802488941d4101003280308028944000200720f5550741c1c0082450038001c0a850b07600100700040324042142d025802c0c040e807507242e980c14041c43e60317034008210388070403600c402a620698000c00c040064074400c0042c2043d51024101140012103102c079001154400c4500e442880000200111200ea11500080c0944500130f40d0f40c03081c600345804241741c2c0c0640b96010801c40d103500c400411940c09009101c0000810040c0308409481072624103020749820f240000d0598104010546030386000f28a14801e0310844c00205841d950b45401c22014009000c059500b2030708003116100e21306c082e007005000c0e208d4502d50241c0c1d02c4403c440c000300140000c0e03220f505e401107035005c1c0e040c031070307920000311400f41405c0442c20b81c40c0d80359025071528a215000c5040d9080c1c0c60404009004400c0740c852504845044080ea4aa20943d005208105508a03400c40d154980900240980740f14200c0c040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 53203807 1250 53202557 53202577
    0x504060b0307030501050a0b091302090403050706020406030b04420e04050d020606010207030503031603020c0a060609060609050a0923131205040302031b01020120030f0609090a08 79
    0xc9950103403200401c0c01c101c41c540080c0c035207035106c1e020494000020300a5607401342007691100c50510700300c5884041d0100c00a4024410b5a10901040c2814414004d407502d498010341d0855507240c0d1400c02400400700c0100745400345060004440c15268012040c2a09000c404400081c0b06100c440d8400c41c1800090a10281c18422002195070000444080d100320b1007040205050001941f000c0e113021002000e0a0440d40041014000545d01000741c907000560303240031008c1c02802d00f5095001e4050820b09000030f204580007101801100d4000c40d04880d070f200003c001c45a1645411034414119004864024460382e00400c0000c007030364440101c8c04850407540d40c40010f4520400c0800c2810349458003074121084045060280381c15001c80c65a07030072b0410078601403440d03010907103501c4440d1000a000070300e1545d22245034001e4004c099410706403189081034509040c0180b810341c1040d601590406881000914035091180c040d43c01046280000c10b095689030381e8a48803070744040091 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 53205057 1250 53203807 53203811
    0xf0302040f0305010b0406080c0d080702010201020d1803080c18010e040e0a140d02071d0402030f16080f0105010303020a0b1b0301090212060d020f121501030804051918050406 77
    0x14081c818580d180014611580c0040b9050f00c0d500204001d4400c0c0c5d40124155400042c108051903595800010700d49600206103601d070402800140e00900941c10740142032402e003200e20035861000c0483e092024400e413601c0d69952140a5101402c1c001d160399040441c402440d000050341c003a8000807120400140013103280882d100c2030a0510703139a6102120702144c0c42d030500c02950401d12441c007000213184000c0c4081850220341c51020003a4803000600b03007103294085025520180701d41400740b4401001c585070300946210156001c0c4940c8910003003409010110180800c040c002d40381200d40541c01000700c2c7c4015142c81401c450041d02600080d0094412084040a458003450080088840046e04d0741c25030518880c2c02400102741034490b02c60029100d0050351a040c3c060303c02c803016250403443e00d0540b540145402005031a440d00185003000020400103190001e0068503003d4030325980c009085a030301c45800a0a004092050713401c0c4035100c140240c5940016031040c010000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 53206307 1250 53205057 53205059
    0x6010509060613090e16140102030405010c0204090b0106050d06050414010512100e010b040c0309021e0105090d0807020102010b1005030a05060109052106060f0d0f0516090e060a09030e010f030204 86
    0x1900105c5581c12403900050300540d0042d14518846031485008001c8920a180344401440000391a4400c5001d01e034184203d416480c000d40d12198804412240c1c411150344044d40c5900010b0003a410070b000d80c4107000e04203030f0080341e2414203000e04840300c0040000b90445ea401c103800c01c0f1404503144031031140c5102d002003d89104a050242e070300b203900704000014030918541d0900c070994400d03103041024941413106030310060b141c0c1d04010302026076104110300f5144403400103c810388200042c5680c4070504c0e02c501130900903110001d0049070720036002040050328080501400c0f4841c2540d2402160090001614a0b5010341001e980b00310140b400300c940c030303843e00c000820b0720381940a0f00c410303540f0354170040c900d0f07000410030141c10903c00c4640c2c602d41e040c20782c001801c0c0045003c0090200041000c124200441045082c0b0072199440d160211aa1518618001000d420781d181006204030408160320500700d03c12480b889400d5650408001c41160040d00c1c00c00030385122200301030782004 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 53207557 1250 53206307 53206319
    0x100b030106141c0c0e090d091202100e0411040e010e1b0c01090f031e03020c030403110f0901030b04030305071d0904020a09020a02010c030b060f04062607080402040c0206010509060613 81
    0x5550000d45524200c0902901b840c03505180b80c0781100e0300321400d002480106001081b010800407a003254112901c83d81409417003402c0ba90807014110640d001400d1004848a060281c0c2c05030060394400100e404440c0c0e81c0301005600643e044c1e46106440407d107c440f949403155800038070020221000100b80711843e541c504100c2c00c100c000940003d80c1c00a45401c22081c01c1046105002e1203140950400b41e94217403840d1207108602c17000700b44403406000d4040c1916003800b1580c2884005240038015070b52824890546242180c080700007a280c00b00003200c0720701401324141c401c20000e20f80980346035450144448640f0240060341d011040f01b00c0000c0141580c00140070354500d0f0760000c502c10010102c050240c070149004a8440d250030f1001c3c00c5041d9801c820355084650340c0c030302100030b9000d2944200343c0c05188103c5501100c503250421507096002012107020398405d07502001410100c210480e1281c0003030040d160f101c54006c0c04150540341030800b038130302c20020b1600003070386541d41c41d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 53208807 1250 53207557 53207573
    0xa02070812090f0c0a1502070e0108031902060f1302031e0c1c170f040308040305010603030f03090b15010203090406090504140607020c0402030c0f070302100b030106141c 75
    0x4040c40102030049420030101c0e1100f400041c003500007100c0105403c0540b9400101050600d0040803403c440464042c3c00252082000c900188040881c810503540c5899989840b5401001c50b41e01c46680d5070401489103200103082c030b100b00700e03441103a4202d031a040384400c0340700030f180c0041e40c4c50300ca82019030700d80b240c15008182c23803262b81400802c9003440034005d00c01d00000040168800300c051402001c080350b0f01180c5507005c4064902504e607039041d180c1d102c2541e8000c0d60809006142c0100d070200c00c0000562280003900c0c001e454144009001440c120140c90341e5400007050b80c1c4403000400d06100c0041003900c80c00b42c050055a080030b000c04003040485c1c02591150307080c00d0300d6a0a000521400c49564811400c1c00740207042c0302e2a06900103591480304250180c0155400800240d03140d00380f009640000c2c00701e848150352400a030400a5550f081c01c42c000840070300c0c01001c1d2816140522840040711903254580a00000ca08104039a00341025091802c00145140c95000152a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 53210057 1250 53208807 53208817
    0x609060c151d0601050105040b0306090402042a080f160c1104020d091406090703030806060415030c02061f0302010e0a120f050c0301020901084015020f030c030a020708 74
    0x8010301881d06039082c04014540796060740900e0600c0320400c0300340200e948507001c4a500c00c00c29512042d180e01d40c0d101080c010002d40c400382403640000707460301c111400021500108944940c2d20384402d0b45640340300d40c1400c401541c41749500e400100c0403800315401181103540046c0900404280a022030303000c0380c2641d001210311031031181d0b240300075410040d05180031009524607500030801440c0c20351035a9529406400b024051014990024400d40c1d5000100d07406000041c9001500720080800a009080d081100c01e015004410005503000c00c1840c0d2801480c0143d408150700918640040d144500382d02285034010412560110703104000d40307443e4800c2433080401d04c04240d014102a8100202c3c0000741c2d1007a4010000c0c104a60782c02000e680c0c220f001c1d0580c805014011118804140070a00c0640c011201700540300c046a42501c091200380501031806030100708071103c0140c0c02c0380b0510b491a01031140510110310704400c810040c5510031004040189041200d445442c07030358101d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 53211307 1250 53210057 53210081
    0x150b0406030501090c0c0b0c0d14010311010809120a03020f0703020a1203090b0103060506040e010504060c11030c060c1c0608010203100503030c0705060a03060509090304080d090609060c15 83
    0x400901040001d078140300c1c140c010321600e10100704070882c40c1c1c4000c2040c40c031044050402c440c40c0c0b0210701c029070b0402c01c481071400aa1000c00405e68048214100328109120a61700421030036095800d40d4007030801e0512811104c1d0243c082414a6030b4060310a4208a019004050742480f40c1a0f503604802e0050005600a800904900c0642d10340000c0c3c4010350701c0c40070100750800241200080194806c1c50640303602a1000c103a07a964480440e0041c11020742d840020340c204401c3c082401115403005020b0415980c0b8012620390300304406a81c6d114903054444140e010350b0000302c0d0078040202401d43c4c00501400420710b40480301110f001d40d21960400c14659600000384040160b4011701c02e001041c0540165084c114a10101c640301d1001c6c0c4111401000300042c04580544079510030f0f8040c00009120f00446c8c1030944a80c2d55980050041980c00d01c9143c5030031200a006001e100304440e5640d64581040d0b00385802101e2104001000301c80942042c01d80c80b600ca030729406030042200b2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 53212557 1250 53211307 53211329
    0x41b051b150a061509030204020702010c0b040b04020906060715051503060c041e0303080f07120204030c0e0609131203020712020604061104080a0201030e0c101116120b0a15 76
    0x24503010b44811908940e11012000c080182100074542e040a140d60441b501107900684502490005a0f00c2c602441c00c02031109649504010800c142010034501a90007034030114401d42d250b400340001c80c8035248019080321801443c10701520840e070071840d0b00c2005503007024407460140e404645013820681d110050040041400d1009203d160120021904c041c15903c0b4541e280d910050711481c2e025204076040481d050004481c10f00035503140107210a00307002103584540d0f0342441c01c200c9011b4080e04d482d40380c8400228400307203402582030f400b03002d800b0030b00f2360000c5e8513685030780840440348224030a040d000c1c482d10020a030440d21030315543c440f64000c3c00c9103180a1500d1401c5403500d5a40031134100d0140b2040c42858000600c400c0000c0d8282400120103201140b01450a460034051b280d0040c9156041007205034080c01e426401c0c11008110303106559018001c1c0000d607403078040c858041071348924240118240384040d07904039400d00400150361810441600385511180c201000c00c007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 53213807 1250 53212557 53212561
    0x90e0a0e030f18090f070f02070305030a050901170417220e0402090a05040507060c020301020c030a0c0308011211010c061b050301080708030306030601050f120129041b051b15 77
    0x52141e11008005003150300002c0703481c1050b406001c180006d0080020031101c400e0310800f030b074020000d05024581000481c3c1d250030441e2001441c650083ca503407030000d0490000011010f68004c1c4650056902402c81903150b482429000c07010741008500340b012400d423012500d030690603011400d02800c0e8210380c0030b00601e8a4014000010400341042000074030b400204404a400030a80c102038a4403403400c40d002110310300009019015502200c0742d40d010016880101d5600210320f5620a88291980441c40c1e9170350f0303048911300b0b06008001d8010815402008250762040e10540c03441403203403200058000303000341401d242001c805000c80c0070980000052010017020010340c0020204000190300d10326001020070340b0358a06102c0da90150004901d080426980c5001d0302c0309694811000704160500d420b04001000c0308807410a040c0460b044001c051820240522580d1407a0003004030400800006c040b40c407540004149061446588500408c20f54103001d141d121006504495040e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 53215057 1250 53213807 53213827
    0x50a060f050105040b030c0a0e090a02060d0506030105090f030a180b030901050403020c0d11090702030c0d03090204230f0a230a060f050108070c1e1208010602030a090e0a0e030f 78
    0x161a2022600c0c0f01f035015903518100d41d9104401c0b60203617070305910003101503180c9007140307407600c5150078000703521200114040f030178524240c0c81984100002c40c024401522070410b0213482d4810100400b07404c0c0c2003001041407250050441a8083c3c503407000c0d081d0019a00c0d0807400c800e41040d00c030000310740d4542d018042810380c104804030089000721307998800d0800076070f943e64030f0320b441030b0845009100e50f5000031350b178a0090055402e0900740c1c10542d800034225080082c0100780c6040302324840d614050b004104080d110503810700c181c1c072a20303005226880c0d00280380002d0030010410410303541c0740c140950b0010645401e60040c10458519001c4900348100c8160654010780c204000c1591031007000c000603a0300084440e00001da40c00e201043c01160b0521800218180c0d020180c0030085000c070008002c000420000144801e944010060741c031914200e8591156618078000103d6140081c045140c40e40340d0700780c015480e810000307440c0c10b82c0000d46056070403060741c80924240c040760032004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 53216307 1250 53215057 53215061
    0x60d02090f06030603030d0515060301060f02190804091d01060605041a0705070e0406020c070b0c01151a0f09030601141207030b040f020d1403030106030c090b0412050a060f05010504 80
    0x1010700220341d502d04618010002c40d07900c1c01192144444503840d40045418404031103e95841c41d00090032003030f034035a1110700140c03510152050400c018441d40078004420000c4000f00300042d40d0003150f07a440d05181c1000074000c0c107551801c00114210a10701c0f050491002d10407007004003c5070f11982e807030782c0c50700484400d000d03a00712506080140402c0303a81d000500118008060b074202d004a00d0081d02d07075051000c02806090140e01781c03031050350300106602801101401c51800400003c3c4040c04a8103004003810000303211749401c41045103602500800fa9001410a001142003c0c40c1094040c40000340740c002c00713a02c5451006007145015442d8200329003503240c41c0c00342c08010700840b0326550f9a030b980c000d0001c202a0001405602c901c0031503407212200c8943c2ca402202d628034102250180340c1c2c983d4030070320945000c1b910b000c41d00340800b070007510140102c4101d2404c0c030b42040c0ca0301d401903040074201c42045a40b030040c0e203c414000f46140c818000e100792202c40c00550b543c100001e00c02 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 53217557 1250 53216307 53216329
    0xb061302070c0308070804090608100e030c070b0a02010e070e0702010e060c0322140105060405090a020d081b0303010f09050c04051c030302090301180606050114070305090f060d0209 80
    0x2011034010000400800ca241c004041140e5001203001e030364026034203001c42e0900564200c07021007810007000085644002034214200c4900500030002485c580702c42c141d580c490602e9004150700721110802a0050741c901a020913920380c000403a9003013581005900b09501500910710001d01c1070180820140e0920400c0302c21007a0354001c02c11420302681a803401d000050400041c11100007001002c5e9080c101e4080807240e00074052400c070000c040d481c5019050884030300f4012850240082c44154000607000895900944408404040d03525206105c1d4000c11103040e00c00440382c0b081d003104400304001c600900000364015240c0f410b00c030649040c0d480107402040d07205028081030040daa2881032020b940c404880d80141d40c03100e14901a0301a018807521107034035505c1c0065040702c0070000090385081d98810f413810002142c803500195001002d20000c0c0c032510f2002c3c41f4200010340180018114081e000b408407140030503020000d0916805001080764680d00850b5008403420300400712a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 53218807 1250 53217557 53217589
    0x40f1502030705061506160302060414030405010c02041104050d0302070602072304180503031f150e0108090106030c0609180c14070f020a0e060901060206060102060127090b06 77
    0x146080b8941d180c00c0d664103000340405800c8800d040d040026075035410119640303500200d4054100d201d140c10080c1d01c506c802c407415580c071241c42400030f60902010013106c0c1642c1058449116080d425024880104640218809115810040031489688400f61186118844c0d40140034503420088024107140e219440f140d1240800c2d000781c2074000300802c0c0d8940c000c209440c0000c4290012003000442200d441010740240000014007100080054140350355420850001c12075591b668a43c103c0780b094850fa00e000180c004601140540c801e241c0e50350030100240000c02c0c80d07501e0f81c980c505400c42e9070b40a1000700d20303950000c01000e000542e200c042c5c84070344c510030404001c039181d01900b1088001400b4680754000902c203000c0094900741200f400d83c02508041c00a515540500c2c401d01d4203a9179540304141e11000003510520024803a0b21503c4180e001d03040c240d2902d050f00b1040b0b421050b10041c3c494045044010045030b511036400414010a880b40e40ea0070894180940340d98000b080d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 53220057 1250 53218807 53218813
    0x20304030c0e07050d050a02090a06021504030c050723010e19030b090106080304091401080706050d091106030a090212030a02060f060607020a080610050a1805060102030f040f1502 79
    0x42001c2040e104110044407919520340c80c031562000360407030f9039110715504003111500e08018072608550326801740081190580e51050a00e8030303802e0581c0d441c2416600c01c0360880c1c10100150000e8400c40c01d42120b40c0c850f4088681d9152229440301e41c2ea44d400e900200541d110031540103003582e00c90300003d0859400d5440b840808800f04842c040d50100c2c0c0005065001904041115400c0950015000305a032906581d2503980322070204c8040c20b500c1c00c4406401d0001c03000400c0c614000301e2100100c64481d00c4d051702d4000c80e4000e00024121890b01600d40a003403441d103c5903901c4540003144a00190200051094905c1c8100a045001c001060304168400e02141a1584e00081c4194000440c030401500310782d240d40c001660303441000e200a401404101002400d0328000516a0150303045201c0981d09035103401c184000251148100c50b0f072240715501c078000002d030540c04190010010303c10b503490413190b544604010751040d03200c01d5034100e42180130820700d4190080150420038a01c05 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 53221307 1250 53220057 53220059
    0x1801030f0603050a030c21080a140906040f06060308072105030105030c0d050a1707050705030a1109060102010902040e1b040908030402100e030106090e0c0a0509150f04050408040303020d020304 85
    0x2000d03a142c10041004091001b10500e000a00c860041555010200a2880c1c4a014a1076100800c04907058400c9003603030741040c103064210401c1560161081c41210014025691a1f03250194000500002612400c2e1b80b8040480400e04d0704000304040c1d802615828400f21035492a284c482d00610710550411000340018489640c01040c441a00f8108940118101c00c1d03a082080c28182070750fa008160b26207441d0120215040311000d00030440c007030350a540450381d460741070686802801c0c20007002128817070b1580c071ba40d140100c5419044071040c8000500e080c0e440d4041350840707210250601280c1d00c907003d80001c0040448100c45600c00a40e42404801201d03078868016001c0640002c1c400d10300314500d412043d00c1b4640325108414000e00a20041341d079025a00003c00740b80252000fa402001c10f8400542003083c1800b08032207000d800500c161759070518201c5c01c01c03101d4040e66444a2a6a10603035150f80f18061030740158090054187e445155140207441c00743c03d822a0804e540083c44 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 53222557 1250 53221307 53221313
    0xe1503060c0d02090a050303040e0402011106071715130204080c0105040e010e0903160308060405010501020c03061603020418020a081e010303030207110301050406050f01090207080f1e1801030f0603 87
    0x507210181035041c0c2c0580c80344036440000b00c02100075000b09801d0300c404100043c1400c0500c100394011070003170720380060707601c181280c003625818116190000325108000c130f1071034442003110b4294840c7c0e10f20000600e0b6540e980000c1c103c211414900b0180c240c01003000d010a15050180152940c001d0030300604d014540320b000882030005228a10040e80c207000050a200d41c20b00071260500a0080040150286840d003e4090401a41c800340114070380300000c42c0950002481626001c0010002e00e582d69948a070600a55140d030704400c2016007d11001400c0071550744044103041180b02d0168a50110b50b900070200c0500415113621a804e640314111403000e0740c516181941e07058a800f590740c00c0c0ba42498840e503000d80108980540c1b82c0004c21043c020301707a00050284801d01d0b411011641d9485586050340603c0c0e5014045007004c01045802006a1008041742e400e0180d030b01891310941440c8198941000030040c001d283e014425007042d6a041c4103907414080110000c00071075040d92 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 53223807 1250 53222557 53222581
    0x91a0901021903020102090303030703020408160e060d0302070f120605070201060506070b09070b0d05070f050a020706080402150715060501020304060c060b040f1a040506030601030512030703090c0e150306 90
    0x2a0520800d01c1680102c0040c140300b0340480b4000d10000c1e08a0b592420b04400042c000d500511464559005c1c048000d14102e00301075000e4100c0e031140300f8035040d0342c4030281040164000040c040f0150311424000003a4424048610002070020421125200300207081105c20345200030000c408591401030140915034030381041e90f0403140c01480d1490390756035050045142c1003054002c00301c1034401098103a1071003c280c2145208a606507200b005001011005803158062144400090f800c2103000740051803189401d940d03c0f0340010b06941c0c40d014481400b010340d0380029000d54000c1609100000460003501030400102028402949060325010b00140021009200109900d032640380c00103280da9039410905409158060030040302e501501c014600d00741d0204164000e6013040e0004442d0b20b00400e0341412030781c01001820300c0105411408100f58001400401410b81d00c0d6a000041000e06020a014212032100a9a10700b071841c00d40103219404040b2900c03e502100400200690034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 53225057 1250 53223807 53223823
    0x10f0b0109121506030c05040f09030e0d02010e04020705010b0a0803070b0115050d06080d0f0302031504020c032101060806060a0f050309010204050d050a0618030804030e01030207060c091a090102 86
    0x180b000e03004031600e189003110540d40e12401d80c204450a051012090001428246040701e0044400300301d0040e56035152015219900400303030205030f1070090702d1140c0c14180040049a84145800364055081500040c12a0003005040d00c035695a0034000c15070381420348081020b48001c100540c04c0640c5540d8480704104140102c0072002007040c001c014641c01a01a150500c070100c005000d019141c015003591404072050410000e002103131418175003030192080364015007207284020a48007035002444081d520003005d2250501c0208004510b40d0103140401c0503a0f00d0400c106034070365151040060200f07001501e180d2292400300164070803150002d092200180c840e04000e504c4e5990356104e41e00a000d6607000503088120568410300308400491400c1050388179002c200040313060680c00440183c0c100c2d20080104290001041c00300e400303002d900c0320900c014500903140011303580c1c406081d900f1100c680030219492460170302454404185046204000c0000302d0304000445000035568a61 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 53226307 1250 53225057 53225069
    0xf0304150318051c020105060a050d02060f0708070c0317030702030304121b05010f0c0f02190606030804030602090102010e0c1005030606040308031017060105010909150905070203070203010f0b0109 87
    0x164400401c100901c50246070784050f00038081d1182e002c003c60580c2c002903100300782c0798015440c1000142c95880d02c02018000d46601402c3c0760200f13491340e0700307108503640304112012a5401c10b010038400111901c1c01012102d01c5050310381d40f01c600d1860495494074050303500042d005014003c0103015a8000180c81d405031300b203d0314400c0202041400d41d0401d0f80751904d109440604988582030000540100d4404c4400300400c21680b02c0c1a50704a82d81c404007030030703900103800240b541c6000070352007031103408158040c450001d881e43d501d565140c0e081d4415071048074525004501e4901640c0c080c869040040f0094002d00101c104000000e4404180c40c888401409004800f140c8562621010780b80555440303100c80b070380ca08281081c0e0b0b03240c8199120303c02d810382c1c50321a0322042c540042030490484106843c0c000c4154101905880685140000107503030142040c40010402258050030303000e003070075401550780d900380e0b401803509548180120400180c141901d00f00301d44d074007422280c200c1d41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 53227557 1250 53226307 53226311
    0xe06090609040902030f0106061e021c031e09050105130503090d050c09010807151e050d0e0703031d03060405060a0c020709050f0f2202010f02010e030301090506030f03041503 77
    0x510000028000c00756681c2c0030717405105690042d0040c080551081050707400130785078001050824296460b68141e10b280ba00016041400382e0380b800380ca64204040050130078100030400013600b0210030340155040400302a4543c80b58291001d1241c2807140603084108401b101c50018850785840b941d0f4801c403072065018080c089415018400240501214030b440204000c400c0c0d65603a00007030f030715000ca00400e401031108448008041e03001e41c400300c07401003460680200305009810b081e07a207504901d4002d8111900c42c0c04445951000b80b1101020b544652217180c00b000b6600c0655401d5403002000c5406a407101043c00301144001030b000e075228041102c0403a1000c1108802c90401086c1ea001901c1d440c1440140700300710034820003140c4100001d103aa148166103c03451041a00362411042c84921940d01082c800f55205080720845844c0c4c600012a42440500201e0304c2d50303000342e104a00c41036540042c8042450300340641c100b1840c3d0351000710300300f80c00c0100c50398181d000f001240741419 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 53228807 1250 53227557 53227567
    0x30308070206040201090314071e03050c101d060c06160801061b020f010e0306090307110108010e04110402130b04150504030b012304020304050c040e281a04050d09060e060906 77
    0x808100c9c0c10041e1111441c3e0a41070440c505507810385c900c80380012a060b0143d10080551401e103044030f40640001640d070101d4034000c0171510303524076044c1442583c00460030031410a2441081103154054258102803490200f85104020040340c4180c110a0400c08181c8101707038950303214613060004035012158015004801d20069500c085c10704803040e0180105800c02c0761014000c000b804aa43c003032070155401048000045034911402d000301c80d0642d02d501c01280108070002100a540c40d40608010b24180061080b0000e41000e0781c0105a40030b40003c041c0400f215021240c50703c600642030050416081d85d580c9642071005000b03011040700d0424210701c034400508403181100e000a13208564a062a04003039850700b09240896000b40e0905001c55642500058035029010405e03040e000c4c0c01545416940c80d4890198041e1203481064a203640e03125011a0543c0c043ca100320028094204403a40c041c000b440d06501540c240700441e801d2070f0258540104407400e080040305e070a5030729 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 53230057 1250 53228807 53228843
    0x50a0306051c14030d181101050918092d0705030a1a151302070209090d02070618080106080309150a020309010c021906051c020c030702010e0a030b0f010303080702060402010903 78
    0x16000e00d85c04422820300740010b03690b80721a10642c1d060503a000d500140f0f8000304070401901e1a108004100fa0050f0b5240200c12403206c2300f50302c1c039401213001000e0b00d500b2000200c3e1456842d0006114414418020039444e42800c020406080200000d4018211003003c40c1c43c0c0c45a5800648840005080e00b03400151002c50721180540480d4001860702520007820301c59840290030034007040b805082518003040c03604070000740c46403d84465a0040c840542440e1044610481d2013400f00090010b12a001c107440304203000301409040104000c1d62103030b01050030011642441c159000c0d4107001004041c05040d4013000b01c1c0c960910a003002c080c114101e20204060a0585585120241085c58007240f1b603039024000300000e021600c1c41810b50601e207a100000c80c4644881c0c248581d004100e540015400b07820031282c40c2600034210010705545e9290300f00c41080c100e84451501c2402c1c401801055000f4404c150024414402000c4c0c510b80340d400a0b2248200c1c0c080030b842c0354038400c010040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 53231307 1250 53230057 53230063
    0x41d0a02040b060f0c010f06060c0c060f0309140159030a020601031712010302040b040e0d0f0f0e0d0605040c0807121709010503040605190507050a0306051c14 70
    0x6001d03032002ca59a6950f000040c0c02c3d00a25544182c0c007442c82c08e00030001480c9128000b001e4049810400800c00c0d54513001c03040e14034001c1c00705054285910341080202260340f41507407064003005400007040000642c10001c41410b00c0f4059030a20000c00304594400035051000300c084030884054042c040e49a04e03c00d6800c2c0c08286a10380d80c0c030300c00000c50110b80c55000c5101d074100c0384034090f0450442445481104503000784601512407007020310040000d8076194001a180600240000400000c00c1c0c601c2410315a51030385c050003084182c4100000d2036805901020034001c14640301d03150f03200c804005243c0c1e10080303902815242d210341c0810300740f01c0d040703054400030620141100c02d4540c3e543d51400e10708000210a50720001c0f030324032104000714010112110004141c2d10185565103e230340390802024007900442084c01410300255446006100e100d0040e880d07902c0305a15100c200d01c0040580e8940d4000500412401098401e821f036100780c001901d590203802c03030985031000e00040b4a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 53232557 1250 53231307 53231317
    0x9230613050702010c09060801060f03110c07060c0b010e0c030a0b03070e010f08011409060414120f030402042d021608280201060503030909130b090c041d0a02040b06 73
    0x80e40341c50301040c0030790360360154405180428644c4070031540d55565032059440c00d07002d102d08408620101c20a1428070705c260300c032003640c0301c81003c81402c001d6600511480c041780c903000f440c04110b1a40c2002d051200030441c60f40100158041c1c5203080c9001c00c0d8a54483c00042d00b41c16071140c50780a200b40e280d070144441c41c090034440d03000c5401503942e20100c50243c0410310801d40c0d0340d441c11001600f45100714900c14810740d0b480c4000d040a4949030b80d1044408201d6400c0c1020b030180c900241e48000b04100148840c008090001d5103030304090040001b15040420b00c59096001c080102d2001d1203442d80002d0180f41c07010006031140d40c840601000d42c44015170083c00d01d00e000500c41e4014200d4002000d0321810040b1190200b980c4680590880b1500c1c0a82c039810760082c4030450503890110749050340b1455001c14103503000f81070340d02e99160039401d03111548280c01c1092021001e0400e842503644400c291305600c607e40c109104d41a8482e8081003000c1d000c0d988926410105032280c1d0308030f034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 53233807 1250 53232557 53232589
    0x1602040f1104061119140709051515030601080a1e091505100b0f1315021b04090c03020603042a050103050c0f18040f0e06040c092306 59
    0x100803500072070710031400d580c014040e04020600c400b00000c640348001030800005032401903080f00005c415114a41084096000d401036481451000b14410209024942c09110300b1200e5205c0e12200404200c001c11914207892029142881006440d030ba00290458010301043c8002810b01c4421428620031003003810740c18a0182405008000c1005204118020709845401000035071290300c080c0700c15801501c03034401c0c0e0701d00038410002e01d100c440b0003c00e401c3d0344400c0c81031040ea9841d10020f0311410103c00791005604980585000c12510400400114000300c40802001c1104c0d9941c00940743c01b8000030b400b41401000160810825a150014103110f89079080e11008203404000800501800358a00281c00d000102d918860700e48162007248904000290902c0415050581e1605040824980c02510344540c40310409452040700f06034040d00024000380c6c58141400c0e500d203509540090383c4036151500d401c441082c1000034041e0158000d4036000591144800289420801481b078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 53235057 1250 53233807 53233811
    0x61011070315050108030702031509031308060402130e0712050304030501020f04090b01020a02090609070e06030c0705150603121602150405010e04052401050c061602120c031602040f 80
    0x841804104030b240500e0032500701c4184900d07030f00e80b900070b601c0703000740000290580c0c4400442d0822000300c178249640480b1383e03421a4101407880300d200ca0b044074154008003807501705009210540c280741052500c11480c4075002e110030741e04c016503036585c0c0485200f5009030150f80c02003041000004e1045a00860300b210087d51140ca1075005403060364000d00c04d01d07030014940840c0300d10303d500100c1c154003003c6c1c004001e54101c1d43c1e030a0900c107404800800c44d004106083d0560043d03640c600340a580200c002100c803d0701d0384002d01e03000e890000c1810203140352088901c200300f040d83c1d0000342c425859515072011603c45220841d600700c00100480000d500c000b60304c0c0c580b990445503501400443c0c8090703988400c0c600c2c00c0c900740b108950054400a907070240c040c0a170b00048441c030078403081c01030040c50154076200340d44483d541041426540b414400c2c07889081c00384e6a40c0d0400101051400038104589445000914a07640c0c2c844d0030004030000000d87c1003441955281e07800840c40c00c0540c401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 53236307 1250 53235057 53235059
    0xe040228020f0a0b0a0e0a12030b010e01090e07030905280b060405040b010b0f0408030c0303010f08070806010e07030605100305071d06030c180a0303020a050c150306101107 76
    0x401103411280101a00103109a11072400c8001c400508506540e4100c0c0c400a410f45408541c00c010340720003841484a4450b41c501600041c8102c4d040e003803560b000780d40010780c0d003100c08001445412450320305410080c9004d418041d510708022915000300c15400c0002e001a124580a801d04285892021024507465028810001029400280903118a10805440c0d54140401c42102d1050718054400c1240300010b0096054600003032409080c03060100342402d40c1c40f6000b07407643e8850889416039403c04001008008103901c040005400440701038844a8100200160783e52014840c840032180401c002c5000c4a019a20035230240c0005044181031007581e40014000d010241d0b5101c2c00501c4c913500750740710015180b020f40e5903610018002c03451521107400d81c81e1a500020900c52901007020006c01d04d5559429400c07004610a4020f8080079203a800c105041108462555000e240002c0c14110250f06200489074084d104840c145c0940849080c105c4804640e881c0d00f0000d8072403440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 53237413 1106 53236307 53236357
    0x30d09020604090204030f11120d0507030e06070f2a030201030f150305070305060901020a0804060c0c0c180f0603050601051c0203070e040302010c0e0906010e0402 72
    0x11070309041c1611410b200c012a4070540c411140ca100d0030111404000c00c56100da0100d650032110003074440b10310a074550702c464007482c2101c100640007540c03608043c06580f1810000384040d00c22a107562440c9002d02c075401c100c3c41e050340c444c1e0400b110641245e81c280d641d075200501d5682d40014140c41c59006401034810242e070104840e44648651015040080e030240041d030240e00105000d502e1800d2560402c01c000d441c080c166401004104070355030300255081d8001d82e1091000500030030900c000c417201c0842d8000246011078803000000e4004c4c0f881806020401c481008120f40c1d41c2011070303031048941e40d100c000c141ea0010702c0108018503202c8242c241404103a02e451b0507040c603a5002a00b048141d81000c044011000140800d06909110b0800600114100038003101c0d16000021801c0c5402440e40e4100705410b2000c44058889806a400050840c210881c05110500b = true := by decide +kernel

theorem cover : BRFrame.Cov 53057557 53237413 := by
  have h0 := BRFrame.cov_init 53057557
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 53057557 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 53057557 ≤ n) (h2 : n < 53237413) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
