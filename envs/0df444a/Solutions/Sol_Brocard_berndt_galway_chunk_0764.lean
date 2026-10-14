-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0764
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:39:15.994549+00:00
-- url     : https://prove2.me/submissions/90d9f1b4-b359-45d4-99f8-1a534fc4e8fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 137230215 ≤ n < 137410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 137231465 1250 137230215 137230241
    0x1e2006060315090c0d0501060f060801050310020703210908040617160512060604030803040804030c0e13060b1809010b0108091c18080105010611060702010b010914060d 74
    0x4182041414102441902401e41505000c0b52441c00e100800c142c5540101001c20701511600c00f098041c0403094101d070005107030340c24120540070b848400042036030000f4010103010b48a04000120038007070a208444030260542d80d2100c4c0049041c402142d030820b10322401d001161960303520400f0a2103803008000404140d201c000c51b040004603107644130300c4001c051a034440c004540e659105a004403c039452440c1c442d40c011328641d141d0740003a40358002e541014042e4840441080108905d800041c4107a80c00343c18001c80403541c0324020301002c40c048866444401407040c4074800180301e40c01c84000303e84024007903181c000b01200c00f030301c0c0c150003251043d0190b919451010201d580000141ea04018020054400d01d15144180d2001010301502c0b00200041d03003808105004200031010050a066070090029596404004140d40e00c244042402400b4001c0070500c6980140b2a181c001070068542441c003e1411180424400ca228140c0c3d030003001c00c120942c054041131045100007000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 137232715 1250 137231465 137231473
    0xe030408010e071203080a06180c030b03010507050f0c01020f07111206060a0302060313020d060617030306150a050d091a070c020d03050901020a020612040c0b131211030d0c0615061e20 81
    0xad000c401000d45000200c000c2c000e03403500302031144455012007100c41c4000100704882c0ea440700c40314624028400d851180a032203101081000400c90218164541d00c00b0480c0d07969481c805844149480f144260b4142d03a000c0850b800c00c00040c2060409580d02c0785069010341c0c071030032080d00420203030807500c0b038111811995070703800340204000c210489801044000007981545003800c08511070500c20804601c148d0408500034038800d100e0300440b450a81600414003001ca6540f501c58000500107091010419800c000901e41c24031039403420308013a8004150a1141456071000e40d013641c0480d0000b4118000c4401000168031960014559410b403d030340b5607120301c0c040c144011a04c00c2604208082e400800818a40d1240044640c05541c0d062110894102c140d01d49454545610011190503015480700d0000c0c441d000000321607260301610701404100d00b40c03001e40c6030300c9883d80180f4011689000d020101d41c1001407041c0c590341c0c81410002a08108420290410400105189041c0d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 137233965 1250 137232715 137232731
    0xc02130905070803040509040605060f0a0306091106030c0901030509031605100e060f0403030b010c06060801150801020a050d0216080f0414030a0c12150e030408010e071203080a0618 80
    0x74003040448020301c2c2d51000785042c1800c000000f205028040c001802d0320f501c540120703501c1d42d16000b0340081414020f02280700c01d50b41c4d11b052805003100860030390300c03942500304050550800204aa200b03c07842d0031313103074038240c4000d0040d8000d14015040c0070303da200601000c00440301c9251942c000501880027041100318005516040c2d40074605071000d0349d00000140f21a0040c0071000ca9005070785400c000c00c10300c000b000100ea819001c1e500250141e820464002030080c1d045d4082c81913510003400e44121b141c0c66944e681e00f40d10446d00c006001649c108022015003c4550281100d008410f40d03004150507191580310039604510007003d8489000101080140a440070f0640060010b5016002c150320680381c864102900f44151680100700070814010403841d00c0510407180c0d928041004a401c80807440703581d0f03030000c0c01481d92542c6082400b00345c41d000000e8178400c440040440344024541c9a034111642d5601602004c41c035130701c0750004160040011041800e209941c1800075103d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 137235215 1250 137233965 137233973
    0xe12041e08030a080103080a0224010303030e07050102032d1207090f0f03030f110d0207050f15180117010603050402150703090b130314061b0f16030c021309 69
    0x580e0950110409a00400040f4402c980103081581140e4111188035110019828260b04100d802040f41c075104881189500180084a1440341030328001d9400f00100b8080b4403003503980380074600130240580d100707010700f6105000e4581405086139905900c0b50503003d08143c8000503400c20074510f4180091402040b02d5158020000001456a09810010a8a4186580e02404181c0405400c002c4051402181203000320250302300f0740716682c1101e0355051035210003134a4044a001e000c3c400d050b001110546031418001a43c9641c090211003031034a13100240240c0c066a18018140c1032100e154003941e00c40300a661440c1c000c000e582c0b008a1b051030b003407040201d82c2e80e003070301c0d82c0c04c050b441402a035002c2580002c0c0c0c0d000380e415504a46507907159907640c030884d1a00a500003841030088003034100300c402011400d5405002080780c211542d4074001e9072400e15005030011980240d00074815944000e400400842d1803034002e0511480c1c60850340c001c1442c48861104858015444000100c100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 137236465 1250 137235215 137235269
    0xb031009050c0303161502091207090c02030a021023010303020601080d2c061603031b0305010848030c060901020a030c05030d180615030b04060e1204 66
    0x401c0040b00950b1411344855402c1170420655403001d0854500c200301d10012800c260304840c040c0c00000c007201c8840c5417a450081c1d5401160190026071820f20081c9942d680c0000107640036005540c000e80b40c82610400f200d4014085814510710b510301400e080d0100041c50b2100e14040c50180d4060302e540d41c10102c4c41071070058050480800c000024010101150144410840780c3d140b10003107040c0d07502e8200000740280607d015030200c0c6519501c0d401c0406070191b10041d50b0310403502c405007002030380c03410503000c40754244504801c03600084c204c20826000c2c1d02c1b2401030544074141329140403c02c0302e04d03524244c0f49403841c0064a140440b40e41d040d440c08201e80c40e04058119640f61400c5e0312440002d40300d83c01110001c0602502c0c5441c03508010083c000d50380e000803c13482c20404101c0820000d11404440c00c415110a8034000c030003640031610003800011780e03801582003540c9488580d955801000b241191484601a111207000001080c40003840100314540b0508013560840c01d02c4409 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 137237715 1250 137236465 137236483
    0x5040e011208030103110301060b04060201090606091404020d0303090506070306031a042102031e09180603030906090301200904060603061505091801180b0405070818010b03100905 79
    0x2001515200d440000c20300000c684c10340780e000c404071220783e8400d80404c0c050301032030b00089200c40d008280451216030550110380a140114014401240d5910b0382200311480da4101004020a0100040c0076052444000c065140301e4a030000b14801103460741414204280c440c100000c4c1c0b83e840c200300744101c240e000000802401212016070406940308001c500da080d10400903a03081d04410700209009009607209000c98032050b4010071103010b29803800354003002805108441582c2c00b12400425004070b28030a4802400540c17411211004200d016000341d000700d541503403503401070b450403050722540380108500810015241c4940a08002c281c1d00c090300b14204140c030f045010010740c03080800310062600c1c1c50504565804070742011688050010026151410500b00002410f02c83c521a0301c00300700e401e800400c45072480c1f00810040d40ca05944010028001a011441c02c14840c5008094449080c00000d9014021000720342400c41030002400d041e99a4401301c018040c0078409011 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 137238965 1250 137237715 137237729
    0x20708030a0f0507120c050c010e010b01021606020705010c1113051603020c060c031308030106020c01030c0914130612060213050f03120f090a122d08070507030204020a05040e01 78
    0x500d861800144800c41105a03203243c1d5407070320592141b00b40544102d91032076090344024807a4581d55a80d5a01901a400710f0a005120f503018180c444410603003018182e445942c00351450b00e00c2e2000445070f14140e004241c1c0c444d2030507100c10100e9607511881180c1c10081035000b01e0030789450b04650000c4074000c245c140c02e0500400025491001c040b602c603900441c1c003107103203803130751980640481014110100140481d02c008000b042c5642c000556a01a49090b0f0b8148060808018100c48400b8203101c1d4080a146851180004d85060a05c040c1040c041c2c240010703003507641c6c1c0c941c18142c005001c000d0715020f50010f0002d104030410b4005002400c01030f02c01003000c1041c0d80c00700e82e40e448285c924980c07100020407040b030501c2e1010111008400020502c1e0050368803950440e0391041d180208403240800c100300603c2c43d00c8501c411485405030b41c80040040310440c1c440f04940d620400003190280611840440142d98500c068440e0900b00c6d0386186d00d07941064443e18444c641a08100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 137240215 1250 137238965 137238971
    0x1b020f010b01110a260a020a0c120804060804030309020303030a020a0e06030c0708210411030d140301060c020a030804030308011d0c0d0c2006070314010815090a06020708030a0f 78
    0x488900f81c00105048095840012060141c0d45c20600c011442ca1008602d03510110000d00d04565035130004403103132031500400c94103070746a036144c42040b5411707000c01000301a250140820007080d801440110b40c001d00a04000c00c84880541c0040c2c2503070310440d80c2100c100c1d0702040c4080701d035900c00416201c40b002035540ca840c50912080c40443c074000c032a0020144500090220500544081c2c1c044842c0303070507044170f1031300c2c102440c0a40c403203401040124003d215462031000114890074004005964502502d45144d0802c08102c0e075044c0407081c01c3c0d030402c0000400000248204005000440c0a5070f103441681d41070000c000e02c42c480c01d03140708040c0e11405040c4280005550221116108031040000b08c02c14440415980f89136844403181d55002c03421031540e0b40c0d0f07001150081c07141d8802c2d40d0400c21210343ca001000650420300400c09141c1c02000c2244c4425040348005400c442c1040865038070409681d50801039a008a48c1190602008010b02403030003100c1c01a10440c4042140078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 137241465 1250 137240215 137240237
    0x90a060623040216060b060705060907050108070206041a0702010603050304090203070f090305030909152d01020109050c0904170c07030506010906231c0b0f06030f120d1b020f010b01 80
    0x613042c141c001024040b160748a20711040d59840c00100e810b0b0310b03400750640300c80e45080c611241d10740c0003601c00d031030100386c1c0100001c109034400302d030340c46c81198800e01300b0b40d6501d905088035061040040172001559607480011000c1030041015200500c2d040d4005a07880c07622035070040400804001207001e005d034910003400001c3e40403050360b0003c20113996007107080c0c1d140b41c03408603039040f54500030790404103800d040b01304007071603030810038010490250400c481c1c40c0401c012400c95400c00c40182c039640184119459a00d0103017419500300307000700c041f0070000d04c82081c07030103566020101d0302103203600541c410420000c0602c901c034010441d041c000c101c3d10780380c000c0c98400103450100c20700d180c0b80c0384403485000d503541c985800703015140c0c00d02c10700034100c1d0b034580042d4001c4142d5002c4a448040c40002c0d401c0c0c6400140b4685041c041e002a05032685141c00b02000f54101040c401925500c0b0b10f804410450796414403554406194000d245808400315403508440900d0341c0b0381c0c10480d00b580c0e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 137242715 1250 137241465 137241487
    0x30402331b0c03030a02060a0b010e040908091e0a050d080702040e15011e050402090d1e061b050f0304050a170304110a1419030f050706021005090a0308090a0606230402 74
    0x16a80c0c8c410f041d4100840e0344c601d180012511207803410341103a40700303180118400502c030618010300319081e0140c03041c1104c00c92111940c3c20410f0b410650030b03408191088107002e2810b0050003030380094070418032181044441d83c0040d081d50000e6550540542c048004440c00b80340e0440100c0c014400d00360780c0c911082d400f21a010703042120707002c1c0c240645c1d0002031440407a29051480b886c0644c2115041c12120304410a210300c01e503a2003020790b229410441001d001c0380f180e100b140c00102d46030b115586002d00c038414984a035000200144d6640c000c0c03181120209480303402091568211400c0701e55a460589802d071605012030b0f4655005640f82e40050141c03d5848a00e00c0e1551011101100c2c3c4041034048210002d09503000181440a80c0c4034801c100040003928205440c0941c003078840a075208051b0000300c0310100d604020b00d90000e0700316004a402401d4041d0424010000e441d041c0c2c0300354403030340180c69055000400305100468a9400c1ca89641e50102c0c0325802101e0075481c0000d01d80c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 137243965 1250 137242715 137242723
    0x603050c0646050a2f120c0705040209130b0a08010e0303040b070e03060103080c01110414030c06130306050c0403140705040501080d0c1101020102070c0b040504060605030402331b0c03030a02 84
    0x38050f0700410310b06840313400c081d803800b41c080301d00700b2001c01c84041d46c16243c0850742c50b800042080706584074081e000b05da54035181c000e54107080b4001d404e0058035118900c1c424064490039000380d030011424603002c10340f90780c00c1c040c8403080c80c00f080045650b03013014a411040487d000b0b022004102e6050030840d0310381c1d404501c560440b6007001c07443d91244102c0100f140141300901c04c4d103855140000d4002107242d4190703c81a02c82504500741d444c2c416003981400701901c036a03481a030b490407000c1410310001350310354003082d04514460b072000e05064590383d0701228000d000b2419445030340304400400171842e041c00741c2809050f200d0040c012030703c000c03003002d4052482d0b40f90041c110381c019115600300364401d40c140c0e001550230054003030800ba82c0d00c0343d007846684180503440c0100d00b8040c02040711802002140d0280344d0103030848401c0c58a04d00041003034000401c014100c0d84074118507060501c0d50034050007401d88040c400300000709020801c58503100c9080400d500982042c4018421250046 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 137245215 1250 137243965 137243987
    0x8010e040503070219050d0b101406030a02070f0c09140a0605010509060c3301060305011a1317070503100905032203050109030e090601030603050c0646050a 69
    0x541c071740c0c4802c2c18503840180d00d20000c2e00402d0704200e07411031010074001800710040c0100918400f10450701d031502d6403055020403510103590040c00801c040b0702c031610160f0040415500404e030ba640030000c26903910b0312800c603d902c402e1610380c9540c9210003010300892003641004104008200d41841c000010702503025100c41d56102e0140820480301003c410b1017180d0105c520003401010001c2c101480401302d002c0c0340c68825807040241c001080040c060f10406058036100c14120a50900e1810000c400c0c1d03114444015000c0041000058402000189040008110409800241e0809084c0751904011885198080d810003d4280120348040308546801d40d50403114450305c0c4040781d42c0c01c4c40b0080c60b40001c01c0c1d0340c41d065441080c16401990b0b000301c0001107640342c3c09900e5441c0110255100390001038030a0700a6842000985081c100500c1a00380c49440c000c40005450700103803c1c241c0d100320f0790307550a14104500c3d20f02611035074041e444651508007941005421080286480b4408c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 137246465 1250 137245215 137245219
    0x110a0e1f230405030304090207141f021c1104050f0609060412030507140109030905031507030c093311060406090618060603030809010c080f060409050708070608010e0405030702 78
    0x888141402410981c003120090840501102d646598070050b4134000d601251055a200c3c030f03034400000003244003207000004002003440c0c3d0400321989800406c001d501c54000c40c00c2003c0740656241610885000c0c0303220501e045840da40d122443d103004d00542800b055a0184a0401000300021329914402520203070b41003046092101c00440c41c05440622901c48050884000c0745404010b110054002e06911803017580c0e1941256a1281815a10400d85200b200c2d4400c00350001403030301f482030f4495064401e40c0c0c47d0a1035115500c40741c10744c007200300c10000320840910001c004854258070980302540d03442d626100031500d1041480720b441380005440100055100d452200510960750070059512060b582c484030980000d181807001420709110490108121100160b1040410f100d02400120240c4414415944000d2041c4440900900040e4003540d02d0000b04041101040058040d001420090001905200010305aa501607128074a6915040104000a031021040d15986a81 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 137247715 1250 137246465 137246507
    0x102100605130b2202090a05150a0f020111040608010815220302010f02190809011a010c02060408010c050a02060603030405100c0f1217090c0108130303110a0e1f 71
    0x8580006442e04c4c20b03030f0409500720403112038200e080c03c1c199801481c4031041110a0407083d071ba11402e04c50301c0440a8101c410b45407060180140050003004c0028010003c1d10000500b4000780c13603c408190819040310000500300001441000d504001c0c8a0390340040c0480b480003450440c24112001c00b920302e0041325040308400c10402c06000b500042a41c001d00c0703505544030b0083c10141c845031a00c840c42600015841c5011070440e810610030300d04404031071101c1004a880c140c006440c3c14400220803070300003604003c0000e00381428860195040a250b03105551a0309076840280b034400042d007440e2107600700300070401603a0b440700810411080d95040c108420030f601d00305814060b52504005d00303298100c80c1408481d643c000c0c107041c86428003000c45101038031001c405544d07468150b620103002c90241008103000d001c103101040b1703040d4840e1034042003501000c0c024003d1030300084515004070317800200700038544c03424681c3c1e40d00390300d0b91039001c0c20042c25180c001482e06118015908000031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 137248965 1250 137247715 137247731
    0x1080d09170c151201090b010e010c0b0a0e150f1b03090a1202100c0201050a0f060302030d08090a120206071e0e090a0b0604030507140604080309010305070c0b0403020705010210060513 81
    0xa070316420307a83d01301c01200010302c4a40e502d402810103084032020a41c0010040f00044d04550702a03c0c0112506030031852a600c0d90392140a014000d0000006030038042c41040b940c41100c0302c400c2c0b625849204e6004c81040503081c010301c00103245180d1300d41400102810710170400f001c0380000758943d445402c86251503042c502c104040c0c0c1001c0000c1840810241040d48941109405410140c0a00d0b01c10408124080e10806200100d074801d0000070350640114903080c2549209209a5070400d400c002900d540c24406d80c1c0301440f07450300c440c9460144e0040400c0005990f00508240b00c00f0803c0740d00c1c0c44410310400d4005081d48803807103000c1e00c01d20124000c00e02202caa60702802040030082e00030ba0340e035a100d00700b10b540c0c0c1000744900069207660030b83c071906500b0704000762002c642139034009500f400344d0b190040d005000c0007441d10041000010071100401c0701d10f994540154000c0d0080c20555080c540028203103803184d105a60017a0a200040100e61608905050a451340a100003002a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 137250215 1250 137248965 137248999
    0x110103091a07081b0405040c0203040e040b040605070804030c0204051906080c0f04060b0a03051f03030c1403130e040f0c0e0a0c030b0105040306020c0703080301080d09170c 76
    0xc050500c0207450418100404034032244846800350003503001e5100e0224039555440f40d4422441000f1380c074840c103a000c0c001000142000d80110354429a280152810142c58107204550b0400444060b02c060241030144018454503204007600040f00c2c5c5405143ea14090b1405400002d030b05800070b005940d05c200180351410b4280d056042c6400c3d4440601945a507109801d0303403102e405070013a01c6030101a9040165192900c0f4541c1104c04040c0090b0410341d91800c03d400030100100740c40a40fa0300036070201c0125a460780d084010314400c0d190702c440c5000714149144051800c61520100303500c10003030b490318001f03000100c200700c520707101c50480c2d41d0781d030b625100c0410300070303004010402910f21307602003051505100010720803030940070200400e0700510012000d54500321005030101c0d00410060011805540003003076100c020380f0403510480e5907691031040b10b602c2680250280d41009480540315940088244002c00c2d0600b404204609080103203a102c0c00001001440f0380121140b0030145 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 137251465 1250 137250215 137250221
    0x9010b0703091509090b030303010303021c02010b19090c0309020a0504020d0b042c0106031e05150a0606090e040b0105120f0d020d140a0c12030b0607152304110103 72
    0x140c20b01c20352000c040043c0d56006000b13910346010741d071070312802d2400c5e101ca142400030035241240c2d015402807103084120010a0203601800c030528045548450802040781c175015100006500700a56036200c4622b0f003800c6404440002c00140105401c205000c00540d0340d9210590642d40d00b25030041c0d0320151460b034003000344040b89103280c00c141418103d40000d0318541c07a00740411148030407240143c1840c0c2c0030f00d00720740450100500c00d01079a0340c2110082d10729143c1c90f480b00d11901c2100c16401e03488000d429030050445480b00c4c03994840e1410302102c1d5010542d50018007500b8110141420156200342240c101400741600566210018140d0b503002003010310800d03d5080103a9481800d240030003500d450710341d0140e402145069045200c805441c40486e02c0440260303403210f20001440c0e03a800c2281003000d4441d010580c403145401c8041c2d0395107005200291280c0408a026048424410251a15080041c900303460002d4a5944542142e10240e03010b03500148e1038a60b02101c100503802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 137252715 1250 137251465 137251469
    0x30e01060504061202010201110a080106081008100b0f03010c0507120c02060d05061009060c0b0c0c0d020304150512011404090b0103050604151109061c0c09032009010b070309 77
    0x30150500f0350000d940103011440d88002c0e4000e90007444113008010310b0040d03e224404910002400b03420040100a11070f070140f94020a80c202d807507508554903822103241114401c08440000e03561442002203113405c1ca000a000f076001d038001e10003848403c5016140303000f410300c007900c440140381481140601c80ea10418585500800c1d0940301d854400c03204008040864500d4042ca0f00c1c204441240e074082d001c040100c0c0c000d0395030700440d102159540c0ba200c81020704034a0070100240711b460b203900820310044c1c40503d0240e00545d200e600d440034041180403650550b9041c84000c004502082c04184001410346410b00e00c0c00380c0000d45c0d00040b400800c0c084c1006170804901d840044200f00340130600901660051114070000d0a400304400d00300e607400d0354030000c181d508000000c841e041000143c9800b8410800c0480301140b4464002c01351036000400c800011100441441040241c00c2000101c00b510703ca00d0344203000c1c00c3c0104840c1001801785050070740c0041400001c05200303001c1440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 137253965 1250 137252715 137252719
    0xb0f03070b280f0201060902030c030c0d0b0901060f14070c061d13090209060a050f01030e03070506010b040513110406032f0d1d0604060203070c050d020703140a050d030e010605 78
    0x1d185440140b000300440050101c0030015400c080002604801b6402520700500542d03030804c0c40c50303d820022101940c02690000c03001a15200303e50300c0303a034644600364003d00d07041e01c842040410b40340004211142d0843c01e04112031003071198201052004003010156502410002300c1ca15500d04001c0034988070788803480e4042c0743c0440907107884810303400c0000c01e244240da100600ea11070404004005103d4001d658000002c1d00b0414150361080d00018144004a007d4038682102c030380301d00341040381c01d805c2a00c0c05200081c041148bc108600c010402d864504010040d060743d00b00d00045e42d100e02c2c42190101602c80043c5841f121510580203041000072038030198030038181101410f603401201117001c855180c00089892808405840000c1e03243c243c000d0415581c4a035500c40003900007410605c108421054024002001042542d10003440d580080803000e00c0c520702801c0280c2081c500700325035080074000c14001440011a160a84954240450010804a0000d00401550340712035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 137255215 1250 137253965 137254027
    0x91a061212040e3310020d02060a020d02040305011103010302030d092313020c01050105040b0f0609040e0c0319120f0c0312020903030a0e130b1c0203010b0904150b0f03070b 76
    0x14aa810340314401458245060f280c005012003180c0d01a42c1f40c40d070721400403025030426000210005825802450000c09003c001420300d5200d03100e50342180c002c41484d01e056500000140103525003003001220b03416182c542101800d06007124201d911a458075407059452842050114550b9240755501d06005000021525516207010640c040c18080c4202402280f40c45017014050401c84480c1090307440180c07120340b8001849003408011312450320301c036555010b2900f0000e141d6030184920944ea40080395042d52092441c18050160b8104007414800d0000040d00303c0344682e0420100311145405040c0b00e42d0711014003000c3c0020f440b0709030130694103000010f00d4115007600440001642d90042c0d030303110000395902d164401200c40e0112226441161210407114001029240712809807000d03001250200b4a1804201d9214040d1401c440348040d108807040c03450854800c21140e050202e031070850f01c50781c10000c00d455030558012490346010000e01460052082d1954003008880c804101d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 137256465 1250 137255215 137255281
    0xf030819050f160f0504050f04090209070f03050a29010207030c0605071406090c1201110f0705160b0f0a09030f06140a0b0a0b03060301091a061212040e 67
    0x14482442c088522103203881040150780e10561103103002140c00e03607007a180e42e882c1a04180c00c00200070b4145c1d0000f45d1103516240d00f240141c03030b1445003d0081c901c0d910b900302007603130041c0c001e42512402000b48400520300301f0300101001503001171520710013100b015080916481c0700101d0a01d01c0b5504050800204120300003001ca6001c0020040070b4081d841c861140c2050741125900d540b400c0d00c010320745501c148a0107443e8502000d005011905100002406940d0540b6410b0250080d40c0c00c4040c441c00810f440003401000c4c0006008840c01e8140d04222a0a02d045c0203910f00800d030820600f84004a40320101d0303805070804201a603003080c92001400d41520b4103c0142c040c07400412045040500410808003aa0143d21015540108180f443c1030411004010540000701203d61540d25411004003107800d0000316030829052812035481031402d4810300070300c0c01440c0e402e12150b901c0305100b00074910104080c1c41c04e9a007485003241c0d0985a08441c020048956070000f120020142c80c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 137257715 1250 137256465 137256481
    0x30e1002030c10020405093409090612030f030e011118210a080d020f03071112040e0f0a09080a02030408150c0331050a0b0c04030f03081905 62
    0x900800309580040390b0382030201c150f991040e8080e611405822400100100d007400e090080c00b0200c543d412034441c0b13540d68010b40da4032500c980c003200c0100450040302d01481201c115000720340140401011030400141d65940003000c4540290007441099070b60480080621800c4d080314603c022812251900d0314070500842440284805c0341c203101c3c10340b03030024404400c3c1c0c0795a8901c002083d603014000e82c031013030384901010754030602e011100316608000d502c110043c44070207980659003582c0c1d4581805200f018061800034030a030448140329091208200c00c50320074016a50201d15040c1c0c102c490740b5544030075000380c2121640204500c0303000c9200d06802d9070000103001181c2c0302100b1211044160000c41d02c48c4003056540b81812402040083d4451410341c4050301e25076030b0007019240b041c56400b41c0c0d41840c9000c0c0e40403a01d17600b09480b07074014442c29840b5240c000e44c40d000350354680741c07540da6252510401200f005042c81600b80018141c20240c012603184652010300621040ca4202c0d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 137258965 1250 137257715 137257717
    0x915070e1002120403061a0a12061509050c13080606030d050d0b0301050420100e041a0a0902280509010c0317100608090109020307050d050703060f0506100c080307030207030e100203 80
    0x404421f41d5203003000402560701d40703000c1c01021110710280c41c4e030a802090325500f026098640d0420300e40e1020b0200000d010441e44a05441148201001511812114010720462505500c054802e034003080038420326640c0880e18008081d031600b441662954103819803c09411081c4403258154a0314080206000e10850103c0301640b00f0161075190700340200c01c008564800142e100300140320b20341c03141800c1c107040e0b200e112400401010700c3d03c90040900011101005070700404582c8c0e801081003240c80701503107040d20fa141e081c0000c540ba11003406400034014003505182e0703810080440100400d140c0181c420740c46001ca105591286841c00c1071f030504200c0b8a82c4a000300007205c03440018540e54042c42081a0254000c014081c100d00d030404104000c15680c005840c580260b48000001a40a10a0030200b8045c1080401d0074a044000c10019a49842001003800116151100081d101c02c044075401660380c1801a1201980d00b81120b101c20802100c58101c80340107480c1c00d503590000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 137260215 1250 137258965 137258981
    0x20d0504032d0e030f010c030e010b0108010b0d15170a0c05010318020f130f0c0f0c0b0403050a050705031201030b0c0405030703150b06040603050915070e100212040306 74
    0x500c9022000d12418407505400318114440a9142802c2200d440240d1180490008507407009040f1110b105030303003a4903421107000300755050100b6550488802c1c8803000380036643c0078000c2400c20000710341c5084030760b140611490000219480d903075a420507923144101c44c5007000c2c002002c1e84448004040880360b503030341a20281035880881c100d900040542c82400b8480e6003107229035007445100d04903424801e64807050242c10b0344c002c2c010312103144000d2682c450248007100e03400700401d040042d148040c20300b0407018144800c0280040d0148040340c5018040c0d0f81199040c50501da031103100c948101d55a00450313000a205002c0000c801100c0b1141d1136206060b28003444044d14281c64001000c20356100380d110703094064000c408100041014000c481c9103c0310403c0c0041f42405000000030150b511540200c0e0100e941c0384148228001c0421200c09075040d4009040154145420003410660700c0303105091051030001101501b8620a0004851581188a410f40c49035124908400941210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 137261465 1250 137260215 137260217
    0x41203050a030f05190c0519050405100203091011191407050303031501031113170c010804020f0d020a05040c02030409110a090e18030f03090c04061a0a0c06020d050403 74
    0x219035240e0b1810f0180c441c8501880c18140d17a51031030000d4418002c040d2103d1001348090000a03c40090702c409156800a01d5a000f547d6139a1380c0c41c00d110030003145840213440d060440d8400d00ac0d01d240c580794540e80c001e1032078550824a0304007060124180c0f50521030010180c00c00740c203035a40420801c0800300000703840050002e964040d500c0ea002e140c0d407400f00301e50302c40c81b24000c2300003c5281d5000b0b40c08040700a4607056100d291891000942c443c010280e400f460510740c044064500f4042c0901c009800f2010918104140c2e04150700000c02d8a0b0b61009058401c02c020741802086540304003600c8010300c2e001d0030a1007a820040c0001e5200d8025100c1d00c0d080b64241001c05144070710800850b180c4c5003047d103482c2d907600d080050024a0081c002c0000c820318008c1e068410405c0c1007040501609036412810703c0c3d8a240c0140624103100000d00c4040c040c4d070820509003c4061400e2035002003040c0d1100b02500d8000380001140c0c980c65607400500307910b1000845040c15003d0b038010a202d41e000b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 137262715 1250 137261465 137261471
    0x40e0c09060403032c011b060e01020c0a0b0a0c09180e121905090303040b031b0f030403030606030911040209010c0c030605040b010b030f0109110d020d0501060e120a06050c041203050a03 82
    0x202c940c00c045d440303c0081960b0029031500e1440c05990350a00d6800011805090300290051000c1342d4282203a01041120005a0001d00e20030200a8102c00680d0f0083c0410030611509440c1d240192600700d150062450742c41c801030113241512415800b40b04030078000320031113960180040c6600b03034580c0304a4805400500701c0442b00d0001d8001c800711401820040c0007103141502e88144103005400280200190391a8107495031848007162000c1c02c1e103441150225a520f04003498081c084880300d903c440140b40c20320f0300348004038031105440700c40c10b2001d440140e034955031440104c1d80c0d82ca840030001e100d1159a44040144a0340f07510540c4942d11845000c0c0b140d036224001407469000486102e16000320301001401140002d401400001c4418600c890400103201140e1060760006102540210743c0d510042000f5644102181811101030b100500c004a55250031510f401e4520009818540c4980110f40b905035a50101c2d0000c0c96003034010030620b41c13103241c001c0c40740d804102c0762000203003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 137263965 1250 137262715 137262767
    0x9150e0a031202032d071701061d030c040f060e0604110313021507080c070506090607020f0d0c0f06020c010807090302010f0207030c090603020310020708040e0c0906040303 76
    0x840054000440ca4241d2124002c1002000310400a54002000030401d074100c0900c00508176095158000301140300317403012105180018000340607041003030000b01d041444400400a56412019200300600303543e500181030321441e40803901e00b0401650741508580340a200e5441c8251903031141050313401122400ba001e448110420054520f2860340c0001c0d5401000030805521011090304c51091029281040d040041c035501c3d45207801005090701d041100190540d00058140200409090202d82040c10602c50340c000c9015400b40f031000034010940b803451076042d90303074450100d21501d900140360b510003078035520f50010640ca60712592015100d01000a94a5030007961075038411040da6072208803451071500111803498071000d00c01c05500420402001260340c0104000203400480310100e203952452050520b40701443c1d00380e511161043c0901d80019020710201c4044984120b03540a55071501d031242c806a1280b00b5031180d01440008000040541100011000300d10301d40b83c01e49915 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 137265215 1250 137263965 137263991
    0xa050d0b0406050906120f0313030201080601020f060a0e010f021801230d0902010c02090103060617011b0e01090e01061206080a031e0318050c1005130308090f03010915 74
    0x3582c0d03010b5140d1010100c00021850b007421100ca400c282400302c00c494205c404185014119444505078000401c0c0f044028000e6580081c02140c10034000c1c4001c15155460448258481c00301400c41190f00c1e032989565000344009400c0b80d0404182c40c0002c40d51080a0000505814043e80900d404101c0c0c00380c4003107000b41c0240380c00d00090900e0050030b2401e4800b5007031000904003c00c00f2810300030100710403c0941c8914030a1030295101d041c1c002030359800c0c803e4044010b62480000700c80d50f8107110540302c2001c182d554030041a201403c0c41042d250300f07240140c5e004d07100e6400003a851188140002035182d4080700c00b0303035001c180580c10051140c0b03549602d50ce40158550180110f04d0031080e90709519005c01c1c401d00e400016107000124200b03084100400950150301c01d079100d6001820080d0103180083c1ea5a00341026418002d1509080b05000b0800078068840500a0031001c24184856250380c020103c2480004008000c4010340c0c0c68410104107162109281491400382030039008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 137266465 1250 137265215 137265221
    0x30c0d0c081005040903050409050f0a05010902090307030b100509040b06040605011103090d020f03011109030f0a0b0121080301080f1501050105160218010b0703030507031b030f110a050d0b04 84
    0x502240b4500d140082c01c1c24180005044001411030812804010006030100715100e054060703018003000b02c90500300800700c4030582ea0181c10009000744100010b18890364006215001c0740d0f0b01040507255560f0302c64800306951400e520094200d9030103400c2104005810107405c0c8541001c0b9000c001281d2100011a404003152001503c08d50007001070640030b15003070801c20305084c4010b10040305c050128002c00c0c00d4075540a40c15889410104070003002e440c0074800c5080c00e29920f0001c0014800c2070711180d89518061199141d500302c51036a5100c19048801c01000320703604031403507603600d50355400300d90b548441c0071038000031038010038042c88040c10b41000303e01d0490b20141d55190400c0303d1001041000824100100e900c4400c0c00d6040b0241460001280d009142c0500304c16115442ea08014096a100074000e0007010324000941003500da420f1401c044440e00d900e40010074400c3e42070a003006040041d504a0340b402c01168890f07416a0000060030105010075090140d00001001c0c001a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 137267715 1250 137266465 137266471
    0x30d0c05031605030a0e011805060a1103010302090903070503070b060f0429030709060308040501123c1104050a06140a11070e040308040c050909100b0f06030c0d0c08 73
    0xc1c8004441c0080c0c401e44604060b40c4c1144a080002404140d240805408c5900440c1d00c8040f40c8900c082850a12006100d901da01c401d6054007844190300c861040f402620050100038441e24810000c41d10660b41041562145039102e000c9a42c0d503500ca08088a07020f44c100d54151282050100c603120f00c0c1400d020300000030f92061192900d00c03070b181d400607100200c0350361800d4152103130180029200300e150140c140114000d0300140e660758203020006090004004009103541d0130482820344090040040c1c000e141c0149110902c0c8001a880d1100040d060700d9100180398180460b14005582450041c001c4400469607202074590700c00003910141e4034054211f10400741441550441030141000102e19184001a1404203032a0f640c1d074803036000705440680000741c24004120400c02049000750240904807410400c1e4680364600760f540d001e426801325a560f0300d9a440403600c3d282c901050110500046c880d51b1a03103081c0000c071600741c0050a1950596082052003d030315400b071401580 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 137268965 1250 137267715 137267731
    0x1b04120c14030c040e0321070e120c04050a11030a0e060a0e060c0a02030f0a02010f060609080307170405360408030c0c030f07080a02010e19020906040204080f030d0c0503 75
    0x764058040e803c02004104101120345140000c0081f00c001560b00c54803507000c540402203105060400d4040100340118040d9184c0c010007001c9046011440001071502102c0d4088401250303542e500548900034140036409103941350b5002c82030011340803503a04000707003070408802100ea40b9618080c0349000c0c0d030780320b01211380079800400100704481c941c40300500190046004981c0f4084858203500c5a0798452a4410700607551000b6802d101c55083c006d40000b0710b40303464070441ea00d0500c031402e40c40b0f2082c8880104a004401c40841a200f04007060710003c1c20010030310030010341a00b68488602d6414041e131030400207610650342100945d441224069a00030360168250340e59406621402d031f00c00000120244404c0c4407070031801c04083c00038111188182c909586480344c2d01e0019085d40c03238003010030546420801414400140e03441d0300b5048a501100c6101c4d0b2a111280401d0013403103640c0065405c0c1c00361104109050303100100030a0801c10b0b0712010042d030546a0301c02c984501054482e08 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 137270215 1250 137268965 137268973
    0x21305060d0f06180c08060c0f030a02070c08060c0901030501120f0308070c0507060e031605010509040b040f090303091202070806060108180a030815030f030702091b04120c1403 78
    0x1c0803a24110050358082c1c81008005030410003c4280311a12500c0f85040307840c007480c01c1003480129424040c2540140040c2c58407402d10382e0102c2c511505010051502c0c46190340441c90070140400c041492000700548004d882d005d0400800c0c28071287d104c00007040c00709080000001e02003141d8009500d4040d08404d038200380d81e241d42e078200e4000401403c2c400c01c00010410707080100e0700911030340c001004561101d240c499a00c030181030400824a40070052880c1801040255903001801c4510740e01d0100c50000340c1c4120300300050700400b61181020340c074034941425a0105901a804402090701a03000340c0e03001d20030480120380d5030b200742c0220318150700a840459515401400c203140c01440034011240c076a4118000645040403504042d0001408a0306000003084010800c000520041d0701404684d9801d030846941c920540c90024020050a40001d03c200c10804109a14610303510050f9611540d0300c40c0d802e803001d58028103841210305e0003000165000b58014038002c030701c0041c02034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 137271465 1250 137270215 137270239
    0x4050109170c091009050f0414060f06060a05070614011a07030f03050a110a0804030f020d020307120207050d060603020316060c110307051207031e0c090f020d060602030702130506 79
    0x840781016004d4004444403585440110f4403882c43d0117818030880036443c0841c1c40d4035217801c200650311030640d80400c0c103410407000e11003c0031100555540c840c4d425101d442c0c5d61b0341000350807103581c0320307074003014003054a4a80820009245000c14a0480b104c111a08480440d0000200349078406d45ca0020080b41c80d8610207501030b0f000307410840e40245c280400042c0c0b507a6280c00136003203600440d400d100058001003040200364202011094140d500c0c4010301c0d102c210080d0296892050b1332002c1c000041021016403102d1082040030b020f8040500b424494240c10703d0f25001410071400200e210740a00b012248002c2280101e060490700c0c04e0341e170014012180c5d01d9500e819100310043d180c141c06801030100c0c0d40c1e225041c10503020400308008151030380c954180741001c030310020821011102d070001c8900200711094205819103c184030000341c0b610499444000030b201c0c0c1d850041425040140010341c1c0b0fa00071000d4000907009483c00f00b1242d40c07000102084131011101a40d103d040b110030f07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 137272715 1250 137271465 137271469
    0xf0306011d060102030405041a0a0b0309030f090f03010c020a0b07050307050d0c0909022d07020904020913050a0623061c03090b04030c0312050306010c020904030e04050c04050109170c 81
    0x40c1e540c0288060040d03a141c01c0d1240c000c103058a10013600035003640400b000041c46420030100100003801c0310f00b2202c3c214248030315003580324030514070b41441908000c1924171b659603602d141210413100040007004500051b131006501d8100c0884241c80c10460980042c4460740501d0031688642882d90717405160122100080c0010086100101c1c10002060004140480700f8401490300d580f0046000e1450260a001000080443d00194501050030301210005813203580c000d54020354101c2d405400d41da10030600c02031001d0a04c4002d0014071403034480d2010b200300c5078408803c0c80b007054958091050142413000d6243d1081d180503411595001e52040d1615800e6044e0700d0140c4245011501c556030b5180380707001070304240c00076a04502c0d041c0c010810010104d03518054181103040050442ca82000041e0042c103121001070701034109500003500b0075200d0840940c43d070310020310811180c1070a1003592031541107030007881e000c1f529607600805c01c140014040034070201110001c00b22a8030f00b1007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 137273965 1250 137272715 137272769
    0x10501050a03090b090124030c06050304021804060219030e070302040e0c03060903090108090a03171308070302010c031d06010918020303070311070e04050607030903050c0d0c020f030601 82
    0x8801c108050f50b03075129000060224440c0c2c1d00800008001185e00c424a0081c0072400e40108400c40c0079040080003000003800801501007100c040b8100151030b680d890012426000316480b030851880000401c1008020035540030f080925403daa50b820480f00c035100a8003101e400c00d4a5014070fa0103e1010401031919410203492410030318244c0c0c851402d204082403034084241c0390201c0640021403540041d5038070600d451780c0300c0c04020060030390364400d0b00d014010704103504074802444c0380140011a61141103444100c030720390154203641d8034012824001d00a102102c80702c0000b034140465a00040b8803c110748000d07001d401c01a100700d0b40b8120408004000c0d0301900b100c0d1002c0d1900303001c0940d40600240c5121030103a140d08210700d0300d15079018142011504414800d071300c10410300c030120301c002a241c1c0c0d100d4080c1c01c3c0019440500c4c14196001e010711017812146106d083e405070802c9910072a40050b0500c00d88042d00300108031800c00da202c1c0d200340140101302e0140d90300c0101e42c4040c95 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 137275215 1250 137273965 137273977
    0x120812090106091505040c2a0305040e0a090606050307050315040212070e070e03010204030f03181707030203060915040210090503010507050c16050127180b032401050105 75
    0x5000040d41d1a034038149003064590034444e26902890301c0c1001c0045007440d000310800b1001c9031a003035a80039064000b0008007881500f41590a081e030301218401c00d400f0b00100e41c040d004500c40c900007494004060006801c580d1030440e880c904000f80005e40c6c0c100010400f0980710014068214400c010407401100c0c6c0d03004209030307408074803508041100c120501084000d0803d00102c881940f070119000350403c1c6c60244103134000e0384104030810220b0000380104580a5040c40c00311806c00340b1205c2103001c0045d07500081e80071640d9451081c207290001a030300003220310a0b0700b41c8407144d542c43d01190301d40e5031072a006089242074400180c010314000800d450002003a08142680e10b4440c004282110422074140307002c680700044085030000104010740b0110100d410081480e41443e0000340f50100140c034100030301452040b00034901c0d00120360f2502a20741440f258625541900c020030240c02101c8016010303000d203c48010840c4942d01084111008800c00240c1c140d203000c00450f0307035a01c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 137276465 1250 137275215 137275231
    0x20a08090114090901060c123f05090714040207110f01090305010f05011a03070f1218110f0625021201020304060b01090f08190503070b040b10120812 66
    0x1040603280075500c0e036404501801c1b5940d40c5000012051500d031560212400c4008203104171140240c511071441a86484007050540d04500c058000101e8110912050721140540c3c600b090100b10003940002087d404407900400d1000300344c08194240422403041c00000b42050740c0407031907680c40b810320071007040244e801032402040b090743c3c9468aa085416a001680940f42c542c8c0040000c03c3c00100b40b0002d50814030220b91031402c150070054144080c8010100a002c441d0072880918012640a143e094202c08080f81010040d490f240e000302c6000050035201e1402428401a142004401d881403100c115064a03c04c00704030407405280128400c0403648580200f003684408002800038602851050300e010602c080e0401c005030004038a40c201e0310040f038002d88104000304000070030280c400d22090181c4919a00c5050007429172168000240190040c50103000c02c00801122884c4035140d0b0404200c00162100041c0442205a80340a807100c0d00502c014005003030303100f12154000e584 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 137277715 1250 137276465 137276467
    0x2011e0503010b070218010b030f0a0c08070e030f190c0e040c030303090203011107051609020c0c0405220507080607180b03060a03020901080c031606020a0f030c0804091b020a08090114 81
    0x280c81b845031000b64243c00c0000c1c46480482400b90000a00f00700542144618a040c00310401e290001012407100030201800c0149000b5503044c140c405002542507100558241c4079181800c4c20580e0540461001c100d5911801010000700c04000c404001d0207242d00c043c403002030038695101100074040c03c13041030303a0555030f03100a9060850801c0003040001e11400c0a04060100410580602c07803440e803010b0352007030040040c200380e903d0129841281040454000805403106000c85024039030842240c0003150044480f0f200f800000101c0b4400c490380d000485440356511740c000c84020a10280e0035a650480201c2441070a40183c0903580c8617002600b08845165290001280d00c5420b9109801c1500888402c02c098107080c44034070b0064002400003243c0503d8044000c2d514800e9020203403640e980c901141c4101840f42203003000040c2c118403070580300e984820301c2c50002e1059149d00200c8004c2641500b03041ca00124a0720180c1e50804040760604040303500544202e00000d03812420200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 137278965 1250 137277715 137277739
    0xa030809190f090b03060a05090a0f05070e180105060103050709300b100b0a05071112010c050d0b010c0507060503070c0602070507051f0807080c091203040504050105060f0313021804050a02011e0503010b0702 91
    0x50030ec8040b40304070941050410700d0003d903180142101c2d4060703c454100f5050000b00b100190304010417400322041e615034060b000f117505414603103040e17003248204110b08035455900c080c0516108507601441c000c141c0d00c04d04a40e101c3d4028810304c03414940001003017091001001003651003021640042c0701508601a41306c00e00c10b0282103920b625151004280f0200300da009020703080c400d0205c88202070801081da000a40c03211580e0b0746403803050b14108803000000400d0644070340031101d00960310030f200f176449614501d000c03a210206405481d014152100407040d150354813020720104010307243c55001c81901d45030000c58040710014800b800310081042000c410b91103407180d03806424803c0001e5078450b0308042c200310030f88106910080c4540c4d0103003e440709003d242c0089a4005402691401564100d48042500240b030a01041600d8961104000a22902161041c15075100b641c5480c864131090b078038003403c0e2104c01981ca00044043c4010702000024800402d22180003c0008280071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 137280215 1250 137278965 137278979
    0x402130b0706050403031113090504030c0803161409010e040c11030c1b03010b0901090902010e060d05271e01020c0f0a05010b0a030809190f090b03060a05090a0f0507 73
    0x50700c0180101c5200d0b640f0001c0205050745442401504199100c11920700065182800842c203840d0140a013181ea64030045804c040c000c044600780703968401419a103a2400e50011032a56103442540008a230f00100d0610341402000d003242d51660050f1600b4184460307840900c0f009100f184d028a050112040182e103034200100043c0c52078005080042000c4001789544040703100480d290b031b9001e40e06108010030160b9800013020706641550130f002900415600048075040a841c1c0704c4d40e004000001d42c00a10345041d00a98400e89801c980a0102030b1205e003840c0d004240d540b61400582c0000d001f5801d0741c01a440e038042c1e524101300016051042c01c064450804400000c410201d0340b2880b90f200c00c10000b8007401c4100e00c002c640c02e8040c0d074a1501c0d2043c003413040021042c4a5991320f010600d80300916103100300600341038280c861000e5100c0348410020506004180c0c4644203100000300e00340140c1c09801d10928203040980080ba015544644140c038141d00c04507614002d1007000f060315 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 137281465 1250 137280215 137280217
    0xf0a0305030a0b12061014030a0201021e0319091e0302031c032403021002070f09050703020c0106090f06090e030f0f041205060a0c1d0111070b03040609020a0806150402130b 76
    0x244441d510308068047c603040c4812845603407800b140d4081e03005010003d000d40c0e008203034401500300c0c10300150481406440054210301ca0710b4030344d0242900441c041c18015038031511600c01c3e16200003400c024120b95204004c0500c500c1d02c0000e50550080c0005032a060301c070710b03248102406504001c07940c42c43c0d02d040c02d0710850420303040204d00250b0110400070351901011040c1030860600180c0b00b91030171300f1101c8101700124003c0184150b1128045494907120fa4100c54501c3c149070020002c09440b5045040500302e20100102c455090500210300745181d03100d0300010881d408011450641607102d4884a6013285442508902d414000050003a0724401001040361140010b42018a0044c00207030071601c0c5c8006c1c2e9410489280318041003003120800c021400c0d102401c044007007400f0b28900518004064001b084440300100a0108003c2c0d6904821f045600c2282c0caa000547c5411080d030361808110740746200307081c21110700c034171900b4554000c0a100100503000b0482c1341e10340503c4181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 137282715 1250 137281465 137281471
    0x190e1809010c090b030f04030f170702010615020309060403020d0f050a08041e060e0d17120105040b0f01021018020a0b0d0f0b010504030b0c04080109030504080f0a0305030a0b1206 79
    0x559460301c0d400020107602c11010b1010f002d44c00032030750642c10809565035805000500c000d082c02800d6806207900ca024046503000d607980c2c03400d900001d140c0780c1e40080c041d180612844d41d030500c0c03803441b6081140c004001e070788500e400035004a040030320707603001c204e8403040743c41c0280d40300e428911000c030102e4410f11002510900032542d02d9619032400c024541d1114410224003440001e4030001d025940d80550200d901d804100c4a40080100030b041c80d005404807a00200205e110003d10010013503160b0308980e04880c0c08550400c4040002010f003d58016a00d002500580154800e4a60200c00c0c1e84940400401090412402e00d00c0c0c1c2e02155103190103410280c40c00f540492284403000a60260042c20310080308180f004240600000e80507011314000180b901c2c00c541c001586c11407000042c5e50003031881100034001e82609050151490703004d400f92074100e00400ba10106540300c001224100641e250780c900d441c0d80d03503003650310000300310f0100c1d400c2d444400c02d05401c902c41000c011f0180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 137283965 1250 137282715 137282731
    0x2030f070b1f030b090c0904080403081b030c010b0a0e0906010b070c051005280f1101020d140105130b15160203070605030901060609050f041d060a1407020102190e18 73
    0xb11410800202458842505806c0d031007607a41108000c0007a042c4001d0702e0440c0e0b40b00302103d440d03681c07850342c0c6001400d4220041c1441d200200d00b80c6403454054200c40c1c0107500c143c5066403a0f03900c5184a110b828811520303c0c007654801d400401903000a40002c00f28940100b104511882d141d8001406800381e03090180c00007030000c2070408903150358038000f0402c08581001101c51540001018200310850405c0500b404442c002c44940440207404861010b42c03084010800595400c100300369058081c001c0364090300c3d070031140540180d11482036209801009214000075401098115140d900c2114084008904401c0503001620300700884009040c4645441389c0302c1c5030560500d82156403d9100c00100800068100916181c2c21052180090244c5000c06d141c00201010040c04600380710150140c89810104101c400c03256020700424080e0086079101c6480b2242d0490907801a0450344e481d0030840d00c90104940e00541005035004009022821424400ca0404071060380480e0802 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 137285215 1250 137283965 137283983
    0x7020f0f0303010e0a0c08010501050a091d01030303050603070e010302090a1b0c0203010b0f090a1104030c030317010f080d08090705040612060609090f0b090307080c0d020d02030f070b1f03 83
    0x3002904420104c41c1c3c0c0002c070714600b00480200880e00074040b003010701c29141446000035a0111b034a1040e43c000c0040c240c440081141030812007400d5140c1e8000340310690000c0e103804013040c1180b50120b407038012241c031580040040c1e4299002c001d110107019045810340c540d80c1216141a60f1030000e030003c0c51665880d0514144400d006160a460440d50310341d2103003088880030000c40e03403080388294020154200010704a150710303000000512a03904080c220001c00740001040551103240c201800402030003042060b40d0b1142c000c0c20031090350140c0328064000c44210002c56124a852950143d076040c101c458041c1d544e030120f02200c0a607001800740e4042d0f21003000c2031095034010340700145201001081140c20075110140d00b07107544007000f46a92200d030080781000b0010416030f200184c11668140d9a5610701131410340d900741c03400c0c081c0054007c0442c1011224004407d6031103e00010f940145802c0980d52080344407880104408407038107a000005910590503101c48014501c81d0b0b0560b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 137286465 1250 137285215 137285219
    0x5040f02120105090312040204020409110a110102030609010b03060301090209011503051501020319020f0706080405010506040605061602011107080a14030301060e010503060409210909090803070807020f0f030301 93
    0x2100050211520141c1240c0c10f00040c482031920010031514560684031200c0201d4a8620019010388907a60003a0f40213810850b0020106200c040188111560b40c2c88540000d2582c1c001c042c280e01044607500d0340441607800421a4195030350041d0b5220100400018114001d940003500c42002138001aa0044141d03040003a0142c251182d190400d0001410103004010b0343e000035524400d400002455804441d11054001d000b0800c00a6044c10308060703480756516841c0c000d00c10304046070280e5543d03092002042d801d0510348140f8003130b41d8029004510308000c0e0030040c2000002e03200101d04001142130011709506090240c180074008001c09082031680505100d9440401111243c4c2039800400042001d180c00004a5440d4042070074503a440b6920000000d00900c0b041e0301c050500c0540000600f81c115015030111206600740e00d84004154a40311010125021010010f01003841007011414a601411810350301c00d44a2040f900d01000c40941b481c1840c0480c91051000e900c08001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 137287715 1250 137286465 137286469
    0x40c051002060f1302030715031e050405060f0606040b0408060601112b030609230109090b0a021b03160201030c0507030807030b06040b0a051e070c03200405040f02 72
    0xa4412144001e100a0600e81002960520409405885080310641c20300c0003204540342889410010220713002d44c141d07540c540c007034058054044021070301c1000011110312200c2c00a140301d0076020b81c1c2c0180c010020766480c00c40780c00501c0d102411096102c9410702000660284d880010006007070f03050301821844c03c1600015151a2403105080701c503411505100c0c1140c0481e0345074a00b61449100300001554002d0002e03001002c08e6040074403900e09101c600713114402003081c1c921840c0c4400d4030081003aa40c1b26109011505e00040091103601024003045c000100c5030060100902d422681c00e03008014204034615603407180c0200c0e0f4842d0402c607190700a47da01840b903008a03087d141499803800425a0780141010401082c0390149075981c01840c81588502056802802e1410207869594a4800004d410784d00180e030711f142c01a00d1038814007240070724041a10801c42c0e005000c1e41803681180c1d1042407211502500420701d0042a02d1040103507103e00440340128080d2a20602080e09401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 137288965 1250 137287715 137287729
    0x611180a08030415030203100302150307080f090c15132904060e1c0b07030e010509010b060a050a030f020706051e091009020f03010504050610140d021003090b040c05 73
    0x1010001c00d070002d01c01000030754050302c00500400040c2c43d005a5031769402c03042c80100703600b542001e07400202c1000d01010303502e08180114040c9001d078907201880c2d584ca02282c0c3c0282800c540d0b9001c0c6400028109080d4180044500d04d4604c8040120b420300c5240c400314100f5000640c444d00c010070004801030048009080c18441c07031841c100318245003a0a044007c1e011400c0d428140c2e024070801c00340300100706025546120003561013041094103007400080280641005404503c03a035180001203020350302c051049085485000d400d403410702e88203050603559078000c030502405141d1140210010190b580c40109641c3d40300c0c21001916091a40030360b161800b0492454500c20205400d1008071032000410081c040071140022982c1002440490300d40140c0b9400a40c156090206000070000042400751003200f440b01c00301320b0b05a80e032a5401161458003041500078583c0701a0002504102d40d030b00300403141d00d050215050b1001d59403501c02ca94200c80595070014030000070300803860161 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 137290215 1250 137288965 137288969
    0xd050f010303200a140102120c130504061a070c270f051312050c060a0504050d0c0803012102060a0f02060105011103040e060f1017060618010c0611180a 67
    0x2003c1941d80345800c0e90300d01c0d42d541c5840d502a1010328010810001345e842501120b2001c4d01b404007a819604082c50600c02c1c50704158105243c120004802141e40d06003489120101c9002004220985522400300507550340500f4040e91200c406000c041030600a00901303129050351556010450b030040700280c0c04648050f0000a40a410142031119424a0f512120319854106004200240c100d04055510713105502d030740080750180c041003040341e080c036a00c0a0711880c095000d6902c40104400300700c0301b40f0b9803407200034000c07a030500050000c00c1c0107503003d050b09071481400054082c41600050540c0d00500082800a0320000402102c00c0d0305010349030051400382419510300401c0e5808540301e003d14011108803000070320018001e941c81d42401c03100c49001901005c650700d61900000c0c004440300d800c4195030b40480c00804e0f01070500710100e49464000144000080d40c81400440301c0c1003c140e010340f929600d0300160510a081000140314105090307210100003e440420b200da40c03000743d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 137291465 1250 137290215 137290247
    0x9120f03030a20190302040807030c0f06020303060114160206070501050a0c030b03070e06040204030206070f0c1d0109090c030606081617030712031107080a1b020102210d050f010303 80
    0xa1240000d03a10080402d942d5140c080004051008506580171002030040e0b900600031880358220001c2807140c0107400c0d50035650080c3c80840201c1c2c56003000d0b80e40c0d10099900780d00140e0a2180d1440c148076403c0603000c00098541c5030b008403081c0717400150041d00401001e0301c0342c1c0d6540043c860018124802c03480c030b64045060500c00c042c1c6201c0001d4507504a48078680e10050310400040d070035a143d0b4100c0b8044e50780144080c0d122034590801001148905030201c6158060200100340c21507042074100c80c40b8000000a1010f0b03081000c064083c09030000300b121761110340e110100000d1082d024080181c10444024214080031002043c040d041641c0110420342c03040130880b8000700c01004541c00e054000c0103201c4c03101d6501300100e00600311812141200c201c0852441c1c01c200000005000804459803400041c4500c2d0002e6004030301c4051009016074801c2610415100c148c09031003c0c0f4819404406041a031540e142a0584004880c000301c4a65618010701c2099000f41c84a0100495 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 137292715 1250 137291465 137291501
    0x3010b0a1803050d03020711041104080f070e01120201020a120206100501090b07060203090f01090f0218060a060e030a020603011203020d0c080a03020f04081c1d09010b09120f03030a 80
    0x59601c400703441c1c1100c403404d40100b44c0c0028a28082c44003800c2005804540904100520b8070000c0040d000f50f0894001d8022500400700c1d1850303820000582401501d0030300c02c1c1d40034517900c3c0602d564501410208100e05601545a090022511001d050302e121107050b005040c042c0f81c00f00e0421b50079081c1b500003a040c1700c1580c000307224101c0b00e00c041e58440c0780d21100040e500c0d00c07005040e92420340e07032290341404d0f5803e007080d040030005a0707080c086006c2e1003640d80101402034030180a41c9114100d42094100760100803c006540c4618159070000c0c00160036140004256000300d00158826008252603101c82800d6900301a4108100d100d8201e0300e240c0700320400c3c81030361a86107610501030001308046c2c0200300072880e005864221401825039001b03e481040d6080c54a105160740c4180e1140030900410410764550710860070214540030052044200340e0828488070f803107800892104d60442c1c441c24107021001003c004200090940350000c5440c0e107045d00a150544507510b00c0014005a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 137293965 1250 137292715 137292719
    0x16030c0203030a02130e0702010c03060909120f05040504022b02090d1b360e100518030c0a111c082206181406041e0b03010b0a18 57
    0x36000c01035035004500032002503528074003400c4014280d003a0350072140d0035034245400c1c0124260152b00c0710100e60441c1c0c40031f01007a96200002400ca40403140c02402c00c0c106030b00082c20003881070801000f59405801e01da4189030719070020070201d8110044408a9060b40c1c0d40008100001080005051780c682e4400c1d45400c61361400325802c4012000001e0940301510b1880c01400b00e5030781c036440a00442034041003140b100450802054100b0345400d50f401d0340c10494945916070174060180300500c240010040c07001c4c500c084500030000100b850703a081c010582c00c030a1591007400100601048440204850072450a00c04810150010107a100d0030383c1000003049180c100162500351900004001c0e180c500500c40b0014003c0384100754801c502c62880c01141c410b412000b40e540e01403811340100784242d02d5a03140e40c0c003c60306840c507a9002c84280310420000340400ca004807400302d03948085088669400c00d02640d41c00070380004030041008102903201c1c5901146400300c10025200c4802407074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 137295215 1250 137293965 137293967
    0x110604020f09090307050d0503160c0c0b0d0908120f07030b0a0311181f0801110904020703090801060603020703140306010e040f021605060a1d030a0e0f0409060516030c 74
    0x100603000700d409902000d0000382e0089007032096883c850f4010f4150f60032004080801017080d03004030b4040e0b05821102d43c0c0c0000307a61090740e03017464140e8803022100c2d00350705020b040b80264029010803852a40c58904600c0003540000262202c070f03a4461518a0600300801130101c03084d0020006810541b801d001c2e0303107491390340001c9001100e81009011000c40c88040215404203215260b1981c80e0343c440301402068800010f0030710480d410b001100d8402921044030074281c0b9044444000302140501003054903241c80d030300038030416100b41004030540b40c0e2500f42c0c600b035808075440407003c268041000c500385a08400383c4020084200003141c9186010310020380010f01d0890014010b640e03448081407040c0d02d5a040b10105034440030a26401021890243e03034804c1c013120b01015003030602c110f02a5502c07101d01100b01103d6080099401c10801101c04c41d0f909003100301c0140d02800c02d01c00031400d5103441c8035100c02c49021710800700d90b43ca0801044d031502c00c0d4040500c0105450140010085 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 137296465 1250 137295215 137295229
    0xd1b020319081b07200f18090c0a0602060f0a060e0f0a060503030408012a020a03050705070f0602030703020f0303070c110a09021c06140906060a1103030702030a11060402 75
    0x700c0b82000c18007625000304a540301410103044011402d00080c0700014000b440c5007143c8501e40180d10341c8424616a402d00a1048a110320550030400d000c0700480b0354100346078295400084801154118240207001514072151540b140e03000da0040d109010450b141c40d104554007483c010340511905140c0010240c1d20b0900400c1d803003104100d400414405680d64121a0080c440181240d0300c030f0b5140c0c0e5160f0b000b82030000344100780b05010300340e0140c0814141c05034002c000d01078000d009100000c0d10b05582c5035000c0c0b0381c2240d66008106000c48c0c4031200c0d001c0c00c409010582d008540f503003418038010703140c000a11303c84041d0307034402c1c010070181315405203030484025884524501b07155100c41c0880c01101d002d4120602181c0041010314403280b4081030a95038040081c010b202c0a90f5030310a0001d500e440c1140c440d008002100082c8039400c050300181000d501e54642401d01004c62001c8500710b0300280c40c2480103810014032500300d258415880c2e0102c10844000d841582001d0b030000703500d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 137297715 1250 137296465 137296507
    0xb030106050a051b100221150d050307020405011211030604110103090302030f0d051e010806010501110c0a080f0d030e030a111f090c1d06040b0a05060d1b0203 70
    0x4101e000500000d814021403540c0c0c00b40d052003001c4078811111103e8000207074008500540e40186044281f0300c4a688141085004025045e04220580c1c464004d01c00340c0c55241c1c05c00c0d155844100b150a0040e205c0e803041174000d00902c801c1c2072a822043ca020345000314090079240c86540510107110100d0444d1000000121342402c00007020b07000c91130b050381540501401e0000c3d072103000c100c0190800300e5400180c070031401d40c0700c8040070086064034048030000130301405019a006100500032540205007510a10200b60111b038090101100092342603962504854003030340143c10160600042004a4a900030013800e043c801101c4074801ca0f50340b801407005090800800b1040703c0071301c14050183c200e1762202900b24204400c041c6a40c00b020b00341d8400c0490b2100d0307420340d00140c04070300405a8845904081c06c0c916560f00c0d00e20411000d400d2038119242c0c400d440010014040c0d44180042c41c0c1482c4d200004a8070780100035a007030b007039030911001ca02503400420000c0d0b003068203004507407d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 137298965 1250 137297715 137297717
    0x6080c010e0906010c0c0312020d090e042402160512161104150b130902030c0a0806040e01090b0610020a0c0b0304110a080109140106050112090501020705060c0d060b030106050a 78
    0x40341e0307888000417506108a1754010707000c3e012016012050000600441c610050b0381e03002c50b400a00b882030110f4030711001b40b1625a000290801044c005014450f0405100da11013903800c50300803c01001314200e034440c14091440c1d40482898404109062000741c0360303000000f1640341000100e10b540981c9441500b4000e000c004101c4030703409180d407280e00842c19600f5504d0400c02240c0c40e404140441d500660444288500210000400e417149000b20317032249009048190400318412029104114090001c56019880c0c0b4040003241d10700340300b110311050160301c048805003081824003074000d0701c0c3c03400708046400c40780700c0c0303004141807010010031207070b0b903080f1a0b5481d9291b0802e07401c05034032108219071001c124140042e000b40d0540043c8403050044045170142c51078110814201da009203d40c6000c40e40124180318020b00c65030004071014003c000141c5003034560f40d5441d0a11740c3c2282c0b80c400e9018003040580544041d031280070041c0102c001d80c9072555050800140041c010214824 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 137300215 1250 137298965 137298979
    0x160302030a020d15061106010308040605131809030905030a0302070b030a0e0106060e1306050f010c022b120305010b0306040e0f15010602010b030105060a050d0c03080409020d06080c010e 82
    0x107501a4000d80c102c0b0059a4440c00c20040800c03c021002c60603040340c81030038001405500316801d00b40022810798100d07039010942926042c504001666682c002c3c07041c070807440d000c2d460009070210309055020b000d901d4681c0005055074240c82c002c1c11901440c1c01140c041d501c1843d105000130340005003981903c0210310701940301c0e950341548201605c1c070560f202500c0d500780500090312542228503120601800c6a0140c4140010110b032001c50701a84503056004201e03803802c04055008811000e00b850014013449207500110030006418000440041e20080081040c4000c1c80b417802004520001c040c6828801545011a0780c0040d010142039a0311646d03680300c1040c0c5400007041564010b03441001600d4808007603a03444ad01500d030910400000d9420702554140919062081c64480c0c0c00091210a00324100410b001d020799041c00105d40302c0d130340c0250110100b5848005000201910380d000f5039285c08141102c000e0f90965404881580e2100c1c455004aa801203804e0010030401d4840e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 137301465 1250 137300215 137300221
    0x15050715051b04080304030b180a0b0915010e0a0e03030108060109110415030504060506271806180d0905090f0402061611030d0203030c030103080a030204150e150316030203 76
    0x8100c181c4881c201102d550800034001402e10004806842100e00686428150b5912440c280750f100c1400106940030350005e80d0701d4000207141344205a00034141c001100c4000b44154001d03003000c4001c1e084150420050400c01c031080c85a4011080d503006600040c5066504d000c0c03a042c0c0d90750301800342075800382c2c4803007400e0944075100d015200140b1030701c440300000c0e501c540e034040c2c01082c0a23201651158240740c0011580e00f004101c28082808a00c54104c06501c074440195035407170080c0c222808101c0802e80c1d041400010002d00340a2600c40300021744040105025518052400741a0018441000000c1007181d4421041e44d0f4800008042480c1a555910016060f1b20590290204802255191109000311106100045401682124900c686d811020f0b603903400102ea6105402008200510014492402500254015007005802c0c02e40340c5c10aca0b0150000c00075aa00001c20320402a9000e03d081058948440340c1c10084c28610300f001c1d04014500591110400f05264000000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 137302715 1250 137301465 137301481
    0x1c140903031201031b0807141201140108030408061b03010510141b06011a070f0f0b01090522020f01180f0308070215030705031302010c021203041505071505 69
    0x84503129420b40740390910a40e140c4c50f080c0d031344112901844d440121041c01c081924a0300180c0d18040d910b044100e08030030046003040102c884c01c40b5031150855525007820900c45d6405002940c043e002501c051501d03030b41040070705442c0c804001c02210407807403558a280c10144901c41142d0541350199445107980e006a6410b4a0010b901c200e402d5800800084c0c905000101014003060845d841060b10290b0f40d80700030120402c90380740702490440104001d0440014240c0040000e12841091541c03845155034558981e880002d900081040d031301d5208211a104580c03581d12a01180d46410111420542e000b041450041d1001c0d00d05200000703c82443e5290300d10410030040c25410115030326135490b032400300c1e0143c100c1c0310101c4c0203060141054110002c14801c7d68403274581c07030361424250f03520408124645016254242e0500c9402610880507884414103481645c8440d0b0096036954070301803c3d00006a0700e03007624001c12800344031580019840712400100c03581402e0001c0b503d41c9030825 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 137303965 1250 137302715 137302717
    0xf071d0c07050f07061d03060703150b07030c020a06020d0e061b01050405070509060d03140a050d0504030206043f020c0a03030807091d0f0c090301060609081c14090303 74
    0x501030320b80e200f8000780000c5030800050141c20f0340c2d0160b450114402c01c4581c4205181c2210301d0455041c1c100c0000104481d2081c3c2c40f002ca021604002e00e59016a1591740307800541c8100c40640016032103c0404003541890001003008110500c01403000d04071100004240d1580c1005152242c0c0c00000c0750303a0781808146038010a00c410300f000700205c0c2490310f0499624441841381c54001c1c603587d0001100f0f464852007101c403490b015243c00e01c000ca028442e4000075400446124107000f82400000b0100b9003500c110b510680c440e400419030b604007405d20740564100300b9411600e4800001c5041102e9440104640105c100001101d84070000181c0036030500d00400031194004504000000030f0540c0080514040e410303649400050a80314000e503800609203110b204002c0d80140b01044000410418603640001c10000440c2040b4030f00c400642940c0180e0b01031000144000c0d0309100d15a02404004c0001d4485554403600413401180540171014030f813078103418901c0201c4d00c0001510b00b0f00c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 137305215 1250 137303965 137303977
    0x10509040e0a02040e010c0207060f0504030c0b070b06040509030a05071115120601020604020622030b01080a03080a0507020a020907020709090308160201093f0e030f071d0c 76
    0xc0c0103215a440754119a5922204a0001c1c0c0c8101c1c01d1045091107690184948103c02c249036026084141c00c0541c107481d000d110f020030340c3c00c01c04100300000110300c5284030304003d8144c40ca02550b0799481d84c1031161402601400541c852450312007400142c95000044400020850510304e440d0384150400103903002641d03219540002c81a003c4003043c410a20003000c0305820007886030815144c200049965000849009400143c204544072001c101d020302400c070107110400240b0100e480f0341c0c0f0454030070400e038403012150780f02c16403503010550083c40090340140380603010801840d250300000d54401010300c0290085800c000807a01880c0f090081c040035100c201ea052011041034600140225801c4130f41a811191203d030401615206008001106420042160310001c540c0d640d0010491002d106404200000154010211030800c050f402004562145024440c1e074805250410791150fa00c0354254200d42018042960030118020b17140c1c140040152031542e889030004424480c507 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 137306465 1250 137305215 137305219
    0xf0c08010909020f0a030302152206052520120304060c110105130309080a051b0604050d05061b160b0a090b0a060807080a0b01120c1802220501020c0d02010509 70
    0xc41740407090540004d003810090f004198200020317034820010340c0d50000031391014443c5400b03031940385011a8068024982050705001c0340d42e0000c483c203911a00c50078600e090a80030502e0b86008511982d03c40d0a0740000c1d42c2100050114044105490385280c40000e0004201c80d540d5004035074080e02c110003d170b803c4091074008010a003031000c02e040031003900040440006500680c040340321500411004100760b800002810a050280c0906800108000360309800c004240000181da541c1c1508807145140114080c014508203009001c40c6200142580131002c001000709940c0300c150511800c81568011034042895110744c00b02c000509001ea9000d84041c0c0707244148130798061558058000c8484a008441c0140e82c0e074400c403500d0b0b440d082005031241c14008010008100c22801c0054a5482240045805a100d0f00c41e41c1004500d8aa143c50140d40801c18143d050b0441d2241d240ea08610650302e20303140d01d07040000b580d9011206900d402645800d510310308690069080d50401140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 137307715 1250 137306465 137306479
    0x1c0f0605030d0504081b061c0b06070609060606050309150615030f090601080105103b010e0c04030c0603021b010609020a0806040b090412050408011404060f0c08010909020f 76
    0x80898010300f250410301407070f4268000e07440c650313a003c0844002c40c03002a90240000c0e00380802d80641c0303240c000140440607804c684a140503959941c03844000c00905209003000102c03200541801d008a0b4440c1d00000180032040050122140000803150700606c00f100d034109181e0780d42d0001c11080e11031046c655000358400720a20a500016014152054040c0707402ca84a9a999540301c1d030a03294180c80c01c4000840c510700601a0404600300c2070b81c0b9454180034042c01010740c80d4098600b603104290314148840c0074006000c1900c84005c5250000036600400307007484e046403a101000401da1080e50103141d400580d000c0051030307d0f81400b40500301e0400800a0540e00d4101801a45c410100c1d80001061440020303603d03c4d0900c40c007812580c010741a1070840e90b07240d44910902480314206414003005000002d0300342000d0040c2d41003041c81021401c1c4c203042500d403000c1a180196100c407034042c1800c07034225080346d00604907411220050000300d148062400494440c55100c50348039007000c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 137308965 1250 137307715 137307733
    0xd05011503120f030b0a1406040503030307050703021509031b010f06030804140405090a121101020315100203180103110408010e061e0903041206021204140f031c0f060503 75
    0x94108580c4071000b1607510360340a050b180c0c6004034100c9001c652900e40c440c02c1c1d030b04d0521450703042c0b9003203a40080b00075020a280613101c20000c4d1554104858000010300d0004401d0100740c0d05000c01a02c401303030350a00640314100707041040e03142e02404040c80c40660b00044c80040a500075084456800491402005055103074140484664424012500c40009000e0010745504082c80b40034491403400300503148403421556120307094030030703e0850000c00058500d031a040907000c0c80118007034130701d03103104411002d100c00901c080c980c40403610105540062241a1120356048400d82d106082440d000900d46051000085d050096401c010403540c602820b41e0141540011198000c1080100e0401c00120081c001070391854201d0708928160824082007000421040307400d9442d61065001504103d00203117007016085003101c05403400f141c0c2c400001d111380c001b44003a980d44c0100d07001561404048090000c4010702c0461182c20107607031030b5203c4150008a5101001418004095800f810 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 137310215 1250 137308965 137308973
    0xb1302061303030807110304090209030a02121c03110a030e03160b10050a0f06030506041d0d0f18060c06020d0e0322140f0d05011b1803020303090d05011503 69
    0x18010b4041100403e29600c0811065030141c5491a076841d6490021482c0c1070521f52900042e410400e422074240c0f09000900d00107a444008050750076050000900f95100500100d800c0d4440c0f0b00d001d101418504081070b809150445c0c12641412198100407a4404602640514520802e842d4101382410804403c1c10084000181806001140340c074402260303d920800c05c60712005c1c0301750200000510001c001d4940607030000755000300010000203140039000160f2942c1f09080c10700d050130b50000c001c41c240d0b140d004031070030843c0a06840d20041d00028001800c00850317040c0200418041440a1341080094603011036900e8581107600340610015a220344d60350382c1000c41e5085040c1424511302d400140c1410102045804100f1005840e42841341444a01641800c04035080704c0e10031000800305c0c0d003d01940a042c1d8034003061444036100b0f800000e000561007020b4641a981c00b400400c0965000000d485048030101c80d090071180b079919140e40109082e2071810300d005484c00000041c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 137311465 1250 137310215 137310247
    0x60c07050306010b03100e0a0e010216021905060d0b150c1501090504110402161a1f120809060c0607020601060809030901020601060e0102030c030706020417060705070b130206 77
    0x140d80540844505907258280e100701c5000454050726403010b18071080180c0041110400e8002e035624000240410804400c182642d2010140c1400d041000d0103900460510205284038180c018807054a69420280018001d200d00300094014544600e1058140e543d48803c0d01ca44034614026030781e81d4038080d00ca2a40300c0358900780404003440b071440006000c0410b070050510a96000030030000e0307140d030101044000d4010f4040c00c0c0d08101e69501010000310000c034201e04048448850303080d685882c9031010100c5070480d00840b00c10b40c40180030000c8030340b02d0084c01d80e0913520003102d50f00c456010340481c80340c0c01503030a42e00040c401d40e024000183c0d00403c185050b90120354030303400716640e441c000a40d43c0c880c101f581c0d0b0041c2d1225004120491042c0300c210300030041481520b150580d05e220884c80c41c3c002c004d099501650025080101070700e404030f90b030081d00c00f0b1400b0380000d1130000006000c5008108018118100203400211011000751182003034603801010b0f0350721012011410161 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 137312715 1250 137311465 137311469
    0xd11060a05040e190513050a0b0717040302010e060604020a02120901030e1204180203090c01140d2c070b0a120f0905060f090c150c071a0a02251211060c07 68
    0x4c81d00d041c020a1520300e040310700c4000650440020700500e000c4d540c0c1d0000044c03000302458100b089254007a855a1000d82c0140d020380e010364004547c0d01501c41005043c4140504128800c600c1003148003204c50b0041094549010000901d6403190312020050703002d4a01c0c01443d0302e0790300444003412074000300300c8081c000340d54980c10303002e80031081c0480d42c9040384400e848060259001454992035036204080d0b0042100700d4121460401003284003e00c190b40c82d8046441e0800b05035003c10442d582c5102900c040d200c00303000202201d614007040a12148201081c10302002485442d00003001c00c1a0404d088002070740c1d00c100404405400c003981c032550180c0300b8400c1003030300d400480c42c51400000d04036051b80c4000c04401da080c20301ca044043d50351080d00e00c0003040c018410f00290480c00308100311201d401805049070391301c09100d402800c020120700e10b407810b000201c9150502c1d0200300100d1040e102c26004076070141d0a036040c142c540f40a4102550381c801c10000c1e0001c5501e802080002c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 137313965 1250 137312715 137312761
    0xf02040806100909080412060f0e0a02031504030806010f1e2d05030117011d0705030f0d080613090b0c180f0619170108011a0d11060a05040e 62
    0x9102c0d07484291010550b45069006092524244001c0c0720b0010f03189041c0448911803203001402000400141068032103034103040d41d980d0442d9110308150f003030604c01c0d4510401c902e2070030046072030143c0e0080c3c070b00782c000740c0058108524404140500c87c007032211041c1c00e032031501140711210038030f080052903a003807402c0d4240c02044030b03105e0b4034030390200d42d00012010081d921071074290781c248480d4001010345503600864964031859003502e10903010702d0403100080c0c18800381410504000c149490448190000c040396440504840318080c0c0c81280c05420140880c2c0e614103002054100c0f4025091441015081c40741503000e0280d4001c8500042c1038200034401c1c02440d90001c0d90410254251102d072640d003120041019181800c0f804d00281e91890040c1081c03508400540065403180c5c109801c6601640c4d500d0704031240da4408000040209070301145c143e203003030352541d0398140c1c0d2006d41e0410794082c1402241c1072031114010010b44019201c120b00d02c400f18a44142700c0c42c0304906c201072000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 137315215 1250 137313965 137313991
    0x1120c0b2d090307090506150c030c0c030601120201050d0e0d0c030e010212030f090a050709140a0e031b1903032906070b0a0b06210907050109030b0a0f02040806 71
    0x4010030600c0420b0702c1c1d0316500240a4082640780c40c0e44400a804018403041d0302454080c00031b0084500003001d0450002c00b070004503280c442501215141c0314a0081c40d920a44c068001080007a210fa0301b4a0400344d03083c0703000350312540710b0448a0003500402d44d81c41d04c18010a0329480803158031018440c4040d02a6503071090030190840107a0325080c2540c085180b00b4820000510041020a461074001c0100c40454001e81d03500e80340d06040044c25044440b8080e1941a0803070608101d6400541001818004201c0b0203650f0b40c1580e41e912503c685081c03d410103901500103460306005030302c052400303d411130002c241c01c1e1900900901e01804124801c102542c01401050005013520b20310140c050b115a01e001120780319002c0310b960040595010030340f107052165054644a001d00500204a11000084d80741c1e00321203003c640e402020107015030301000d0204020303a4811240e00c100c1e50003814a0b0301039140c1254541c0507102d034025121106000143c001030a440c00119607105100d605004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 137316465 1250 137315215 137315287
    0x40b0a06020105190522150509060f0f010605300106200706081314010f0207060b012307030207030c0b030108070b0309030a050a0c0f0819030203060901120c0b 70
    0x720046079011b91791180f00003010700381c14100e200001c03034451174640a5110885012401d8070540103a44084980403145e030494800d101d1024800d00301e058104040c1c000f00303d0a176041201c0240103000ea1101d034540041e440050450f81e00320320070301c2d10071281300301014412580c4460f0f0281c811003019803000c2603a01a40d8600d08201d0000c00c044054403015914001036441e42050091001c40804051f03a03495802100d216049909104036140c11481e039002603203030382503814100c00300d44401428605000c403190402050000d491510081081200d0704241c6448241c28202d1030116160801840c0c40b04110010520520780da000d14121075040d42165062501c03650380c1034880c042550900784c81d078420320008001c10300038405400351904030f1519030000803040d22a51355615070031100f80da40c03141c0007900445020a80e990904001d0242c01c0551450a1a00125220b007405114984a103110642d80008115000c1003000042900c400f10340e413180e203003032454101e11082c2d0308810b020440704056 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 137317715 1250 137316465 137316511
    0x60c0e0603060a1502030d050703060302011b1101030e0102070501022a07290c0105070e10020111040317040510030204140d05060a0c03230103020f0108090d0e040b0a06020105 77
    0x1c40c0d00c90a809054040700d9840c00203256003e81d084185581903000034007009042145034860301e44540810f90f004101d00f131031070001400070301840d503251903e01c80341c0c0d0015000c902c0e1000c00350a00d403428a030010f085009001241e00900440300300402ea5400050100311080c0d490080030100b0304001090445880961071060343e0760850f124809800c00c140c81c43c204540d40c030059114152951f400c244d0314040c41810080c2c01c45008075402004544021002c50700c2e800c16070904088100907000030804000d910101c41418021880010040d5120b10340c101b00b4640c2c3c0e04c059900418000d45514945990414050043d40050003120003170354040c4899400c40c907003410103010072500500a4511a01d034000d41c80007400c0030906810a0580701c0e4018030240b004200303030103da0898402c1c43e00e00d075410351042244c100c0300050814108903844e001d0092442c808070b1944402d9240f414030034461040310300490050034004084030b901801c1e10500058454064001e02c1c0f00380c0d040c05140100f059403400e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 137318965 1250 137317715 137317717
    0x903030105010801061b1a0a060f210206070206030709080c0306040b040609110907090810021908071407060509100507050316020a081809010f030519030e040603060c0e06 75
    0x11580b4005001000100411030050074811564110600142c4401000d600c1e1111552280c845c070f03918400c1d07101c08000b0813080350711030b603000381100480283d000d0b4070b440c40ba000b5a00c0724a4410402d0a481050001199110710840e182c02da405000d80c0e0316490440c9000d404241c0d40d10482c0401d00854400b50b0441c5404a4198030840e40a40c20502e5900c490302c6950080844107030445020224060005d80360b5502d0382c2080c4244c0c0d03587d0f0358006260600f984981401e200009650500f401030110036000503526016003121419841d2908080e81c4011003250881c0030142d055096240000d4080203201c0c031034020505c9800600216000008210041c1c1704490b01181d4210014800340007144c02403848040310b030b4052170984120f0310101720a455071010b0398046241000c0e204214015203215090042c042801810000908105540340da183d40351111407461808003580390000c4d0843c01c03d8050456460001c0c405081002026282d262810040080241c80301c0810180006c80d00b41c2c0c90584 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 137320215 1250 137318965 137318969
    0x20717010501080f06061806030c0409050c03100506030d0309050304090606020715020a020a1e030215280c12110a060b0a050613051c081303030807090b03060f0102100908040e09030301 81
    0x5041c1d40d550074204000801030f07030b81c05000c940c9c5c18003c004081c0d4a540d01e501450700c80c1030140000e461a08113810415241100d0741940011003810403003000f59523a00460300e201196010708000c5030b28889071030414154481c540104c4c50291602e0000f140003640011546d00342d600d11120040d00281c0e80e2000e03a51280b07a510000e40c490000c10050084000c181c0d203d440001008850324140c507140d900160b00e080303240201b03803a68030011a10314808075810080c0700428a1000d5009003034140a0402820606110406011060084501d00c1403034030a1040d4402d15207402c0642d588070416245c80c41c00b4103107042c0c81a12070f08038000302140c1d614244040f5020001e526420740d014900d44000e10848000d100b18007012a0013032000c2902140716a002040c407007070680000d110b513504515020f8004280501250100480510140200f800040c1142d4000e501182d1040503245038000403458013102035080d4030000c0c00c2440c001c0c10441e420000d0020f4600b42081d550881e510491041c0c0d0381d005c24 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 137321465 1250 137320215 137320219
    0x3090e0a0b03100b0f0a120611070f0f17030a020d0b030118030311091809010609050c0702120a062d090201020a0b0406020405040501150e1f0e01020717010501080f0606 74
    0xf08251500c2d000e425032002c581d000f00644071000c1000c250001540355006507015000102e07804000100300a028800c004014030a5502a41800b0094495220114000d08000c103d1100541420180104089202500c00424001503601d2070f049102002a42040031403102142c1007100c1142946018000e04803800030200569101e40c00c1902e0407000303000201c50f1943c0002040141c042d854450300c06ca020042003c80c0740e0607003414042d14250031038000380e1280084524010521040700580011211070390b80440f805198281c80d25a0181481c3d07000720014412841c02c401d140d48480b20030508411010010000c2c0c11080c800461402544c008030f000900603000003d4801c00261056107682c1c03c14095100103052544400c0450102d45003a0015603550110520444400d070f400551003c048000b600c03141c0074072014000f14004880e1b000f10000c18016138402d004a542d1003000710400625aa40c00e50b0307480c90603803c40d280240400c0c0143c032828000c5411200d90894006101ca005105c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 137322715 1250 137321465 137321473
    0xb040605060d09080408100618150504020f09130c020714030a0314041a0702100c050a080c0c030105130302070b0a12020d0b0904230a0807060c03020c060403090e0a0b03 74
    0x200740e02c228001c01c11050121071102d802d00001c1005141004201c005908070100040d21508046404001000303a80c0395044c4103080c03095004d1480c40c50028141110360580e801b5071204131840c1c80c40e005010310018280c124507903204000c0c1c0e40225400211028601e5001e52340da254451868020f000410003400c0c0e090381c809803600001038030841da841f02d1070401c01486d81c1840c3c1c0783c0244204502010404601403407011650000354a0228000d1040d10418240420b0b6050182d6070f040d01d6019440010b4a0b060004c41d102d1511403003030000c1c41c00b104008000704220302d401c04450020202e00081500144600d03200071583c03000b40421140c0440c07254840d18800c00c03420500304065032001060841c0c00c0c3c0c80302d00b814416112914624001c40c4241e450030301d141c8070b900200015112850a0301030300d0b4041201000031031828402c4071a41030b0040c8010542d42c01110094019200b1001640e01500ca80401c20080c1030f8042804000d841301c2c40308100c800d44501c50020142c40360401d507143d02d500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 137323965 1250 137322715 137322727
    0xa1e0e010503040b0a060f080307030930060204050409050703050d03020a02060f070207030b0c031b090a121b03030c050d03050411090712022205030303090717070b1c0b04060506 78
    0x10500c40220b074800c58001c000702d05241c0b07a1107800c103806155409030350729274004100c4004040e0040620305c064100a0f04070340d41188480b031456500101d008801c0240c3c401c03400c103203091110940454001d818090000e02110103035141c81b0750b031f40645110a0302e09010701c141c54000140b0178001c5696111840d401040305440701c3c2c0010301c11010180650040d8482c212001000545424001e0701c51200001c6103a2289091010117800c02031035800110301c00420040401c15035903400c6400c0603113002403c0e14804074024500040d0f04802106080329554200e00700104065000f500301c101240309105039100203c004400760240d820985005110742c43d000100724080c01d18454003035221600d49030640c01c3c140d0000201e0b080340c0c421202c0c00d115002403440c0741c2d4403a10601400b0000c0105030002c41c518036091106644500c114061140c0c405000d0841c805281400c22030386014020180d00641d44245c9910b40c030300307850071010401c402d150610b0b0802000b07241c04c0c460761044a2000c0c00a40c5000c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 137325215 1250 137323965 137323973
    0x10e011802121c0e0117040210050c0c0a080f070e06030a110103140f07180b12061f09090e0a0b0c03130506040b04050f061302150d020a1e0e01050304 66
    0x100180d21015451003803031039a80c850f001d407411005a412a80d2140d00d25136265000042038011520120303880e900380d50091000589485081c00041665450440c0c0c03550318a5000604158510806641c0a00c590300081042440802c800c190f0450050450704042d540c0c106507580003004680301380d455004220f6800101d8240c0300004000134051400143c2141e01024178464084244c81c2c4601c00302e60381c070805c21311704c2c0c1001e004402031010000c0812510b2404803e00554410b200644460003800404110b56484804010340e186500800315012405000401805201300d0f00c034445195080548a001500c004100007850640103180350883e6641c003104104150310280c410200219106900804100e041c090305002d0380c4504009252030805050891520304010752181c4150480c0b401e024500c00a105198441d990580d03415201808800780003805000d4030100c500d810340005903002e1241e0f0f228001d0038035520054404101c10076028412030b8402440c1c015140420800c01c08075000c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 137326465 1250 137325215 137325229
    0x30f0315030724090b070b0612030702240417030306150421020a1707030b060301060518070c060c11070b040b04030308100902070305070b1f060c110306090708010e011802 75
    0x3c0340d0b03079003000c024195071030040342e00300d9010010542d101000316081c403080380341c964412621601000000c5040c000705030006402540e800301d0746400d00d0103484c128001a02d944060714014400103110384802a2156017050f00c0c0d92040344c000d84151a41000030400f03040010a9800b074508802522420352038074810a900d0141c07030501640d014605000019074407003241e5980e000c1829984c05030425030718510308245e905e0400f400c000d00c00d9040034401d21042d192800003a1031181c10b0012083e46072203100042c1d8907402d01c4038000d0030b42420b0084440950b50403042440042054070200e4004030b030f81d080c80702d0907800365005000c28440c08010420200784a0703402030348c01400307030f010400c0c0c00f555480380c03941240d10454044022810106440f024003460341c896540c4090364104c00358101c88401401c42c006030003402140c0c240400c242c081402c0c0208041522280d001c06421609c05040c80309216503280014482c0442d07660810150900c08030043c02544034110300d13036401c1050f85020398204126 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 137327715 1250 137326465 137326529
    0x81203181504060b03120d020d0b06090f0108070309120f320a110102070506011a0406120c020309040608100c051806090d08070f020406050603060306150d05030f03150307 75
    0x49032084c00c4480c0c030340d00d402c6c000500d81d501030740c00010781d00c4141c0090482541c00d4410300c24410f11003803010b0080750b141c0d8101816250400d10b03001513140e980c01c00c168010922460007a0400b04024034681c9159003004030300f0902002c50304e0b840d90701c0032100095500c20020000d15a02582c5114025421320152409400605802d0805003c030303407028040f1508a0b0800d55043c2d41d00d600460042081458100c0d049004000c05400180b52909160018050080102980f1406940c2d03070f2003117840d5072083c8151410070320010030900643d40c0d00c10302c0d0344d940d2164450003500caa1070121440072107070141c1c017183c0b00e0010040b451070501c807a00d0200402e41d00001c84454010101440200004005000a180540c4150344003040000b079030040c0002c0701c8554001e02d000d26000c00901c0340590340018041d9000160f140c2c841804101d00d000b040d8121032000001b0101d21010600683c2c05030020051413168415007000c88030003002000b01070341c8000c0c0b4883c1c0c522600300200c28058540f1a0255000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 137328965 1250 137327715 137327719
    0x131109091015030f0c060e0105121b0705030a030c0f0e010c17040b04090207030201140f0633120f01051008090115092f0d090c081203181504060b 64
    0x2e05699283c40302480e25490940442e240c0c04000824082c443d0084031200c000b22003841c1090a203e202e102c2e03c0740c6482c001d490000a007060421529138402d8000803903141503070140130b80f62240e01e80340c0040c0207840e082c1c40c402c008c549010b203420080b0b4880c00103814161016520704034070391a5621000d08014418022511440c402c0002181d07540e0710132b00400080103241d0005a942d0850300300203085815078880c0c892584900828442c0c07840712030a080340c01c0b00040b04c11807014850320325104036401102c0b01520550750b4900070140301c1100350000e4614080d00b00c010340210fa0312581c400300381100900a07a0303804901100e0302040d0030311070ba04450f40b100080300000344501d6821403441d020000740d030014000c070341c170b481020b941800004801c044840d0b1044e0914150408684041803074028034500c1c1a800780c1e220111010710507003840f810002c0803520b0a132030f080130303810240c40c03442c0c1d0044400c03860000000c0301003212148005420521040b4204c0c220b945912503544581c050140030191607 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 137330215 1250 137328965 137329001
    0x402180d020d060509060403260c0307021e03090f0406050918010f06121b06080a090203010615052206210e06090102041d0105030a02010c05030f031311090910 70
    0xb030009070300340c032509000394840c200420040c6014074009010fa50f0703030488400418081d803003d80e90540c1c3c140000ba003010003c3c0c82d1640329511205c2c100d20f080c07044001c0d00000702c500c41000107400d90220040c206901c0079030f01ca508050030801804240d900600c1400d0b00140c030303900001c03103000c00c90754410000700ca04400842d01c0001d000c010829034100781c100c61480703940d170300c24001000b003200340b502e80c4901d840003000c60b10307817a1000141244600070190804c40e51184101d80c01c543d030030f500540242451903200c034501a03000c0d800a005402c8130200042201c40010b41103401c6404903601c1048078040d6803040c0c480340640940a40170502c072820b9585e115201c1e100d00040100c24440d50707200391003103170005071220302e0f201580000a031402d091495003030b404801800300707480c00303d00b10088030f8082c200900d0100312483d165142d4412006240220003012003070140518554402201c240d01403620301100e4001c2d10200a03980c201903440c210654440009861084040c1c1c00c4503125980c06007a807 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 137331465 1250 137330215 137330239
    0xd020a17070906030507030903080708061302030c07120c0c1412010f0b0306060f010c0609080405030a06140a060b07060c05090324010e06010c0305090f0d0305070201020c0402180d02 80
    0x44080300d181500c04401094001e40c091160396454444d0341c3c0e0200c09032a003409801d4103a1005000792002030045030400844a00207641c984480d1038082d0b8036941240110340e03031f2070b01e2418203255800410702101d180050030070080f1603030300c0368842180081d0042d1703098403154034000810424070780e2818442d400c80c4045c00000801402072040314031084440c080410055200c0b41010b01300030005000b14400e0700d03110702c0007002d641c2c4000e224003441d600c40b40000b00c003081401c089146000c0c0e6403060354103120b0201020300300419a0400c101c4c2002004444255071554681c14081e10310038024221460814000d800c007141c42e9410034501c01b404c509110345032501e101d01190500c0c0a034042e0111002d41c0b864a00642800c404000b401400f452510b1030440c14250002060703045881c00c06400c000003c6114005035442404d03800b140e1500420041901307900e481d0151a41d00b080e201a40523005103030040a0a05181c000ca0300007441d0300e0b007031244c45800c2604001e00c0c0024100282d80000c141050 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 137332715 1250 137331465 137331497
    0x809010b0603010b12010801050c0d050a090219030303050108010c0e0112200c10020a020d0f180e070201050702060103050d05250506010305061506030103020405040f150e070611030d020a 82
    0x4501802941d840346548170508030b58404c02c0720301a40b1100b40340e89003008111010103980217460324040301c1c003070114141e10707410840d501812490101941c09003d10301816401214075826108407031103904c01303120b01e0b80c1c1d0301551402c0706e40f540392000200780b0020300c00300c0399846a01150007402c102301d0b0009002c82c12a803901c6212041c03800e2441d25010014100c0204003003085800110420201c0661504c1101c0300000e403100d01c860141c00074007111341d59020b41c590041c00c0c514800e40807498076030845a9203185030140c034801030702e5100c0594078120202e104540f01040040c107903500300e0014801c00c0000b042c2101c01c4da0001c40d44035088499854940a000d25400c0c001d0100b5009900400070341d4198108141406000f034550700f030307035000406c984003103480b02c1c0162030460790115400907080d0b40300e05100c045025820b000038117401000341854001607069215a080c281808100d44e099a160501500c02c050045102010f40e4800d2009080581503078000b04401211468210358550f04041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 137333965 1250 137332715 137332717
    0x507051309051e0124050402210a0203180a03140a090e0129070b0c130806040c090b0102030702010504150201020f04080114070306050d03030c0e0d03030e060907030507060809010b06 80
    0xc00c04030801c00c1400a0840405d006030029110b83c46481d100021465580803407801191140b0b500494001c1000300300222044001c04100790751f40c0000b2810b1920180303080080d40308a400c6c0305401002040040103140c002041c40c0215816120802a01c050081054a503045406401e00300150b4200110f500f094004c142c6008110790304600c0750340c1c083c644181e16201a40100082c25103414000c1c003011070050640d80341c02140c0081c00995582400f00c1e005103041c50350b00900e1300b03071043c41e003480104200c4510081c1101e00c2000200140440701380120389900c10401c0180c0002d03400c0c0070070302603c4006654003800303079414000140b41a0b513043c484038180d00700398010449a5581c003402c0c4042c41e5040300099202002d4076081216500b0540082d540c0305c84804040c08156603141c140100c58040c200100c00310310000d0a107104801103160081c040c12403c80c1540c071768041c010106100220000d01c103010380c3d902002500000e03051040072a18084000d004001c203640324240d146254032158 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 137335215 1250 137333965 137333983
    0x4030807211a0a0b031012020303040f0605091f2c090f0a0506010302090a0303030e0a140a02030c0409020901290304080d05240d02040b03010203070e011803050705130905 75
    0x210b082d100b881c400b0003c10500d18142d40c024107580504000304101c1303403103c400440a4506021702c1c26840710103800460b1030741c02540c0058481481c00940451b500d90040c0207010320b140e04441d45000601184581440c000d1030102c113001240c4038001e0031200403910160000c11311400d541c44182d11003d1000100344e0300c800c1e01d4a1440c400e000091000407429806450303440324081c02e0a618000d821400b140a00710385100150825a42d9005001140010300c90f00d24450b802c90001841001000030306a01c66642c108224401e205103025044a814103001d1802034580090119020342e00c0d0284004840004200784d480000075a0303100a00d030303903500d00514091400381c040c2a446d0f66070001504200c41c000b800f08254540800c9103144cc0007003c042110b0052800c0d1a0306030038900d28404078000c3c05d043c0b40d030310382e05500200030072008540c00b0308400d05988090380c9249180c1416114845042d00c140030243c0940c0080100b0b0140c1d0606028240d22801da01e18001051801ca8540c0b504058402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 137336465 1250 137335215 137335241
    0x10f121a1818060c030402100e0d0501060f090513140703120e0111030306030604060f0905010f200f0a0302031503010906051032040b0603100501030f02030403080721 73
    0x229081c080810340d02d030264a29085540024011803c0ca144044694000200024400e030480c1c040340600500c500c2c036686006901504110115143d0b01c0c08901800c0320b4069248081c08500000a85151364000e403030050b202d0b51290102d03c0c005864141243c0f0f1000034001140c8208070f0b001000801e9201144183c2c00e0381e036148803586512000041187c460080421801d5005009010142d907001c21850f802542c4008009540d01d55400008060000c0200107442540382451890042d62070b03800c8085851310b01c0a0500c090700000030341c2e0025000d20448640d40d48020f0010803940d5004c1ea00541c1c004075201418047d40804000003429101030400c22210300c0e44804c01e10690310000c442603130240c030441d420f1042d80d03a48040c12040c070340425091600b2450710342d4000403c43d19160301c4010000000b900041c0d8a140032107501c041d0f21040c2c030401f40041d00e0311011041c1d044403031090301d015035415521000035889036070781266082001c42c0044400c08840840000701b80710ba128040158140d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 137337715 1250 137336465 137336509
    0x1090506030601060507031b02010207050307080313060f1b0809040f0e0c030102190815120d09090902130f110c010b041503170706090503040608090c010f121a 70
    0x46001807609002c01a440781c800e01806110310070000750008030000c0c0340051404210343d2a10503000403841c10246902031034060240d54800300303030644080000d1525502070340031100650341e960411945c505400c400580050080d50b203001c280044c0f0341101a0050080c400c0b00c2c200401030000804946d01c030075001e01d07d00d5070b030802e13458180020300c103401203030300b04400841c01e0003c00c6200d110018407000031041000b5000700020100715410f448040300e0407000c6e1030402d01601c01d140303c03a0780320b640482003001300b80f9105c0c000450000da8014801d140341d0140c18041078000d03002440c4045d240f041e4140c010241c407088882581c42400d8040c00795010240008507041120109002c11140c40d11648510385060120510206e01d0f6945101c08001e004243e8590395103160a20900030580c02c04002c00e035010018002a8265001022074000d010040640d101040c04030f00540e00204160001000316200f02c0340103034040d03c151700220000c104000880700d1030b0138440006210403008000d42c14440c6c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 137338965 1250 137337715 137337721
    0x1b040f05010e0a0302012a0f0807050712080a05030606071502090103150812071a01080105040b0112110420070c06080f04030503012714041704060813020117010905 72
    0x2078802e5620586034000d4521400003400d50300024405100702c841441c010a40c0054100004030070a8030186454001c8503625400ca0146444125684011000e0360b003031007440c2010441580020054840c07980c0000c0240c0b8161400340c0c20380d01e070380005180580c880d13400d1010078045035142041e074148454400c401640c40290800150072241c9444da1b081c24491100c80900c501da00000300c50540d030040101003910f601e0309141c8000b02048104103200b24002c80000020f801c2015007003039005034411800e405803a83c86d41e034440c014040c111000381007061050500e202d6800c06034481c80d0402c400e51400b1141c0c001c49010304441d980081c01c00c958007000700701c3c01c1103402d40c8409502e0b003140c030803000c0034068289502c0c0104140810f000300710300a02180040070909840200b45908405462000d011920f1f4030360f907a103071103441203400769035150140300a50011513145040314150741e00c640340e0740c4140d01c40c42c100210320010060101e0600900e500810503150b05e180d112030003425034400c042182c2c9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 137340215 1250 137338965 137338967
    0x14070215010803040302030c04050a0605060705060f070c081611030304031b0f0f21020a030f060b0103020901020d11070b0f0c07120206040e270c010806030609151b040f0501 76
    0x40c140e00030b8035160814002480103950100c1d00410b465001c40700403030070352680c2080303800410465000fa079019030001181000c2000c0410b9040c4a00c2c1e44581d94921ba40e55094152401796150000405a8008100c014201c0403860b06a090b42400b46900300020074800012074550b5025810036554034814a00800042d105048070101601200e0f903400b001c07030710342844580101101c0c000c0700c0d24494001d191804500d900c1207584000c1c0d400600c01c000013940c9040003c0001408002510417078200359901c846075000e802201c4403400e069000307199145107000200d8440030038102c8507816016803500050352100340e0025100e04410f40c9055035032442d12a400c140392851990100e01c00140407400300380903036a41c600342d8046400c207501c0070031a5622a800300c010719510704d241038544800340c6002611030f20001b40c04c03040020280c880c2400c50711007004240d0340708000c0325070300e00c107510100075525040709401110740c01541c210508440c4d44600b2000b00c0f40c0360890781102d5004c8400180401c115 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 137341465 1250 137340215 137340253
    0x40c020c06180f0f03060103080313020a15020105150303090d020126060a09060f050d06140c030105040e0309060405040e0307060e0a03031b020a0303021608031306050c03160e04140702 81
    0x222404c4801014801c451408613459807070500c0301034803c100100006040c0c130510003c07882e0441d40106038104c000e4032112043d9050912000c1c4500540c6040001500307040003d80c00035001400500660801c000401003113000c0003120403c904003e02c44c115000c0c46030a11000161040410207002e20500c0d25501b807121820f80c0d680000207440c180700b0200440c0030b2807415001a21000c0d0f45050301c42c2d4031403e01d00003511442d401c005080c003540041181205503900030318140c40d801c51b4248070075401244200c7e40c0780540c0c0c00d0154007140420042000f4a0503a10007046401c6201c20f42c3c0c200345442c0c407007104884803015203458540050300c2c09400c050741441f230181c844191508141c20400d1105000b9138034800c581000742031642c00103200d000003105050140700c05a00054075070780e904d40a41c5d00304041900030404c0f00c1c041d0030032001c200c1e00c1d007505043d60f124000594040f8008803107290220740000104c0021500305030f03100201c285505a8220152041c3e0701500102041040043c64181d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 137342715 1250 137341465 137341489
    0x5010e030a0b132f0406050a0513200a020106090b060c0a030c0804170102091504180203040f0c080d0e010906050405060d06090c020d02070f05010509040c020c0618 72
    0x8260003100110700011a0300e03880310f0b006400034080320304160031450b101c206032040c1e400714440840307040d0350041c0ea40802407220400040669007448003a0fa24401d10000010134003a0f03583c40f491540400d40200c105601c03034110101c0c1100c800d550714402111781e1a042d40816180c50050351550000e008491040c0038010340703402d0503600c0d20718100001e05620b0711341602d450b00400b0011202100014801c9100030b13035000e061200441d07070701c100421060034000d50225041a00400d00c00c84079048115046c011303142121030b0313203000c2d1501c501c002801200940c0020300494941c01030100b21f40c042000c1c800703404060701d007038001032142200c160000780103030181e0010385041204200081c420190300c030040c2e4048800075240da544505116500a010307010720b0b0403c4280515104205000304d40c00694203030321712151b07020380d580e4989400140102405d40d0041d5070121304100020542400c0036445071519022030700c161421108146c00150b01d0750300c0b112010018a258101640aa140040700e442c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 137343965 1250 137342715 137342719
    0xd031b06150e130b0406020705010b060a0c0524060d051f0b130b060d0b030f060702030a0906080108120a1704030905030c01051e0703092d0503010b030709050c04050d0b0105010e 78
    0xf0075005242c2d02c0140703040d4000e1005100b2900030800304104802504a1043c0722001030a83d130712041d200b41c0007880000000429102481000e41d814502c40640540c04845d005840085e115a5188428001d03080c40b40001101c1901c2107290030b807128540d00892050503441c00705c0100d000c01104003040040b40f0309000940c5424540607404025580e08070403280d802840c1000403c1d030b100d040000a05140c031004540b0210301580040141030380d801300041c90440c845490302501ca5469180c11030303c20009000d81c0da41540034119146907134950f08003a00132255030780703044081c288204030800d031428000d0b41c084001c0303400c2104c1401f0524040c0032074080b00c030f02886d1007070801000074081d101d8890003103e24942000002f0710102414030408850001c0c140007400750900c0140c265000c1416101c011980d0082c80e2800000702c0c6d2813406000e0b502115200600400e101418076984800500c8064944002484204400500b6031904042c0c0d41400703010300e0740d612496242400140442c030144803068 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 137345215 1250 137343965 137343991
    0x6030b15070c0e0a140a110915041a04030506060d060e0d030608120909010e0612060112020103050f07120c20030d0e01060f1205030f280e0d031b06150e 67
    0xa6440c19601940540c040036624000c52244002100f01f44a0b12410f56031942101110001010341c44411008008459458424040501c20708509510701d02403404010306a400040200e881d0381f900d450000e89980c05034000041c1c942400007107504d090300e5602030b030020940f901820440c000061180d00102c0e5502e100441c42d04103004002562a4414002d542035a03020602140e01520b907c03040d404d0081c183c03000ca501d01d507100c02400c3c0305480b20707900490010341864000380034406030f1403400b070107102030391608000060110043c402404941e20b0080c02c02034289441a455400d520f86140d11140c407a02842c5d90b1550740c04044181c5807814110001a07048c04030401084a4406075101151050140c4800309030051808500b14861070078065114140490b0740391801006400340c0d85001c0c0d00000803101c00d0800d600030b807000b8900b01c5e080e45e4058284421a004a0302460b107070b1202800d403081c4211161140d83d9064110360f5180c0e15008101c02c03c81041c411790304812821900b001404800b1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 137346465 1250 137345215 137345231
    0x111030c030901110c06070320150a020304110a0609030b090309090106050a030609020403060605030c030d020613050a300516020d05011503050f0709140106030b15070c0e0a 76
    0xc0e9a4038440c2000d40c2c2d040200c0071030340e074071340d01c03400c0c8414036404100902d480d50395081d0b42801450342e004404c400d02c1e425401a142268480d0000e0342425150842c1407180090f61000d02c0c050003504018415a000c01d150b641c041a150f8801e660840601340c81d032120f160761420740c00c20480c4103100400009641c0c4c810040008035543d0034203868111811881c081c0c0ea21801d0034800c601070300b003951000d0011400402c001c820811150071103800d6560503021500c07103441c1c110400d03a9070043c0d55180d00158020341c0109110300c0010a201ea42e0900a00403101c0411a87c0d403000405044400c550001c01050f005007448003c084400c24039030401860a942000110804503000c50b52410009104144000c4842c04020082d0403400c83c480c0c0c8540c071403503100d0340e9040c00e0f503d5004101e02c0744854080c0220200e440301d041d20607500c0a02500002046680c208201074000300341c2140c1e815400700f40c60346800c00816a100080000030310422040d102140707010051340c940c0401810b1441840c0c100540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 137347715 1250 137346465 137346487
    0x904200d050a020d08040b0301080102030a0e0303061302090a0819050d3612030207050906150405040207141614010807170604110414030601060c080f0a020327011103 73
    0x2002440c030742c048502a0f088400e81ca0300d010107100c0c6c0da024011202012000258150040d409144510751000301404800a148903498403480101d81c1d103035100030120800740382c0026680c058056660060509001e4907102d802c82e42c0343c040035500520410045000200801c0340a02200c64400a103003020510020345403069440c546000e910b01504a11102090f03080350314040061b07004001c042d5800840d80c21605009443e16410f004a41c040c1040d5408030310582000e9400f4039010346240303145414141000100400f951020b84240c074210204000c0041035081071003030701500c1103400d810039101c40c40c0c0703140c1000e0a24a280c810b810711240c0010001c0075900309022150001d29011140030f9aa036800002c0c1c001d003a40030141d43c0d1400049408a682c00200500a10800e0120304603807447e0781c0d50004aa49008455005164140038800052454241005400c10280760700650b07040c034540420164203440501e1100e9503e82590201c00800e58004102c03440310085170002d0f51414030181d10b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 137348965 1250 137347715 137347723
    0x6300f050103110301020f043302060f0f13030c0819080103060609090305120406061716090203010303020304150c060504080304020f040e21090a1413090302070605180904200d05 78
    0x42500ca0020b181135001050814042040508a6081c074900200271481e0100079a030341e0302107419400040180740070402c0c0030440c0c01014800c0030b007422980c030800050ba60843d4580b21040c41241d81440c107200d901e0307500c0364000780712603070114a030788001b001d41c51405e06800b6a4001ea01c00000d40d07243c6004100800c1d400300071202c00f040f9542d03030351105441d9072402d1b800401709580202075a0b80c11421800c49440007181070340c0d400c10800300c00c1503090b4562035460100d01c803c0c803004000d03030302c104000c100601c6c4007218016403111905084a242c0100e40f5102d0607590126004c0390b060303200004010441c076154004503008002968108000c95410704003964600420041c032200106017002d050880802604964074440c01501040000741d80c0c1046d119a17446071000030b48280700034810b20005c0e1000788100900d4130b802d503000b40210b0745011020317200350b80a2050300a103000c1c84d20445840351a06c0010500403481131100f42d072080c02900705c00090194111402d07104485481400002c10000a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 137350215 1250 137348965 137348969
    0x30708060103021804051801150807030201140c0f03040302040e031c05090309030f0607020c030d090b0f07020301091113060f0e06061b07050306060a06300f050103110301020f04 78
    0x30800507031320f2042014194030702081e00f0300b1641c454104410414010507001d6248000d800d408024060410000006959070035a40282c02990313011607003c0002d503120f6642120403c2464408a01e0310b03c5604444d802c01c900c00c4082d0038550300028040085080602c034140020712407c002e1410240d0320026407000c001c591303035175039582900d800100340d460070248200c82c0b000c54000d00710340450a01c00b0450f030704c0381400c0760070b04058020095820418240410b0085030300781903555240364903050002c42c5010f40c06c03100020a07102024450480161424891502791a000f1800c00710410621010051400c0ba55148009400c0c1031140812000900111000559210340380e440c0e03043d905d51002c40c450740603d40b80700307c20070703c080780c240c5c0b003200003181e40d80c02d540b000c0c1c0c1900d0244d521101030124403240e41c411000002c0c001255240b45019021441210f140366500001d90722400340691000d80325150401e025040e03561004004000c0e1840489032010001c1e4025030422502c585007807501d010368 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 137351465 1250 137350215 137350217
    0x609050108190e150f070503041205030703060b030c22060914061e04170604030c030318150e010e01060302091b09090703020703020105180714030708030406020109170307080601 78
    0x200308a84002016000650343d814801c04840c2104c512481c10a22900c4c1a506107a0f45080f582c04501c0d06403080007100d119942001500c94803803d0910215190380c13004000c60200360f590030022422070341d460000c40c041c2096202d0642c84400c202ca003940851665604000d01360101c44003000526080840b0504035020380c8808400c1035480004148548221304510f5100001102d0507110004448041e00a0350100b602ca81413030445c101070750340c0e27854003614044c003c51541c0c0501c5000901c0780d00003104026061084500d070320740740e60b44d5420166004a6141c44c4903100c0e1025000700380244a29100c1080c040020b012003461341d0041044480c01401250303100401c0340d0f00c6400d0503459022216440e4003d04558428504070070001d000f50007408045005500f8040071503c202c82c0814408a9200820054030100c1d02d00901501da414074402a5501400740e113100180c094400d1000d0030044c82c00b03400105108059140c0420780d21b850300c82e80c2c0000c501c148140802d0035405806503078803042c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 137352715 1250 137351465 137351491
    0xa090506060103110f0a030912030603020d020f130f0b030c09010e010b0a1814150c070512010b030a0606062606060a0314130309150c02130204080d02070f0609050108 73
    0xc4c0303510a031000d100e000501d41c2c0d400c40009a601d0120340c140c2c400742145006000300800140d24460440964407e884003030351085c1c2144801000d4942034851051740e0000401902140744540349078000c0e51490140807202e01e80e43c80200d41682410300260105500480d0b0700d0303100d0360403e8400540900180a19240f40c28042038010100d800b4050301c240200b00014601d42c40c550340c8406103242171101907542e000f2000401c602080300202c009032250494154040c0850314108400d014109900481d12100d075034072100621507030784052081c02141c1e030182c180030803076a06040000e000201000c09000d01500d5660702c0c0c3d80d6800a070450300341c010380f080b00c01603a101c401650490180003e00c41c403400c0003400b4008d0243d196008030150321319a100ba11044100e65a864001c0c5507401c1c00b2401c1400b041034044040010b10341921018650482030030014105a1200000340c5805001d407102c00140e40300103824040058145442c20050102d40741440781c0703505103070000b050068041e001d0a42220 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 137353965 1250 137352715 137352731
    0xe030a0b060d02030304230126070201020d090f1406060a0e0402060904050f07020607020c0a030b0a09060507090315020a09030f03140c030702010e0d0c06051b06070809060a090506060103 82
    0x20310001408482c0341c0050460b0346558481030340454036150710512500004501e8141d000650240541c01c002c904039200441c0d05080030658081792001c01024507085542c2000135010b442610701c100e0340c519024050700c1464000ca481c07c541c03410306203a44980c0990001082040a9039800481025210400702403510703503c880c40454842d000700241a948281000304001c1300c131000e0741000c0c1c41800294200c03189034450106c141e841e21030521000c0e800080b91141800030030022169142c015802c07000c0021111140c0c0c403001e080700d100343d9044002490340300d01003050012030b03885a40406503c807405c5143c40b041c407030090038030182d03840010058070800c0c0b00c3d0000c0c117000d2000300e00403144944c2e86941e0b58103030b40c00003603d07544581000c0b40400c189001e400060304149a00d2104aa131050014900a0400c5001c0e00c60f0340101d6554450080e20001300301d140141413049600030000c43e00c40c0d60382030070070582c0c540c10710b0001000d4920240c80c0540030000f00e000003881d240c00040038200010740c9d00c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 137355215 1250 137353965 137353969
    0x607080409050c0c1501030302030d020c0703050a050f07350c0d11010909020403051207080403080c01060e0906061e03280210020f0a021003020c190209070e030a0b06 73
    0x8000c40d84035a0407186803404000200d02c45000400caaa803448003074801d204526500f204102c4e0080c00046c0060b4002d104403c0c050b0390560081c0382013180002250003c681da5582ca910700808006e00700c86941002d61960401c060410101340680100b141c49010203c801019200c80446c900e044070201c407242d2030943c000c00041c0100c1c00340b2400580f5594001c0c515080003000e0041d40c0c0710050010703298000014009140c0d1003a141130f6644103000e0003282d20030000001c0280c00008042d1480502080000700180c54200200000d040781000070407114900780c0c0806420740c0040010600760409803c2203e40e45d00c0350030403042003800107602d000c0d0402c074001103031801c0d1503111403088090704c400545000541801c100070105108645a541e4524900c001700d0320b514101100c40501d80c88081d14074014505042c9141ca40011840c00509080400d445280360044c809a2607940584030b10101041d0300b8000312156021085051141d80c14200402103581d41a42803406000d620820340451125 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 137356465 1250 137355215 137355217
    0x70b04020d0f050105010302010e04020708090d1b031b06090503031e1c0506130c0801030b071403070c11121009020d0203010e030a020106060306060c03050d061a07050c0402030f06060708 82
    0x1600014640b1420740c80d0300d00203008003400c2c04160b02003240c517101030000c0e240a00071280b2040d44910074134280110002070011003510100b08480032008504030120406507607403020021805070011024089c8080703031016140340c05420440c03c0184031941441641c40c00400c880700840c407000008414a9510f01c02403041c000e210700701119940f0a949841c1000c2a034002e5405510125001244452180f0180045516080710280807452a0004001085088800d01c2c0c1c40281800d2141d10446151420000c03a402100c1440c08600101010010b00c0140d03442200c11450994031000da0b00000c40255540e01c0c0c0d640d4445901340d45441000d000c544500340d07011076495018000740080d00c0b000c5909622a0454140840158a4000c0000d9074511034040c620495445803101e030340e005007a45046800341c1c003560000415544555000070b400c40300011120007022000d4025403200396a2500e141000c81c1000501e10803070050050002201800d185c0941080781200d805542e504680351003c91 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 137357715 1250 137356465 137356489
    0x608090f0106090903030605090615030a090f03110c01030e031c020c07060f110102040b07030c020105090307080705190e070302160b0406021c0203040b0a02090a0506161109040305070b0402 83
    0x215400c1c0070b4000781107a002e400c41210302c5d03c82d4030306028460301e40c000e00c1051001150b003d40c7c041c407207540e88003031140c2030001035070401030f40200400c0c1c004868403070800c0c9c1001d6400c01c4001407140084032140d120140541010007100346401d00004071201c0b001a502c0c02480390111300c44404903040000011103604a81c7c144120344181c800081ea80c007030141c801c0031412050402300718000c0a43d2100c80d418804c4806941c0d04a0030740e418108291021242490a11801c0741403140c1000002d09a540c00c02c040c00052000340c00424140303090005018080410b404c45401100e8050b40c24801440301c1c480060303121641d846d0050310343e00303c002131410000c50400082e080100d200140014001d403034004259022100c0303211080002e40420440407440210750241c5280e00c190302041d410401a001420f01c2e00c0010121a0450345030000241954800700c0c0154101c030031000399000708007130481000000d6204451550581c0b8054034054001c0c031442400401a04014000604643d698903204134 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 137358965 1250 137357715 137357743
    0x80a03113405011109030f0f0703080d02160606051e011704050313080d031505030c040b0a0504020d0b040e010c091a040906080a06060f0f1a1605060a050c04050604060809 75
    0x10014444d00e5403040d2640c8031020f107070b02038016141600d807810b100054a90401c03094900411600385152120802c58000b5800c0d51511902000500001c1c2400c0140c581c0b07090084100054140c83c00007001080076050150282103a050000144561717046168a99031210700c00c003210710f13a07545150490540c421140c0000b514002d040c004110000001020340288080d87c40401902413003440c5400d942c062807054981c5640600501656070800750040c040074180540090000b54580d0002416a00018030712000b03217595040500562900d070140c1a900f00081008000c480c40440c0b004150420740e00945000c00700311000c044109104104490003400c03c1d032001c2040c84c1e1078446064960412000c21b81e250340c03c21401203403c810f2900d459040f224111012009a4940322022141625442e2410015003052200645444950302da840c000c3d0300c106c000d1f105070f250825440c02212405017086000e030f54280014001d0341ca03180e04403070543c2c0d050b0621881d56980c1011607898010804040a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 137360215 1250 137358965 137358971
    0x20d050309091f0509150a030f0b06030a15020a020c0a0612050c1201030201050c070e0c07121103041406040308071b140120011b02070f1e090902030a0c03080a0311340501 75
    0x9002c01d0700203c0c1c9c9494811042541d46403640000c241d0794000d40d81c0003500d01510fa400d250b4990325103a00800c6040c1160040e41d096800700c8002175031415807540610042101024440300c00c1031303070388101540722103c441844e042c110707071410000c552401400001e05200000802041855040050368010302045040c00101d28204040da1803075040300070115240c68812180300c0da0b003070140203110007400c0c960340103600f0310749003c808081429100317035030b280c005104000c088042501b0700004c2c1025402a800c084038410115220b2600c0c09055200e8680e00b800403058240e00e0f030b4840e8103401d403400c040c070b20010782c0a13628008a004026a070150ba10f00c01c03550b580001280e0300426168110f4141d00301c05201c2035074405080201c0d242c500e02032410301300d0303440090100c3c42c00d6500520350603001400301c407802103c560764142c0c0c1072155002a10421404a820310702c0e00d9241c00b8011810240040c85400c200d0038884a1384070903003a9252a05a02254003082c0d150424030022161050f0428000c2c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 137361465 1250 137360215 137360219
    0x1b080f07060807050309120d0905030f04031a01060503070c080906030403020c1003140c030a0209090a09050c010c150f1b0305060901050307030f031b020d050309091f0509150a 77
    0x126603039000074815080450030150000301e2282c013910607240700b01000405044001c481418852142c0c1c49140c45c2c6c88000c3e0b84030102804903a0400180c100c00b050100c00c1591141503051054581e10048d404414041901c40140011584941601d80027030560424446080007840e1807243c1d8010441c2103900440040100410b155000031403140c0300b101070762001e2148204080450685003000b0014504d540710201141c4601c0030b0300d00440e840003158a0060403e403400c000140c40d01c805558803505c1079102e400d0b640c00c0c000103200c9000000424241088668010b545040060440002e011030700d42d51174180d10f07110619908100c40000040000d00e034002d40340303940500200400e0b42c8481c00303041000c00200700b80c1400034460040e250050001c0842290a0760201da8201324411103407600c022483c14040180c0315002a01c0d80740b480358001c0c42d20342809406100500c1401006510400010b9462a0003d11802e0200c0107684054031421910380c2d0742e0290060740c40b24004400c0c0c1010000c400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 137362715 1250 137361465 137361493
    0x4050d230d050604110406020307110a03050109080307020105010b120103020d0317010b180303030403082a0304080408060702120f07020402120901060e01090e060a0e0c040e031305030111071b08 85
    0x1c030f4030907801120100960034410341042e009004a00482c005a442000b00300d01280d40c044140744903000090140721001d40342da40d03240c00d45180340b4044a46d4480481480500c41d020f005080c0500015074849040c503d41d0502040022418070020340180341c040018410303d03118880030f0403444041c404944180d41d4400103101c1c0355101c0410741501c40403050181109203804400c40703020b50381582e51110b158407112044010f219411520055054000c80c283c941000d01c00040e40c4201c6c041c6450b2500d56141030b5546061030f1000300202c086401459403c80d81150010a031030400c00d001032031680b11507040c40410001c0c031590b003d820b8828154020444100015080302c41039882850341c10415913a105200700a40750b00e01c1010256421400005560f14056445589541310034001c4400c01080c500214044030421580c0c60402d410014004a009510780301c20030003448140d0003000202100d039803144203801210001440c0030000e1940816034032907500300c03101400d006803d0b03078000140228 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 137363965 1250 137362715 137362721
    0xa02120106080a141603050903040f0303080f01060c050a12050c100c0e03060717060409080703021b060703080a0b0d05030a0203090906150306120316050f070e04050d230d 75
    0x5440b2aa03507040c10141403c00a01c0040640a4240d0901ca0490240fa003881078000e0100204900014801030ac0000b84084c1c0c800c40010003903000351944030690902c4131403014401c1050304600700384416060000c0000f400020400015a0808807a6881e0700c0058000c84040c800c440c55025180f0802c94644062026507100310b045115a88038001004100c0b000d054031401d0441d07801000c915801c0301802d4512034070040301e070b04c210300910006005010790388044041c3c120160980060340616208141000c0c5a500000020411212241040780300d94008096410050510864540740c0fa80f5020b640c941c641c0c1e910300d9030391083c25039171030301e1000500a5030b07a0824400b885c82035518201017140c3c1e040c0241c10640031000b600c000b901c2c43d40d400b010f1007a41c4035890391807822407004020030342208240c0e16081041c14407503030141041400d01038415142840a41012903600784401c180400110000b43c01705400816041034864030f2040e511345c210b5031460103c45240010005241840d1a41d6a4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 137365215 1250 137363965 137363971
    0xc010c060f062c010b07140a020d06150603061809140601180c03061208090d140a02030705040e030322020d0305040918110d17070606050909061501080a0212010608 72
    0x10f80e42202084000345581c0708030020301c241d45201804011002c0800c5100d0551901d031804e03c0c0031642c0f2600c60b40c3c0030a400b1140342d40103944050b500d0710146681d81181d2501c40081c10545014010300e8100f40f80320303248050317100c4030312100c541c0e62816500f00102c40485098080c0018152103096a5481d001c0190b1000e40782c400009500d000a250b0501c0e0081c0704000c20b5030303040406044402419a00d400041e07228101e2280d010301d101010380c00084407240d0703140c211200c010180a084020780b060514000240d080356110351700306420070303000071000010f0b85e03030040480c489441001004200404105030380c44000c1d40110607104400c0505030014010012102203000c10094411b02064480f00040000c0d00104810b13400d40ca0720070b5a140c00042c82c4510ba000e865040301070139412201e0302940d440910100c03101c03516044104500c0ca003a40d12190301c813501401606061520700c000a245807884011681400500317008074245001542c161011000302c0d27840b032412540c550502800ca07403812 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 137366465 1250 137365215 137365259
    0x170c1006060201050f1003050d0f020c03010c0201020c01140c0f1c0c0c12020a02090408090120061609080709051504090308060f0301060303050306040b06070c0905010e011401020c010c060f06 84
    0x540800c6401c003011810b1b00840390814090115084014411150001160202005c40c0324403d1003150650b000c0c46085e942ea181500016960132408040f01d0941d4600c3c182c810003010b0703001c2000b40c42c0c9404422502c540f84251005a0b40d50411004070312500766a00c100f05205290170a008002034200c040c1e8a07a1038012458040c42d40f24440c4100d0355992007100086d040750003503000c9400580900302070100c41105052811019811584001c0864002406400c0a80c4a08180706551540d00c4032442c8112543c07401307100745030800c00095a00d0f0410f11500d00c11681e40d40006c0c0b89002d107030028400d3713144003c2017403240c0138050400824801050f0361a5110b190101c20a00c880d140521600b000c4991548420741941c2d1520200401000c1001c5000d82000c5c3c1000704000003518652a440501000c44000525504103c0480d0041c0016004405c2c60a0201d00c1e1070956a0000303100070701000e00f442c0c82950191185005000303414603030300840301d00f803c02e2004140201091155444c944c0c0c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 137367715 1250 137366465 137366491
    0x30212101a0301030f0605040221010914061003110a0302060d020903072103030908070b0c0c0c010203071a1302220e0304050109031511040603061401020109170c100606020105 77
    0x801001c00c0c1688020302c0014880000b400d041c01c0011440c2d001164414001040c00c143c04115601e8001c00c40001408500b01d0707503469a00004200c59a01c0402900c3c0e0708400508441c54000703001e0314520214000903140c0da990000b210960703940d070b100b10b002855015200300e49850340c4d0954000a9040011024464001c2e000c000c02c41002c16042000c40c4c8002c0104a8040d0546440a900800c80c0d0117090354428401c101c42d1002c0340c03584400714003a0f000c042c2031603641c2009041407410035902c01106070464004010000100e450480b8a440441026088040c1900d5488140d40c40715007410000350495902d47c00220380b0403080d1540f6000448543c0d091099000b0b4403540c43d01c911aa001e80d45c04901d25580520100c0d1a001c94100460840900007501c1400d414480b105600b00e54003d1001a88400050110010003202c0e0a01c095080c00203005044803681c0303c9001c5441c182c03450300f1420000c10802e8503120704129005004010310700401c02c00e51a480001d01034038040f1480b8464041c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 137368965 1250 137367715 137367749
    0x30715110a110630040c0617010e1312020106091d030703030b030a081603270b0a03060509041b05060a020709020f0405100804060f0e070b0a03021210 66
    0x80125440d60340950101d501c000d1075a1030010845250410b211480811154507441e8256004c101d40501c844c40c9a03071030107401460306240580c150349854200900308045c10344070003d048181103481c2d0548481101001d019520502c881d00b00c481e0741e5802030300f0390251110a40409070198415026216800d000703010000b8201600001c040001401c50080da20405c0313104040380c420f50249054940c0101a10010b00290715405401d41103c0001d40c2c000c05500d005108054114010008203610080d8000c4460b059000c02690300c40345104200d2283c1001901c402c180b03109501c0750300603080041c54a04241031500308031203040c0399090340c0800015041030219042c40c040d03096583c110401d81c000e02c022070410905078065088551000d542150031b01000c82c807603552820007450344920340c1d142000c0f890301b414040d00b5101c10140d000545440e000c00c07919109008140035060b2022075040943c4e410380311038100d000340b140c00c81c100b45001020040c050002c1c0e032215442d085402400e184030144d8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 137370215 1250 137368965 137368997
    0x3020a0812030c0a0327051b1503100b040b03010f1406070303090203070b040b030108010f201809040302030c0c04051e04020d0614090c0a0b03061201060803041e0f260309030715 78
    0x241826092741c040c40b0206d003c48071042c540011036003c680800b8280085580e0002031701c8641143e00908680310000c401841000307203c028100080426004824200000c8408a1401d22401c40050105501c2d07505180664808001e80310007025140081c41c3c3c1c665558404003003681080c0500300e101c2d400c005400b4842d110500414028400007140b081d91101c0c002c1c240c2582360700414800f0291120030203d03840950f214080d0501c564001d030040c40c0c1d1001c1c0f07605030780c1c100083c1c0741040c0d00c42c0b1b00d404184801c4200c02d0703603d09555419104030310300a869500000d41800c110002c002c14031800d20100c0d20312240400003150013140c03450200c8451001820800c03460182c18058041c2d00070041c800220b03a407a03c0b040645072000e501c0b0000a07519100d100c002d00311b034410380108000ca10308203000e04c03000c0204d2401d0001050a12a294503041c04e1048881c4554840444120513480d001b47d004c2940b0414002c0f0340b840300d0300400300c1d1100ca03581c46028560400c000b003000081122103910314800e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 137371465 1250 137370215 137370253
    0x1303021606020d0f020f030d05160908070510020f010c020c0a080a210c051002031906030b04020f03030c160302120303060a090e0a0b0c030103020a0812030c0a032705 73
    0x1c0d03249034000d0251030101002c03c603059558010443c0440c4a22002c050318400240024014070030800c0c4080303268500501403601e0441580e502904108541c0001c22014070701180d10710070388008440700c00041c100c0c910224584040c08039181240e510f88032040c2d50550b000242c0308280182628070708151035231400f0058036103a207801c01030282d80380c00381c8005002d8007600107500ea40c415030608881d160950b460b2145802205052011120360000502002113112041000c40e04240c500c2400190700b141c2d44d021082c1c0d4003500007400740d254281000d142f0741e028800c1e0f5881410003821182c4000003c001c02648000320b20040c3e000310101100140d50460100859201b107a015144aa801c1d1070308a00070020101c1e01e4035110580906040b600020716684c0e00540920300e80464242c030395046004107c80c0303d5445d400404681c0c0001500c0c0e07901e034031000507a94400009030103140c03074103403a0201707601400d6a14548000c2c0b008140c08041d0076200f0301101058a80500d048503000280642201c0ca4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 137372715 1250 137371465 137371469
    0x41a040b040f08040b03090607110a08190509060c060f06010504080c0904020a0b0f03040611090d0b0a090c0303170a0e030f030408090a1206050601020c060301030f0203120313030216 80
    0x300300c0c2480064045259003450003890b43c401c2078000d00e071503610540c0170280d42041c1d07015015a0005024031501540c4001800288050343d0041d04400d052035459004604c60540001c00e54400201500c456038015419607000b100040c1915a8400f1701a55894035100104e80f4a104001804c001c284254852815241a500c03018010f0040544040c00c0040c650130080040707a00c8003001034046101d8581c00e01500840c058410101d8603070906207064025a203068016058491040c412842c071540c5c0c1d60201c0c504650480075820440d02d400e4850005440750a102401c0010031140000402d0340c0310f41d03250102d001448400403940c82e0944007500799001d0560402c02c9500a0203619200b046902c01141c1051007015990310b0004118003060031040a9445803629402441848050200602445900400034800b900d04880004000b400c913000600001c0d182ca10000b03020411500c0802c0b6100385521007102072502c034075111180c035440400b020811001405000c08216136641140c8174001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 137373965 1250 137372715 137372723
    0x30212070303030f0b060406031d03180310090804060f02010207050613020405060405060901050f010306030b04110114030f070c110405012301030204050d022e0504030c06050a21060f0806041a04 85
    0x441d1600e23042c5e00f100585003810305004c511000b9401710300b820380c042005164003840302060710145100179003010f0a050078200000c85042c10b14401e41300082c442c2d000c9030180c484e241800c401e0903000c01d20807402400354440c014500e100e00340601c0703044204038180c140d40510803134080c4070710340d141014001036841c1580c000d5008617074000148000e00d0942c0c036040d20302c84123140c006485652038030741248c1c40394151401c1c4c407040c083e416002460b5900c11440d5650300a0110001d00c0c40c10412007102555000230003c0c02040928079401017008009135404a11b440000c1040c0020350b15084924074000e0454110b2225200e14a4000c0542d4028000c0d00c00307c1c1d01c0206200c1c000d684a8003071100140d03003844030a4505070454929004100410034100e2407034190741d82e15403901e08600e80320030b107007005400800038000700b80001050301303500001e000344c1c7e000c40c0503042da102c440c00c108600203880349070014114410100804581000d0004525105502550b164841c407066402c84007131150040e07030098 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 137375215 1250 137373965 137373967
    0xe1308070c0f150c06020d0f060b0702030d050304031413090c030e16050a050d06110a080603060609040f03110f0a03020c030606060f03180c040509060411011b0605060a030212070303030f0b06 84
    0xd408030f00f03642e0107011f20100c94071000c124413034210025012680c0700d42015606a401140306410340c1000c01a40074800c1e010b042c25032560903d9103001e0034600c0d21058842c410100000c11900e00300e1010080c50007440c1d8514240032040140c04043d015107000c1490b40024402d103400036018045000b88041125005080b40d1800e9080c07505010000e01151410b0f04d0058481ca14a64070361001401041208d441c0e903200c54081c1032020401d81841030241549229103846000c0c40b0201c4c0300241c615440035414101166981c842c90300c07c03420808924043d1580b4016426000203068001c90100705c40401101603e006a81c0e2404000c12402490024402c0000030f100180c600c8124104a141c0d94010b50200c13124507882d080090203903102291a420660446401c1c003040010440d0a0350b89900242803002e242030b0344070040c000c465484200940030315112030204045488100e11a000f1f59005021000088281061603648041c2840100c0c0080e181090b80d00008240d40b041c1c02904a00401c1b40e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 137376465 1250 137375215 137375237
    0x200d080d0e15270316051608010603031704020d05011104050a170d2d09150206070807120b060a05030108120c10020a20010b0307080f06010e1308070c0f15 68
    0x3540c080700d00440c2041c0d03d80300c00c0101d1101d4282e152000440305125100074100c00c0036a140c00341c1d0710403030b5a00900090303042540c14400207400032a08103182c101c03c1003501070340d07070303079000088000704000d10151040d480d1513a00c0c90072031680002007060300c506942200a01d40c1c1c072405030100445004042c8840c0d00408610401184a000b0101d140410b030003449000a04408101031140c1c807a622841c0800c92602c010400586219a40d01608425001500f01880c100201420001d002066501007007a4049070314480403041e4001d1241d000003038000c0b61540a60035025006600038000c0010500c141e1b280f600407903811030229580480c448020300300b004c456a81c03c0000e9080301d40000203001e4460210817410050001c02801d00c40403400100b181d00c40c8905044c01c00e0000e0304003803c00e80040c044205524030000d0700c01c1c1113a801c43e2181c104c50b5100078011074403941d2070b40300800003c3c0018980c414024441e5411081c0d402180306601e503d40e172990324540b080c50b82c00311880491944002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 137377715 1250 137376465 137376511
    0x30b0105090405100f0c030b01260a1103040501020c0c0a0b0d05040c0509042a06170a232401021f0b0d03020609070501030603200d080d0e15 62
    0x106070b0494815411200c4118080d00013806603109165110a45a030750b020845150790701d400b44444646085c00d02c1d0744115501c3d5905441c2e01036a0400c3d10300c004000c004240310a841c1e038007a500d01c6440c2c2440700d46a0400340341583c080c1d0f001000d1600c1c1c4d03101c1c54480308460b140c20342d032000071240130401452800c00c4a4400c02d0103403000410603246000600000942601c854044510070b07489519000b0014551042600c0490041d5071582d8504880c0d10341401a283c10034000030f000d14103c00c1d6814560746e1040ca84003c2c0041d080c10741c03038030103920020042d1056134550303050184030345600721300103034042c1010801c070560714007d40b60043e0f200196040011000c40340309042050300400c0030450716464404644100d40340b10081700168049002c00900d0740c010302c8410042c1c5000d2130207004152035a11440f842c0101c030b030304010824980c0604070086654100301c0f40c0406510516071502c840c49845040e004013000b905a209602070b0b810304d40d5165044a006900c5000c0600706060400705501d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 137378965 1250 137377715 137377729
    0x3031209010204050d140d0201020a020c010c020609040207030c060e011e020c1608030408070f05151c090b0402010305090109020a090903050c1c110f060a0207110d0b0702010b0a030b0105 82
    0xc00d119540c2080b0200d199214580713842150360040c0c41d5400203282c4520700d0340c03034081c1d680000011644148a80040c4a40c0482c280220342c3e42441c14031107000300c60000030790a108030090158050710014035001056000525140f407540500020024aa01086d4403420f0b9010001d0524103401009a01c10343c10580b54054801c1c2c1c81d52900b2907000380484111545c05401b15008554103500100342005407240400004001e0a8000805103c0c6440c02c0082031040c00e103c4c0281c001d402c070201e10300d445415403200c01c400240c90002c0600c80e1410f28103000020f400705540680c0040e04000c0000e460382c405020b9881c00c0ea074003600200350b503031030b051082c401820144000c07004c000c010007199840c18030400c12651402642d4611100b2924500009400101c1c40007061080741c01c80760500f5102c500c082107459015444460250750303000b6500e022040c0f070846002c460780c0300d2100c83e00c0c1000e1000354070109201c0e44003034000f0840c0700c0201080110315019488010310707844509005012904060f0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 137380215 1250 137378965 137378971
    0x60405070e1f08030c0d090302150a1403040f061a09151804080a0306080a030c03030b010507021801091a130b0411030a05060102060109020c031e04080f03070c050a05030312 76
    0x101c056030410b501c4180b1100b00800380c2d841400c8035070012641e140d6406051001c0c8001402d5801c2500180345181e0100d211a000c1c4282c031010304102181e1009414020049a42210200f410350b903503920349440d0010ba400c50800081d15420301e0580410040510710740740a9004000401205c095920281c8281400d01c40541c1d09410041084d6090b07010385100d00564043d52152400c41c1e16810b844038000d00f03c50746617000c402180e02580140000c01d03080405c04040790307090703e8003066140c590700040e03506100c4c030640250460060607992619170712200c883c5058554812040c4481c0071400c0000c060964011602c0751701c44890200d40c80d0301c59281e0301540c0100300203040482c4407199080d9030100f5030001c440006c2c0d0a034460040000710b680c1448800d000d00208041142007460f4807207015900e02500140c4607508019100c1d000c24003280a05440c001c214003811125140d01e4910295200e0700142c504035507030190100003003140c0c07814824100c296000a8015800c29800030b0800503481005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 137381465 1250 137380215 137380231
    0x50a03050f071b2103060515030c0d020d180f0b07111e12040b0319090b0403080702120c070f1403150703090206031006020d0206070e0f01140a030b030708060405070e 73
    0x700504640c1c0030500c4c2090801802c030ba80b8001001407410050107400000e1804104045104008224108003040c054642403012550010380324000400a400201030200040040c1c10280300d59001704445d403010030b01800e21450030703680552202003040c2d0700c0d85c00c6c440d1440c2c0660860621030f007070001000340186c2c50116410481d020315608401240306035000c0d81040704009800010001d02000c01004d0039120020102c040011148944407241200000751000f001c114102003c43c1c14503108210f086404174881c10156035030440d0800660340e9041307501c502c1940100f003080c000b921204220071480b15000c060064100300744207040c801e140c4a001400501415980c0a2003005a03da40000e140300c0e441c0f000700d9040190904c0006860144180324840456010400304001c0e070354015447d81241d4020341c1c0b4000e030005201c0050340e00d84075800801c000100045542c40030107074183c1115118110640658140c59110310803141c07154802c84020b440c590008008014144090040b1a800105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 137382715 1250 137381465 137381483
    0xb0103050f070c1b1401020d02060c180f031c020f030313060b03071509030b150d03050a0302090405041a0f0f06090a02250c0902090906190503070303050a03050f071b 73
    0xf844400100808854000e00300041c480f501e054891b503010402e00c43c41d82081d000a25280c07400b5008814a07216068030800c3e46861881209555240c2012202c0480c0d4001c06076000d81060b42c0b11002d0204200800c540180300b01100a443c018010044034000c1c031041c00004403049140e00c502d400344c10109240c2e901841921000141d94116601c43c071001069556a181401d00d5810907a11810021300181184010a42020b0a981e140c08850b040e44d5414100b140d04e03a03d5011059000b40210400c580c2c0150070300d0100801c000414800a00084004501000030b0f180d10080e02c808080171284c083d00b080031100841c070315141002d501940b001444102603e0f00b072440340e810300c030040c07688148a9200a40e100310020000610320401c042d0504020860034580c44500041c0d11034406010300780203510045d00419241d5140c090000581809030840315801c0ea030340b60061959025455103000030f031420001c11110560281c8650003061255282c4040c00e45001c48041e0303515552404440e4585 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 137383965 1250 137382715 137382743
    0x7090302062d0304140c09010b180103020f040e0a110c07230409080a030b0103110706050406061212030c0804020108041217100303180503060112080d020f030a0b0103050f070c 77
    0x2001d02c010752107107100b6501000311001c2c414441c1d1a18130600c141d94880c55040780184402c0340c910302a87c18008000c03d150145200400048e00203200e20b000c4000c0d00c020010300491580001030915020301c031039071010800c410800c8820b0000707000740342c0d8540c0d0940005c030b000c1040030f843d10400c1d01c4030309041500d5a0034035480700025080700e1961504484414010441c8003103140c141c410410002e030203084c01c4c00100c1e84882ca0074450311800d2001021956580702003814019140d0010014108043c0b82e08001c0c0d0f00760900d855115240180c2c0c2c40040d0610180c0314107a4400c2440c1400340b0303411f8541c003985403150341d60800035034040c541c0c010402281c1c21588201e40382d00503001d03008503040c100d440b103541d056007002003012a1584450668400c541c1081045071030014110381140c010481510301103029180500440c800d1a006500403030000c02c0140d039595401c4025409501e00610030030500d01c245005400303440088400c03241c40854400000c01d080c1c040d044040d00c2c41e1003141c0b030044802c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 137385215 1250 137383965 137384047
    0x21302090301090f05010b030604050319050903010606020601180603020603010302131e0e07050114040902030c130b03061804110f010e040e0c03061b1909090c030e060709030206 78
    0x202c95140907590f13410001007038024000300303205001c00e40c80254054102803502d612001e40d41d00c110901808881c10f036014000701c0d40d106000303a4080c42c0d8024001d00110346e039400003c0d550003081c01540ca48e941404e220302c0501c281c5100d07072000c60303a0203030400e41180e01c0c0d030702041100000240951403152b11a960112001d01c5480500004030011030f0005d24400307078642c007a180406503003001c1d040c0000c0403100f60030416080c0580d01214141040075a8035a00c00c07001d10181c1c094081071643c01c1150074004188607080340b020f58842c69050b07405440301c0710b850911440c110015200544403007194500d80d6130700e0806080c001c1c490758042c10000c0c10345e8035620100d000c84d5101c0c0440211504100288046450b0a001294100e10b20881071880303460700c00e814251600c281444454401154942121101e0083e290b07400100111042040b044200003c050090000801c9918090103031500158480b0301034110720044d2600034208031305100c0600815403a5403404040e44403d21100c0e20150800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 137386465 1250 137385215 137385221
    0x50a112b0b0606072001050c0f100506270c13060207080f0a050d050d0609060e06010906020708072c31020916030b06180102060a02030c07021302090301 67
    0x10640100c005100350103035007400307411403101070500c0344a81c104221110100d010b1104445405241a8001c0300614070741300140d83c0e910419500c003419005146000409450105140110100c0506e045c44a41c0da00ca08000e1143c45020901a014040c80000800d1500354840b441c3d00442c0100940d2400c0500500d020304440031758808001640020001c0c407941340c05000010104e000c41d4003c3c00c80710980e641c2d00c0d8403074800300410700c1000400f00b0600c007250706907044640108600f500400405803074a51b07499a040d03040300c0b00303070220300079880000341d0754130024521003200c0100c005040078030b04091309000c00307100c035584211001103c0107071110300c0e0200d28800303401456001c00002c0904e81c28030403004440905c4a049500040400c2e022015803510800203034420b141100700c800000c5c840000360001d00a40450700e0308841c01003500100c0c80c091010810400100340c080740d4080d0f035600d0350001a03203c102c035000301e035000610035000141050340800e000c0340c0041c08054200b0f02d0140100e421 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 137387715 1250 137386465 137386519
    0x504020f0406180b1209010908030411030c100e0f01110f030a140301030308131a04030906020717190503070510050f130b0c0a02070e010e0f1003050a11 67
    0x466100281c204002c03034100d050515400d400304000320042d407030100000c01500079141038803856107000b00022003039002903000110303403640401c150f5143c1c100750400c00880001281d9090080c070901d003104000340390003481da201031b610f107640d5000511141814845240003a5100c81c0c140a5019041c1c030344001d0038442031505018081c000c649405003040d00138400381280c14030120380c0702d04000510119a0107203c0e10b510180001c01c14481411528100d03581007607120461000a400d441407008042e44071244030100d690b01c4e070803a1812601da0308000091004001140e1050340180c1c007529403a1017805494040500070001d8900b058100e031030380c504051a00d1845400a9a203008001901c40884540c42c1c0000180c070459255203455920ba91403444060b2207002158008a04100b04d54801c20106001d8044001300c88803039659580007070f2000304295a45600201a840015141807074072241c2811250480000d11a0701025291507001d50083e480061308001000030710f0103084e413401c400c1a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 137388965 1250 137387715 137387737
    0x150702130203250f14071e12110c0d030512090309011205090a0f230c24070b07021006080f0606040c0903061505040504050a1205040605030f060a050402 67
    0x1030b0380d00e00180500301c074480f2a41c2180c0304001c00300300c3c1c20716943d110300399450580301d600705010f8401505e56110224001e01d00002e1404280c001ca491105410f0075980300510310803040501402c81100341590500200d6003a90a99484031420000da4a000410308070042c0c000c3c14042c6c03401c4c410201d000e0643d1412101150698030000300441596405003040c0c10b00403441c1410806810501260b41d200c1c418103c000c2c1a103d030300c081071400e0241c0c0c4210340c1d8520010904041d82c256080408580f210222008140701310480980d03500d55650840030f1446640e92410307000d01c5e04640381c0c0d030000c0e5440080c100340118480d040013201603165074407840c000761000e10300802d1440c0311052601d190610040c40c0b140103508107000079049603000418001920380c4403902160120a114008480c0d907490341c04150700500388001d00c01884404104028964090500035000401d4000185c1f80391040d40315400c00076508100044080c9090005590480b00c001c100c48602c598840005050740c000d038079420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 137390215 1250 137388965 137388967
    0x60218040c0f08011e051e040f060e0a021305090703141306150b0414010507050d200d0c03080a0e0a08030106020706021603020909160305010c1d0307051507021302 72
    0x281c0d41540101080d0300500c5e8680c841c0341d0700c0180400c005040200e0f8807810340110004962120010007841185889400140c01040400a10356080001e8206072141d024800c0840e4045607207190940222224001800c111120052901090101002009211300101139645c2c1180340e0080030150710314001c0c284a01c0300040d00c9610300700402114600f5203403e080c00e0704280308004554400d001c0d2000c0710301a05149420040304001a2124820340c42c008000c0c0c003802d415444116040400c0c2201c540600e68894506000105120b940d40781e90315901e4081198110708000103441f8024284d40001a10b5000c54a16642c0c4040c0c1d2074480003220440c3c4924010005005942c2e041026070001e0900b880184082c81c0d034031100c0412881940000b0340a103030700c0c2c00001c00c2d8035010842c0b03070300510381c0601c131440b116600c1c107290340282203299490380003e45800f00c00c10350401032201038403038110080240494074907100422079041e000d8014013840c0d440603c84140541ea41155410118034880c2000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 137391465 1250 137390215 137390237
    0x30403030209181501050309010e0f03040602010c0f0503130c0314060402030c101403070e060a120b040b090a09111905040e0f0618030d0608010207030e041107060218040c 75
    0x580451141c0380f010300402840204000489105010b414410382800c001e547c035110f10030050701516007150400103911400c07416005180000008104035030144e0b00800c00031034034040c01c46814047c00c03500b0000400500104155041082008102e01d01c596042c0410690360b80d180820404010206221604000c0800c015810148841d013a070513000c40b0114948114400046c2001d02201040500790314044000b41500b80962704070402440000c01c82512407400e07010080044c1c4d141d81c101c40c44603061032545110742c00c007400b400c42682401020103542e642e801c1582401021a181e05032280030500c40c07a4009621031103001207410003c5102000c2103814101880103686c800e411816480d4460100743c801514003180d407076041845040c01a4444160f804210f1460040494030301102c0e01e07141c00098942c1055006201442c400d4445a846034003000c208400c840040c1403050b00c4030307802c00c042c00010301180d0040ca0f008207c0124080001e4907400420f08440d142c15240740400e080501c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 137392715 1250 137391465 137391469
    0x31b120501050303132c01080a060609200a09030204060f090e0a05120304141006030b0f04020102030a050d021c0501030209130201050a08060d0501090b220b0129030403030209 77
    0x400740035000940043d407620f04403d48100d02040c96200c2d0a8118a410608100782098144031101128400f00da26030f4a58554100c6c54031450b9803c4112403040c642000018440414003641c0000b280ba80700c0e080f40e000b5941d81d81c1201d5400305040404001c00d0481c04001a0348600c21403020b06580b07580308030500c0c00e0000130021649a20304141459001c108400c0000f4800203410400b40345101e051600c9403a2403801095003c142000f0186500620070310350343c070080d140e000c04100c9004030f81900450301c41d2120844082c0058401a005030020040c1c2056180540000c00100c2c960101c0145000c0c009414601d40446207440490402d07107620042081d80780c250982504460b40b00f00c05409100e1541c0041e02c5845182102e034140402100010740650381c40c02c0801d00d030703500000248902c603014504106100c0c000c50300c01030001c19100a000300c004003030b02c036030048561103c40b5148990a001004010030554100307016000340c080940d62280d240c45000d035015501c00c0d280581c5070000401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 137393965 1250 137392715 137392721
    0x209040609050402030a1106040806130b01120b06040e031b30030105091008030712020609030c030d050907080a060902090705030c310320060705030406030c031b12 72
    0x32220540e94108003d02016a40105a202c011030f8054400b0140c2d2030800003040041c0103c0d80003444501a000c20411801c02002000d90414401c3c5101c501c5a03032204071102d4101052300e005409c400038540011060f003041da001d02030030894003007120304048a1841103c6656050f6000d4000e0303401c0302c3da01c29034460300c10b800340a46248003051086a415145500042e40c0014451280305205410108980503421014000034250500640360740d8060703810315419002411500c0c0c00144160710014420101c04403d0301c03c09803648006d185803400b83e00c1013502905000d069003d0500480d02c0001d02e24070100040d022583c0f103100c010400c01464010000b103050f0040100d014040208100803400000c1802c07501c0d90882c0510305001c109011181100944c09003a0241759640e20000100c1840f245004003401c0050390301e8070ae04115101e9080c40202d00580f40c004081d0b42c4280814064180283c0103401801e500d458005114606071a502030310700209083e10f400703d8a0420741500d4010580 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 137395215 1250 137393965 137393969
    0xc020f0a0804260307030324030311060a05011a030a060506070b010e010e0402011b050a020405010902070c090b240c06070905040b0d020102030a1416050d0809060f061309050601080102090406 84
    0x81c03c000301c03004501c1c400c0d4592003022002400c0650721011b008100740c0011000d01380f1b02603801c40300b00c01900c07464082c00c140000b0050090070306c203607400900000d0b85801018160340803018032400d503c0481207050140c0d0405840c1e6140076449440c00300d420703101c01024000d524080c001c1c8900b02c2d4944558280c01c22410f800105908100714200805130340c00c03030f10400d60180010030800c016842c1d400d10714244802400001d40c0a070030440000395419454024001b0240140d070804806580c0d4103405c07003200e0ba03030054a0340001030b01c120807030f25540c80d029108008404409491500215408003410107000300e503c500400e800d000140300c241018424203400c002c0c1039611250380e03000d64001031345ea03000300c81003030003007015501d240490300c0c00380002d44919030440c881e1010000741300d103407590300c40390101c045100161524000903040100007501b680100c140542800e07250320303442c0600050404000340781c40c42d03c0d1141c070318000003242040304e54020003911000607200c0300c072041007000340c401c10703 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 137396465 1250 137395215 137395259
    0x140a0203040b07031a010507030201181b080601030f0f050f06071709030a0c060b0a030503040801050a0c0914040b1c120e010c0c0e0603160605131d0402040c020f0a0804 74
    0x44107496010b03020101d09007817070f1000d0a00790b481e00750070701c2c04a01501800d58a20071409001c0000001c00c000b400700e0126014080e403e410b55192280c0e001d6940f8902444081c240f8045c0003c1c01012960241c5002040c50080042e54a0f0a008000b0705141141c25504040028203418220213400c100c03007245074200780307481d000c1c61502c0b104180c010314140e00204090000765460364415215910302120b0301c011903001c02941d0310b4941d203104281c0204001c880705128141000480070300c02c1d2051081006030359201d4041e01c103901c4040306001c000e007050903004e03800c0820020503a0a06c20042160441c3c0d074803034000e03c0c20009502000400030351079a008203050055000c101e40c00154649010429594040003441740c950b074040001c0c0c600412008103c9141500c0c14020902c19440001440075400c643d00301c083c425560004040101468440c0c080d80360018800b04005240a40140c01c0a110a1040b00e4111210f400c45500b0b085651200b1035003240c0c001820000718690740840c5080701c1c54 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 137397715 1250 137396465 137396471
    0xc0c06040303080a0f18051b01030209150c010605060c0d020c04020913051003020904033b0f040f0204060f121401031401021201140f1e01030f140a0203040b0703 71
    0x266540c05040d00001070304e0100e41c130340c8450003800c0311039007036100c5464420340250101d41d0360401c0c10401d4448a80d80080c0031481d0b042c0c101c0c072410354064021560206005401c030340c2d2101d2000b401081c0780d040f0b03403014034003552211400901642d031400540b8542e00070700040d08842402c00703406840c144048803840e00481c0144207051160b601e08590502e4156020310115603a9290640c050750349105400083d404007400c1c080c081030640c0b2811042c0c0b48000b0044c00810078941040c2001c003a130307409070280202e24042500359002d040442d0300d0714411002030404902c119126100c2c50598009400420015031107c0f00a03425503805854500c2100c1d03908401c01201d50328000069507000c05010150560070b041e080e07500302210960403291860302540c960101540c580d05240e521108040303020b8490342a80400d00c1661504da9944100070002c00340d81c2058400010054010342a92180d5004550f52001d45004614000001a2107080d5524005949141a1401c0044424040c0001c400c040c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 137398965 1250 137397715 137397719
    0xd2a0e060d031d121002040f080f060103120507050109030518040204030c060c020112150e09010510051201110403050a03031103090c040b0a030501090b0106020706030e12160c0b0c0c0604 82
    0x3c2c100145510742d22414a00754402c21074240440d141e81c00310002110780b0f1042c00300c400d600180310f90160013506d001380c0744400c540d0364030722086a541060741520b036110f0300410b0041001a0030b05501d120b02004ca03003001c500701000ca4580908607035a007982500806e0b03000400702040c0c100d403140c990b03001404071800c5043c60b045489840e91150240103500034072110340000c4042d0b81c002c43c0b0007104003c10b22014000007661565420002c40d0a04c03c0212580343d07403020684285040c01024851003c420900320020b2800003000072218034403000ea8025540d58038854000d80348a0002d1000d14000c2008140020282c90001c1c1100e81c02003806215074424000c1c4005c07087c01085242c1300a800b00c0340881c04a0780c0d03400107110040a0f0b07200800320f41c609078000e01000481c42220b812144240c00340c40319240e40d0340c810382c2514000c04849113140c200444810413110100c0141c62285800d00e400d50300700c0001c0ea5101d40d1844c0c03e800c080610503000c038070151400801c01019103c00c1c820b44046d41468 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 137400215 1250 137398965 137398967
    0x601091109061e0403110310050403020c0f01050c030429070201090e1b03010603050f0c0406090b0f0408010e060109061d01120212011806050a09050a020d2a0e060d03 73
    0xc01549a000d2003640d00282c0800c00d400c200d20310030854280e01050503511360f582d00d05050041d01c1044120b00030b010780c0c2441103d4400602c21070344925055009403407855884070400842910342c0d0382e02810711100340810301398550108003401c003a04500c04510300981c410356007040052820350000490b0503007000342d200140d902104003030440300060300c481032984a00645061105c1000c15540100501200000e101540340c1c00550040c00481442c021a403101001c010300c030b2049001d10f0340030583c158010066101290f0051102d0103081805500303241d20390220314250b40760bc40146038554440340c01444110a644282002441088101c5004441c020b0442c04075000500c20000007640c204500802d545910394030304100100716008002205c003d482d443d9203040401001e552503460240001e1294880340b00703400c50740b900540140280e101c5542040081c8244440032241c2451011420f4064542865040764091014450001042c02c00004901d140c9000348058821009140140046 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 137401465 1250 137400215 137400217
    0x60b0f01230915070318030809010507050f06010801090c0806090607030b03010207020306160905060304080409090c150509151204020111010603020616050c0a1d0601030605060706090506010911 85
    0x1516048015400c03944000c00c00d6070540c010356624035000f01c01d400b1507200c01c02c0000c0c020003103688a911005074850904903014040200390100400b484010480c1d20015070048025000052180c811544a411881c8040d81480000e1307004a03071681d15509901e0412003880c4260740544900d00062403186441c0b2600b950360358001d00075109042d5075450a00301601c00f0340459078450f801030b0482c1c5503030508000c96002c0d04c000002020002d40c00c14804900780c94960200c80c091030300104101c1c14076060904c0000240720091080785d8660076a00700203060808044001c420411a49511b504e980501d01804240395044800a000000411886000301d452410484d00150203203860742200d00c60303e03065401030841da00003a500910101e0b0024501801e505201d000d94804e03410b44440325610428803000714461300903444d4120649401800890904103103541c0101b0524000c41c8681e5a480407a44e2540606030a850090300c07042040c06021040104600411101900b002010006000c2001e5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 137402715 1250 137401465 137401487
    0x409060f0507360b03070807080c04050303120c0403120201020702010e0a030b18030c03041202030d0809070911071406070306080601050d0803091203011205010b060f0904091518060b0f01 82
    0x100c0f10310b145a041031820000701400c094000c1c04030fa160380e810030a40191500d0341c22254400002d50310700006c0e9000b1001c0040e9800c41c3e0000e4000c5007815581440300b0f0300003a00030b002e1003003901c0500000001ca0101e040488010056400069403020140001816106442e42d03040c011180d0040400003d00d001c10132a0340310202e0022143c802d003040840c94114842c0c41c00302d60031417201080c0802c040982e0000203510751300c03c07012200045014001074400000031201070482d0313080101e0070043d21105400243ca21640c5a100301e19083c40340c0d58080350500b20f802c03492603690009041240c40ca07054401c031006011504014007080d89040000b40f0a01c9025078010001c007030220100c0d03d000402c200703000990402e180c82c2a100d61f11003101c450000308860040c0d540f9801c0c80c0301c501042c106801100c000303200c1180000d14280404041c440030380f8405504981c040020110342100b811306208000741041c1c059007440244440d03042507002c3e1041c440c03442c0e1149102c10313400111303680c2000c55584 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 137403965 1250 137402715 137402777
    0x30f17033303030301060e01111204061d03030301060f080f010803180402040806090f0d0e030712020f03150108070b0f03060f1c1b08010e0705041a0409060f0507 71
    0x1500c05024010400c106548481c616003510001c0008034009410001f4111184002e988040066068050043d07855001540d1101134420800041c00764134825040c07841c0317940782c14031a0000c1500043c08a459076009034010310004400d210f400e018183d10051880d048800301400d0304e00e83d414600f5064507403003001c801940341c0d28040309011091b25a034060360001d040c4481554240c0c13400c05c1d085038540c0b004c560221054043c111b62460041d01415405e99520300c054014400c40d41010103070390302078503003940a9a00c844490208107003940d00f08085400b2184603180481254504441c0d00c0c0340c49459008180510030901c0712019412029003600d9100404681d003114006004002c640401103640245000720366000440052000302c0c08641c0310441e106010f031410b166903102c62803c035808400c0f2100301c1d8200240420051400341c00c01c2d010107074102c00301085040c81e40006021144080011201d1076180c041c05082c2440601c240d503400405400d1148070002000c0f07010011100024040c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 137405215 1250 137403965 137404021
    0x10c1103130e0a0b031c1107060e01080711160906140105030a05130503070f0b0604060b09010c03020705030304180c170f0702010207060504061407050408280c030f1703 74
    0x66809850780c1c0003198509005070540311601400748461b40c90130111a541c80c01f0841744900c1c2c4142d00400a103c108442407503444041500e40c1034011140c0c1e0b0806800b110402c540e140b100283e0110901c56014601c24039040d00d80d00b03a192000b140103230b4409900518541c607400014510f40d07600041260380c0900d4081c8006107507514004941480ea0501c04060100c1c44040350107420481d820403d010300502407145c880040d03994004100039620385008035207a07440c0502901045502403868210301038030a005440ea45078480000c41e1564011364004040380e02000c240103800f101e0340c4200d905040c550700d01040c6510a104840300060390141c00b100000041000103074281e071003913044c0c03012690f00c14018091420642442c60251594110005040102001085100d8010400c4508986c0000043c120603150703001507000d407000c0312000c4100040c40b03d10801c00036500b4a0070001030340c4103035086408440c890a01c031035403260203201030142803410010302c03521411081640421840f003110305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 137406465 1250 137405215 137405221
    0x6060c07060309050a0b0903040303120603030e013209090a0b01081b07050d080402100807080a090501060b030c041503021305040b03031308030901020f010b06070b06031608010c1103130e 82
    0x15914003200400b028010042000a00c4a11f80010000700304890203541c80c200d86400301c50241003100c0481c40000c0c00300f01190aaa205540a42c90120241c051002001d82d0400c0a0454180a40d0015250035507200300080000b02464104041601f040b281c200421010076000c2c006441d041011b441103680115444420704c040e17224100301c403c02540301c02601c02400346e041d00540070542c180d500702c2c400c4580002c00c0595a105103556441148c00c0d540d203003425120b00051400818207104242c030207540700c00c00814000403000c0118016441c4040042d91a0b141c481d601c461041201604010540100691000002d072110081c0c1550703800c9500055607241500064514802d500b5007501c0036045c4e6400154210300030001e003821403001c0c0c095030034841d0704116145c00c861402c260760307520084c203100d40004500c69001c003660251019046500e4078601c11501c140d02c100c107a1000038182c2d101c8000c1c1042c170350301c22126401c82c201c0000079070415a000c840b02000700b40b0ba02034002402194400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 137407715 1250 137406465 137406473
    0xc09060d05070605130e0702070612180510060501021b0105031009051005030d05040303050d020705030c030310030203070e0906041113060602070e06091003030807020102070816020906060c07060309 87
    0x181010254800d007103420103a070ba0040613115810500080038501c0001d58001246511851003912401c4030341e011b44070860900200340c034210b20602903038003402c0d910f03d655900009204002c6c0b04940c0150014584004107079002415607642e80c0041c2d045420401c05010302c1070341804c0c0003008a8090800946035504d02c10340c000400740640c40300c002d007030038241841588030311056944203036031058003a00d01c12910704d40150f038640b007a40710040014004014441040304180d0180080c2489070701505d142c5014151903030310b550010758020400c202d15560400031480c0400c0040c1c01054084010b001c10720340900035070748601c0001c1014140c2d07076900649284a42d10140382ca43c00d4000b0744803c120864850600a58901031402200700a8649a0104107145440808148034290b800014000030741540d8044849110241912040d507400344414000190b10324064400801071400c0100800b40600401240c81400b41c1080d001e120304012a1328841000302c0c1d03541c10ba07091800e02042c442e40d01d00e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 137408965 1250 137407715 137407729
    0x90c0c15041a0415050c030c0f0f0c06040825080901030e0a051903030614060a14130e040b07030c091401090f0801060f08010b1008070509090f070f0305090c0906 71
    0x401d44082c018082c200420092400c902400403006204204195175a2624403070262000781c0700100c0790366042c400744600c20040700c0140b12100e290461242040c90441402e454802c0546c0c04a4862501103248840e9106540000c00309019100300d001420a042d12420080d120358600d050406449403022488002e0030406525025846000c4034100a215008a17050701c00340310b011000a03081c03000020744494045861409107030000d06a6143c82c85014050b10b400a4919840c441c190051000e005e4140c451071128000f0000e00003075296520745882c0060074540014001d205052500e502040d65503444012a0181c844000030218003c04040c01078804241a40c820280d400296502007585003040d0004000c441d00c15440103046a1240a00d80c203a074885001c040d089506001c2d12a03086220b61851074008205040a40c500410000400e040000446040120305e50340c5c0c041c400155130011600304912074519081045080aa20242c0c5581519040ca44600840da0101d103c0342c1e2501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 137410071 1106 137408965 137408993
    0x24090506010210140c03100e16030e01091a0613050c090f03070e0a0c0306090c0305040c05151c0221040c0b04032a05100509090c0c1504 60
    0x152030344020303030001403d801210f5000313880010400340460486024640290743c0035100200d17112701800303940003283c07042e409070302d0b04007007402159414617081e030304405481c0202c0203a210740000501c1c0d44020584001300507d010144181c001c800c4c0018500004161031600300703140040105501d0311014420a403440500e50300003841074450750306c1800b600300c850a00003400d50b1a40110001c450384038040c940429a07640070702c000e00070010340c0080280303402c948c07225819680300b5211920380243c105a024600084461950100c6260180c5521104d2030f2061250004e02c6231003040803081c2920145e6035001291070208400301200c084900380c98200c00d840c5a414011701d10026034101c10001c6a00302d2000e0407000c01d4540e0f521400405505c11a56229120440c0074104640408007600b04106080100003000107800c0104c3d56180c20a600b0040000d00c0d503690078081c1000c0004 = true := by decide +kernel

theorem cover : BRFrame.Cov 137230215 137410071 := by
  have h0 := BRFrame.cov_init 137230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 137230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 137230215 ≤ n) (h2 : n < 137410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
