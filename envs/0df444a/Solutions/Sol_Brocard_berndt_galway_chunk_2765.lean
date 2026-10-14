-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2765
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:40:22.669978+00:00
-- url     : https://prove2.me/submissions/10a02483-23fc-412c-affe-8c5f24c847a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 497122302 ≤ n < 497302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 497123552 1250 497122302 497122309
    0x20409090b130b0105010807020f1002090f03120a1428110619051e160206070c03050712030914060108060106020a0c03150b10170c0319050c0c070f05 66
    0x1680c00144040034010350540d907031030f2140d500c0018480e2604006030b403000030b01d00d40d100313104424100341d02d40140e41e031000385020203102a41218441c4c1d0300c200c0c181010812289000908040088504001d4078184110b07884186d800d840d0015149504501c00c02c01e030625401f0003081b40c10090406405922506d8a081d0010641d002d000d14200196004100703215446520001041440c0f4488101280c01e580750324002140610005100d61810a03690a000e0415601c041c800583c24a0b03034212481d5507207203c0105d030100b041c200302a010510401c140f102082941900095000181c10045100f2460360744012002032442c80c00070700b6070054001849524403d000c880d00400e924402401d401c601d5480701942041079200042401001030716a000c0d81c641c83d040741003d084004c08100f6081000c04010b8a10290700b800d517841d080080c0005502c00441d0b1040e00c0c045c1541105a4421162074441d4030000c24014044803103010091041c1180d040c1c0c20007080c00030708003032005809034901d0441031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 497124802 1250 497123552 497123573
    0x801050a050c1206040f02190c05010f05060d0807030306030c24030509030a0503180601180c0518010f0c02091812090105120c0903030d050105032a04021c02040909 72
    0x1004040071080003407000390100303e42e8880e002101160001a0702c0d20b210845002840b0741c50000320001c0f000d00d030007981320303402200c1d41c909980158001d00c00210348000b4003089603c1118142d502200040e9400041904900074095082c420f00340096210b4983c0c583c588009501d600082c4e01c11019202c00c002200000c80303070109080541014042420480c0b4202e840b8024035190300108240840012011080c8031580d001ca60303041401d681155842d5803030000c041200310b50550303d02e8200031200040714490300c1201c0840c04405d0000d1841c44403000119115a9210001c5007041031124011025070365022080740108692903221500c18040c0c41f01604080d0000300c40c01412405005400d03141c0d81140458100f580111039020181c1c2e90030001410302d0107103088158040c8408a45c034507001807240d0186050b22011011200600392035040c4051404040c46000c80032640120284180c0c107280d005461910300281035042c94008070032890003240c000b54001401d0035100c030405024400784c3d024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 497126052 1250 497124802 497124811
    0x60c13270b1206060d050106090e010203070f0207050102030f070501140a0c020c0427020d08030c0306180601090b0319110a03051806060907032403030e06071713030506010801050a05 80
    0x2105403140c282c2c841100c0e2200002080c0324002d850034102081004400e43c84503002d03200044042120384052402c1c40e00030b4204580040110b8450f111050449000003002411100140c0c000c601c6c1422130a9100519008508119902d40d260001144400004694148544881d141c006403c4100350b4009180c421040c024600492405a030000030a6a4228500e40150000710490f0300710348910100da8086182400039205101c048140700940140304011030052008980c09a10006407001000c00c00406882e00340c08113805c50381c10000c3c800c02c200a55032196005983d90b4900d0303040da4180c41a21242e4401250705040040c90103138142d014869542c004050310043c9014201031b509150343c03800302400940c4104140d10008a440740329070050751072402401050030044018540c148810f10ad40d010440101e541c40d07000f600720b410300f0400c0c2c611807134000d4100280c4c50740307009491031241d0010350841050882c4802c040081681040700c00e00a0407034600024861030700c40c00d5201140c80282 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 497127302 1250 497126052 497126059
    0x606011409010206010317120718051807030f0b03030a02010f05072c131407110d0e0108042a08060109061a03131e0201020c0901030203060c13270b 65
    0x81c1c0e12069900103800c0341500e9000440f041c8104c0311001900041c040c4e51103a0405000b00e40c00c2040e41c80d4400c0c1c0e41849807040380c07400e5000e6600c68003044465040c0d1b42001c40504000e0000490a51094101010781d1034003e00015007042c0000200e419640120101e0001d030f0f450f8007188103205030724410f41c1d82c04541031038407160a05116000e090410b03001342e0118000d042d1003074047c041d42d40350048415449850711040240350240d503416401c00320122001400304d10a4074100340151400300300e841c2000540c0d95983c0c03851011000545100c180500142c50359030758220300340c50b8094103400c0c0055522070804d84203c03071b40c40d0030307444e924002058000c092f0345400c0c80e00070000d0f811849000c0850030341e0071003255200c0d41d4816180da903224040324044d0540e45000116866002010800060f0900030303820740d0704000d04802801540c4200381720082d0940d208100155004075480f014046031242018001d01055980c8001c99821300c04e2080d075101180c601e46160842810380c07051210105064 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 497128552 1250 497127302 497127307
    0x2131b0806040b06030103080a0e0301050a140a0501031115070203011517031e030a0b03101a180a021605030406080105090a05160509030106180b0a050a0f060309080d05040506060114 80
    0x1030f00410103d00042c400100701d00c00110740610aa401075035044003172040940208040d00e0020207000160013100d0790f035005807414034085603c544041c0501410380c0d0b00400890207001c4036000f40140c08a0000c80308401ca40301703100d00300050381e081c0940b10300910f11003c10a441404d126011348261012413594070342d54010026071701c4201040c2d20308440107088000c030703940341c0d60740d41e0740e19010b0710509000980c54020450703034105181280d80100062180300c0540c002608481003804180070303800c29400e03521641c480c00140303049102d030024040001c250b400c1c50388a002d07951f03c3d186190016001440030401800052009052206880380d025900f50000e01c00d0381400c2c0800d00720b40c850f4400c64005c01c400010003a40648003500f01100600781d12607000314141d0f514002000505030507108500c04e0310b42c800c0c0040c2c24075101300c2c80c80695401820300e9645a280c41c2068008000c000320441d00b440c010301c402e40f01c240c0746210703061040740240c015080701d00c0c00c40001445154407618951348008c05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 497129802 1250 497128552 497128571
    0x3200307081504021903140f0120070f020303160b0f0f0408070b061c0b0603070504060503060c03070309120f0f0504060f1107030b0106180b07030c03050702131b080604 74
    0x22075800ba5001601a07a44208850886502080598035904082e0041a000c074103000301000000f4058400a038040007041071081101b81c001c54103880c4440c2112113042481803030041041c1c00e03d02201644024116841c0564510780b03e00000c40061040d10008590000c01102442c07580c0800c3d4404d4444c0801e101c640307420b0750703401d8082c01480c0025000c03880310300c000380321501e0b0362410903802d01c4600c090b040d08500c00e1414541000c000c8503024002d0299180015587c1060301900003950710003800303060140c0c1e805200380016080140500101511000540c0204044104e00001480f0382e6841c010415003544024100490160110040060800080181e42c0d0b01c16074154a007034186c0b61480b0301d0004450341e40e10b400c1e91900098110740c40000002289a00f00c150f0b100001c80b03600080c15825540c020b2001c00f4000d039403010b0041000494100300281c409e50040880910061260482c0c168882c0d1500444545110450f6490120302074001c0d480e4010b4001031780709004990900c0680d24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 497131052 1250 497129802 497129833
    0x8040812030c1602010e0915030715080c031906140108060a23030307080d06030b0106090812030601050c0a030306091d0c0f031c050d1118010e0a0320030708 69
    0x40c0c0c3d60680802903203002030f07a04680c8500c40c042075010009115030807905040d071880148115681501c0e100e4810000009180381000c0d0501c83c100705507881310b192f155950718044003079500c000c2c618111141c1c28000001144007034031030f240107807440799140d154600000002401c0c41c40050f140c24424000c01c0002c10450f814000e8070212440d00107000c03041101903102082c03442c066120000d10790007002c121301482c01907ea1114003143d005c1c6401d00d02c640d0740d42e4019600b0302080c0c02260019040410140400c2a8001c000e680001061404a28040b0310500c120304000c882c0404500081e210751081060b6100c9001e9007501c8200c441c40ca01d182c84402c1c0c107007680d4040d4440c050740601028082d01c503e540d811b00600001c400036460f1090000074075100140664040315101c5c00141c904101848440000001d580c1c1c1003a4686004005483c240010344801c01000f10180d80b2411b0101c1c0800020341245c04513108201080c0d44441d100100010103050000310b4011a20503440b18040050514 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 497132302 1250 497131052 497131057
    0x30412032702040c1808030304170f190903051005070e010918090807050a030302031f030b041401020c0d0909060801052202060909010e0601110d09050108150a0308040812030c 77
    0x907812100028029006613094400e10304000c0750074008540310500042c0810044001c509ca541300d0041440c0311070259003076240354052a200d0222401060100000c61035101f040200203110314288006000e942c1c0d901d00340b500ba0540d60181102c0c2d00e40d0180000d141e00802c40460390102420f000c40c04909001c000c0c0d6107503141e8a0303c4441c80b034a604044003481a40001c541d01160403a0035070300107528900340034010758001c1d1400d50f020003004c280041e00f82c4010107080161703580325648035041d84440d150401c00240407605e200300b95500f008188034100f400c02880e1926005030311f4500091b49072402403021542c080e44919000d904200030442c88110708407603891807622003080706200c1e46890020500034001c940a01d42c101d0020380002c62510240c48103e807249109a980c400c1c1c8507900c100190710b6107011181240460301554040c04a98000c0c1011544100c0c419400c0702e0b005440c60000e104a0b000e40e1043e510610000303030031f1151034070600014468601000300d00e461760411000561036031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 497133552 1250 497132302 497132381
    0x903070302070f3507060f02060109150308030741040e0115090f06030609051305070b0703020c03010c0c020306090d0c08180301050a1a180601030c0c050303041203 72
    0x140c0b15078550b210310000c010802d403030034144042240c0c5d4143c1c503208003810711141d8560020152007000b00024100000c0c1c003c002900411002c0780d20740c00d00e10390310442140c0016120200b03010101800291031104a405803101c019140006a03003030b12020554041415816945400850b042005000f0740034200030460465038150310804c000b00b013441c0700301c9a5107440e1f0082d140c601007041c0005101070b41034003c2d00c162564441d0403c65510b40c0d00c2407a80031100c09000030042c1c0c0100d9000c0005c0810f08001d05400390080c015a000000c0a20020f401c40d10014080c50216074880700c40e034250700b0b0400400ba400075171040203049032109800c01803c111a001c0c4020f040010016160f01c400c0003174041c02c01000300180082c4481c0c100050b185001d804010310840004100c285041124a88559017981200381d4104400c103e855110044019140103803012060041c0400207800007142040250b10441c0071b50300490765800030545c01000d03202500c105000c507000543c1070300009901d41c2602d840d107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 497134802 1250 497133552 497133599
    0xe010905060f07170f06010809030705070e0a0b0a033e0603070309050f010603060b03030f040315061205061012080d0e100914010b04060e040b100e0903070302070f 72
    0x20f580d00441200d800d885507005002c5111058141300429510144050141200740c072000c0d01a526034004554038003403034901030995070000400300705c00c1001e0490250000e480c5103000ca0100402000304250b40e080f94402c031442c5480401100c05072561890f60002d1652070140244000c403200d800c511020081e0f003500303105030310001c0440c0d0050300960000c400c0e6540401035500b041840081c06008000d98441542e41c2420600341141e903180200450303084402c1c0100741d0b0b0500f801c41c5c6840e20001c0c1d14203a03050103183e0b19580400c45c6000240a2a5075078403d500a01c054035114488903401c1c042c030b42c00740d0304038454820020b00140101050b5820a03d038910b00203903100b1801803503840d002c55140007405d030364030380f000000a01a40f150345040b1000c628000307102c5000380d4020b0004843c02c91107182098060003002c1000a0b841020080c1c2002c0c3c80055001c0640e10360a42c080404429203a241b5241d00c0021050700305a014481d8400400b0b02203520501c10b403038401c92005605002c4000d444 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 497136052 1250 497134802 497134831
    0x30301090e160608040510270203011103091e0d080604150f0815090631061121010302030319020f0d03060303090b0913020903030702090a0605040e01090506 69
    0x2822000308a84a40b9290001c103203014036039a850050450041680c1c2a11140074208076801c60b07c1c0c0c28040c8820004600005580468800c51511000070460100b02e07850f5480d00d07030500b44025441c0241d809a4810000b9100400c85503180140c0d1340402c0e92241c905411170b2900403030385600030034070944c0500b05903008034502c20aa403140c41e00001039088080e52030070491001c81c04e0308000411250074000c2c601034090315240c440702e469a9007402c1b038044c0400c1040b10036030643c03031408105000110200c5487ca06145056640e00401d80d0040760192201e00c1010031048840303032002170305003403000c3d11003aa4500c5505640100381c4034441ca1100400308940001a078481c1d510030090b41c0c0c0d162703502d0300540d4440314200d41c00802500041c44180c0c000381c0400c1e404a03881c1000b1045480c00c4400400040c919001d01c40d00c80041d402c9442080da16000500c40100580c880304919880f4003441d1000181d2181070904102c2151b03001c1c0e5650595038501684400041c40004510760010b084c51640d50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 497137302 1250 497136052 497136071
    0x10b01080105092806051314010b1b030d02190e0a031b260105060909030a03111603030f050717010e3106060b0a02030d05060411070c050406050607020303030109 71
    0x4800c0301e8074040e1031482c0b020130701c296440140389a011106031402164000103202d01100c0f613000351a4003004003207000c0010b400412214100360004d0080c40c0180c200c0c00b001e05c0d007041c245420f640091603a100503503000618079010070001000705041010908180700041c1f803500200c1e02c0b000443c00002c4c920700080542c100c4071200b80040100512200c03c0b07140888803203034030411462128015100c510b60130000403440520384840701500c070700c0c0c215004504040351454100c0242940d02c0000080c1c00080080240700501c2403805150180a51004a16912442d10400c1219001040740d81040190301d003421101c802c01d0710f03290440d0071201200302039031610520b2150b40440030041e60404540844080e880309012961944524013030f800810080307698454481d40c2c0d10070714180030f006800130405519071041301e500181d04514040c2c0300191450008405400c0342d03100030403e03240d21a8400c030401081c503041c060040601700c1070324110308203060350340866503030300060003000b41594854600e00c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 497138552 1250 497137302 497137321
    0x6070302040b2d0a0e0f0343030b090f070602030703050c010e071211031c081503070906090605030706090510022401031e080301050418290702010b0108010509 70
    0xd00d0300008a06200303640b00c541c1d04014008004c035485c541c0c01410900d0148505240c041b03440c1022401c41070410220303000c956001c016540811015041c41040445111103020340300400e1005144111113415103418042c48a5107030150b500300c010f1ba151b01549040c02aa98040251407034a603250400326111024102060301400300520344a0485c81207480004a405c402d50043c44040d0083c541c800d0080f01e40800d241d00c0301e08070b20340e104036410303031180b00600c50344100c0c25142d002c0c0c1c0301443d10f24800d101340002424442654000d01000b62244030520027100d0380d1156000901e01240105002450a04060306e68441d500c01d21303128400c240400294207000b40494908001c050a0703070f0b00d2000401401c800da8243c00c0c001568251881400201c410100507481c8106680064035941560710b018204006400c81c001490304040c82d519418000510f540205944822686035030b005259280e0b2b540716a55400a00103011a030500080490780d0340c0048141e419030b18280c1d1601242e0b5104400d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 497139802 1250 497138552 497138617
    0x7090b03101a061605060c04050111070302030303060d0807140d03060501110a020d0515040c0303270306020a0302400308030412090312020a11150d051e0a0b0306070302040b 76
    0x10348580151b20070008854000c0380100140c0383c003602d880140082d1307856101e80d21004d0b804001e400d903008102044684c9000b203081011140300c0c030740c0b2070b00d013071031a0360781c080c130340c00d40d00c0701000c265004513416003402e078040c0200c0001e03003820319103000d0a001c00c03a0713840e0b901c0b0005400603003d10250803990781482000e1099485400310200240706505007031400c0e5154a507184010703800100801c1882c20030801060341140340f5141e03903590103200ba08580768030b002948401c0750002455400c2102044100221660700c44546d0114070030040b02c1000c600720714040700070700400c240c070305080c1000384005054202903d0300300d40c0000ca90440c281c1d4062055400207155040039000a86603121119026800120000c0e1188960300101d2044011814040d24007160b4600d030403000010f0107141103a540f030758071441c1e1001e646d144051440d0580b082c2e480e0440010b44030150301d181c4407080d110081c101000750607001109450704502e01454036000034200e00445580c5600c082000300e08100400f5030510 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 497141052 1250 497139802 497139847
    0x705070305070f0302090a110a0e0a1a120a140711120403080a09090c0203040306110909090604050105010608060a060c02010e030304091409030a02060f040c030507090b03101a06 78
    0x44842c802e85408160328071100ea0320007280308015007400107441950501506102c404184001814090340c00c0d0255500302d104a5402d4104800c04800a0040c00c003554402136840072413034075961b41d0f84540c2c194400007801040c102c40c4e10b0500c850b5004050000400c136038010b0b6146005036003003e080c49101d040c4a40000490b182d4040442c021041c800c1d884001c180c0e0042c203449003000b403981c9031071560039600f40c1070300240580c00a11042002c00c0894008031800c14950100d07a190842d0000004c443c41802c0d103000c12250300ca01304220810800341f041c1405000981042c9525241541c0010000b01243c0914410440780480c10f10031a4000c154056001d90010b05407501c540d140c5507000004c1c000d00040e401e4144809010540003040803040b54000842030740545200d80c0e4a40b002800040050011900441c002000001003803042c010040501516800400c41c4051030040500c1c005c04014800c0803985451040801c0c0e5100503028400401c2c00c1d9100c1362110356814409090000002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 497142302 1250 497141052 497141063
    0x1020705121308100f0518100c05251208151309150c0201110c10020c0f01020f0706390c080408070602160b03150f0d0b0601081f090207050703 63
    0xd080004a2855000060303105c035002800c000c0c664034010000410601c6142d000d41d140c0007002e04072041242900500d0200082d070400919008111080111081e412241c280100c40303072051180c10020061189400c2c40d0343d07807810028070700b8855034103401800b990b9540d5101d1141070a650903e40c0032a00304424079600884014001c2c4840d50204e0050b05c0d41c00d84400c0154a4101121841d4960300306480b01c2160701c0d03008000c4240f440031344c0301c02548000501d440034403603030060a0b0105004d00081015540e10000c25888521610300042a00c0c010340f4200407100a80d03040c2e031410880d14289079529082c014a6080444500b0b405542d0569041c50140c68a040014003003541e910002d03c480446006508031483c00d4022403482003c15000d01400504413002c0021412500112003240010b580007051890580e0b050000168009440101100c1515420042000e10341c0c000740c010750301440d2020018660840404c1a041130501401303240d110660120b1000f05100082140801442d4001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 497143552 1250 497142302 497142313
    0x3040f18060b0a03140c0a050910030e0a0609060605010f02031e0f0c0318090603190c0504020301081c09060c151b09031110080f06040f021b010e01020705121308 71
    0x194802000341c185ca9004135041c00102c0c01140100506d00212501445140d07981030510381c0a030108844054504000c9082603143d04120a0850051120303e501e28482d180c0022846664139180082e903c03180d0106040c01180b00c2c0e00350320305402100303d400548412030041d055014410358039110303003e5a8844000f80c600414a22040e200000081054005036010380030301200e02c804210f8840d0040b00c02c65010340240340b1448180480da5066070b201489103003829244d0ba00d40d000303c4d00b2030f0002d0340446020340c400201ca00041c0d030850700307510700e9203103e142980c80c1303905000c0060b0080c1d515160082240328104e00803550000103a11000e00008012200300705a00c030480001c050070b46900040e02d180d01501800406031415800911600145031921000c1d60b40c5c20f600c45110b420300411054002d500d50000103203a040302d20060040e94440103001c00222850340340c00782103a10b0007002010680c410410880415000120144420920010140e0b20064041d40034a0042c0c10713070101c020361045 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 497144802 1250 497143552 497143567
    0x4090c27180302060a06140d051c0305060f0d0201141e1305191401050a0c0b01090e370804030b070e090609060901090e0c09090304060801060203040f18060b 69
    0x11249200c80071070007a42281c20507140c6083d03100403a404c0e031062440c94000640b4191090602e44000a0344500800540700300c244440e1310044245220700010300001d980c1d00c10000f0900d00880010900101600c0d002e8031031450781d0000c0d00312408904000c44a01e40410012207403004200c3d424807580b10410b010340c842200c3d605d0008202281e0246520640c282c02032941c1006006c0061000c440040141034604601c103001510903070320400441e010044940e0303050022410804009001b002040c000082d441d00e072008150420200e070140b1610480c1c13003104c1c000e80407202c2d072410522410f821041030403c0000d18000b00360307100d2540b0083c400d105035410880119040340006681c2c6100396440c0c0107603030300c510802412030400c503601540480e44900501c003040c01d0341d0148aa1a103490300721200c0c81c04610028541081c11a50b0706400d5100080c01d10066500002c55030062109000850605091130700301200b4040c1802150703030248009450980b80b80e5282c0080c00200118a050360390380c0725 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 497146052 1250 497144802 497144831
    0xa080c010c0306050607080d090f020d12020d021204090c02071d0a0506060a2115180e060112080307051c05091204081002030c0d061701050604090c27 66
    0x4088440d8002c070380b601c000051030b400c02404480003c2d6001d801c0382c2c509050060a00700a0a6540d029164105170340102c01c01a01d8480d112300c50140224560919800717191390007440c20842c15115021500100201d210203440d55080d01e055910710813021803002a107820807454500c0b9a0f001311000d40352170507a1350280704564429806000000b000784010b603a10300130f000140c819115400e0011340c0301c488400180694400c0c0d04451200d240c40854203641d061180004c2440c00e40100c00000e51440956820596610070540da501040018148030f41c0744c042214800402d00d400900803010020005000318440c03c2262240c20003041c015440900300c00b1400c00912040b50039030307440c0c841e50071002c400201c0701c410782e07040310740745001803141c10188280c50001c1d402c081c102e004420418000803040d22a2409103001800c20060820104200110110b09441000d0b0940340902c2ca020104008501072a400c07406440d40741c1d112448c403101402840382d00d1042c0145070704c0303490325218a1204405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 497147302 1250 497146052 497146061
    0xb0d05030a0801060f0c0b010e0714040618090e120708090a0e04030e090f07120209100507020117011202150c0f070f0b090a0302010e060c0105070305010306111c0e0a080c01 76
    0x313a040ea218403908880b140c0c15143c3c040c0e803030310140070080020010403000c003032000ca03581e1100e2246000c4d036541c8003041e440380c6250016088000458626091105000d0b5a12740701401000440010b00500039501501901d8840d40c51461078144000500300050144910460307001c102c002e0b00400d000c644d1103120303801c9014141c800b00c0028400320704281d800e180110101d40507031410038500809881e03c24056981385c03032200080303603125028416a0482e60703600800030384220a64031595600c03c0e2030f100040c408540c0310420301035041160f00500548a251003100740855041d12a0f008003566030202c9041c40c040c0b024030885510a0802c03402e07822102041c0f80c01180d00c0320404020254492207445000d0081425a50300501c41c0340741000550301c0303954012780003140038000b240750003404502c05013907900032501040407030b0321500100100030261240d0828994611000e0b4280701e1070040801c1700d800b0b0042101880350f01c80d103801302003042c14002e4514081c2d00c4201c599944246101990107003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 497148552 1250 497147302 497147309
    0xb2d0901030b031c0806010e040204090f05090304030c030609080904090c06140901231b0d0909110d0b0319061b09060206040b1b0d09061a130b0d05030a0801 69
    0x90404116500c2814001046503408104d20b0021a40c000c16800445580c040141603034100f140c080c1c490720658480784000d0000e0091880c02040c0680aa0946800d41d42c01130701c03e8940d0340c0300300010004a42100400b03001e0b01c0d44000f0100745d010880c184015103005881086500c030b80303808049003c00c0310303007840700c005c44050f5100c00004c21420504280b8a000304442a80410918228103884121065103075680e165a400300c0c905042d104400049040412115800c2c89e0344a40268001c0d960003274002d5000340703200c4005000740046c00241c0e83c564041c07100c2c02020141c0f5140d0440080d0340a005003560828000300400315042c807420000041c2c40000044d100700c00106c0f1040032118800c050060a4500710f400510003900c1e40c2d519407002140c018041070f101c0003074290a90b85a001007004007003800c01000c001c00c542445042c02c004480f50310407070a54445d1814081245c5450f102407241c0270002801d00002d1508890020801003100340d00001e040f0b0000240c68101542c1124640b8180c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 497149802 1250 497148552 497148557
    0x303030c02030f04121205040b0a03051905040507030c050415120507030b0c1803030909010b0d0209031b130e0c010c020a050603040308010e0f0702122b06170307020a0b2d0901 77
    0x509006d00c0c05942c13620460050286464040106602c114002c1c2c0200350000520582c80410300c0042e039240c030440b10300340c504807120f40000708100241f0201070b20310300103420101c4003082070708810614403800c1a454070a00022400d145070b11024820b081c0030400c003e5800802036103151501c2d000540182c2e20884404c40f00b48070f034614246180c1000016030b8058880600b580405074208120032100d604000c0803410610340130407044800352400e11004040b07880c2c8000d6032540200e01010031002800512030908a10314181e00803d04110001e52a44007407000c0c28005103084103800030030303e50551500101e0b0000d500205010070154440b5010b812150520011401615903156150040900307035100f8005070300c413412240d040c801000c02401400f140040302040c14010010b9024421035200c0c0340f00740c0e1031340c0b444100200c41500411810007140d4101540c94200c065002404d04846806540c440b510007007a648000a01940c400d146480c02803031000c0c0c1d010344003550444075031203403107550300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 497151052 1250 497149802 497149823
    0x30507020f0a03110d360b0a020309100e09060609370b0f2b05090a15060b1209010e06190f0501061d0f0d05151008070303030c02030f0412 61
    0x140c079442001103401e0020301e034103801c80e10341c81480c6c010540440c82c1400450402c444000040c0660080018081459141c01441d2148180810001b50368001d20901003800a00300242c58659603407480c06a22403021a16981ca58811a01045c0303514084401c10352000540c0000c0e0180403120fa02602500107003818480030182c46d01050030107801110400350030703003a050101e101130255203001400141910b24040c140c1c49170f0f011091062b528103449404064000c09032010900500b20300058003450141024041d035807400142010f9071160ba04000c0c4101039440100344181801e401007905071260790102d071110304141407144440c11010109905841ca80359030040311001c68018541291116243e140e1540034030038028600002d0302c01c85030740c41101842c80f080c81e5690012420103941c080c1d40108540e40f60981c0ea2003030100081c2c1460401100400b080001100001d044421b89506140100300d01001d840c050740746000d048820b03900d00701c0c0424081014400016030b0414a03016104205 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 497152302 1250 497151052 497151073
    0x60e0c0c0c0d150906051b04151101090b04060203100519140d061b020d02120403060c2106140301090503070311012a020c300a06060b040e01080c030d030507020f0a0311 74
    0x1401c912592080b00c035030030307419074050527480d000e114001e040640400011594840c10381c1c0b0710b450004c0840e8202d032581c0e4040244060020690b02240280001303940c0d4003001002c410003c0800c1f5014800e0800d502c0c8074030210140c030307200c8200c11440e03658055428041c049520040c04414028125140010300c5000d0390030f10320510001d03000c590480381c4c8690340e20341411511182c0141240c01542c8040c000e05008000c428032441a1004030007000c0c90002030200d050100c0c83c03010052140c107051080e070600c200d0001081001c8201c41d021603050619100c0d02d01002c0c41c2da40506014101c14096421040e450351030f00094081921711800550b09503100420b44d03100700000a080c0305c048003104a600d150065603040800c83c3c410f00054004100c88118105030340315001c1d109140c101283c000e00124040100d0002034003081d02400c9003002914041c107000c004651b03a14080d4078440200340d195004204000d000303014001b61740210700241c80520300c036070402070a24554414444080e01ca03105540 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 497153552 1250 497152302 497152351
    0x6060314030a0f0e010c0212162303060910092306060a050915060d06050603130302010501080d2a0506090114090f060c0901021f060e0c0c0c0d15090605 67
    0x13110310205850740090754080d030f000d100085440010024552160040041107407040030a03c0b00140801c000300640803201e00d80001000701d400381e03542e00a50060302845456035001c034441c40350008010340041c0002c240d00300361038502c2d180b900c0016101f80c5002130300031058001c40d18500c900c00555094405507501e4050001c24031040314501c8070b060700c25591880610f0404018007a442200301c002c02d001352120001a490f1b8800d0b280310340e4402030000c560081540a019450040065101a00c03a4480d1400302800c1c5012841d090060307020112a04614140d51844d081546504102102c40034604041824020040380c0041d9400035140000506000800100b001c100e4110001500160301c40000c220155002198541e06500a80c5550300030020480c0e405181c0000d00c4102003a2107180550003d81100082c1040c10400010844904001000540031240c504140c1d0002c1e00f20101e401d1030049040c0e000e00d0071003410300b042201020b10200ea00054020310141000600e094880c4518 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 497154802 1250 497153552 497153567
    0x80a0f081006020a06050603010f060b040306050106090b0a050a030908030c13080c030a022b0b1e0709030206070609060f09050f03090f121c0807030e01111606060314030a0f 76
    0x202e0005a1090041400203070885e0481608040043c0010500c0b02e001c21852058032007907000301c07454110100302041031091901645004003220309100c41c410f428101024a18440c100c40d1270148000001c05143c0c180c400d1340410502500b00300c01e9038507400c040e080d402043e84850350040558040d2030300403030841008036154040307140c010018100031865509128005118003120a500d10294580c0141420f41007142c0720b9161040900009600c0e0103494807004450140c078002d107500400c0308000020f038000910000341c07901120456104c1c0c3c4c0e41d103050b402a00f4848002000541008992074a07640a5005144480c1c840c00580700007101410409949006203124260b02c1100391007484244d00302001c0d00782149150354203031614680c0d07140e91040100020002103002078000000c01010341e40c144203414003552000000d00c4090380940f40d20400c0d005003682540c2e6101e009948000b040300c07552200c40199402560002c41d080002d1079903840c1d80048400300e000c45c001c1c800398120148581d40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 497156052 1250 497154802 497154809
    0x115060f0c060b0a09051e060d02210d030c020f0c09060d0503070f0c061e0c060b060c07030b04060b01081e041e051f060803030f0c0403080a0f0810 65
    0x4461030a00000c00d000c48410982400560b02299140a00da00e99258a8162005010b00190215640c10004800b09520031400e02ca00301002c500014800341c3d40c0c80c40301440200303804a40003001c2900f100704c440b0840000d0b181001e0f2501c50300207003c400b1a019040451090441e03003d581c1201890b6401e03070f84500c00c050156030f201d00540c1c0050001d15001001c021824001c2c02200d040249039a582c1103c52107800301901c00c01c0303062204100c0e540d40f104840703044a4041e4282081c42400e4840544071500c0d07200010700c0e0585515610095858840584200703d017070108a400b00c9075a0305041d4180b2070140c0c1c055810909003203004206501607441c25000c0c0002c1c0d4a0192981303042a6443c506400c0030b00201c50011401d01c9581d03480c00b00100c41004e0f45d0088001e4004100f010a01102c16104038080c0384106003040800c01485a0100c00d4951021013030103181310340d94504840f06520721607504018035108000c601541455444503940c8280d1186440f41c64454441c050359005400540c030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 497157302 1250 497156052 497156057
    0x20309030c04090302010603051b15070b06120c10050c16060504030605070e0618010909051306090206040909120e1503150a0509011205010f0c0f0c15020d050405011506 74
    0x1401d9400e604080d0300400c900b6000f440000b130525101d940e200e0420000300c426a4083d00c2150315a904c5260000440912031212510349281c02600e9403407001201e4000c201c140702d4045800210152003041c00340c1c1c60804001050000c10283c0104081c0807a00442e0480015220b0301a84070318503940c2c40e0103a01503802c561500790819207180c0d15400a08001404602003195101050311551640c0c80501164007200c1d00305000448813400040800f00c0c41c0d804550810f04000900040c2c0c0040c036101e0103003903003080300800c20600c14000f14101b40704a9121924603881c0c544903c2c1030206140c2c4c855502c40c5c5030741d00c401c004c0b5066404c11000c0021511042141281000070400800300403950510061018080703c001680e034500213843d02109034441c3d106c5030344c0102c09004104007031050044003a1040d004101c0303045402e0303000f0300020b03420101000344010070300d02c10240f020790100091410340a040956440310031a0150010708010368045032a907080004544622602d2075181040c0e0313135140e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 497158552 1250 497157302 497157313
    0x9070507051e0319050f03070509030c0d020a091a0603070207150804080a030b01110d08072d2003040909030e0306241c0b040c050d08030f040c081e060702030903 71
    0x41100d400284e040700c0e1340e02d00b40b010800103a40300ca40264040c5109040540314a6113a610000a0500b89210484c084d48a02d450b1034807840180c1c1c50a100300180c8103807050004241205001408940d5200300380300d580807030b001c0104084994001a0038096508003c140c076040c9222103805e0b91080e0007500c00504004060240c60105882035001e0400080f0501d0250100c010514400d0305189a500030040010340c203004011a054010304140300144142a001080c070b42c7c02d40e00e04000c01d0300e1445280c00c0001118824001541202100d8281c10301042500c0d92182c1d1807100d10002c001006080b00400d403107420400d0341707160100d211481006214800e0400c1c00705414060f4210301ca240d1680d0b8004101c0c000d013075254040a144482d924891440705c0c00a0619080500c0300d490f0a0380514480e00103182c1500000e00d11b5000d4a420030440030490340152541e280600713440b03240d80c1003078419100d0001500500216460f07040100f44149040d0b038065112400c0403622071040d0454150140d100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 497159802 1250 497158552 497158567
    0x4050705010f0c060b1c031806050703090509060a170705010813050c01030506010203130b031902041d13080c0114060306010f0e06030319050408010c080402010e0108060d0209070507051e03 83
    0x80e4125442c5d422004021090050f0103010000d810224803105a00003a4586450074031a0003e507100000780c0142c0c03d1450808120b6a8000c01000c82806900d0090707005101142d060346410741d840c00a09012956694110701c044409503a0b07440e030703118650003c1c1e04180070801c0030000000b41c01c0f03202d8000c0301400242c00005d0055000e401e020f00100e0452004101000280d191420200042d10103001a10ba4a00f8610302c0c2c5c2512184000c448036500e8410030003048442c3c0c47c0213010824401030b0102808507a13950004d05c455044181003d00b4903000001c81e40003500341980b01c100c0c5e00ca0a400d81340c8403034035a4401c3c503980d90350074010485d035004030400511400c0c00e000c85040d44003100400701c0b0700e4481040282c0f0202c14407480f000c8080360000c030741840328403130a00800350110308602c0c20801c146420f40000b0041c142d0031058905000d4403c0c0800d100d61038072040790039075079000780800d2041c0c181920020040e42c4502005d0302d0302c0c010b03840381c00f40710f4810100b4030003004c60060055040204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 497161052 1250 497159802 497159813
    0x903010e0d03063f02060a09170c09041205090a030b0a141b09030f10051b0c071404020d090302070617100302041e0912120c020709020c030408070e04050705010f0c 72
    0x10807084c118204e00b401c4400700016514100207200c0d8072815900d004020b460003c122601600b0245000025000400c0108960701c074800795990154000340070804404200000762400d110328081c054100200c0e203400b00a1003940f81840c1c0c00307041c0c241000c1100348101e510340117000c1c2c000d40b0007500944c170400c4035040702100100a80b1054000030150703001c0d508494200c80c1760040d404286624180c40c0c00c1000303401c030702800a0031060942c07035800c1480c1c9440b00d040b003074a815043c011101031405914104c80b47d51102d038180d4540504007041004a202e56040196844c02c0750700c00c0000080d40040604070801640d03501c6030040307200140349403500703045608210152080c80072485205a182c4080001c03841c560096082d458003404094014651418000380071040c600800b514041c00c0070840c0c00004d40c0000c2c2c0e1011645404801a03c403541c640007142035119075400303801144a2144c000c9903800c3c000c0d007814040e0344654125100302e9552401521800d0303100390318501103045220010302107a03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 497162302 1250 497161052 497161139
    0x30a0201050d060b0301080721030507030315030b1e0105030a1a040204020f0304080d0b04020a1704060615050405101107060e03100204031a0a0e10110903010e0d0306 73
    0x35070b2000d011500540b00c6808100e260026404501c099018210401c45200070822400184040f12091305080c429620080c1c0741d0310071304600074105591060803060f08035014003084003455101c01e41000b0b6090440410344165050015440100e2198000141078640020300301070f01503000035030314421000201401203c120040c01a60420b408001099898107110003d43c4201d10448160761218509400e40e4201c0b42c4280c40d407130041d8410003503003420320307080cd448440c211060308134856580d442d40750201c0902455400001d4250a41c44030200242d00070000d44290383d0f06407103084080302d8040041321380c216400c40402898110305814003030180b103441040300c2e903c006002c5645002d142c0340c0c800100e81c402d0380142d0b01d0300c20407003c2040400b06544a1904005421410321000e590404a151a01c0300520080749550751850b001d00c09001c2d51080e1400001c000f402085146c880300182c58640040051034400607292150200d4081c14080c03e5852544202250b00c0c00e0040b404d000e6039948 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 497163552 1250 497162302 497162317
    0x10503070f0b0309072103080109112703030a0309210e06070305090607081206090906060f0f04051810290613060306050307090513030503040f05100204140d02030a020105 75
    0x501903188040703017008405030403000c06d601e089502c01c40300c0c0e00c9040c01040443d060b00a00700359810022008402107a030401e032046201c100c8001c0208500c060a03c01c1c410684e40d010942600010520500b000d406a0100103214010560240042d0615251030ba501021081e250042079090785005c50900f08540034260030b91080c201a403804444a00041107a0009e000c1210940d07030000e500c800000700b60707000640202040d00e01c1540c1d8106200740545600300140601e0048507004000001135841c44403240d40030b000a00208018201442c400d110359840c03e051042c0d42c8205006041091060311982d014201000c684848501891308403641450b07900786055801f130818441c0204644899540c41d00800d2148c0f40005c44a2500341031601780b805070b60081c400d19281c48100100c00c502410701e04075147c5d25240660707507540c0d640381c00710481c0546400a4081d100380440c070001141c0c1d681c010825105518400a0a240c044080007080c440740c1034000d4141d040354451200650041c000b07003984 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 497164802 1250 497163552 497163571
    0x40b04061503051213090b090c37020c0621060a08013308061302030a080c1f0603050d030c020705030a060f05010504110304080904020702041a09010503070f0b03 71
    0x100b42d480d12002e1034134090071040c40144000003100c40c11200c1c0d8943c040c00030280c89006000c112014000114000401070609084200010f00f0b0401d1468201c903140111400b090108140a614000c0903040b00c0b414040202602c1348454240071450b003070041e030b10480c484615003986243c50009100c00d02402510342e903042540c001000c1440c20081c000d401c800c030500c0b044601009000301c2e00c13003281075102d80020804e04c40400140300880b000725486500150f11940d400c0810b80704d01c0817030f240911003100034003c1d120100c2d00d54419080415481c1d0b01c10080c44903484403030000000101282c016200042c4107520011100044a01170342007102c50150500642e40d4165072100420304058104404546650340c41c0b070444105002c2c3d00c5072a0240805543c2040f440c0c42992200d01d8610010f8070150030f03010003180381001603646030100c5880f664013074001d01c03070603101603820041d1845c484000342c0700e195003074008145410002041c8046400b4960b207904801e15002908e6240c0d80050188180c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 497166052 1250 497164802 497164841
    0x20303090a060c1704080705040b061b03070606090b010f120f0e03071a15011103040812030901050721020702010306030212160905070c080a0c0f0602090f030105040b0406 75
    0x25039107401c210002000b4a840796500040c2614101307646400501d50154454824032050002801c00107911080e00e6096a001500c1c1c80d0708000030b6940e01580c0341d645080d6109400c600454039021001c2c00241d4410881401442e80ba5860300c01580c04440100d4002401c1000d0b20f41294854088261100303940c020018080c03102c15050700035104580f0790121b4aa01c002020001c0207094513101403026088110300185007072030300026101d600300e84009810400104041c1c1a0003400b07008450082004e101110b4034a80c0e81045101c40740c00864504030f1a51030030000403507585c091100143c0c820040703030307000c400559480207440082d00000000c0e41015980c080c04401a1219820050214400401011010310561140704500c0700d41c2c004c1c2d55418201803d005810340c00010100001d944110300070b4903081211421151640061000340201507402c450105000c55980140482c440a44403403112000e000181800e0303a105441c010000d000c0c02e00014041090743d404002201503100306400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 497167302 1250 497166052 497166067
    0x1518090606130f051315030f05120a0f0f05030f06061b070b030a0c1d103506031b0907052a1c050726040306091209080712020303 57
    0x410b11001070b000300421000240c0184418a040090078008810484090040c2c00501000c0040c5030308031320004081c400c240101004024042c09100b080c117100504040d00c401081000501402d10020036401080402160f003100d507209908507442a81d140509441540340c403014064543d02100310302c002c801e0416850349102e01d06202d00001000804059902c90501c104614100c0d41040c0b860320a00100c01480c0c0d10031b03401d81072203050381181258010005010f4503c165480f000103150a80c9800d214142d00882202198803004100080c1c900481d00341d40d40030915994003404040080d26044c03070007142d080d0f0310300440262f60100d1240b60107401c00d556005c600400440c020480001c0054a400e4500d01300d50400c050141441e0316400840400201c003805002442040c1d0013038900c2c42003c011000c207040c200032005011807030624459942d50b4a0a02c0c400920701a1403c07101950f4000c50b14072103034407426030340341a102c2840117071544030318181216510742c5608001301d805000600042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 497168552 1250 497167302 497167327
    0xb0a030501020304021c0c09020d1503030203030a0e0f190804030b011805060301020906180315130b0109020301150f0e060d02190f02070611070801090309051518090606 74
    0x1005521a1002503224200782c410046103411650031440030035510105c0030040340030408605e0071945650b00060340d03034000f1580e000152101d00301d40c0802400a040010415a000004510440f01e90b1000c0060140517503505031210b169541c0042290b02ca08003110300c2e14660341d00c8031010740c03090680b6480c0c103640c0e43d00d0000d2810264030486900c814014080c3c4040c1c500c0c056543c2c09032046008618004000000440324045d4410b4584030310800e0703143d580541ca04018103045040d00d11150943c61400c10240051290310250468403000210700009520303106000b641c0c142c1d03154151804484050345000c03250300e104102940100210342d010380116454110081c000280180d001507030301c02140c0e100160f010390382c50701c4500b0440c07083c08181c1d18660214480c03040c1c80d030341d144c00041c100b00041514503100386900400c00395441c000d0010209900100501c04486080e11811070b045400540c2c030751140504003042000ca45801c2c00b00e0394501d00041156031000d00107203160b0a108080703104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 497169802 1250 497168552 497168569
    0x1110020a12080601090e010e040f0f0609050c10080103020a0512150903071707031202030a0f1b020601060f02061b0c0102160519080706020307050721081806190b 71
    0x40741c0101d0303214414080c0e19640964502e01030308204c00b040070503501d419175600c0900001000030b4006d8500003410000c0020010112191781d03008841445181210b041143d10741100d408144e00c10303401c10303480d0a000342c002c7c4412130403a50000c0a20310301901d0a014454104000300c2c440c9a43d0198060b0702c0305d089081303070855019510706001545c0f075240910703004602524ad08810744900c54240120f2000a40c40411040c400f640c40c040580c40e03440b03104c6498040c11084060500e9076003002d0000601c082d1292600f9a281d80359405c07522180d0340c409040d40d021003140c0403080180c2080000030b02c2c0704c2200490340d049060500c6403614008a22180b40e08a801a160f980b9000c5420394032201030080422400c1910a00454082c505046580e41e0080f01d200b00e4030000c01d800c0d0080000740000f0700410543c1e51090704000c01c0d802e581c04840000e201e41800c20601c501260800300492004810640c4651006503148002c0c909505e40d51008050b20300c4419a00d91099140c5008185544415a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 497171052 1250 497169802 497169833
    0x80a1707020330040e0612101a10030b090c0711060307030e10050702031c02090603040803010e09010b010e01031508010e0106090b0d030c03050d0f06030b040506131110020a 76
    0x800e9444103401c80f2009191100340400010002d02800140849030854480c6608004100d40e01400b0100240d90300e41031250341300e41d04c1c140a140c032440c40c00b007200c030314044400008122010510f814201c0015011904203501c40b84c2c000446500268850500d54002c1450320700815034800703500b11240019185504c2220700000003038585204021502e000c10984500c40b00320300c024070a0789400c8800940d6402403c00c1001d42c450a0641c0611034801a41180d550b00703409080c0554074031b014208042164800c1c410703d05043e6401d000214480b0341071169080508050703464000310740c2030f0b400450241070060881c5d141c880704100d0000701914248a0f03224401812000030980701d00c0c0c00c0b107290440d540010381c14041e84118002c0000680d201080784041c0340e06040c441d803607180841000c2c0007000d091180281080c6041c10210501c8030100d01c1d94819803103a0202c5015503561000c4214065450000a00004588a0b440414584407442d4101034074240304035010120561206a5086c40042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 497172302 1250 497171052 497171083
    0x412020f041422150b01080702150610030e030708070b010f031511090414070e06120a1512110a240806040209030102030109200403030e011202070203010f0606030b0a080a17070203 79
    0x200c56805d41d5811003601030340300a1500281215094591b50140402c034000c00d0544101d0313010f0000c0c8a124001c0e4010a540740c0c0140803a601c44180b0300e04400b2961040100741d403001d0003080001460780505410809403580b0851811455403c01004c0025081034408540885c0060041402c40d80341d40c8241c5040f0f01890404e40d0039030038140001b4210652415030305001c1c1e0010404d04454254245e038041c0c001d1310010001032013207105800e034025030145800180c158280c044051062044503458940410b030121221650b80780d6854080050400b01054051114801e0f18044007880c003a2030000d40c0300a0141000d031900d108100024220383c000d800c0b680901c1e41c7c4891440f105c070180b00c8001e09001c92036818910b42411510080c1108031940501d40c1000346041c01d410b030703070081501039035010380c1c2c0070340240325034000c0e10400c1014003014065400080e180c0301d0072040c01d1409040c2c0c41c04603079292024182cac588035916140200000c641c0061110941000482c0041e2020454120f0081041 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 497173552 1250 497172302 497172311
    0x40605040605060402070f022e080f0a050727051918090b0f190504060203070e030c010f050f0714030403140106050120070801020412020f04142215 65
    0x41c41e11404aa0014140c9401684180a40030003c3e140820390182d058044035003203003011082117440f01000705c00ca100c1703284031078501a41d0301042c0c2000485000e02080e41d82034810b42d4845000c44121842102d50a001800e003181a40c2c4031805004000301c400001d15401407955101c0340441c0d9481038849916041043d004010085c1d100e8400c40c00341d03044000b07103003403040c540079444460807240090b09803482c01c0c0e0803d0203c0d5128100303503030f900440b0406100c24002c901e8541401c1e0000e41040310010003140c00a82c000c43c00385004281da21030080140c40f804601c2119075802c5607d500030984561207140208041c0010410408109684055003401503a1362421403400d64280441c803810511180c0c105402800070382c0e0000d162003111440042d022503012004584a807500d16203600400565100080104807c0102c112100d1814004e03940582c01079510418401165405460408910f0000010541d0220f8030210011002800c8d400d400103020640c13289070040144c540140140d0307a45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 497174802 1250 497173552 497173561
    0x30406020c100507090e060a24091a0309010e061014030a050102040308090310151802070b0a0507140f03060405061503070906110f1509011808090117090a110117040605 74
    0x6c01528a0780314400b41d130070030560380c9800260000800070040c0900c1802034000640c01d0a48036810075002440260081d0340d15510f030104044080d4801c4d03c0c040704c15428003500032131000b0b0010b0303210301a4010031f030070303a40321403502603500c2d2400151364050f54580a500c1d0580003040003400a00080d41c020350440742c1c0c5100c2c040030180390109013243c003658503041c05005421014120031190480d0820081032098050039030001d4001d200301c540082545c01c414081c0400810035911151281311a519074600401020742c0101c8140a0801030220000b4100009100da0805800040c0c1280d0043c1c0000c08104108850704a507801c00c45011300029a154400c0207100d51142188145900001c0989446800c0c0303030130580c48840c108803092003c2d1640000c103580150950014603690042402c10300c04810b41c0c505500290f20050200d030024071102e0040c136031030130305804c581d00030b84072000282614038181e594001c0e650303503003001907040c042c100e00000128050100481d11452182c2000a22440d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 497176052 1250 497174802 497174819
    0x30a0606090516021213090e06060102010c05180d1103070806090c0a03320d031d030a0f0f020a1205271804051603080a0806090606030406020c10050709 67
    0x400a0884000e81c8002150103c05a000f0030529140100080c581d03688100080c100c9200860725404008403d20f03208800b4610f1030007142030f5001d404243c0c000d0155250003a011105c0d400ac1541081d01881e401c40d1700d4015143c400102c040d00c0f1b2142c120300b01084005000a03082c10020b40c0000d1207070b0410020448158418040c4441a4104440e03011b10141076031105402e40c40d0600042041c00c1c00d460483d030f44410704c81d081e500d06042000441d5003440c4c2c000c00c0100903000c600442c0c01d02c080d842c100002018804029220440c60943d500f5100204401c401c85290503260380e200c0a6000c0c0458000204010307502c00402c440c0c0e03503101ca0b640c07422918400d032071a8204460602d5082c4d6820f01120703055441e0f200035408800c100040801a4071942055800c05818003000d000c8041ca05400104000010010340380d00002c81c3c644404c01c0c0e6444003403101c1603a040b6110342d40240100300040000e00d565010301201d50b44142202c2d00045c04c4240300b42120340544040001c0799035800100f007002c8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 497177302 1250 497176052 497176061
    0x90c010c0c0b0901030f0606020c01022b050a03020d0603030305010302030d0f08161101060603060e15010f2105180d111c110102030703020702180601021e0c030a060609 74
    0x80ca4521200c40c416120031411001501031400002c0c8001849402d40c1c0c407035000070080341072069040142c90750b1130101a603600003010031140940115501c001c0780c840c21502c111400c12900d11680b940721042c044c1240c056000c01c1c0d4103000c0c107a00f40600c03149242d0500c03d0102030741c844e445c0040c0550442c01014500352a80805404000107550195a00389d4051141034004140250320300c03100305a0501903c080c40c405548010540ca8550000391450b4990819000ca503500c0d903142d082c5485600c03081e10045100140310340414001002d4080c12841500b82e42401c82400c042a11a280c4101140701034800554801360b0803040058000d8161406101c0381140d02c846080150400344847e20341500c41103600806280c500340d0f94002524a03010b0401e0f0126201d200e4001c565900d042a0058020b40044405a00600d43d00c0c00e0245051501c0840b40e0050905030000c2ca000c0426540d61a03a02c01c40200014950190102018043e10204046045584200b001103212401c05610600300c030f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 497178552 1250 497177302 497177323
    0x3030f060616020f010207180f0c1d090a2406030c020102070c0b03091c120c090503100b0f030f0604050d0e0d0305030702150a0902040b0103150b070213110309 70
    0x1c0304100300041c44412000a0140b5440c0d0545403020305806100041c4d06051842c0d20095804a0b803040135040d034941d030380c860114100e018904114000701200c041b217100d4508003096000149a00c1c1c0d802c2035280010f040c6612015101c408903243c4903003001864420036504808410700c00905003405015054005c5030902140d0748000c5040c6407054a03004ca241c038180c480d41030b0002c00000070070380485041c005c11503107102c541c11807804804000002000c1003241008083c44a1406179002c030740d07034805c09124044400040c01401d51000340d021510081031005045940000c804030304001944050045c5088441180050801c1e0701e05070500d9814008088500000c000d00f0900c074038100da80f40e024130ba4000760103141c00c0c0d031640c5d180002607151841210700c00310344030515801c01c44180190307040320a038180309403400e000844040700150140c0781c00d0300f446031600d46008001d1000204050240211900003030003294040e0a2840b10821101c0c2d010202c11440400802c0100c1c00c44100042e0484 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 497179802 1250 497178552 497178559
    0xf0b0f060f0a0b09030a020a0806090c041a06030907082514010503012c0c27010801090f090209071107060e10030207051501080d0906021b04090516030503030f06 71
    0x207800001c1c0006640036a02c1c0125141c103500424075110540b41000494036540d03001d080350800a1b12240e0007681c85408480c2041d0600c1a01c66880c1d00703040034007401d80743c01c945401a140c4d00800c001001030580004241041034800e0150014408008000595044818061036481000800a20b4030010155003000800e040c42c1c014203c0181d030300c0011030781184c0f240c50009030440368011903504054103c00c018503002d01108144090070b1700300341c010050244405004c40d070040174030458103078003995000701c240400c103070074010030403922a42c00405104000e000000784001c8036500040c6d0040c2c090f180580003404500c418031454008000351000341c80c1c4c40c100705850350002d40004c1c1198070030074036074000c240c0c02247d9041048010006084022a0716041070f03110340c0c403004002e0b5600444101400010b0290350b0001c1d0f000c0c00401d8000c1001034008100955100600030301020304110403003240ea512825005141100001c1c3e83c5102640c40b9001540d600e0034000b100080580002d0030a038070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 497181052 1250 497179802 497179819
    0x90b01020f0705151204200f030a11030312090703020f030303011406090609040207050a15090809060a05120421090e1311130b0901060203070c0b090402070f0b0f06 72
    0xc1c0e800c0300240380b400f2180c080b140c0c00300d802101d03044a551400f4444044803030b403400344280701c2041010307030f05010303946041e2143e2070382040000d0400003450700300401e1135010b401020094010440403455006001e01c090f044070b103040d560345860315080c8000c0b00c0c10403060300140c0d0140118a41040781c040340e544224011400d6504205035207403405041882c1c28400c0303400040407009500c0d020242c03622101d00a2046488030000e050884c0c56008013101101e58240407001042128141d1050824507078004103114107183d141001c2c801a6840b00008800348030f8140205064a400140080c4c031a51003400c007010030704200e001410304a05407411a0007448001c0d1014400b40246402d45944140d03407641c0d50004e81c3c0c59081600101a241044503088540110289141c400070742041551107026240441075a170f84000803a00d038000c01000030640448110200040c0c40400c000e130141c0c9030028401450060390366a4002040c5804004880b03100621081214070701028401c0b07a40407405862580 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 497182302 1250 497181052 497181073
    0x10050c030a0c0203070f0620070b07050a0204051008030906130f0f091104050904060f09080d0b13021204031d03031908072111070803100f150c0222090804090b0102 72
    0xb0002d0308a9805205888e0308404401500300c0c003040b44c5070041c40f2003901281d840381c1e5420300f291250f0000b0000d90041e41010049601c039150302d4a41c1c4116041c450145052030855801c100003540003d01c0d44c3d0086240c80c40129003085101c01781c500802c0000c4402e05050b1038000081e0560b02c1e4122180104801408100b000740c84030b40500d54040e90060000808210b085102002044802c002401544020035526102c40640c0c1c40010040422900503443e103034125203840c26031198a004071090049900441c00003402440300d40d2800907120703480b0720300a200c040443d180d03412110219403440301a0300e0b01d44c41180c11000581d0407541034500000e071141c0000a141480c044a0007013541c90703a40301500c0e0300070205070b01502d00c80c5034003980f41035480c02c0003914040e440030103000b410b111002d010070000b81c2c0f9201382d81d00901a070f425200e40315091030607000c00007420341a0703850006404180c800c0d0441c01159200b200041441105950303211418918140c040f00c1165030740b28155404105c4030b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 497183552 1250 497182302 497182307
    0x106080a0b0c0c010c02010e070e060a03170f0d0f060e040c0509070203120a02040518040b04150b0301020a030e011a1f0903080d06060e09011410050c030a0c0203070f06 74
    0x111003640c02001200003610350710380004140c070400541c2500b65180801c00000b983c0d043d00440c80c510790f580b0440c7c2d4080d44906441c03006580030b540d039641c4030ba4480d4042000800290b10820102500240b03282003050340f1203a005940d1003246010b102070356502002d0f900104030722a00c0058541d0000402c00b900d8682d84461000019008444c49035503180001209203200b001281c0d07494401c1100a42c4034240204010060b42060203410b200d000764070042e0030030008600d0300d14410ad410039001d000303e88a98982d43d0103910b0814140840e41e40790508170035181c409000a00e503d0500780e5000030002041c155050844070360062800b040e04042200514940c1c2d140c084103041c05443d81c100c218109a08819209258640e200411900007c210042c941909a00800454049440f114055008141048001c1009014076038056140d400f03032000f58101080758000c1e030707100c030300b0241d190802010205103141c204440010001c0c80340e402031402c40c00c00340b01d03080080c43c2d1800c812072a1810458003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 497184802 1250 497183552 497183563
    0x612120804080412081c11071101090b03010e0612030c0a150b180403110a020a09020a0c02041e0f0221070e090403051207020a110114130f1502010608 66
    0x8020400c0c94408101030040a200719802008103580612160311300303141c40341300f6401c070061710f2001030000307000c82d4410007403400740396026010b03010b80610701030481d83d4101020707007803920160420007800800325809103418021406030880414502d4070b032504104201400c02200d403c07540d2504240300070f80041c0350018103446680c0e80075029140c2d410622600f0b40046c5180f142003644440c0e0034900e42c1e40118440078040c0580e000b0395816125242d40e04440b590f0b04510140250007103407200c02045140015030243c1044000f44c039009041707ca4540000d015a00c44240f000c00406250440c0e26201c403603031080464a6591860540c14000a100802d8813110340402004030440c0d40800122003620443c51031094010007042c4001c11304040c20014000d8004081207406903000d580407400c0140009500c241175540100d400078030458940045a9181e0032000c4402e031280280724038452040c000c64900050903440c034a0703600062a290020300202da98200d26019645080414000d902000c40c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 497186052 1250 497184802 497184833
    0x6090b03070503210c03070f0c0608040819020f0708160e01050d110307030501050f071407020307060e0a03081605010510031703280608060c270a050303041203030612 73
    0x703c07844d4030130f41c08030780d25040d11030015415014080040c0500c03c02c43c6038001501118001c40a001a198441d00706035034000050f54042d14004081c80100c503100581c10341035024000a10503251104000c02c00076180495981000109801c5290b2112003409140c4840c0010a07001c07450002c0c65140c4000b00da04406001c0018003800c80c14840032466440400030344008640c0b0034001c0107103103000540602d070046d066910742c00140100800d000400e1000b81640c20f142c0e0000c0103082213500e440b070141c0d0014081c612440d00700911400c0080800c1303000c0043c0044041d41300c910b1019040501d07065084500051801c50080c40d800c4050010402084030701d0403e18500312042d41e80d0315416120f43d260503604044421102c0312006414006013241c20440484500400b05c2d011380e21041c021800d180510244901c1501140d8104000c941c02900e080e102004040c24810000d621100402d045034040c0e040102d44902c14034950082641c1403060304010541e07419814010040d81e550400d40207803482 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 497187302 1250 497186052 497186083
    0x705090912071e0f08070c1203051b070f1d071b08030405010906062301080c270604080d08011e1206110408010902090903070228090f06090b03070503 66
    0x401c83c3d01d82c02180100b402c5a0000c2c9500908120703441d0900c003d80c011501203e00d04516000010440c40c004010800300707602d92111414159200081c0401075100321416489128152001030640c0d407100b8000c01074408c60303116a00780000344000c0000880c01500c00342c00c00c101d0348040301001b2552100c00c44060351200d10380e540c0340c8480c01d000380944101d000150001d4500384c80094030703501083c4a840342801c00386034000481421401900c50704001c69403d510a0000c110b02c042180f40c03080881400d034036a4111b02c0c9980030400206100e6009a000f420890340a03029401845410101043c01446031101c01240e44032110300f40c0404480f0361090a40c0128520143c108124440c0c1190780a02040780e10240c5407603490041d00c0c01b8002c0c1d21307070a0780154a20303004191013030305c04011501c080f50003814150401107220100958030760700d1141c03140040b070200d6012652456078007481c1c00c202c1c032402010400d1410825080101e4072171000f440d100c0d5011800411803a103000c28031681c2c910460 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 497188552 1250 497187302 497187323
    0x607030c0c0b030709080f010b0a15090915050307080610030308190e030301210c120f05060103030314010801020712211b1b41070509091207 62
    0x1480c1c00c0d0101d00c041d41100d0000d9402104200031079a020f55940101c40c01141210850502031740b00034201d0b95503106180c1c01440008003445007003105401000682901d00e03080d12441c2c0c3c1d4052080460718413002d42c10201921540400c40c03854100203110250584078050051818880140010044503100087c188542c001c00502d07000254010303506a01b82a00090040744030a1840e80d03104c1c0d20900502080340100400c4800b180c0c1c0a40c00040c80c240c0c0103000c0018207081c86000000132482030400c0f11643c249200e0100016024001240214401d4070701084a55000b116188c1c440350503040030050b40c3c4103103d20700216028240c8200c68003002d041119a4a00e901d07694603584c844000350014040c1088040444110f00940b21514040c03166100c0503294220141101801c032801d10150604050400c062296007044202e03030f1104410903c0d00b0010101c1400fa0045401111220990740c2c01c081c20410450801c603044692003800c40001d0901c0900500c080342140c0031b5444003034480d00382c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 497189802 1250 497188552 497188577
    0x5060f0a0b15090d0606080a0c0810020c281713090c0806010c021201020c0c040b040204082802040e1f0c0207121a0f07020c0901150302030603120307050c1b060703 72
    0x86d80104060034020040d1245d0b90241c1c1890764000c8071a104407001c6100c0c80c100c4c4241400a071090383c42991130740c40601301c1d0074043c51b0140382c420286c00b00d40341d8101e610744240c4002100c1500c1c03246a084407025068441c40e07080f200280c164526880305414030f00b04000c3c2d41d50154002c00a0f41d118509080c0402584200d0010482441103c44c540c04070398800035440030801400a255403035040111014001e0040f24010301c4103078007481c4591141036000c03008440c6041160060b600c101d18051b01200c0d0f840e022038000400341c070007580b92846c0c5600208050341020781c400404012070f4210f1003003032020b074810b40d10003551840948184d4440012a0241808020104110f400002440e010141b03850800c10b00c28060b039901902c1350320252068143c0c140d128104050a0380c100c50b0b058003980b000e0540b0f100140c01a40c001412558180140070000104040c2000910300914155030742c0c86d1581e046140c1e6a00e41101d204421580d0130741c418403075035140d45920072074044070f40c5498100c461500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 497191052 1250 497189802 497189813
    0xe04081308060717060d0c03201306031101030902130e030d0204030c060f020105040b061512040c210503090622030b062e1b05060f0a0b15090d 63
    0x401d420200d0300b40544014400115032100c07a0038401d03a00b8402c41c0516071140000c00400d030750b15120041018400043c10004280803110020b06400800c0c194540e80172280d00051108184080041d0f480703981d40c0042c01405074140f01094520420300301000000f14903000692801c00c4c20300c110900d03907100d000045809100b401a9050340d20082e0301552180d440c0d1500301c0002c20503010740030020f0050b2010150a5205026290055070400140e00d001c0d2609414454481c1d4845540e032014001007040c00e0700300d503900c800140300718024202458040d040c107d260f9000000326081c0814a1540708211000c50000300880b8243c101c1100e1450366144e0142c0200c0040d03045003c001c00181c1c03503080000520564442c4240700c0c00b021900c1e0b841d9035201040d0031048902821400c0c1240c5240e40d00300d1001c6005000724505000f56221a0500030706d656622840d141c411600700c50488204c81c180300c1c89110601070f01c12811811a001c03000d160350840c1b101201e02400c00454400e42209030301800317111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 497192302 1250 497191052 497191087
    0xf050402220603170403060c0807170c0702061201140607080f0d06030506130209071d10030f18110901031a061305040602180307050d031202091c03090503010203010e0408 75
    0x50303100c2c0c00c04412003141404c0503410780040c80282d03040c0d0b081c15440000c040c8650303c50791083d10b150302d5412400280c0802520044801003007801c508400f0803030280580d0b207403405855038101d5240c00c40f0942d8140f00c020b0000414840000e80034034070501001d00043c0801003510035411000315020344560000c0c0b001c80160001e03070300103402c5000e440207018031a0b412038030f070801d000e009071038034120f035103d04100319440103610742d9240000a44a000d03040d5031402d0020405042120700c0c002c1046c440803a1280c048881280c2c41c48100007404440b10b04102d40620081e00d030703c4003101d80d0b010641c07440e11500d2140c01d007100d81018046032040041c0b4155a0307146031032502501000c1c1000f60389404d190001c002e41c07001140300c0c072034a02072909885a10700016610705071240907005c402c054541d96070aa80d03e582203445402d1240c4c00b48260740b920345860b490b00700020101035109161030502e041c0a0140c401e00c1c0c10483c066401007006003c2c2d180e00805846d00183e000340110f6845800a00e080a42c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 497193552 1250 497192302 497192309
    0x115060504270c050a03140105091501110601060e0f030303090303010506070c031b0e090106060e01110f01090812100501050f0702010c020406060819050f36070303030f0504022206 79
    0x640f4092050710f1155000300542034000c00c503281081604d0039003a07440d48540d0244221540101c600b00012506501c20030303011000001030611843c40e80c0c1d034031421030a1030400d8200782e0000d03440500d03140562800c415505010710b025070256140d404c3c558480d07502c902c01402100c1c095a400030380e0a082040c0c00d54000c00450700200360044200d1400500c1101c0d10840c403c0f440c08110341c03404102660b5043c450003040701c54075110417091107003020064500d084031070943c009501440d018214525401c0c0075a481081c0b0072a0f0103607440c200800004246a00a00070f02c80304035140000b0b000a907004411100c545101c204001e0301c0c3e400a2004964416030800d0094000341481000219a0b42144000d8002c044a243d4050903000080c454030480c0c00440c0d205221020800118050084408040c20780384640380c0382100801102c40d0005000d00c101b58a81c209501100c000c000f455414412801e420001c54014030090070140c0000d02d01003103800c448860049044d000405a404c941e2200005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 497194802 1250 497193552 497193629
    0x2090f0601050c0d0e0f01020d020c010e06070221011103070f0c060603120905130c090e0a02070b070c0209060d0b0619050406030f11061632030c0115060504 69
    0x71510748400007491200320003903490007101c5480c101b1107150b00104048040c054147c2c0204060b007441c2c0011943da003441901d060704a4010825207003d41c0b1208141604082041c054143e400400341c68a070868102080340480c2c44018001c0c8a01107602002c415088013003440d050b42c01080d00e0400b20010b02a51340002e04603140700c045c441e0700d6030700084c071007048032001c440704408407a00006440c1644ca0444a2100080d01311009009451002281641252080800508080542d950000405010380d422000f080c01c1c29812011454802440c80e8081001d40340c0e10700c08039169444c0e034030b00b2102800040c0b062500e03907a804c94400170003034408002c0070024010f01c0034035940d0411200c401500030090b900605618088002403c0a00c1191048001c0c4054412125860384031344180c01d44094080400c1c508a2004c61b585a030b14440c6c0480d0519264007840c0d860a0341c04246086851002603031807034032407007041000b241e80c000080e2001c03541603c0c4100510f107451007006403c001d0f842c040418 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 497196052 1250 497194802 497194813
    0xa120302121602030c011103160510052e2105010e061e0f1b18030102040303090e10060f0c061d06070f0c020a0513021303060506030709050402090f0601050c 69
    0x1081d078507101d41d80403101e00130b5080e2040b00030304a004441d110b020b05d00000e0154010401c0204400c2d0b4800e41402550013242a1512030311100c15910a8400a0750341c11010302a1140c1020701b00b011350310407281080401c507070403078081c07510945006000000208031502040b0040b1001400020340002e089004814140d80c8246040041c9000d502d1521503003100000d2003500103200c0000d68614140260252154480c40014043e0400143d5000440d906170300c90580d103064000e51002d002520145120f5103508140c18101800321460460040500e001c2c1c00d1095030402c040c1d9000009010301482c2482c002c5d103204820b0405401a00c2100f5240280c0c590403034882c940d41e08085110f5024100b02e64514406185100c0200c171446c01302e04020b540150b00b10802c0015280c0000c4900005441c81405400c0031440c18062500c01070690081d40c24540b21000c2001c0c40c13805011070b0026184480b0204a0b508007038000c10309841c00144827001c070711103020214011340c0c001e00a0300d001c2d4005000b100c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 497197302 1250 497196052 497196067
    0x102060c0d0e07180f0207050a0f020a0306020426031804051506040306051006020a031b140319030f0903050910020304050d0c0f1502030712120f0608070b04050a12030212 75
    0x200c0301c03620b21a0305041d1038217001190050302c0340219002107030000000c2c40d0904254880c5011170704901002c80c1d010703c901d030001000a14a001400091100c03030396100d1654640c1071891420100c240030810703079030000c220f0842c0004111381096044142075400090310b03a280d41d2225180000c44a07010380c495008030300001009556080684a000c03a46aa00b802d00c5d0369800036a5210541c81008001c41d4040074418a102c0451070003101007030203541855038500da4419a01e00f50303800a61003071040f4031003081e00414150140500ca4200d07110703000c1081141d4458a00402e036000300140c56100750842d84401140034800c0060f1009800000c00400d10301100b4500108541c249100d0104980360203200000c440044810307020444107160003543c5041c501d642e445081d00ca881d40441c081c09038642c440c202d81e50141c4244d00c5507080c0784030001480f50030110454038240403503011a548840800050040d502c80544d44400c40302103101030550301c6102c2c642a4180414003c0030350303141c180441d404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 497198552 1250 497197302 497197319
    0x4030e1306050a0503031603050913091103010507050309030901050f09040c0c12020c0607030c0203011b0302040602061503070b031905040c0303171618091d06010f050102060c0d0e07 80
    0x44102d54045a02d021419520400d16480740120389081100e07201a480180119002e070008218410005040340c0c4203458212074081102c024240581740b8540c0d044080509041c24402da6401804030f0402a0440c542688000d640c0d114614100c0c1c100080421040b448541c80d02c00d4130756000004005002c0c03014510f174014494a0001000d0316218851030300002c669001241201c140c0d20081e10b02d501e40451504c00b540c010036410300c103e07095980c54240c200d18105070406100905c92990700941c0c0c2c1c82ca0204000c0c6403050150003881d420041c40180c1c0425640020705808403200802010f4403996200304072030881c0001c2e021000340c00e007030200304820000c8201102e000c0d40d10079160341041c00a16960038200c80008c40d0170000b0000f0560110120078000d550140645050082c0021802d40742e0880314140c0e1164580f240061403000c1005640308001c1c0410b40c050201013111090803450200000d6903800040c042d440c0503e00092042c12940040c0c00801e01455060100c0e8072055403240078 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 497199802 1250 497198552 497198561
    0xa12060603171309060b04140f040c0e0f01080903040306050c040b0406030209040e010209010c0b060d050f01060e01060513150903230607030204050a0302060a2a0b0711100504030e13 80
    0x21001201c240b01c001103501d40c860320071070b0155a03555206da400c1504042c60410701041400859620050000b10340f65995610700a03e900c211481e070f140707000d81c034629041c0000141c2d90700c0c8107414842404100704805000000f61000c82c2d80001c404111601e4a40c051049446150080802040b00050225580303400d9001003122120603982048001230b600c000900701c0c0240c00030580010420100134010510145006822800041c00380c201c00c00781d555014074205100817030044c140d4440c43c0c10004c42801a0070300c2d005103102c0c10b049191181c8d010100c070a215280c01000784c40702080c0b290302c0a80c1d03c5203119402031544070b500c841c1c0018241d000030f42c280040c041040254440d680001c5d901e544a8020f8408a4001412104141d410340c0d003004126044400142c00304410f0b00d0f03c0003044900380700d443c010320103044c04001503010b050403c0303005948014000018021803803444100554000b440c2d00c0030710042880007403a515503160071580e00d103201c4030f6035501c20124101d100708514035501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 497201052 1250 497199802 497199817
    0x60406080a2a0608070c02190e10060512040816080c031804060b04090b06090d1b06030203100608250203040509090109020d150f02030a06090e0a020a1206060317 71
    0x22200030522140c1080c0b0050030f401000c00048a550205081d01d01483d0402d01d05403000b0590010605020b041500751410359210100d0081900705004c040000c654080024204c1454028039041e0030140f240d050610140005082d907000141c8040c40ba00074024848450b0360004c08513036200d04202070240d4075002207803501460001303211100458903080c4125811500b4203204036042a1806460000404019005580051080009000907030b1080c0d000f107600c61080c00d8494031280d0f0880c050b40b9048940d0803601c24503204009105c0034644040302c00f400c450301e0f841c00050b1960742001c0882425922900c0c1401c16203060b9580a5480d0003001a2044d50001c1c0d84401e0b0340e5446c0b07640700c0c0c00d9808445000e500114854000c50110303c55007000303185643e081c42e008c2000c22103010000101d0744201d4903070391000d07602d500a01520405004500c1044101e0f002401c49070b02603000905d9a102e10301c01c5c2c101040040649004200311504010003c41c1c00c10254201300c6041032580b18580d12948 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 497202302 1250 497201052 497201093
    0x1218030e031605010f121d070614030106120b030f0d021c0203041a09120f0a1101170c0c100911030d11030301060302030a09050609070f08010b010c0b060406080a 71
    0x31882e03401c5211602407030b8220f84059484100c0f07081c0348401500e40b400002c803c01c3d60035448000c0c62170646040c100a580660945000341102c41c50310310001c00a00c2011601399400500b08010084554898115102c04141031000600c0d84901310007e494521513400d0350b14030740503011586490b1500442d1510503408050450880304094040890703c0340b0450040d0110f50319428480c10401e9100c0011b40301c1c104c030282c904984030000340394052400d04403824480e229440a1040310800c03020306a10520081c0a00b4900e5968112500108002000804c42248204d0102d00c3c5680d1481c100300c40100200e20b07079000c211107941414910584042c00e07001500903c00d4600a00050307114200d00407000c0880310241d8116402c000d030031806580702030001f80606880c0c0d02600301080047c41024001c03406400103007602480e0080150103008254402c1115903d8440400056604645c090080c260302001200c41c50b9101c000080041c8010341181c1c84030b10402c02d59a04002904500e0f6140f842d0a0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 497203552 1250 497202302 497202313
    0xa0510090b090406021308070b0d0c03090515060103022134030903050f0c0c01020606010e100c060608031303060e010c0f210f09150903050702011218030e03 69
    0x1128824140c81c9111129030300700c0320440c0010b010411940c082c0c01c001c1005c51904003030a983e41c4066151010300d401c02c05a180c000903050121610381e21490a0fa5806402c0501000300d01e511107075203d0503a01c0100d1259400e8400007495030384a5070481d20a80c458011080b0001c10880d070920340a04129507119642003022100003100c130b41340315010b251102c440b0400c266003649400c11030103414402c07012818070906124036451546038101404d0034083c54001000c03500e10400009241c070b100a0310203030500001c091204029141d00e802c000c003007c524106100003000c5403415078000c156644c4040e09901000c1a46203904000e0003240003264021030f4244511140140c00c03608036041034429501180b20301102001490150100102d0b10180140c054514400c10005d40250790300c41408003501692686881d080219044c00c44510380c43e208010402a175450340c0203080d9100318400a4184030741c0070070b620b03150000c40d0030400f5044400304624803000e80380d2802601c00701d44074031500e1180c080c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 497204802 1250 497203552 497203559
    0x1c06120b09010917210a0f0b0d050d0509030712060204051509030c0d0f0f0302010c0207080a0803012105030f0304140102181c0b0c0702100504320301050a0510 70
    0x50061107a41904000f4440d035900e11083c0259059201c0003078081417941040c0d0020124111a48440c403901048602042c100e1440f19100111032000309030f144126540740911011a1002482c02950415800d000e590741c01250000b074a8060f00c0e902000a40850541e16010000f4a80241c41103800660750410724401100b81540c941c000c0c503081541590002c88485030900c4c2174124075001c1030040030008411b80e415160130001b1142120300341c0242c0c0d1074a1001b0100d550404c8510010300854000c0e081c410800d545000e1288410f06c00c400c0f04242054803042810004c2051a0780d181c0d2100131280e50b1401c10411000a03001100c0648410000800c43c04800406000710b40c00340003266851005081c8600403c52002a00107180440e01c0400131800d001030b0314040740d0750060081c130f4041503c3d00b010348100023004102c0e144d401d04100c0c2c03c2c4000c00200e41180214041d00e40c190102d1500340010b00601c1140e401c0d004031495042d07013000103025001843e0b51200f405002c0090081031700760349 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 497206052 1250 497204802 497204821
    0x30a1409071404090804180e06070f0e040b011b0b07090f050f010309110310090b1f03080f130b030a0b0603010501020705040e210c0f010903090b1c06120b 68
    0x5191190003a50b02d00d418000c181c9151a500c000d01c0540305c2d0380701c41d050984444540304c07540c0310007118a01007a134556250b501d0400400605070b00c0f00c82894189031081540600402d10160f840c4e1250103a074880740350360944c1e1b0040c5010304c00340c81d680c105049030706046e082407010300c4010368180d8041962107101040680c04064250b0603500058100c031941c1240e40011001002e00040550744480049002c16243d5024401035550310880400401c0d130070842d003440e0344d000002509040444107a602411129440e1901c482c04484d00042c0c0341d52111030401244800c0d104100d8031138901c00a4040202d142c4401201442c0181040181005a03040c2c000a1254510080c01840e01507400220104821301e00b582000460804070019205a1940c0c0c010344044080303c8285440d0b02030001c500400201d40130800c1d040310401000081c80082101e84000d0405111405030540060740001c1c140c1044030750994a003140c10b0000d408005403592541042ca805a0901049441e103000c400070503103945 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 497207302 1250 497206052 497206063
    0x9080d1a01080432150109060503060412030e151501030603080d0c020c13240308091309020a080706020f0303011a1e031306060602030712030203150303030a1409 71
    0x200103840b569603d4540303440d100080315100c400742c4000154070303511041074080000c05103429951134000748803103030498603003a20b14a0141c01800b4024640581001241d0f0002a800d8000d500f0255042d80c850311008201c02902068a01c42054800c4081c900d15603c0340e90840307485941c1c5401d40e0b91001003103030011410b031503041c030002c0c111207014131440b81012101c0c1e10002c10030303d40c1c2c01120505509000820f03501307403094800c5909140c0d901c3e002e150314030101440d601400e542d4142c00340d02d1815a9030359081e500400d49054043c0d8a0082c8502074507031030340d2142c1d6600d50010080c1c41000d40d1007040c2549c80d4000d020f0000140507040f4507031050900081900d042e1403102ca0036200214910b00702c100075410000080200d4640c403882090400005001580500724048c0312a030718170301034241601520a164040740456008014003404034210400c00602e0810518000d41d07a070301c4800c03084910044250109505000000c180000b880443e801a021503420555040c3c190303a03880b0000b52142d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 497208552 1250 497207302 497207351
    0x41a030703111303060e030c01060b040f082a0f09090109211d0301060e01170115080d0e0a091d06070206060108040b04060f0501270209010509060f040909080d 70
    0xc400f800c0103200040d42c94008140100200d0101c03802c025442d0101d909545036079010542003100045c0900480e0300e4038203244042c00e68880107000707501c3e484540f41d010801030158860079a50170340040a05640b00600240d4541c03009006030428200b0a40b964000c0080c030800700c0d460380d0346285c0600000101c00404400e440c1984501e9005103000c0120100103070f8a92280340d0555907481e012607150f414411043c0603150b0f82501440e950480b10505003101c000c034030441124282c01404000f1140000b0f0710801645045c40d15001940800012507041c100030f800020013035080408104210a040c020030740c0281c0340c902241c901c2d8568400a9868101c1076454a0010f14400b0003e03000c1014010215007141c0705030f00c00111540344a06802c00c0780d000380c101100103800da41d83e07a11a000d1800303a0765154020180300f10700c2d10825070b0002e0a00e00c51b10701094040e410200d0384140140152003528010030b1107083c18048441d0620703004a00340d002281b076078802854403000004000c440c1005003c0d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 497209802 1250 497208552 497208577
    0x61803040e06030a02030601150e0108190c09081209010e06040501020c21062d010e13080f0409020405032a09060d0c180f1e0b0303041a03070311 64
    0x3040d0402030a8151100002c00081d003503c6004819030058504204141c001c1150850f03a0000c2200c501c8010142912075900303a04211042091003515065411006441c0250050003d010502010195041c41480d8000200e0380104554035aa4503141c40080035844000d903510601c0c401c6403130800c6640d020702c0c0034007401070f80030303040c00161070500241003c0203074010501d0038810707158032281c2403400d0811580400b03030300202406210442c2007000300c030300038126540340c0425540c100300c1111886178000740007820303240d50552038005012600d000c944c008103400c610b8540d605e44810030800039610501c10035010b8400d045c0d1920781c0e10395403c2e10801e1480912480c1c0f51032440307002003140840010385107992010b8052060b84c00184608030fa60002c108561a242d00c5160135003560003261842c41c040c860341418403800d110950003c00d00d44d55000ca403418005000a03019004c00d2440c0200e4004c50030003464104101000f02c49103000c2c501c620240d80e030602c2000a6200050540e00444441009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 497211052 1250 497209802 497209807
    0x4080414150a03050c120c07030e010804050a0209070512090106060e0915191512150305061303020c1011060a18150f090f0b090c010807030209060f1902061803 70
    0x1c041c404e401c00c9801200d5000c49030f041104002d00c2e1640002d06881c030100118000805004040e002034030890f040700c007420a8452843c2a40301c85403680d04604000388140c024100252883d405941610720714501c0c20b40a408c42c0c5000580c20b8000c02d503500524012484203c03181e0000d00c2c19680051140c0c29407080011883c1d003203020b000c061000203039001840400d1600214001003000070900789000d540d40d074145000340c2c141810f000c481c2e0048540407403030080003040c0049040080d101d81c0019101c180d4050802c07090404a040011500c1a642e000f90a013411500040e88040d580c04000303c118150303901030700e030a2490350450f846854400001040d10000c1c01c0172610025440f03c0302e8440600220720b9098148285040700c3c5642c60032103550743c00d0700d481e905101d403885c2d905500402900040060403409000070f45483c6d0003d01ea9005c042e0001040d04854699509070f0740c2c5408050710441d1039840d0103803c0500c02c0720001c2e12200510580300002c9240030f22000001a03076501502540c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 497212302 1250 497211052 497211067
    0x21010b2e03051b03070f0306090c0e0111010e0715020f070e06060a111002180a060c0f1403070606080d02121b0733030c1706180408041415 61
    0x1400341c40020154004075205401024a60100c00c0046200705c07082d039907000060500d8074001c0c0490701c641c0c01034003120f440c08000c1c903075654000307008100443c000d090260074110b0301400a13000d0a801746401e546070040a00c0050a8064410040041011a001d4540d544450b404240d130f40c000f00c4c8290504200700c031000c10940e080020040c1694030301c503e440c610045941e42158039121180001d0303020f0550010720700035110070b012240d410f42c071411500000c0c40d0f840c0400c020083c80e101039000d440c1e0084101c0d0b4004003c54030007000c000045031800d0f25200c0d519424400c0c01090180f2035941140101d05104403420300c04690506240340300c8550301d08203480d01c2105500f0b66178940c03040a840c8a039540c041007512903090400900b40c0090104541440c05040d541413107403000204030189410695121001504a0070142024096044204940e03603403000048540c201640c80c0700c00d482c03030b201c20710041c06805002403090f6006d030700d08640912440c00911952844400011311428030602011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 497213552 1250 497212302 497212307
    0xb0306010303080601020f0d08090d0305040203030906031f062a0c0e0903160507050a06050a0903020f01030b0d060b01030e0a020a0314070512010e070914041121010b2e 74
    0x79600800b06204442c055007008402c50b20f0011004140c1e00030849d4082044080b09080016880b5904e41e443c0c01c1c00b690500d5408030f9a81c0c0030360742c9028400c12001c40016000d0300c0002c0340c0c425608001240014099840034003900c4143c04003841c0b03501c6214202d08007614544c4091502e0000c0d4006040c201c400d2a20340048028000070300310a1740c03400200545505100145961a805400340c4042c1510710303c0c1034100b011b00369950388040c2c240f0002b8004030f00807e820175200400c0f66015a0030443d03030b401d0700c1c00403001001047c40c81c031343c000d040541d200700b0f10106500003c0410400c0e02c0400c5074040c1c071000701d9501c3c29042d00003580300b00148000c0c000150241d10302010751030b124085540b0750361103000080301200c0c2d141d08840c80d07a550700c0715240d400c03008022000050a580c0020400300c40300c0c5090110344003000f400a8610301c0407449440140d00c03a50480407110001019041d205d102514100f40030b000240760180c4a001502c070300a03841610b5040951892000040008000d4000c0070300303 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 497214802 1250 497213552 497213567
    0x207150b041d0c040617061306060312050903060105091b0c010905060103080d29060a0e04061d1b0301031403040915170a0804060c14010216150b0306010303 69
    0x525800907159402c00c5103000c003440e825064a20100054105003008000744402c81d08680d110308510701c01e0001450826201143c1c050f044450031100a008070054105800901100c0c0c0c401060859110849048240c1c094080e00c44c41e41c4c11415542a80d90f600100512aa010390b8140d0a89581320040d0240a262000800107803148500100d80b110345a19514240342c0300340d02c15208040b00107042c0114071114070409a54420007040d020784420368400340340141041148550140000140b49a0b07524011990100110780080c070a128242e01c0b103408006140344c900550401c0264000800d41009051644c01c038038007403480c0101d04507880c503150600c500440e5102c02e01c20b40001c020100b0800c0e03d90285100403042a014505003900d00001c400415580440144403038010030306180008184400b10360464103645000e00b001d001300e0a0481c0112600d10942c1c00340c0d8400524900452000320721030841c1c5006961000c25503030018510350644d8140c0180d540e040e0032050050000a000743d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 497216052 1250 497214802 497214821
    0x9050d08090c0f120f0606030d0f020d12180302010c11030f03041b180603020907020c1503060a05040204140f120604021c0b0a05060901060306061b061806050a0f020715 74
    0x30340000134100e01d1414205015003401741110741140c41000500d003410080c03032a03405118a801e82186c82d00703010007519070b0040501e8404101080000303c0e581310041d0085141d1f2901030300344011107031075464042d00900c880380d5171074049080c0c900c60780a040004401d81e000c0804a8620070314541e51a550400308a2034030145682100c01004013140005c82000c0704291115402d900090460a40c0100014900d00030088002c41d4031014040f0103039204e00c904c1e50b02000c1c0522400b622902d541002450700440d0390041600948003040000d05d050040c403040250100a44401711400c0c00402071000b0050600413000031688800c0c0400d00500f081c03011041030216413030800c483c0903060794994010050580e84418880c0d21070382070001c2d071301c0e03c28111401407095090070810b19140c03031009008261100c038119038441280814a044c4239260b0445030424140e07605020740d450707244c6801c100410b070030b495081209140c40302641c20400b0f24401ca841040d0000c0b0318040c51001d4410441c0940f00030301d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 497217302 1250 497216052 497216059
    0x9130501140403090302030c2b02310501150c030e0402040b030c07020a14030a0b09030c070b130f0e0105062b02040303030f09030801060522060309050d08090c0f 71
    0x54078880442815032654042c6219565180350b071490741c01010328228103181d05500c03859050303032525044103006c81030304040100c01a81c64500800ba000050003402c1c500c091244d01c070310f4242c0c422940382045490030391295103240d00308516625500c0350707001401841d01d19808104501103c0300424010240714104900051001d46002c3d01c0781d0028801d03410a844000c0010f001080107400c41c506802094040d00d00e803040100b0a907500700020340e03103c00354135004e451801c1c640c1c0861344012007030049034140d81c0114111030029907101c40022140c0d00c010100390700c0e810002030119918011000160840d1074095105045900302420041c0540c0000d282d0415500001d81400c1d040300c0050782e00304a40d001403401070f1980d2071410f0180c01d4540151100a0f83da240003150744c00070342c0040000d41500c01030b00d07199403a1041c00307408030603031801c5840d41104403501000005000303905800c0700c02e90b14803907000e440c43c0302c01c03000b41642e4040068030305140541000c0c0c400310050411102008075001c1c0203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 497218552 1250 497217302 497217311
    0x207090b010507080d110d02090108060337020315180309130e03130303021f02040302030a17071a0117030c0c040c020705090a0213080f03040e101d010608070e09130501 74
    0x1b9403070100d0780c0064201400950042800c007815a00085080d903c84026005031091115442c0300f44003951217807060350110050400014094029500308465243c0c2c060122620503c0c00c03040d0302040038044035002e0070790710140d000494141c00802035981c428006001700e2290780c4603100c0c00c0081c100a0081c00e1a501c003e1000d8a0000701c1b590b400402940a9005401e8007212941c1c03484460541261210345e05004110400042c0c50000c5c11101c2e841d00700781c803a401100d0301c0712462410b103e00718001e0072510703518043c0070030912252081412034051900c0003240300c0000184a0300c034085c04080c035006400c0078440361610304040d00b20031201d001d02d106071600141c6910004517070000c04d50b00000c8595001c1032502041c184654000050554840140703038004550303c0850390b034030850103845c5800e800c400214420307a102002c208040d04115947c0c120340000740c2c100c60b03034143c400d11481c1c000800030004106040d01660b000103560a000e4a0401990340f40621084981c0341c05100315002d642c0e9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 497219802 1250 497218552 497218571
    0x90540020f0d030c03020606040903050d050618090d0807030908071b05120c0405061504090f090b010905060f100c020603040c1a04080d050f090f210c010207090b010507080d 76
    0xc0e821802c0545210b5101c01c2034042e03980c01c000345440700041c003030703030003280f809880300e0100e07070031070240c411142c0750400100307141d55008003007182d00d04c182d1042807080310744400f4051044e0300401c0114444030181c2d105103040d55240c604505541d80d104004e041920104020400b0034404844106400008060407458581d035001081841320302100028080e0400c0821040b03071301c0e003070040341d4001604603502008007120012501c0c1030321440c42190384a03030750364245000c44a07460700080100da40180c1403040c95079440d10b0800c06030208441c0588134001d640400c0c100b5242c1f208014122590603907904001d42095400c0c0300da19480980260351000700c19100041105041040d5180b100c0214506900c89261201092420504182104c1880401c0c841000302407014002d0390080c1070704455049a01294038045240c40c02d80f1b401c41c0030381405003610052400c0c400505400240c81c02e07400c0f580c080c1e0303031401d00004031003801e11030314009282080f16401003103108014100b0311080c41000129401c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 497221052 1250 497219802 497219809
    0x803150f0613060306120c060f020c030a031205070809060a0207080c0304060e0319030e010509120129030303042109090c020705091806161107090540020f 68
    0x2202e0b12107140269505001c0c800c4071360500176000200300b04018010a51300568070101c907041700b409603004004050b990b5203115442048501012103010f0141c3d080441c190400400482e10220102e4806003414003040025100e5542148500014405070245841d03c070298406136000c07100942d006a4284210510102c0603c000c00082005886807080c181008041c503041c881c8880342c011100f201c40b010700020030b400c00c048811014003440c00c03d542e0380084c000503c061600c00d50002583d2302e0544a132820b01944207026441180070003e84481100c15002c05070789100c1102c0003841a05072841d05140541c02c400a201c00c5117079401c101c12015101e0318840d08032205d014946005910490007040a400c001880c2500000c1100d460444011440106070741e03541c0117400b921000c143c03501d071030761824461588030400c1c1e41c881051b194043e07035412528014000940350081d00d80c203a6040c40544100c081111108104041901c0504401916000a0140200c102a600035201c0c01c251070070f030f99 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 497222302 1250 497221052 497221057
    0x80d02070b1e1f0e07140304111c150b042004090b010c03020c010f110f0f070605040e07030b150705010906050f0907090e03220305190803150f06 64
    0x424030b81a491000780322900d81c444150000c0e01c148a080f4070341030000400511140140c081d102e54144090301600d8515003140e02c120100c9154202c050040203000c10031150300345140c4500c60840d1500003c955101c0140c0a4182c0c80c0e400818441c0c00382c5180f8001e1405170041ca11200e401403002510050703044d14007841c8600960244244800054144401261403060303180c2c3e07800c207103041d0b000e034034540e5400395940300103602c000e0500081d402d00c084030901c1018100020020348003a61020b50580c06566a281d10403031903005240100d40e80400c40f58800c00a9400f1601404281308540c0c2718441c0540003459011501a0000b14042c0c010300c040502c40000c10700d031032045000041d00d10745404c0910464201511213042c0d08501814400706c1c00c1d00060013000d4907070120f0000386102d0500d125515501c6081c0c1e03601e002c00800c030594014400d1440e404400c5a00842c15610075a61040c16204410514900100f1218080c00800c00440d80c1800e40d0881400242040e9001c0c2c900c403002032542d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 497223552 1250 497222302 497222311
    0x708032d13030332030a0506120d0201391b0209040308010608130c051903140a030818030403030e0607171305010801030203100b0102160305070e06060a020a080d02070b 74
    0xd1300d0b4161811042c106111500414140c840343e00020b2030308050043c102d03101c00360442c4000d6460713002091180e0307604812100d6210b1508100c0345525402c000c0a400b80034041c82c0c02078980141d800300c4001c0f03d10840d44951100c2100c240400e21000b400081d1803411038900b0080e812286101000010b8450020a5001d603000391140101503141800c0204500320040c185a10b81c4211040d280014034550120000e40380b003102d084484041007040e5501c8940d059101801c800304c40340c0d046012001c00f144c0041a24040d83c1c83c0702c0540d54804803d0402c0c3d503c03824005641c0d004003c10004240303e05010498030000806491402c01d07140c60300c05c1b076481c0e0b02034000141d40000605080140d10501894010002800c008125625540029072189102014003c84a0301c410620040303a10038814040445528400c0c40c85664483c180b40c2c1c0c1d5815075000d111011000358002c030303500746440d9060300c40441032940200310b140c500c2da844140b00d800503000c81e0703c00354091000a00042030107030110710a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 497224802 1250 497223552 497223557
    0x40905070f0f0f090c1d010c17030406051e040213060b0307030b100f1209020a0e040332030406110c12090405010b070201090b090a05090a09050708032d130303 70
    0x7510b0510120b025480f249038000c1030501c2c540710600c11800c1d04800382541117010b502035400d0045112005070744420070b04200424201204a040103903401c003034091405240148001c00984d41e403141c00103421114504220309040a000004006140c40e00070748214001100010035003e944100c5418550000d0350700b200826281c6600841074206240800c86501c0c5900c1d04003010701c2c4c880c84c003910078556070801c514459201c42c148070954a0741da00000040c460a60024418501820f004160707803400c0300801d240415650070044d5084884866001494030001c04a203144c60300e0f55450002c11441c40440001d4106101046404201b400300c0c205810b031050019960f01d400f10100800c40e48142c0180c0e079030200a01840f03015076442004c10060300c5905113046c0e1364403010000074842d034401e0380c480c42c0d00c0f10800341085400c81c1c0070b420481da0742d4450800c45000035150380c0d000d522401000d582100440e1074120740030b43c4e003034009500410f40071210740040c80c140144c003003050940d00a0f00150003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 497226052 1250 497224802 497224829
    0xd0c0206040b1f1205030c0604080a170106050901080402030705040509100e060f04121b2a0303270b03040507150e0105160503090d0b16021902040905070f 68
    0x6101450740b4082c0d00c00c5004801075004942a511a41000c040b03025202c400041c451640c070030000308104864007807004c01c0072180640340a01d4922130a038800c00704400020f0f880d03281755020181c0c40000605945031900d8003820003102c1001140c00c0b0b10b00801c2aa890312030400005900c4d01da5200c0c40e07000e080d4903c0a041940d0903400d0300741c1565501800304105d42d220400300700c40100c5404c4482d4000d58030080390942140542c8040b0303461181c03883c00e03040c00c00444c0904005c2007081038010700d481c021499481448049840806941c0d11103210140100c0c083c80c041760a6281d00c01c0421400b00304012a1480107915112805200d4208640c2154194041882408400c3c00b030100904400300702d1400a600e00609000240140503441c404a00e007010365403030004003c018815140d6000d80508007204a1055080803c040d210684018905500209545201170310204090a21011014904200700b82903400d0000508800409903070138040c4034000b18402d0a0340c80200000d0810136a03005 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 497227302 1250 497226052 497226061
    0x3050a1409031b030304020906280f061e090504020327030306030c030f030d15091a0f0d020904020d170c030304020a060f0c03080901150806040b1b070b09030d0c0206 73
    0x2034544040420090180c2c1c020300401005a6450b041a03500500558602c880760302000d501105280c8104412b241108e9208008504001c124075120300b202e8003552114007076091054680c08020303101c800f00002440010700cd004030704044d001141c0100289401c2e05000c0c11b2034202c034848400030005250941c01c0042880a039140400203840030750300440107480b8113803100c445141c2d0b92062108418540e82c40c2c2640301c0c0c0d0000a40c1d80c41c0000c180100c0140414185100003860826540003100e100fa205080c042616050040341c2505c0b00e0381c00b408440641c2c0300c0f502000030400d1600000c079000c403052055060404d40a40c05401c400203040e004503100d040901c10408104056042f0204012200c0c10940d85c041d400503a007a80c1036010f0030007551903181c10303103428003521a2030006440039201e5100014800800210248542d015503059002c5445a0180e40c510360780e003602e0355618100502011000c0342606028980103d0480d048a00d02212080a40140c640000c81d60015030040d00400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 497228552 1250 497227302 497227327
    0xc1704030809210303012304060b1c020c0a061802210d0c120f090f0b1803010e1e070e01140f10081308090303030103140709060609030303050a140903 66
    0x755036083d034400d2405004022020982e40d207000521480180340b521111203107200d5000d0703203e01018040504240500d50300c44007a1801c3d6401034040b142e441c14a104070580c0400c451082d51340e0b4100f000090048090103898010281c04203c01c2e5445a5030b148940000590320301102400003016040003080d14a0784c500d081c3d084c000c1c1d28182100303000e074418000000a0914444d0092031000d41060070040042c0641120707881040d4000c0d241c00000c01d1b4002c260f00c40d446001e01403a40340031790180300c0800000c05160a85214210840480d405003800c1c0f0f0300c41c1c56428000e55201701440480c2d10310340d6108264404811300382e1001c0c0844000b81103854071828250800c50f501300060b03c0d070706c00d1000f509100401300000108a00b50003900e01d4540d5042082e424126006000001c04694a03541c590410700000d602044a0080e14821824009039654442c0503030000c856207615a07008841c5141c40640140800510080c1d0030b42da2550070300c030108420607040d03000b040c03414021901d854098482 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 497229802 1250 497228552 497228569
    0xd05090706020f06040b0903120106052d07032003030a060e0a0b0a140301061a0a0e10020a110105040b0d060504060b0427020f0301060c030206130803070c1704030809 73
    0x80390441d00030a21698180340e001444d9074105600c01524082c070790700d1030741c050300314011400750606005c0e1081c00051345544c01406800790300145036080d82e01002003042d500030900f00b494151025a810310054000c02d00034810710060f407160a580b4000346689565403030440e403046404040301956080280305e8840100143e03680070300070120810025114000150b06a002c80c4545c0c4924100c407400c044e191b483c01c0d04198001c152507901c9002181802c484021160001c0027021300080d480d11250703410340b03032032907203040c1c003131881e8000d80f55600854130345282152000f1121814440c0030000010b4840c64100105000c4944c07a8002036410300b404200310550f0070b00d0303018448169061100b4002034280311409040e19004ea8004088000a40d0110000c0d00900c03542c4075a079000840009402038020091140c480e1080e400e0315001da8400a0716440207145d4000540011010310000310014003850b5200107944c05502c040600024400000e00d20780d0ac50b030012074200e031000c1010507450070204403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 497231052 1250 497229802 497229809
    0x50d0825050702040c03020c1603061103041e02010c0c170c04110f0d09021914011701050108090703060501090e011a0d02090a020909070c021207140111070b0d050907 73
    0x4049004600c0500c004200d8001d1180c064030465480d180c40a0701e500a50440304044411001e031100c10005601c9003508108602c000e5606500f42034102800961480c00c90b4071450b405081d0000902003820080344448044504038180212586d5060205a50341c020000601300715039800b410083e444081e40c28a900300820b6801541400f4403010107030410030a035403550300b135028060740b203591395448840644801071010b90040085031842a480582c1c0c1490002c1d00c0103884641c44411a1500443c3d0801108071840200d05642005011a40c0308210054020480a086402d01912600c1303d074100c480a078426a2000d03903446000711b0400342070184511600350000c0c13449a002038180822182540503000902c01e0403400f000418100c4164191401454098203180d12440c000101400542403104261700c50700745408941c804090010707542c01a038008080f48452804640c0055418403e00c2c0100000742c007072028007091103018440640058050307000702141c40d04081c81f2481c00c00c441d981 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 497232302 1250 497231052 497231101
    0x60c0747040510020f040509090106051905010509040c020307150f1505130506030a1709090109150306050c090405090c01110d0203030f040f050a050c1c02030c100c050d08 75
    0x10801010503004903560151540d4070303c026907140e40c4403143d24550302c00c0d41c00a6620910005c20700c40e10540552007182a1030007902d403405600010860141485280e01c200c6000500412817200c241c20181c21216035100180100c0f810300c012551b03010044070b0700c40c40c0e040304156103a031010040403003409030300c100244103da2945183e0a00d00414200e078101010764a81c1d81d1185c0103d103450301d081251708042d40e005442810540c0c480b4010100aa101005061191815800206108545208801c04459402c1c80c4162441c59981c0e0440a840c0050903017112032004e1144c0c050300d4031f0743e0140c203206143c00e81c007520440c0c49810000d860340c10b84455181c41d66200800f07940c607403a0004102d9070132541000d0410020383d0740313140024a00d516440c00810500554000390100040004d0080f200c01e4102c0b000e20000c2d0001620144ca41104030b0065450f5012500b07104150a003545541c2c5012000d2401c80000c140c40d03220149451039108560000502620420130000e400b500c401c5060030b0ba20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 497233552 1250 497232302 497232443
    0x20f0d0b04110f06030411030f0a0501060f060e01050a0f031808120c090d0611040b040603050712020a020c06090d021c05010c0305010e150a09050c070c0b0c060c07 72
    0x280109100c5e01004100822640511400c004aa40c1c204041c1c030038003000e081201d16032840c030700e0700c0c501a16042c8610824001c3c11200403a41a018441d0484200c2040e52010300f8241030070800c03120a030708400c2103820300d6a070302c4058260042c0ba10486900d540500d0401da0f0721402032290154010008129185030303c030030b020501c0c0d15074404004000490304803201040c03034844034801451a02c0f40b580410040c40f00054000f40c1903425801c079603c80c6203151103030942d0070403010000042c3d00c100000880140c002450b50040d078909000605035860018140c500141203941c041116013000d840c42c00d141d160208907a40401c0002d000380612080546000c2c015540742003024010848090111040d49000c1102058180c80d402d6019001740700100303050200c1d05105854242c41d80c07101d5015200075561202c0402c03500d000104603580251030710018189540e030041c40c0705032900040c00c11a1010300703c5040d02c02c0d000b02034031803180c009801c18040c0d8048510041c40701610004101032088203d25 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 497234802 1250 497233552 497233579
    0x303040b060607050c09100509070c080f0c0111070b0603122b0b0a030309080709113405010515090403080402060a09080106080d080912090409020f0d0b0411 69
    0x1020308160404016149a07484100742e01c0c2c500d003844801c06800750000004000c01c609100b8542407079007201c0c0305075480714164940b14011502d0122006005d0719000c000c001d1b006180ca2003000504001c03080727038000105446420840031240d8020711055585040705800e03c0014603042c8014844541c03001c040b9450320150302100c2c0c441d2104160403100e400a64100744221000c2a0020f503032424000340411310850722440c0c060400c08050155062034851444003050700020f6105601890409115550a000d18500540c040803064210060700b580c0e00501c0c041c51403241403020a415100f5000442d061a005c0d1003880c1c050903c0c00b10f980f140394201c0600021030780040181d50450340680e00b072035540d00b03202000d407a400007950003c101c1d0740c82c03c040000d414801040c40358103010180d480d5003481d00ea080380d242e0b462200001d002013017241000700c00c1d802c0c64907510080709a4809419500c04001d00342c002181107281d41c0d03042c0e80019209082104004031030486c414401d6088403c01001c041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 497236052 1250 497234802 497234813
    0x80a0c0f0b071205030c0d0228030c020303061507050f0303070e100c021009080f030301030b060a051e041e0903020f1902040b0303120403020307110405070c0305071a0a060303020708030304 83
    0x1a50383d6080c0034000000003050550051104039440c03c00001d4066590350a00c400c02c80781c1009240b400c800c0381d8000d4206084040c481d011b82d080340d545a03401182140c0b221020049000c01107002a0002c2004001c218005001809203000d8202e00001843d12850b0050001e03120040d50710403113209441c54607403000e4081e0400c1c0a6116030360180c0305442d00000f402010740b6054501d41066005214854030340c001400000700030340c182c1e4410303c21191381c1c0c2c44006c107224100115002e00740e4410a0004d130522006260ba11106040100030801302c2c8100c6403410300c11210080c81081c40d00c3c02e807548031100605070100b20310441200454000c01c3d1050081555011548038400000d02c65a100c1c80c0c80300196600300180d68175043d9a2500001c50705007407502075036960022008540d1000d140c40016010324083c40f40c2c81c41002ca0f6101e191400d54555421103003a40140350881e04a80d9a14010402c1840179103403600c0740240080000f2071a0860602130700e00304043c0d104203401c0e030042041100182 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 497237302 1250 497236052 497236073
    0x405160e010e061b010603060e0304030606120803010b0a030f0f2301241e030501031505010503150c070b040305090325060e1f0503040204060b0703140d06080a0c0f0b07 74
    0x51048400704501c4d1110040e6001d8446984050041410280076003100703000800240112841410100003140c0e4803105520490f118a00150486109100410105c410040140101901d5107000140403006582d083c2c1142d240c003000203400c90750381e9410703400d4010b401c58208101e20805036480856240c41840e080260510100c0c0168002c2c04100080e514042c6138003802203003100410303203030101000600030002c0c6800d1105694200119250141820551113018181d48010300900801c3c88061480c950580e006006185a40c0b4201300308000b1036603468245005034070a40d0361696031400c0303030101441c0501c0002a40c01c00e0506109280c1e1390300f10000c02d54101d980314180b8000c0c1c030203500e0001707640307150192040040012241d80808080e40c0300c0c0c003c520031482150700b00502030719800d00301000d004904004000c10412010000140d0701c60001e0240c003c42c40402060341900c030040981002009036080366010380c150424080c502031030f00310b00d01038506110158204401901d4170078089 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 497238552 1250 497237302 497237317
    0x1b080c0a05011b17090d260a140703090b0a080603100218100314100518040b241002010905240417040902180301110a0c08030907050405160e010e06 65
    0x30f1014049200310480039400b9102e420302c00500000c2c2c001010704201e10705441c948401d1548182e036601d41f04000484200341d60211546943e240080e4032007444a1000d540404025014002003090016240311204010074444140d5580c151107402e148051615080c81c00d03c0b440c001a0060040d46031035030b5001c100c1c00381104101c032490060760003800c064008100e0b20a259510b08209010001080300076034070002191010784001251030641c40454051907410b0b580208801e00300c2002c6100a107500e00e581d088002a511100e04441e02000000d440c200021110405030f51a551100c00344082071106106090403205030082c0d5170310380d0008201e000401000145031403203540c05202c0c00b06114007a0707000f80c07800340d008564880701036201e1001c1100035200107100e5800d200c1450340210703d02095038044201900c0b0f00c001d460b225902c840340c0d0b4000501ea8030f141d01c1240000603580e80c55001d114001c05800041402080c140c0000030400301c03643d080c060510080608500b260313101e5400300e4041c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 497239802 1250 497238552 497238563
    0x30b0f040506120a03020a0309120b0109230709030219050d08030c13180c0e1e01030b060f03040c0b04141002013306020615010305041b080c0a05011b 66
    0x240da0b030314000590540a0722060701401d100e88450300c0b0070503400181b03401c840c50003034482303841c069600c0020400303111034140010980c0e1a5035004000d1035000e80c1011850b140c1101003460b11550f503520102c0b15050032601c3d400041c40d000020420340c100820f1030140001e041090a07005400c150100f090400c8010005100a000000007140f045203141568180101880210b030601e1781c0706001c06a030312021501c81401c624182656100d40d00031000c600c50014040c206658000c00c01514101d030070000c8a503541855200d1030200c2603a42c03401c0041c142d40251605541e243d042608090801110039001507405030b00400003406059122100075016001c03c0f14020507101403108100e02500d9050921422200c0c1140aa8603000701154403250b4440324003040a04995111012681c030003050300c14032205e045054200074039510a41205a0140c000d51880c6421140558001200100d0354846c402540018061003080e1804803603c0700282024a0011443d103069260b8106025403c0c074000e00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 497241052 1250 497239802 497239811
    0x120f03040c08010608010506010f02010e1f0609020d02040f050d0b1f03080d090201110a02090a020c150403021005010603050c0d0b04061a12010e0903041401030f0603080712030b0f04 80
    0x204000c2440c0c0001030b103101c00090040c1030352583c03283e011300400c1c0e40290201d4a04100050f0032481446003103003100650300200f884114071240c1c00c3d01c401040e0203201c0b900e9194000442c081c09940010503002101100042c1d58502c0c144142200c0e00f2541c102d1031098401412040100d49018865070300030607164006500900f148400865044013036000401c400d5010440c407044180642c880c0c90598000c0c2c03074520800d00102032542e2150107080d4000d60090f00ca501003160b00580b607010306800c2d140d400440b18070410f051652401d43c0c104840071001a44103407500104501c030340c02020700400301c5040610440c1404e021446890003111180c00600d56500789003065540c95400c100010f01c1c0c0c19030752102800038030031800090b90003110810391400d00c40c0000039858001e451014410810f9a014505107410521240c90910116000e03e04050f150400c02c4031149040c0703d100700a42c410f46844c1e40d6a00c4620f001c2042610343c000d424185464025030080c5604c5c1e0712098005503038211070001c1c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 497242302 1250 497241052 497241061
    0xa05120601151806031a03031c11070516081b060313060908030a0f151214010618020a0e0a210213050c0703091e170f15070908120f03 59
    0x454480c2240091109240c2643d00090481d804d41d1000680f02141040446081104002e0694a224400c2300060400c45408090034201311548190007005070365040e0307031800400b07403109860400780f030130f03008501034603814108003c88040001c0e4208265140760a030b0207050140c000703801404020199000301c00c080000408001d8540c0c0320641d02c0c2da0100c0c0c2e0039121b043c40c2e40c4030703001040102800081d0516120015000340741c00f0110504841400c02403070742c940140ea0711a124824009202401ca64035900007050031000c44125450a0021050058681011a0000b44404101c0000c0380c0500850740c801c2c440600500200300c07132030109006050030340c0050320201d8960041c100e0300c001554034103020302c0f003403a00c5a0000e1810720700958071000c0c801e880b00c0c40052500002f010f4146165000741040100d06011911012100303070002c182d8a4210000c0f180c50309142011422610000700d1404002026420000c0b01f0b01a0100c40300521f2501032608110180748544150801c47c441c0110025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 497243552 1250 497242302 497242307
    0xb040f031806050c150615070c0905090102191805091b031501030506010f0e102715020c090117030403081306080f130209071209110a0512060115 64
    0x4100788124038054140c20741c0c03204001e280d9040710a480303c060150043d0110852101801e079405084014502480d2550740305035461203034401642203c042c0038111700002c410301340340f2a0520459010001507900c41c603100120408015408003802400252000301c52900c0e101103a4005545054640220039121401240d007617a210b02030283d6010800002c100c0b66280000c101c03071038000203880c01d102c83d81725075006440440c0c1121503040042ca03072410010030352404003580c054461042c10180010b001c110f0455200100c4074046844036030390b400d42005014228150210f00440c18805440e00705503200c00924140d00601c246180240c80c9040e10034480c105104960003194001c076610b40e01d05821440070868101c2d845031002140e84e6a001400380c82c0e01000c0e80d0710031074046145000da644540d0805c0000c080207801e20b800c10032440302c4c521400080f88558109907000300690304424541c10f00308290b4001c103030080e5001e034000c0020f5089203000000c119040d50342c0c41c0c1c4410102048940308 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 497244802 1250 497243552 497243567
    0x50609011202040504060605030703031e090b070f080d050c0318120a050c0c09090a0507140a0303080703150b070c1202030304060c290603010506011d06090402040909030f1b0b040f03 80
    0x2527050042c8000041010b801c071112540c0d8802c02c4003116034a0300c040400340d900c8030252103452041d0a007005030b0400900345030050315485200341c64150602c11003c4c1074104840d001c031030200803210000148913250031f8001c190741c12402d03880001c00d0691490070140500d405003052520901c403000c1040c84070002d06201600c1c2c82000a8804101881d2210703d0036692406194240c800780180714002c07075aa03500500c0400968000ba244407802031660360100d844810082140341015652421102c200808058000081540007a04e41e201d680504040c192120380743d00c181482a200c900841c01070324080300380c80c04c81c0c81e5424401000507950406aa0315403030254000b19a00b846404111039103132001c0d1107030082c00c081d002000b155944078010340d19a03802d841c088040500901c8040c005103001002080b095202501c0542016960b082e01c0e8151021f440c0c00301c02080345003c0402d000c50b80300700c5150ba64003d58100401c2e0714072070748504100e080c0140c4080c0181824203032900078580105036 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 497246052 1250 497244802 497244809
    0x61803030904090f0b0a06080d052506020d0e0c0d060b0109150201091205120a0c090515030f2203032a1119050c0607060902031c030506090112020405040606 69
    0x4180403e030458a02880b43c144000022a01c41070a10b000c1440c01219108100a81d128203009000c003903400c8a050701d4a40080ca090700203440500d5024001c000c120002401035407181c8405138941d00c600301c022065481e207004050b102e50240103400c0c0d13140da420a0905180341c0003280010b00c40e05240040b685480140c106401495800061078255581588140192802050000d03044201c0724421181c5105400343c00e2482464180440c501c000700d6448900c00440c80d041118401d070360b40340450748050b100311030301032840c001000b0881150301400c0c40613400000c1c8002446400e01c022200c00940d01d2240c03002c0c0415542c2d40c5400c2c042c07040300581d0591440504005c000717031204404000c1c400030514550303031814060156a9015006806100c01d80568070501604a2500300d0040c050711344c2044109076101c40d00c3e1242e680142e107040c0950303c241c2a0071210000303140c004480180a07250081d0213075002e0904070f401000324281c1b920b83c420301e03564102c4002c50191a80e00b450005000b1581 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 497247302 1250 497246052 497246059
    0x3060b0f090c04050a0b0a020d2f16090c021207030c02090115020106091e0e0a080307020d02010e07030312021e040b07060f020703020706050a050d02030f0405010b0f0618030309 78
    0x41c148500d14050b20090f100712a0200c50b00c1c412182c0301c940c414840d01800101c032003d079002040b00b0910030b01480e0703c1ca600306079040c081604202d070070640316400402519080601e4010710b65405030b006401e0803280140c16409018070000280321802980d40364201c214025401300031502c00205403013480100300c025001090b070615540c4610003402d6507005420408055032a051000418443c00e014080c0901c1c003102c0e90003946822050f00e4000350a04644e1085c071030141d110840c00040c0300102542c020714583c2d0007021440488107005e401c40740d400031160180c0c0e02115041001030b03880559821100c04000002d0703250486402008521840301040b0b110072100403402181010301d0700c0c060322071a07000d00c5c0c05001d480000e90700e0784120f100d08807001c0d0041e00800424400c0e18014802400c0300700c0d0524220345080c02420721138040781c205a5a50300f03502148000e01080c81400d001d80d0100d468100e0784200100400000140c40e8410341442c4101e82085803540400c5940502c10742d0203140000c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 497248552 1250 497247302 497247319
    0x311060f0408071704062c1c140d0e030f0a08040918120503061c0203070302060c150406050403122904021209061f150309021f09082503060b0f 63
    0xd0301c0c0a032030202580450390b030b4000c42461f41c2444441d0240902c2c0d903088090300f03a04005440343c00398000781201c410103980c466010442a01090420172400345602d88550f01c50140349404000c05050001000b01c1441360f0380080007010201d0140340440b42281d048020010710000c0008051840440c0d1074409041001403030f03140a0001c2d00030300250300c248000c5440c54414000c4801a0180c00a656000381d01540700c0c0400340014200400240241a0baa10440360500e00c80c891080c2010001c8904a45d5681c4400c2440308040c4c004241101c100c2d03030420103100b940c8001c140f581d8600c050342400f262050000540c1200c5480d141e04581d6022003c440000d402d00c3d00c50754084c6e03610801c0e990142042211600303180002002c610b40d006850780c148000c01ca044800c0310440142800c00c20503070b8811000039401c0c2c0900034084099039002425201e00780d2007032030040c05c02d0924841e0a0075000000c07440350403002a00c508007525065982c0036100150f217403c551b0200d100034106a12030354024005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 497249802 1250 497248552 497248559
    0xd02070614130b06030703030c0f050a080f09040c051602042c210a020a0f020411070b06090702010b01140c03130e011502010b0a030303022805070311060f0408071704 73
    0x60160500b40c8a024404483c02ca4891400341680ea551030310010f80040c98068800e000103500700f0242164502440480d841d10195480750310040d400700c9100003407080d0000300180c0506140c020030302d006600d402e100b07003412a40ca8418800c00381804000303100f507980c3c0c1c01d520740d1384a607551480c181000344450b41c51800c55a4003199504d00a40300d00c075441061142d555aa65120f0004664151065602820214925a0315004611410310049900685907100950340f0584440a40318080c01002c40d04070a041000600c94400800340c2680c00b1a41400790300491a40c10154985d48450f0708461b05030340c1e4048a503694110b0040f0049011007120f41d90000841d00c54101449060b1010900110310483c0c2d82c0b08240d089401300580650085038440741040424003d40c040d141c5040c040142144c40404510b0300440724003c660f08a000c200c01043d02c5040c5540030308520140380b04980144680d0600042d10f800c1c00c20003d00003001c0d030b1030020325407007084500b418140208480c10f034000c0c0c40c0da84 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 497251052 1250 497249802 497249821
    0xf021201110c01020d05180d20150a180c14031f090210230702040207020405010915080303040b0c0a0203070b040819031a014b080c0d02070614 63
    0x2000024171041e0400c0007062240340c500d8802581d000000c4c0007408140c5040c0d0041e512403081c0741c04444e404040c0044101e01c0d800c02c5c44603141c81510080380c4045440c0c520788100845030701c007142c180c40d4500ca1880f880080c4504400400380c0d0b0680341004a488606030000c0d1400c02416458243c1b1038041c000c0c0184c20034a41c01040601e0f100720350061301a001d1040850b8119401c4d0b40078512050102d100700030b079806240c001c00c800c070300103400589000340c150049020703100282d01030307025a503035251080c241d40da50140e8000506840d4014510314141500e4104003828040c0c440d0104803c0011107c13202e900802c202ca003801e40c8480099018505405c060303d55410540c0c42100c08035000340000e054610a114554610182d6090304903481c05030401100d030940d0301940001041221012001e1011a01d0642040d54400150712281c3c1c00d48040c541040302081c0c0442010b00c4000001c0c400c60303808580684030348d140100741c01a101c4205c0d09000001e0980441d80041e052051014130a0050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 497252302 1250 497251052 497251057
    0x706121e09060c080f070e0d050303040b0108160302090609060409050a08090108160818030408010e1c05040b1209070315020307200307081b01020301170705010c0f021201110c0102 79
    0x10b01407201044810380c4030105448001040307031002c54590b080000103098a001c0d000485588001900c0d05050b030320340c0d0380e07000c0c030715441560305503244034501c030042003000e90821000318005c0301031050310415860f650100c0d50a20000e807481d4401ca40310070018500380c440d13912901c043ea400200315010311070642820b02003580214072243c002171181e0002600804e5180c140b0590810583e102e201a503034802403c02110107988240b6003d00017000002910b5209007c1c41b00c4001d0b5510107001428410105549a0907524186100f0700c0805c3c0010010749c071081040d17902030800c01c030402c0425620307080003905020307542d00010810204480d490100c0603160380503610034003281c0c82e005100340c1c1d0480812503d040840011802c0e910400c9000002001000a41907110700f22f07030220114004038035000c0c20380e0003d07040410309040c44a022132002d101002800010503003030904e90542c10712500c0710f83c2510040c04010b40030340d04214030341c44c41000940c00340060300e41c0d001c100340e101c0c184200c0b0039020f035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 497253552 1250 497252302 497252321
    0x1303030306060305010b19020f06070914090f06091009050709031407080303010b0705010204030611090a0603020a02060c18100e13271707030f03060b09030706121e 72
    0x41c0c070741840031403001c1c06071141c0380c1a10410b50301981811030302c0c0c00c6000d10000000c0d500d811400f134040e80b143d8240d03080042d03500903052622039041e42c174100380b00703052b4510110441030300c40e0f0341040c1403040203030300604400e80041080d00c90824a55a244d01c88245c000d99038001075020740340000700000240e01c0b0700c2e41c405492107201c4043c071750741c0004000d5075117011900444145410401c010071068407803000400d2514801d00015003060380d0303504d60000f2661000480002d12800040305c0c0e960340b0b0440c00c020041c3c03c541c04c0850401008080007559a038000300712522415001840100444c040390b03c0242500c0c00420b1459051480c0340018030140075615181e014034007490405c906540140110b81d1007030419280c81800c8651081c40d2003409003c140142d82500c00000b00124075000c5500510500b4041e49031007908005107132000341165915802051010001c0c001080e5035600400c0c0074040702c040c0e10f0720030064928160007400600e80b52540c0540344c002c024104055842541044400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 497254802 1250 497253552 497253557
    0x200312010e0a0905060a050601090302130b0913030804030f0c1b0603060611030f070c08030711090609011202040507090807141311040b130b03330102121e130303 71
    0x30b80c8500800400f0f4071032910004006400242c00500724218540c001507020030140340100d4a07680d00d40124032500400b42c40d0f81142c98449103540c100c1c0c206071036100d400414850a217a100955030f100140141000741c402001c003c644020542c0b06849881070042181d0001c0020403100303074007289602210001d11880001c00e0924400080f060700403001100a43c040c0009941782071592414081c0c19803014108a5a560810801282c03150040002c0d1200c00c3c845c1c0c7d0070305151080d2600704910581d00422043c4a0101c2600500249a0701d1403031400d540c0c1d041d0340109079900c40040944000034240c03c521007034030400c00001402c540c0810b011070002016280b0070500300c140ca00b41415950b1032200c03100303081c50400c4200310360300340783c4014040400e10b00320403410551a46100040b83c0e10503a600080b110841c011091287d030300c3c0038000c5031040d030b9094080486d1503540020751100d030b0400c0c0100c081d40c804900046180c40b6403000c100056800c0e815240da8a15142d50f12001c0e02c207130b000032b400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 497256052 1250 497254802 497254829
    0x608090f0105010819060204080712060e0c0109120302152e06090b0f0405041a030d02060115030e0a0c0f080f0601060e0d05030d2d0b0a030320031201 66
    0x80c0d0803042c8210750580d089900078042202210504060414060404588080d801c1000284140d8203000c1c400281004000082242c0903600300001921783e400b03000101e58101c00b42c43c06c003982c0c010071110102d94140c5074030130143d5006d040c240d0410048140c1400072180610810017444401415102a5460292800729424802e260b8844a4045014400125403107620038826409158050b00700c2032074801080385819180c0340800c054a002c006142c100b400f980c3e40802d000e240074064482c18100030310040c01c80790314114030b40e140e56002c080c1d91000d140d5611103444403000244982c0100350703000001000495600c444c58030796100d0130700c140741560081001036090028003186650490340e103607445140e01c2c0e441d9000c200d20402c0b032490445172440100490590390516011b00441004070311030364400790300346002103d074001ca180f0041d422245004011076099545419102c1502d13090314003c40220680e110301011781400000400c1c1c4c510000c14070200c09074030501c00f6816034010050100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 497257302 1250 497256052 497256073
    0xc1e030f120902240706060f061b020915040921020d0804150c0509030105100806070302120c07080903060c070501060b0a050a0f021606030609050112120f0507020406060809 76
    0x741140e41c040c0c0000d602c125080302d101110494001c441118592081c1500e28007540ea907545000c44049900caa08903981c1d0460401402c0e0700a594440d807410b9a04281c2c096041c83d0340011001c210040c420b0610201e00340105006407182c3e44900b0000d5070107644512040d1008007141a03280c081a80400140b0400c6030752620b0510640045010380d0380b00c0381c81c0c1d030035401d20003400c8050705e501214282085014002100d86a4090180c030380560381110040040d60b041842c01402e201000b00b208041c9030041110031710701100d810b4020342c88000303c015582c551420345010f10962040d50b040b2603041c490300081c40002d80c0c88400600d080ca00c110300800007517941d62051815400303228080c1c0041002801b804070164080c0d001040750f440184150740360392800c032581401000e0329822050001e5500c10f001e2005850b184070b024058801c030180301c11f51090035034940f070100480d40e0445040014615031a4070460213181603805141d40107000b404042c1e182d43c80103002d8503044403801e106124400100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 497258552 1250 497257302 497257337
    0x150102121801030e010605221a03060412122a091202011409041409160501050901030c0e0604181821020709020d020a020d080411040c0905040e01020324030c010c1e030f 74
    0x9e555034100074018001c1c50380c86440b8003400110711600b25050003140c00480070701803260310584410500481002c40d00c0e0310609000f44440001c42d030035205201000500740002803d8403400d0750074030350918112108895030704191a0500642d10b142e0f4215051181600c0d502c1c07102d580d028403500443e0100c0d0342c1c0340524040c48060071407512401e03021440810801c0080d520036000040b1403405401e00200c01c5445801041841d882580000041144100c99100e11191405596a91400c81d9501c008201d400c1c0c44980c4400d103450300b003070114a080c01a0709500c82c000d0042000500a007542107443c0c103101210301010b9800111401e0060194119404d02e142c040c8800e580195000031400d05d800340000c05200043c01611600024040500000a01c5540324000d0040b0024520005038482c10700842985810300030015540000c20840c0342c2900584002031030340761410382407800b0851645035060060b440b84040d107888400048080117003052541101e4a542000e820b42d0743c040810072a031442 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 497259802 1250 497258552 497258591
    0x10212092107020604050d0609050a150b09150603220302031207171902121e010b04061719181205070f061d06150102121801030e01060522 61
    0x313600150a001c1070103141002c42d03126068521500d000190641c05444862030401030000440c2c0e68102281d40300c0403580e242c000e8000a08080d544480142058546c5030400e400c0607250b01d010343c2c0302200003490341612151503501080c003441050001c40c0d85040c025165842a020011a41d045001082c400c5100710516542102641c21440c10398403460b824010303c0d9441c01d40c0344001c07034081c0580406421000326890060010b140224103040c840690482803820503405002460400e2108001054002c15011b0381d4840305802c16601e0f03901c0451183c3da04070036107140c1102c00d152180343e40c4400104a0032428460280089a010301c910144c02ca810f8820450b0080c001900c4140290016465400c0411055080803000007403a03002400d00d0f252040032582e118003401004a81425541c0620078100c110842030495460522028800341c040103000c0c80d84d90400d65116401c0102038001c0d40140701409004003190841c0d15181c0e9404e030482d030f25a00c1129608d142030040e40c0791142680a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 497261052 1250 497259802 497259817
    0x20d0806030309280b0309060609040b04081312080a09080c0105070318090e1b030a0804030323030c0a020c0409110d0c030804060302120708011a0901020102120921 72
    0x452400e11501c0c00c0c006180131400042162010b245034000d60581c41e00d140c60058051844296100d26001210a2400310040c01c203d014180c50402c0c440800c0b00c0410060703100d50000452507803141c00550781c190207170036980007400c85690842c4600402450030001c207054006135130350a45813030f210042c10b03032643c0c8444246400b00c0c40070412803002900a5144c8148050414291042643c1d501600001e8902040440340c403034000c0398460550455809485111000c00d40050600241c80d07581c04503d03100e5408040c3c1840140a9940220000104940c108152200040d503c0c0e00303120f10307212001c2d042020103c0150003100c00d600c0b010b0809100e003c00454009502c0001000700801380680d1142c201d005607180c04009030003101041042e0014402810103070380060303581090304031b60304005502400c0c000c01c20089200400100c011601c800320601921144a90f80b0130456005034020705c00d04104102d40028002001030100c00401d00c4914224200402d40111101442801c043d2240a2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 497262302 1250 497261052 497261059
    0x1e020d180f20100c30140405040e0a02030601060201020405010507111c0c170a05150619030813050d0b0a0507020a0204050901200a080c090409142b0503131e030203040303020d0806 79
    0x7003170b105482c2c0304194426005102d81444d5203010344540c0881c003600c2008a6015a6900c00ba006000310b00b802c2141d04e00620141c4021414681003c1c0002c22600c210000981061703460345006100e556113040308a03240707010060b080c40300c2c0918034042e0760204140c070603a044210405110f1712a5103000c01c21810786640f00010740482141d00792003003850b650242125400250340e42240a0030051564a440610701484d00c030382d29505920315924080d081038226900401180103103034000b441c5000c41c1d0fa04180d280201213401d6582100492501c00000310180d4001c3c200703c01e0008000042d0b002e4140d0f01c0d00c020103521070039004298152135104122240c03002815250009a8081c001005801d40e0f0308010808601e000060f00c40302c210900048a00c80c3e29005402e07940c004043c0026100d4201c00004e188d00301c51803181c20040d249020027400c0d00030500343c3c9002101086142444820903000d100d580c0d00180d81c141c1070003943d075006404105d01612440c149458441e0080426911503100103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 497263552 1250 497262302 497262383
    0x90409060f0e0d0c26040906080709091a0a0b06041e0b0304020303040e06131103160e010f1b05160911030103170d1e020d180f20100c 59
    0xe03074407a503407a82d4240805d4134100f5000d4546014542c01c0000744001c01201c203020a9203400c1094003070600070720340d00400086192044400014000c0c1c019106c02d01071410060925540d1000c600001d440300f01c58150b8000c000090208440703100818a44610b180d004c4a001c5441e11688030218510080e900654554010b110411041003c51551a40090003922298410018421840c191343c1042030811800340040100b10304403d04090486a5542038500001c1e5002e02100203407009100131011001c0001a000145407a50143e62251341d41d9406421244801041400500415042d0144c440303010f040280300d02d414000700f02905d042c1d94211403680041f5100251a803520317801640703001c14a649400e51010201340c0483c010320008080303130380075942d104682d82002c200d5030741c0070f2800c1c0c0d4402035054060102c1c022011200c6a240d011525482006501040301c4461014850712980b10441e541550341c6954000443d079607980c8208441d244501c04542e00c441082e00b004926a003503a0403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 497264802 1250 497263552 497263577
    0x5030f0d090915050603131a06040b090610050f07080c0604170408100e0f010504050d0906020102190f0c17210405061506070b1501020f070f0902070602090409060f0e0d 74
    0x3080115089042d001d0200613a0703026944045054840307122014888d54a5010064641001c0c00ba00f10a58001c0703c104d041803900c0000a1195480b4084030b00030440c02160301009003500e039040b100082d4128107031a03114003850b08135664442040b202165010b21429504cc0ca4041e0102540c0030360f5580f901401002c40d50b90818402000a952503d803988581c041b800c160041c00e103e0039002e030707000f54060604d0001804020700104c0325580000704580c07042003400c0c50110b64002407000030301207142111305106041c004072201d04194030068889401d075243da2080317018460090a00701d00e2008942d207990101c81140c44141011100a4625044100010810400003084208840c8001d02041c103240d0381d511020310017042180c030420310065100c0e400321550303010070020030003813072800081c05142d050181c9200100d5072071086010301d80c2c000c1290781c04c01045805032076009001030b00070000140d081c100b0501070041c0b5040300303014a1500760706201100300414040100c501d01c0e19422400540e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 497266052 1250 497264802 497264809
    0xe06011203050913051311060a020304030b0c0f040803030a050105100f030c11030f041e12141005070819022b091a0f1608040f0c05030f0d09091505 65
    0x2d48030f4a6112200c031124882d001140e00c1914014401c8200000c48100d452806621030000800b02502c218010300010300c449074004112416294000a80709003a100c800c2d0500881c004e007285200034540126001c940107000001071072284030141c80034002a60303648140949104040d01c5e1500040404501d605079a020b6003203805c000700d26203450058120008100345c15038000301007115584c1400182003065480050907030070300c030400c40d0302400140d20384100100c440c84102e10042c2004010410803010401c14000c5c04c5104190751011322440c5007034140184508002c0711001e04c6c0701d00e00c944800c005240744c405c1c0d416903e4443c1000400406a80500b41c0440c4188079030414542c070f80e680500080d00c1c0040500103e400034004d200b00703042011080080c0413000701404d6200080d1042c0903c4154131202468015402c01d080e0745a100490410f40014440c50f000749805110301300402408400010b05c000d07405015540301c0c034a10341c130b0b41a5102030340c034104c440448410103102c0601044c0b4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 497267302 1250 497266052 497266057
    0xc06040b0705070f260a03020406030f0e06010303140c1b010807020604050d05070f12050703091e0b09010302090a0602031306110606060a020a0b0709030605090a0317060d1704090e0601120305 84
    0x1142d05d4184401851810584290740e1103142c071240000e4001c10200001d90305030081540310311030300c1428041d401401028540d00c1070b0510020342048108654507451a8021048805c1c01c042c00f02a2554000b000600d40c1c0c0b100e16a0352400d00040c1282d0004038000d2000c2040c90003140c1c03000203007043c0340b10003a0803586a00142c0c02a80e980c0384c85030440d000034a80300c030031a0301c24006456960301c07400c1ca8280a0152001688001620130159140c034040d548010810003d40701c040c888940c0b601d1400004a00901403400c00c02d4100300c2808001c9a404d030004040d061207c1014940e401c00340e2a01c2048892260511400b181c9501120109140e860000041c280c3d09030a4411a0b0760301c1c910b9200c0c00c4200714240c030040e010132242d00090007481024040d140c0d100c14603400400320090503550084c40c6240d1890000302e5080c41c02c010030020358588601c0a2516000f120311100880078540782e0030141d0052083ca40d116152a001400c24040414040d0403034403405d20051100302103403001da51a0713 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 497268552 1250 497267302 497267333
    0x110d1404031b05012d0f171f15120c090e040302011a03010b03060f1b030115030f020f0a030f02090604030b06090a27050c3007140f030c04020c06040b0705070f 70
    0xc0000c1c142000300c0804500c40e40300d108441e14000e099046020300d101035612542040300c0203040d46110701402c8ac2c2044807001c1580280c040015407038401241110401026007254051200d04024002856415008070b8801034640003843c020400a0003010300302e800780ea24154041c1c1100e80000c034000c0b0481c40300ca40c08103a00208032503080da050001d000690090b0400400300c9038405004040c02c1d4548038105c0001ca091004611300f0781d00100e018082d01882ca030350820140c0b1000303010f180d920141c040d5046050041c21140c1c032a41c0320b14011480324805c0310310b603006864000004050341820f000da0a0b0070310401509604100610500d00c40c10309000c0c0c0d09403034a21446c0c0c11501c080d114000312120401e400740c104034403031601000c4107124240a10400700c4c903902003d000c2c04420810144030070b8030340044805020703251811010034201000c103d040e82d44988045001001c484010809500c02d0f4070890780f0368040d43e1500b400741c504d8001d02078080c180c016407805013400540b03c06440c20a0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 497269802 1250 497268552 497268557
    0x60f041e050a0e16080f060f0a09020a090606051b0c0114131208090916050307050c01200304050f072102031c1e110d1404031b05012d0f 60
    0x8403050148914035001c0d0008130700340c000351034075000c01c0000d506004001c10040e40c10058805800c0c50510b9015916016000c000324075036540c41002159590308840005201215041c00b000750785240240035a0880c1b5400e0000c03c4407010540e080031401300d490b410a0b00140c41d000c0810749212102800c83c2c010210901450010b22008103000c40003a0b44c84401034441e41601e0b5450b00da5006104401002800c65891031842424403101ea94015041d290300501e1850a203845103906d0401c0c90241402100001005242045c0d0754401c003581402548100d014404891000202c0e8414aa55141a2140c0c09603100c5403610b0269561000d008449224001403c40301c81104c9008552020400741074490b02198901e0680c4c2d04d00c100000c81141c1c105480d04001004140714a003807a150080c00202508004204a01000580300c41d42520003840c2c12403007051800700c00110b070700d50304100c03801914045091400081c80c2c030040c07221028601d9007504d0042c0c11070107120406480816026007454203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 497271052 1250 497269802 497269811
    0x1206150d0501090c05150306030607050307020a0c08210f032d1e071d040e0316060b01080a090f0b04140a03090504111303030f02010b040e06060f041e050a 68
    0x800c4003401840c44a5005090000f2420300e454100607506d158002d03004805181071040200340d940110b400d079403102860a05664a944c0d80c1e1080782403e8134028014403030200040d000c80d1341c40b1300042e9240b28114078403070b42103404940aa603e005015502100c0c006503000c2000407040710034081020058500300d103044141883d5600140d4151000f111ba013981c603400d0700800300440900343d0443c2e4120000d03040c80d800a02c1c600c030750120100000070f4038a0050f500c841c0c01d042e01204c104110342d290400580c01503d840036a140040260450741d00c1d0900040200001c21060111881000010383c0e0001000001d1f61041c0d85200041c00000c2082e03904010551145031280e406020b0b9920561080da41c045207981054100021103060716003280307201405111210010744986418001e4903014101000c0c050107440c1d0403030144c52140c21054025003004200400943c0020f4842c0c05560200c94100d0011071090512044a4481d28000c20382c802c001a1442540e40a90040e0307000106901e0105 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 497272302 1250 497271052 497271079
    0x30c0a092304270b1504091505100b041404090204180213060305060c0d15030f1e021e130603110a060309030509040e03070b091b120615 60
    0x144407041540a00c0e00c0600d000a59003031490284104150f01c2180e10030441807607401001034a0076060303040c0c01410802c5400200756011030b2026048070200000f0014080d8884500d001e00d044050300300410803042c14a00440e4070380c400e01c103000041d10503101d80d403030506241c0104403a148158240050b00140e4821040c0056100c5010f112182a80b0301c080e1004c1071481c0c0b0600445424190644800d540740c2101440010360114400d80c00a640c038a183e501c8805401f010302c000c21100800740021412441e00108001c0796050316001036000713961250800314200280c1c00340030703480c0400a502245201036201e149010700c1492807081006401403c100c2e40c40d8011000300c40503a0015210111504040c8a1916041500d64050041071405000341e0105a8000e441d5000d00e01c50b00d40328548a01d95002c4e855803c1040d81c036a5a0404041001400d00400c3d29484010340031010503002c20300c009540c1241040c86040181d42c581c20024043c90b41c40d2940000000c440d101410f600001511341d40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 497273552 1250 497272302 497272319
    0x20d0f1b0602060603160b033103120b1e1210150e06031204120f020607030f110a03120b040912090e0a050402131d0706090e1b030c0a09 60
    0x19005024180c0080040d410400105860006921b03207a180710400307144140000000c030740c156030304901003001c108601a01414232401180500143d20528035200380810149540082c0b41c10002e450a44200411005001441b01000c581140f1003c0f00d00000080c10341c9091170b00700c00d00c811048100b07a0b140c0140001c01c2d203041d501c1d55100b8224880c1b2000080c401e0051080c500341d00140c00720300510a00130810450009406248141485002c101c92130106010700044000050b550003440c09944a0051801405d1449081c40000c005804e0904024107410002080140c079038154685485114105600da800f4140314100d241d00f250301c40c04130400194060289103104021511061107850800c60010300460004080130516802c01082c00090f84882c000d414030704040282c04030300d80300c021070390384010b443d0611650600c7c82000700002e0704962200ca6403084d0b9100410509154840341c01d03d0301e52a01f2003040300400c84c0100041025035101038002c11802c070103410134940c05961000070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 497274802 1250 497273552 497273603
    0xc070b0310080303131401021c150504051308030405150907090b04051b09010309140705030c04020901021518030304060605030f0a030906050703140705010e0d0804020d0f 75
    0xa02541901206211441001d40340071005090140021410341c5007101542c01081c1c0303103042c0903140441c1e181e00d40450703c10071f40403203581c1442202011081c000c941c800000a1a015100140c064101000842c90386447c1c002c090058203c02103030b0368100c8003901c0b40d150307562014000f20341c2c17131089030380504c02449401e084074851821000a000300302d1800d20000305a4600e040b5440c807991420082109441c6d10040c000c041c40301400da0182c603206c0030310040e801441840380242a60300c60381d404d00c406003030005285003501c03802c0d0140c0381032121300710610041e03008020080d40560081c100b101089903c08000c1644003203c4080200c1c9020444ac0300d03811030b44103a409403000c0b5210007041c80729007800c01c100c0c40d00ea10008000c0c20322a10f0398800904402c0c42d406145c003007003800181d050030716101d0785803d5607603a00003038202c0c0e4030190303450a98001c1070301000c076202d10302030302860286032390050382014481c40d009081600d0444407070303541058960341c1c4d60f811984001c0400b546074401628101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 497276052 1250 497274802 497274809
    0xa06120b0d08130f21050309030a0c06030c090b1204020a1205010b04050601020d2f1005070f170f191a0a05060a1704050f0318040605040603030203071401020c07 71
    0x14069907456040d074052208044640042000614034030b81000b4502c080607003007005c00c80f222007078500321684e85419800c40c0310f444034050f40352044808010602249000400407100551420048010100c00c2591540c61070301c40c0d480806401e02c96112404842541c01e944284010000c2c1003264031883c60700c00400309908243d81580d0b5411b81c0c580c3c030381054405c4507003016003400100300700d5008040c007d2003144108d640c2c030700c0d080e00200001726442040281c80c50000d400000e4443c12101c1e65400c03001098121203460004010700250b0000c280a0700c0380602500c007441c41210165541d641c9103440d86e80107814501c998000c4903151607484801c0c031441030798140000002d00d600c1400c604000002d8103e4100610520042091000d4284c000c1805100003440d4007a11a441c4e85608103981070130150110234180340000100d2508903d8130360300042000000b1981008000c2e250814803007201d040340401000759100300422004101411001303044000c56400240c81c050100340d109007086180c0d031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 497277302 1250 497276052 497276063
    0x608190201091d0a1a030606040903020f030c030d06090203071d06280f03020a0f14070b01030b090616090303030b0a170106050102010b060a0f0f03020f160302100504020a06120b0d 79
    0x2800d203c0f41400034001c103143d030703030740c0d5107010380e004c080c005c0000d4444101800c0203110b00e80d82c6059104040c02844501143c140d400d06894071140c448400a481e9070003029141d1b0454688200030890625a1094034003414442d900c000070140c01c514002c1126103603038060307544480c05208000d560601500719103040521001812180088c14202402403804041d080e0240742c01031010041080e400403404800f0743c800c0c0741c543d26945200c4041d00326031240500281911a22000100034881082e0a10f80182440412104c03a130707841054031a907030072880a107840010014202000464400d400c410b050007001010b00c000d00e540d412108001c049003440d06200ea0351252404c010561302882420030ad81400d03070700540b50824001009000d02107040600b0248091003005203035540c4240d06907281542c480310090340d101046100c40b0307080c0a0b603640407030041c070503008080d0b449240ca01a050203668064281150541800702c2541c08980441d002c0c8580caa42e400d51840551756070311389020050041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 497278552 1250 497277302 497277359
    0x30f11060a09021f0e06090d1202060f0702030f071403190801091d03040e0714031528090c0201090b0109050a1103071407020604030210120f060819020109 68
    0xf841885030345112980710103d4001c916200d003810b41c1d00314255440014003226226940c26990300080e6080d520080090304803c1055028030100d500012028058101002600c90a80e00c44100700c0c3c0d2840741482c0302214142c24001e42c00091200701c0c08544511511003036908190190490030340ea1135408440c179000980d0340340100b211100038491103484068406522854102003142d00d9074038411403054010b0025080300041f49035101c0c540030b14079000f50f190850390781d0903c5101842421403035003070103200716011000b1510416900300822b82c2400758001b481e028518042c0b182c001044483c0410066540b24039a44000602d03484c1c149000c0c0c103102d800010541800641e20003162400e4200c0588040c0070014800307a1070700a4ac1101c0c9140c041452150780f43e54500c08503810307008070350000b5000f101084c107262843d5040404840c40040300c00c41005a6017907064060306440641c882d09002d5001005125048040d81401c142d0040c0103042c000301c40c5940302e03048080c240c0340301840514101d90 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 497279802 1250 497278552 497278571
    0x302090a03140718090206040e070309020a03150c0c12080615041e080102070f0f0c05060f1207020118111f0804201018030c0b180913030f11060a 64
    0x240100240303c0003800508101030501781d03010031050310a0707000302d86042c4601000140c03034920a410241207182c0c05088041c070030ba641d25105994405a05406000b00d00303100c817850801d13201e010145842d40d00141000c0706221010419039000c0009091250480c43c2010124103c03a11480100000c21240540703900c0c4c10003107268646081100c0d0000c8207140d0041081d8404501d15868544205410075a00703c3d22544600d400388011403140d1045030007100205000c048420490050156448100204803407991598001c900703c803c03a00c0c0001841c00c4014008000c03403042040600b1803040640030286860242e42c50b1001081d141ca10100019035080801081000f1110291065640103542e41c3d1841d0003400012a4910410400400c01c24850902c988001c503955108d001590495038680604c2d07266106a4120b92000210012587c0e648602d40d6403820f00359880c500c00c820f07074010160b03c0760407543c04440b5081003070010703020400240c07400395004000b808224000c003060350380002ca9420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 497281052 1250 497279802 497279819
    0xf0f070f05011a191d09070503010606030501051918020a03090b04240c05030a05091f0203060a0e01030807111201110a03050a05061e040f020d05010504050121030302090a031407 78
    0x20200743c0c199101c02e0b6144c0c200704404035001001070100341c2e03d060b2003035540c0388107150303182c2582c0354809a403540c04c009000071300705c0c1c0503402b440c16242c095075035441581254105000341c001c0b80c031503101c2c146020b0002d0b1001800760f5000d040205c82505c0d0110f0f08000e903845452143c0c1c4d069130182c0d555a0a842c070310707040c41680503103c01400340ca0041844007500d5803501400710b00004001a14403074603000042c542190070301440d500c00350300d0244261a03107101c40400f00290070856203607001e03103011200480c2d10700001f0200e1b4103e0f5405882180751000d146e4400d0142c403950702030700b90007240b01240c2c0358225800380078413a100304608042d1605c0c0d06030306400070143c440240c184000f80d490030301404000d403264403036190203201101030703506802d00401c04680146080140144c4d0380d0b201082d0242c45943d10340010303040b80d0f801c450a11407030b6201e0307140c4000c0c0d40d0015400e07a5000c1c5d00c1894440000d0003600500b2062500500509030240c1c1e0791120400080c0503580380482e900003000034041d120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 497282302 1250 497281052 497281069
    0xc03010c020a0506060d031101050a051b16020f0f0909010e060709080604030c02061c0203010305010e070f0603090f170c0115050d03080a06120c0801110f0f070f05011a 74
    0x8100c0e100400c2403480585565499103805094540940c8004884200341401200e140640c030310b0041c000c1049287c08010500100f50503509400e03072071480b103644c8403108010802d89012039500c907a0411240c0b140d41c20440072481682d4025005130f458499021290303142d95039940b04428905c000710f003541e1503140482c20f100f401001c1c00300744418902c0c01d01c80703400d00240c0b1603030003076060802c042c010074607000080342c0b80100580743c200140316145074000c08082d90050740c1202d200d0030080c1308820400c40b1480c3c941e0380d40e004130b41c04503141401c20403a141c801d4121244190284031210242081a114120b0300180c0191403401d60000255441e455a000d00c2845c425807400340da01c00700c3c9414800001c080340c0342000003404101410001c0351100d12140d0200e4028001400010740c1c40180d032815020780d81c2c1c2c3c0c4c811841d05528100b070201c0b410380040c2c12500c9102e441000e180c540010b090342a0041d800c840d00558401c10b188642c54000b403c24400c884400d01a0310004107040300b0741e0100200c0a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 497283552 1250 497282302 497282321
    0x20d0b040510060f210813050f030105280608030f070213060302011d03030909010e010f1e050d052e0b040e0318150307050a0f08160f120504050c0301 66
    0x5501e420310810001107503000c54130079120700d104c160034050049904416a440c1808001c0d0003c3c000050740760f08200f445080750201d502c01d036800341c0304c52801030030103089403000c0b00e1060940e64031502d0300142c07085104081c00c01e91000d00d0001099074942c81c8440c516082030030f554180701c1380080d6040551031b00200b0100318034020307401881824207680c0001d0108018202381ca414241c0201100220b950510644010702d03000f50042c5265a0b48410030300c9800000e02c503040c03410191002c041504160b080c410303101003595a05039a2524985014414821015902a02c0e54000e50004d9030400310203040030074001c03010144500090f40c4200c0510100d49402044038416441e01383e040d0200c9a020041e9110000790351034a132001d03594180805c00e060300320910303440b03c09000810081c50a070050040c01298030550f8507210b9070711440c4400c0d142e0780300684042d01c0701da08000703422402c10304c2104546d55000c518600319080419804600c000d86d00203807000c80301c0d40c00c04840c0460303500b0244517200c1003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 497284802 1250 497283552 497283583
    0x120506060721050408100504060c0503040c0312120f06060e061312050309060a0224070519030605030a06091e0308130203070515090405060303090a061209020d0b0405 73
    0x208411691408401c038861860703502d51441c1140707001d20701809981510000c14400c82510b141e44602c020740401000b045900f1103449142407503420480d03200d40c080d6442250f00a51400506007161520072024030b0104040040100ea0091681028120301462003c944c0141000c1036040c1048401752240890720203150185a09120004800155000800031940c80d04025450f40c0c90038200ba0b401c503c030f010714082d084000017501d0300300ba580c0081d1301c082d541034203400c41e1401061a54401c5075088140d0b51500022000d2055440108802c0c003c0c5890741011f00f03001a03042e50b960b000c20704010050700705071015030b5544004030500000da143c1c1200085002610440c0816965014003a0311029000d210441540f424250842d2801c01a4501074038008094100030031031440c801050340c0c42040c0c00c80c0214103003000b14029080c00000e079044c4440040001c6101801c104084032040d4103200c400032034075100d40c032200158954406c1520b646000350840f40745480c113410468a445116800d070340c02c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 497286052 1250 497284802 497284807
    0x1a0301051504110906031311030d050324091006030e0304081c090306020d090501150810091a0f0906010e06101b14031c020906310612050606 62
    0x70600301412000d1000c9044400140391581544000514000c1210a5400c40c80002c103022801c1c000b80707c1200124450b0a80c90b440a69440c24140c0b55082e10342520302198003800072801c50201c02106000e072040c5e8030121001664800f0004914006c2500c0107012841c04007002c0c404150315010f682000d1466400a41c83c05180604055640d00c3e10100101c0d24038000440c101b02501c40e810200027150420803d540340c2600b920450020000650300b00c0e215860003082c0d02e45444000075020456400c5405081da80d020a04482c004e8644600c0c102d40f548400f1050840e140e4001250500400d03102e005140c8034a0703d411014a04401a04500e400422850030491566034615001c2000c013110b2401080014131145071111315000d0120080c0004c420111980e592140000641402030901200e1119203003440940001ca1140c07002c11604032101b0041c0b5101d980e845a18405100801d81085082002c5003028040e004c150360003213000100c0b118103040b2600d006004a5070808403c41d413651 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 497287302 1250 497286052 497286061
    0x41a070209150a0902272d0409080409020714071809111002010e16120b06030715030c08070801060828060603090b220807020d08070302011a030105 65
    0xc21004004042c0c2c0038019402c0e099030920340315003100e940140b5400a05544070b0420380020121100c2080707807018205110440307100946448185149200f1180d403002034000010000c00007486001301000340c026440f141450001203c1200610041104110061b110080e916010a24400d5400c2001455110180503c14510030f15038002d00003000c5038000074544a90b1808001580311451004d070b0040c2542c8954001c3d41e010f402003038141d01c2e070304199085900003002d1411140c0d05070240550111a0400000020f9086a05243c03c1a801421a80035980d10400d00c000d241c00b0390140c9000903190503402100c0c46e0440855a0054032600f810340305581002402030020300001c08608030309005000b601c8942c0c1d800203100fa541d5002d035506000342c2c1e40302c0380054050992304004a03a49440e80340001c003d4020350744003003842000d4180c180c22100c2c040e00c4206480e004031100380d81c0400e91628035400030307550000414000740300e5000030444003c01000c820030b171500d5201d10b40c020b904000422 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 497288552 1250 497287302 497287309
    0xb030105061602031606020a03020f0105070207140a08030f18240a1106090706090806010f05121203180c150a0c050a0203010914070b160201030c1b0602041a0702 71
    0x8808a0000068030300b44420b4a000081c0380c8207540d211248030428a4202040303050b804902490024000d4003266003c900a07045242200c00440d00d660060300480010b02840071044200c04501c40d000f00740352800c81e141e5074110b0650340401c45082210304001101c4c0c4a40003c0419159040411144c3c1d041c003842c00c0c2000640010650b186d052a0300000550b02d903000e0040241b0312915182004032256890015609036440c00d043c001c4c030021406000700022401400520f0230306a50180143d0104a841e000503c869034201428500e16401030300414100082c0030400355214014588030b0107004402c00740143d0500000e4000180241568050580b102014004035051000c07070385400b046284250600c03500f041c1c0000ca0080d859400d00b5401e1082c0000032000c2c41000501500307540106582d5810904c0511a03180d1040c00c40e405d018a00000d580039602001d049041420540200382144007201000e804408d000c503801e950110f028030544205084072108629440d403e1482c1c107840342c000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 497289802 1250 497288552 497288557
    0x7120203010303140304081204120e030f070510020f0105040f060e0c22200a0906050304050a03030c090306020a08011a0f0313050a140d180e070e041e14010b03010506 73
    0x40040d18100101080400031003100b21340d00f0044003840c0322034270700f49807503c135001201c0c9a4010000034101035050100e0300d8003043c410026541320b402000300780e25240070b010540800c070400405501076080718504110302805101c0c400c1d44a4070b04203810000ca407030304208451a690a00c4c500340d00a005d40d0104e500e131101d05544400400401080803038080c0501d40180c07606125040002d0b07000c40f464011064007002030400c0279801d442e00702d8119140c81080302c0e540030132640501b0707991043d000940030034082e03032010340d48500c0c610701758400319100c1e01c07410166844080e14500113074014004001c3c94443c85100f44010040030145442d140c205940b00805000c041d080c41e0404148003600300c00c01c0b104108207020385900445800c1e0b4101c4040c001c039240c0e09080002030114110510016508642080c001e041c1c2d00d0841140c51300b034030360312004c0301e145400e291940d81080c1d0300d02208103603031420340049448440358207005c25088443c2d50002100901a882641500310500040c1314941d07a8006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 497291052 1250 497289802 497289827
    0x120b010f0819050f010f0b090601020a0b0f040c0f0608090d180b0904090c0f180c0f081509090c04180305091c0609111206010501090510021507020607120203010303 72
    0x2e408000c80c1c124100320b410004540405990f0390301c0c0c006029200415900b18501d0300d82d003142d42e0302007566003000681c1c40d0382c1d0040c001014444600006040e040001e41c0058200740501004a543c5880d07550800031442d90360052404940340d00200807808108201310b0710048054541803580e240080307a80155912540202c041503c0c0114200341291102d83c03103000041d030044002990b1603550340e0032000c0020a40900c216031803003d0644410700501e4014041804010b40e02c00e11013502d003105c2180d202d4405410000001c8a10070318485d0b40d5903003002d2030b00403a50503001d0645250b422080004036030f5803001400c84c01d5070000c400d0740800d0b0000c0980d52802d400346d07504100b00c1b481064020a0350016880208101d00c1c2c00451070901c901c0f0f510007187d205007507680d000403030881400c0325501c0e0002d200740c6002420150b000c1c0200d0615800c60f030459420344c0100d500840070b986014400300c808494000041e17124804000059600c020081520380c00300b581180b4650654400800302000e090 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 497292302 1250 497291052 497291083
    0x603010938040303140a0b060f09041d010609060602060402100f050706090c061d1f020c0a14090609041208071b050601140a050d170c07120b010f08 65
    0x24000407020801004104001121020040403840c26140c098024640b050079610011070100010725114001d1242c4070f41040010009802c0c0395540c8503a00703081d03000644480c0c1207601c8101030800031003c940c0c6a0004124940045280390500a9031801c44d10154480c008552005040c4005a200c4103528050003a40385000c5002a107103000945041c41020001884280340200e44d505001710f543d080c0045d940181d070340c0c01c10b078540b420045046120552540da40f12915448503900300810340c00a070000c1080b1300548003900149400a4010702141d0b000b41300440710090240c100d0701d03041d60f00950000b000c4501c010141080c0c4c0b2100b4202d11414420401d0040702c40220310302c14068003581700484402c2024011062181c80c0c0a5120502071244da0401424800b241c0b501e03107800d02c4d240c002e441c0c02030320200c60070f8601e8031040c0c0d02401100c0503070f01d0080200042400000c0501c1004090402c980c03146006066034034080c021240160b1001c5140800c41805024000010035002040032200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 497293552 1250 497292302 497292353
    0x70803040b04020a0e0708070906111906110c01020711010c050304060c03120204060216090e10050a0e0111120f010f0b0c0106080712140a0c0e19020d0207020906030109 74
    0x14404071303c0b03070074440e000729008016820410800310f070f00c600854071035002642c07040c286565a000035070341e00c0b0842440760388541145a51581a01680b00c8500819004d018041002065010000c0d15944444d94800140c3d40000d10300c000d0150b400024840d40c0828644500603021075141d0549078001c03401540c041000021001050521440441c0000701903c1411503a407030f610034000e0b586040140006002d140c0b104000a4111064814980000443d00152400680b019403040040c60010310110046a88141c61000c1103401d2245400c04540d420000707a40f04003500004003c00d000170007509503228a0001801745001583e001400c45440d0306000d80c45034210100740b0301400480d04a0b110f01c1c421468006070104424101c090070602507103450010314514030100380ca0b400a0715001e001780c002c42400708221090460841e0780b1142c0525011350b01000240c40c0001d03640304e10004046a80c0207d003010551a0801c00550491022002013190015540d1480341402c5e41054204000041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 497294802 1250 497293552 497293561
    0x31a070c0b18030d0603060c0804081b03070515042f09090109020405040309150c08031503070902070f141b060a02102f040605041503020706020d061a070803040b 71
    0x40941d216040c1c001d01c0143c9888101035240d030002428644010744071141000b440245243c011190103010302e40018996182c59a000b20f11a54400d04a21805052008004001c04600d05226035074503503031440c40c2e05109041500301280f07051410b0841100e4160810101481c6018026030405050410386501d02141c2d900a840c500402d61040c0194005042c8005c100405500980c040701741e0f0720545070b4520341c07046040c0440e800301810700000d200f4001000884c20900031401000610100281150941d940329032040050f6040038134100c8001080003116410841141800400c6000c40401403070081031414403500c058800c022001d00440307000a10140d180d20a11201210b03c0c000034003400b4010202c1a40416001c5a0324580c07658020240c140031520090800c88044544030b070307101d40c00d05003081180709807204045d510109055082008500046150001d05082003d4901c00250245400c01700049980c0c070b4907145540c40d404011383e00010b1a0142541d80250300400c40c1781c410360380d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 497296052 1250 497294802 497294821
    0x3060b010509060c2a0a090902030703020a08011517030a0309020a150c050c01020c09010621060603050610050a120e010212040f120c030f0c11060c07031a070c0b 71
    0x190aa42d40c1c2c2040d40001d552080450010b141608001c5504049100c030030340c5606010b092030340e200e03502ea004101d4141048665920f81064103100c1c0000e05071044d03035640381e00041c80c008480c0d0041042d45d4440c00380c00c20040c1c003d0807200007402da40c1072800c02d100f541e80c00746c0d403a0b11980d24220285542c40b5400b0702036483d941c030352001420016141150a880c0480d01600c0401c40d040103d9051241c43c941c818103500c0810b41c01c1080201802c1026181d080150540c1c92522004290142c41240390398107013410014080c40000700b94588001032a410404148108024103130400f03000d02004000d421001c680c490105892100c500e80d00041d403124201005002e0303c1581030039546d41d5071ba00140000d0180ea1078070018018405c1d082071280000c0d01109554419030b8503406000f150403103049218a90140e102c4042092158002d4841c20410f0000204540c02003048034546502c40d4105004002c1c0c2d00024220b044070111013200c0c10700e0049401050f40d0452140244003040d580041514100d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 497297302 1250 497296052 497296057
    0xa110a0c06021303060c032c0303040f05190b070e01031e18020301020403080901170105010e0d0303150b0a03140105030a081b12030f0a02190f021e0303040501200403060b0105 77
    0x150b1280050101b41d80201000b0041d100461081c0c2c140449144c21441d11145d01855000700507001000c0c6003135507280c3c0c0b1181c0c100701100750255400d020783c0c121051503036807900b0040c4580d403042d85441e07520b040980004191842c02e054017418545404d16000e440e20f00440d140810044184000c02c08072500e1515288950070254001d4066001140110400c00124040e00c8500420303a5040c000b01e411800c0c0702c0e80d41e1400c0c0b041c540860302044008403a410f1031406004694000d040c003141c807221201041520003100e60080d030a1000124800c8000340d40340c000c040101581c011010300b03950400c0002074841c000b0b42e40080a856000400881d140b15203054dc14000f0400401e0b01c1450040c0c0081c02005d0f48101c8034131401d08081d100140000841e442030700d00700040100900c03e002220001135607410f0901014409503c100d1852602440070b0700400060f1000001c00766881c0d00b05443c1082c25142140b0006100d103804044500400c00d03030b0b505441c00c80760880c1012820302c031013000580307041c13 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 497298552 1250 497297302 497297309
    0x604021c0b0a0605041b05030f04020604030f0b0106020f030403031b050f060702010911060301080318061308010e01050603010b15031905040305070b0f060a18140f0a110a0c060213 79
    0x400e00c1c0030400540b100550703c40d03c00c40e80c0590b014800400f81030a00122103a0710b00405c4045282400407580f44000240802e0b48148040e203041d14180c0c5039116122041c51424049aa00049400521841c0d40c10b000008409410304011401c042c210381c0e02400e0700c0c5441c2100c41a1901108000301844800c110030f800c03208254050382c3c00d9060080000740a064140001d941091111038924014240b0a084a04a4400070082c40c1050070030710140a01081d0425403641c414403d0108486d030862603c1d1803001440f442d000002c0080d61803c80f82e003920070041516200c0d0745860034148241e190005580e1456000881c2260340780d8484586002e21100ea480701d804061400c0100000c054101005000160040c41003006550300c1c04481c0201c40310440c1c2c0a03812100c2c88104104030052150000310f404001c10002c603d000018150000f0040c0489a0130807000001e018485010000d00c130b07400510703403e400003901d48190683c0c0034000c0c21394800d00a050329070001302c034504651443c2150015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 497299802 1250 497298552 497298563
    0x1802070816050f03070b010608070e091608061c02090903040e07090e10150c02060c0d170703020a020a120309020a0906150203090f060c1501030f14030c0604021c 71
    0x40d900895908001c4030244081100d45210300030100c0100540001901d6440b94020315031200d5a0802004070341d04080642440140180352801d61202d60701d44206a00c9028410a8020098200c19000340007000c09013403076004a404002056214079035900a0069640640c1c00034010f0701c03120f15192840c8220b5128009c0e100f221400c0c42101603005122404851800b24221255101c103a131103161503003a40715108400782e40c044009940d90260800d0b01059000a100900740500c0e2041d190034440d0505d802c0c1c0c001514031401e83c00303617001010026006811481c003181428560301020b0b50f01c5d03113081806080c00c3c0d0700d00784280c003082c0b103600030840349030380504030922403a1345103c0c1902511544c05800b41d902c424070081c0750a00d10000980f912540018031040b10070718070a090010342c0c1e016620f0700d0311502582200002d600b00121405009522170549800d01e800a07040802003901b4602c80201c50307800030492108078000008060380c0080c1c0480312001110a4545048417440703040c60010700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 497301052 1250 497299802 497299807
    0x70c020d06050c07200108060f01050705160501020f0f3a0f0822060522030e030c04050606030a0f02160b010503070602030316030203060415030501020d0609050c0418020708 76
    0x4a4040340405044c0c068400c8400701400070180d24103008400003550420300060700980042c5072031800e140b405505203c1814100c2c41c10905d611040c1c01c043c0880c02598031207541880402403035a04004400307100c000d02c1d01501032280d13148641070322480c03922000d003150201000042d03018195107481c132262100c1d480801c040c51090171000b0700603040070b202e1035020414420000307000c0e2911300d14480310782e040d908030380c0360018a59691100401010f02610150402105580c2c583c0786034040c1005100d000f61207041c0000d2000082600d045001501c142c056404c103c00d018240d00d41c4415203070060344034200403a800c426100010024001e9611100a00702450b40c00340030300c0b04031403011b8181e400c15015a10655120742e41642e4900c003c2d28211a10400049500420f600c05c1c0d0142d600440028404940100198452100304210313400c2554240d50015504403110074501c903100003400e240806114a18001c074003141c407809071b4070030708071690b4900500f4150b16200e40d0454180580c02200d094 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 497302158 1106 497301052 497301061
    0x1050d090203070605131e060509280305010e0d05030c070515040b0a051b04060e030109020a0902040807140a140d060504030519030b09070c020d0605 66
    0x85003562004014016582440b81d2001409590381d140c0d214482030b80841c410712160b81c8545050307000c8204095011480c80c1440c03044502c00c1c00e100782c841034014089029042030407040140504101a540131440c51980000c007035a010307100070002c40c05000045030341c41d0054042c030700c04604207000081c83c000844000308940791182d415100a034500e03500c03180e0b0482d800d6034110340d500c0c0340c0c00402076141da03a0300c201503014080c241d885084c0440c08101c3d4010b48a580640d0040091a01007003c042e202500449595503002d00404025661002c4c9503000390081e006607400c86c000c2c581d00060811107041c42100f9440014040d00d01d4900d402c40e61034401709801001c40d0404130450200000c80d58612410707100d540241c0b07030f50340d03581c500300550142d941041d4890b07014903141c80101c80468842c0380c02c0c203178802c0031800c186401d52a6800005e2800c50358240042400e81850b0410 = true := by decide +kernel

theorem cover : BRFrame.Cov 497122302 497302158 := by
  have h0 := BRFrame.cov_init 497122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 497122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 497122302 ≤ n) (h2 : n < 497302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
