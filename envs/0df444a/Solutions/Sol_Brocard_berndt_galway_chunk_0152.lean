-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:08:05.421718+00:00
-- url     : https://prove2.me/submissions/e2be83c3-21ed-4476-a9af-d6b6ec620335

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 27158279 ≤ n < 27338135 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 27159529 1250 27158279 27158291
    0xf060909060504060b010e030c0d02040207060c050d0f0504080301031104111902240103120201020d050705091e1507020d020d030309020a0e070207090c02210307090618030b0403120204030501 84
    0x804034522405c0e42c074910900346002e85500140100b6150804156823038410122044501c0543d00c3d550100ca1031240c0c0b00c2020890400c10900240c8a508450b02440340c05103810b010085445440c41894021a00070f03c425045030301e1aa0b8003031158146007641600075441c0c0030a04441000700028010208880e54042c29400301910001e00c0c080001004054240d81411420300003085642d059055036044050385c2c240241040060307002e4440c0711a02c40c01e02c1d00d881c1c00c01001aa03c40d01411680c4000c84400c2c1e0114210884401c0300760321140c5c21940074030005d9040500c111414002c2140500c054441b44c9282d1440d0000303451050048c40c10780219807100c2c0c20b2421403411071800c4000c2c102e0034201c01d40c54244200000d41c0d4003002d001d400c0b1003d503503010b8400c0c45030080202840c1003001183d0800e070304030040c0621a04c0e808c00d58044011130103c90000c143c1c0e9015203030798400441c84d881138a09545c5181c4911691203c00b600603800e0249584a0840c0d050131800204060740c0120004665 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 27160779 1250 27159529 27159533
    0x50106020c0f1503060402070503070b070207090507050a0e130b03011d060906010b0f090d150f05130f0206030606040b040f03030207050d15090819110d050f030a0f060909060504 78
    0x61084088055215400c000180340224603c40244e03500883c0690f4010b8886e512460498618410000701900e60070801c010051581d41c00a14407045c0e60000f1f10520940d10398007004d8401d8000c1034445000b244900008040303d003041080e0b18207600400a01040903036100010a0031550450350f0310150f6a0b400d60b0602209008010180e000030b0120000c000780e40c03501c9414029401514850705a800c0006420000c3c0d40d501d0b80e080300c29917001404c1c40210a0425880303001491003000c56013003103080c8000210400803d0001800f0681c00003028101011280d080200640c4002d0078558410014800480d0762611440a0000707014044081c004160450030060f150840b2580041c0c0b0403c048030791171001a4030801800c1110704010004602c0349813038641448103004540d914465400f01d0101c1344195035212854003100c50a0304282c840400100708222124400c041ca8941c07490f201700080343c20400503a110820943e10360f000020603d4440300c81d40b090380c0040d8000d8402c42e4480040c841 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 27162029 1250 27160779 27160789
    0x216050106080a020a060503100905010902090f1903020111010e03042601020414060304050705030f0309040b1207062703030c03080a09020a05010302180a030308011509030c05060d0f050106020c 85
    0x240c0100001080e0750036951307002891854441c000c100801030040041101c1c1d008056041020f0a0881e03402e1040390307121880711000b504813030906d40c440e0103552103511940c109000000c4003802c10510b2648854219001560030000f4100080800d65803401d510711121414405000a8005000b0524101c810000304010303428031100c031100164070411041140220902ea80710400f401642c40c1781c0ca03640d940c1445410410755501039138060041408276146084003200134001240e003280c0810010722604240699107039aa458002c0d00e904c0f0039400c0c0302c0c080c0101c0110b928150064000a00046c0034134008081d255550700c103c01007558601d640c0209a0454402d03a0722091000c0e04000009440d00002d6009005118240c140b50740051100e45100540144e98060007015007040845980c6e0b1900a014500922401d0030b511883c141d83d0802da4400c00c1000c0841ea0000c0c40b41089030309003404c000c00c503070282c40260041e65032000850881001e60061034001c0c03c00c1d070050020500f200050003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 27163279 1250 27162029 27162041
    0xf0303020d0206010b03130602070c182912070f090603060b011b03030c09050405100501021e03041a0405040e0c030105070201020906030109020901050705030d0b15160b07021002160501 81
    0x240543d080203006114641c2d102060782d0740000300f81550b407000710150501d03c0080c031803007d0250141e0039400c40440e02c9200007500c800a642c0c2841e0810040fa0b00d070000021420f9103684594103110000039440443c0f5003050b103070490a0010f010340c2c160701d42c3c4100c0400c042c1501d62000c0c001c2030b00c42004006105542c8a142101c600a00303001012846220b0038680000d003609000b018160303605041c003406882684d007039001e40806482080740d41406001141c1100d030794424203005228039a035035181c06411503111458040340c500298207040c204100d00d040b070a60b03564821400c85040c08000b4665541d401805031162145000d00020400c1000349802c0d1000181540d05681c0104a0001162030380001c80341143d80d145c4005071108a4980121034611910300050040d03c0041003402c1aa4000d5104101104044070500e005e003c0400590801d402003240d500c010f1084080c1010100d90070110140e0701410034419542e541c100d0406510898011005c99540c0009005900c1c0c10080244540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 27164529 1250 27163279 27163303
    0x5030624041719030e1201020f0403060204030b10120b0a39080903040612060b0c06090607140412050c120a14060108060c1606020304032a03120914070f030302 70
    0x1000030f85180303803400340803c2d01d00e400140c0a60310140980303603282c40030b5043e19038168425060a07940c45c1d50341041806074205002c01d5441c681c0c00300c04503010143d5070f44902d00310382c4110080040e4060980714a0341d030000041c444000380343c0311031605d4203412607010703140c131041e20904c4041c5a800d101542e03054110060b080d404103101293f020b12034804c2c00041a24204e402a03e494207001b44214018800303003019600c2014480b00100e0b82000d6614041035040c480c03035050040712010703034844400f00d61110129040500d0000c040105004c84805612048801405102142c010841d1400820030f00c080d010407840213500006505810800b004d012242c0010017a03008040c0365040a04080d255100a4040c8005231000030702031003c21200360126290f640c02c400119100d01d02030401070903a44503112101ca46c3c1d40c184034815981110483da622045426039620a00040d81904010061980c50001d54468490a02d9004800410044840941540352440d4602440d510380a881c241c14940d83d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 27165779 1250 27164529 27164563
    0xf090d0201050613020d09050a03080103050d0801320a080c0102010c050306031c120c0305010f080d09091d071404050906040f020d03050403060c080117070303050306240417 76
    0x50001954481c041c0c2404e0b4000c3d0000140e8840800310364034000c1c038041d84020098011440d0510031300d904604e219040f2030040085d40c240010b400b208403100c0ca001d001e140b528040c0070212007a014111070b460240880a02084103035070000b00000b03002c0c44a50f5129021a45c00401c400c40c4030750703080c01544480e110728207019086041c140c0010703072126420340d1002865a4032400c00601d143c498903220001c004500c2041000c1c210214004010300001d008000d003441070307c0c000045d660000a90408480c40b281c1d540e214040c108416080a4080854445820000484a0600c1743c805120703002c010300300c0303401c186e402c500c64105210980f200101221129080305003000046100c50034401a03403a81200c0e9024141518038080c0c03128040c0742c1001c3c205503d4405001c003510340142d4660305039010039591006a4464020301c560716845400000c0028000748040f60320340c28202c5041c0c0c030310002c801200c21005109000a5103540042d4803101c0c140381c0c0c100118202503001e06c80303e040c194503512 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 27167029 1250 27165779 27165781
    0x18010216030b0f0a0615050d0b01050307050a03051005180a0b040905031602060d0203160e040e0d08040602040803030705070c080102030f060d020f0a080706021204080d050c010608060f090d020105 86
    0x55aa002620080200454180541c0000c40d0075041d0740c020000390860760b1b058024440d40c44401411a04030340c514011103442c00f5401c002660181080c1ea10800b0f00d0303038400b403a04211010450140001400308441c06450400210707481c0e0314140d00c04241805c1c04500d521502d080340905054480320b5091900641c07909844030040380c2c001c01120368112281005000851862010400a00c1160704088549102000f400400004103039110200d404540e10000c54907441000c220442d04d0030300c0e4600250b400001d00c1e90000340603894440d4014060000141460b603902c04d801e041d079000301c0d800000280005028420400140d950348003914400008500314980b2180f09031918a02900c86c910404148401b94215520081440107441d8080c1000c092550744c5d85815071382350b038180580070150042d50325620352100c0070300540341103801c4a4000c1c0610702c0e0030704064030360303600c10707882c00225548910022a220200300300803030050085d07581150b8076183c28000c0070705040c0050004421a41440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 27168279 1250 27167029 27167033
    0x1305010b09060120120316020c1518010203040b03040303021b0c0d080706020702040e01021e1303030c0c15050a090909020108040201120e061816030b0112080f1801021603 75
    0x120035881d030076a1350010001590f07800a00d55240007002c0d0b00000c0f0707a5a000040240040c1c0f0801c6020075404181c0031944003000300c400300925040e40ca800c400c2c03020020301c401c01945141c80500c210004041c01039a15003501d5240c8111260b000301d40a50100e03800080d80c0c000b4407902c1c8000c00314014600e0181c00c074a00b0610000e4028181e010015113289400329880b400d01c082e5504071400654010010030080c22041840c6010f9084840d11084c800c0301e981c0c03000c1c250041001150603010404c0c0841d0802811680c0c1030700c02050801098464609217500071400700059040090070050b25211300d80c030b0b80101c0ca401007a04206422000b0014100200600113076080180b1a4006509003015100c1c0c014106403500184034010340a0094460603081c01036481c1c19141036081c0d500e180003550138243c140f100d0003007803c440d840024107a204080042006d4182c00c0c41100d00742e8410508a450031807214500052a0000d84a2080c3c000760b85941014542c2c04000c104030398090002119804c81c51030f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 27169529 1250 27168279 27168287
    0xf04030308180322051c020d081303240207080a03050a0b0312090a120209070c03050702040e0303060a0e011206020d02070606180f02040b0906070c08061305010b090601 74
    0x1484020103001c0d01c800850341c0e94010300400d103410803410b001c4907110301c0302e11921403842030010180040c0e4420711201040500302040303c078510150140391004200200c0e0309000201020a0040d02d40071014000401039030480c0d2003940045010f541d00308082000201001064185c030341201c444144108209000105148247e5004500c6420000381950302c150060f0301601114900700c0c0e050040c011070035400366804000c0c00c0c60060684040714805e490384488440e02c180307060040e52000ca42000504118801e07800003818503c64905a0b0404950303501007801e440020204166541000c4100a268201110718800801003034001034100d501d000c061100c1414606000780c5603907000208400b540b41ea0b501150919588a40c0c20445030395101e00540910128211107510340341444a051180b80039070007642c043c0d9a050582505e040c1210302004100c0c2d0001008956a8030310000001e060030301801450310036030020301503040d0301c503c030300c2d1050031101c580c042e0510a207020350605c42241d0b80 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 27170779 1250 27169529 27169537
    0xf0509010c0f020d0c08070f050f06190e0402030f0105040507030504020f010c020111030d0207021002010b090703020702120708030a110f0c22050702010b040b01050715050c0c030d021803030f 84
    0x1016900700030b0003900100f0544000b915001d81040304038a80040d056500181000032a80c5443d19030343d80580f14000c01c4604004104400e9124106101d407011000c1240c201c5000c18546040c010031412042001c1002c3c3c0c0c0088811f100c02c030090500400403400c040c0034556010046280801107850254000b4090003500100c031030400c0b410f0b4001c0302c01c590207035140c0100000c1c9101225200c80030000b42c3c001960106104034007a090008040704114014010a000c0c0040203049a04958440500320000d401524099a0054021031060404141400008041c141002c080c56485289003000340c21040c9900f0014600e900c19910011a40808a11428405811180d5013891544119aa8110401800701c0024140b81c6024414120b80550103001030250550302440441030601c0191214068110068142c0b00700c05020100c82e410365104907444040d1100c564208103150580500d0350700309004a9440e00d0f400201112011000c000c50000803d04400442c41c000c0d00e90592016405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 27172029 1250 27170779 27170783
    0x1c02030c0c15010e062d030c0d051c05190c0204140f0109060b120c03060102070e07080f0f060105090d020102030f0a050d052a0a020109081c0608010203061503100f030f030f0509010c 80
    0x10841211b91602d46e401d1110200d03d05000b05904800921810035a450341c1d48020310580c5521448100c609050090040d101c40c2030030700300421304181884405940c0c00712640b03070481c3d010b0794400642400c4c0302407210320381c0070310b0100080012540c107240c24403003100c403680c000c440c90710424002107240104000381c0b164811240c1980c0ba4480d00c440c00140e03c1d1645070740207a004800c01008110419501c00c54041c41201441c5013002640c842502031104400305441301400200704008040040c20410b940178151441803044a140084400c01070307003075400c107105010001e80c00042c0c8011048050041c180c0141210b0b40030f000407041194202271401d0b125844003040000441d004602034000c0d4410320403140c001034001e80d0380143c0d050311420105c100c200301804d5440c00c403001c245581d05109482c07080001030441140e200d060326001500b40c0005026010035600248041600404e600c01c0c840190300c15525081c0b4608146806805040c0b1076031071400b004003c0c005424940e03809075030120b1007a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 27173279 1250 27172029 27172099
    0x8030403020d14060c070605060108010608040f03020f030c0a1401050f040219050a06030b0907080606090d0c05060703020309091303080c03040203011b020709111c02030c0c15010e06 80
    0x5a0707500c0d003c901d06040c07031010360542c041c0c0380821032000c01e4100100a024855503080100c2e42c1c400005480c00e2078207014520000e4036640020300050402c02c400004117000b80104c80031780c444440301c3d9286500c690700412540c1c00c40800d4800700050804500e81080c82c980c02880540342c2900c00003813081d030007040a840b817142ca41000588080d4035000001821000d440e40038450b1321500058064080c00c6943c17401181030304005190f80b40710b00000c6000705e50080c1080d00d000d032820100890310586807415078003210106800909940c03031030000c220719031180d0003441d00c42604100300603131080300806007281c2c44044220840025445000c0c160320140300c0c882e80b034403a129030022a0041222051290b0182281c0c0c2076001440d400290391012070312410000d20540d44240c01c1c19019010309054400c50b4520035044100038002600990340c82039100d41c58504103801040c405160290314185582c214411100620102d044005501d03070001c002d44001454505216605880b401c560004104007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 27174529 1250 27173279 27173299
    0x108160b040803092202030403080402120c150d02040509010e0105030106080d05090112060504090f1104060305061303030b090a0f0b01030b061903060b0c011401090e06010311150307030b0102060604060803040302 93
    0x24805117006014400d6240004540301c0c906031402604145050320182d226240e043c00b0015150000030b1000203049020340314802100c000b0340f00c87c186030005a8007450f030701d400b4000410951904181c06000701706c5085951190351501080c542124455080050a0382000c2c0c100110580c2240c210f030b201d90001e1034107607105549a180d560040146820060388076080101d1a000e000d1009a040c030301c213000d0143c10b0740c01e140c1c4008100071107000d444010040d402c000b00081c0d08122103046083c0c068001e0501040c1a150080041c1d1503490843d0b01c1c407101a602e21419161408a11400101200a0800b004000030300c200040e083d008d005e410250b01240c2181ca00d07400c40c4a0b1f00300500410b500c003c0700352038800d00300e080c40c040c0c08820440141c40c01c0d42000019030564500440142183c440041c0a2590a50304e91203000c3c17459001c6503401200b40209000250360b00b40085121395501e075000180c0f1078030a00024140007026000e9442203080c8041807143c404048100c408495040f5111084 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 27175779 1250 27174529 27174559
    0x603030304120f2102070c0b0310060521070f03050a09020d02040203042102030d110901140c030c0a0605060906090609010b2503050c100504080403030e01050702090108160b04080309 80
    0x70f068800c008034a0080001e20341c50070130100c4d4010303207541807256080010315616450303510141e00045035072810ba074800d0b50003000240c1c05040101894001401c00d106d400301c030045e941c042c041040c1d0340c0d0400600300d0300304140300d03c5e45481202e80010017070380b0620004003d0740002d0194054100080d00c2030f030307002010800300420f0342d00700500c580d014000110203c2e24518003a4880d0402d0300c0c8007081b0360401095612050744041160310040051716644140b130020503044025401c402040300b9144000c008811a00d5000c100c103440b402e1280170041140c2c6010301c00c5c1b114090000d07009030f005031404802e21256a890b840c5150650b003510b00d001361502054000d00c2042030a0200d2180141c0c0004464401d05901200505103e00369030304445600c0c40d0000040201d81c0101c501810841c8140300c10700000740f142c04d4280100e034052600a052400b10780010f2410882a0312401050b84848103840340d441c0d03800700d00e03401485051041801d152921440603240e101d042d040300d200701e41d64450039075 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 27177029 1250 27175779 27175787
    0x20306070305070e030f030306010f0302030f040f0309080303010b0711030c0d0b0703140f01080708030708070209041502030a0b040605010302070305041703041502010f0b0a030f0f14160e0603030304120f 89
    0x3003c6100102160b04000c406d14440740c4940c030035124140018149000807024034000e000704c0703005044d24071400b6003550711790321400e202e991507644c11420003a0108002510401c200061406800240d400319980c61a601e0700c084041d10508109009030425002c041c0150790b84402009440d030459426441c607510000b00700c0080c030850740c0808680e94400180821600c1590075113042e91001811280003645684c0040da49000340d11004012a00800a400040c1450340c149074200b4410038440e8080d0600c01c440105030380086410024195070351141c54203900c2c05000b407400804082c00d04515000403920300500c42d00c01c502442c0d45500030a020294a903204204650003060000c84124101c130110b08000e02910300c024030b0010003400d24500b02464a02003070b0351001c5a40c4000281c0540b401999102d05401c200c08054440320b0700340070340032080fa100f07010400c1c01e0300c00c840042c202d450510100b1601c043c0c01425481c002d0340144100000100441c100d4002003041b401c0c0b02d005027036030f944112 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 27178279 1250 27177029 27177047
    0x15011b06110c0f03030603010606020105040b0c0c0c040204030609050d03021c1a0d0f0606060f1709010e0d020705090109050906040305070501090204020d1a0d030905040b0112020c070e100302030607030507 90
    0x20144036510000c01c02c0f0102002450080b80d0460003480056545c0804900b83c0e981a64090503081284010882a04001e4010300c090000c803429a1400c5c0120b0001030100e0f0019402564000e0f2a01031042c20400d003803011800c04000d508045040c6009548507606103100940250015a03903032490300300000340308003000b46000004000b105140180e241c0b1034a075659007081122103508000e0081141da000303840c44075502100b40d841c210500e061184100d65028040c04860040d540d90100b512400c40600c00304100c05e05c05c1d0001d000c228501401d11288043c140d0001e8038962404052140f0300d100031821503001071301480c1142e1035401c0c0b414824010079015200a620510004281c102d20300c042e00084041100c007910b04814000300303428030400c0d90352194018002060305074213220030301d080c1d8003142d000d003810300d449541001d070541c07514202d0740943c00e4000554402602044001c0c94004120750240c1d804643d00389151039940800d94903074010340300900b8180c40342c0000342c4103441440c3c00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 27179529 1250 27178279 27178297
    0x12060e030a030b03070b090906060306010c0c0f060f0c08040302040209011b0b010501030c030c02060a050c070f080c12040f0b1b011d06090705030613020103110f0315011b0611 77
    0x150780d03111580407016008049121009009000311400021501019029100b0700c12000e0403041556580c0b1080103c0c4d90300c000c040a042c40000307000c1c0d40200d904402d0110161004c28402903865081400160581c80e400d10b16004200900c07001900003010141583c00300c0e40c1c1514003589036840000144c54903000d12819101102e4080e1072501400019508103040b9031003078a0401c4008201c060803401c0d203045c5234401015074004408135803000000d1b40301070742c040a84841176091204035907030101c10a51025060311084c0c0c0200742c06580d900107104403a08510140f03aa1032410b41392150790300d11000c251040700200c000100e40d1400040b4013180c00010b604441d402004400915186801c2d00000c420941c48103209010004031204000030760001640c2e0020000c201c140d80e03125020070f5040101c40103e040648884804070300c0b0548101400070200760341c02054803854002640e117910114000024100301000d82085950000084024500703500401d0214a4a8080f4446036852190f0390503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 27180779 1250 27179529 27179533
    0x61a0907020706080112030c020904210503060a0f080a03050315040207031106060405011a0c01180f03020f031809040512040b0706050105030607020c0909070f060804030f0f0912060e 80
    0x100080a5030202c2c40300e00b0b5480030346808078180d0322420384942014003408010b001c220010040409480c0842099501600c10f240d0710210b121030404c140b458504000102010172004028058185010031a5401401c07200c1280c0c01e0803450180210b83c0c0700da05010240a0000000c040b40558456082072681c0078800351095585d111180f9004110418000c061403090040001003072003407a041c050705040703a0f0700240d4020781d04158205881903620141254480351350703443d06200c401140042c45042a0f00850260b00d8a000c00d00b07002e41400242000d11a20782c004004000030000c503c1c103156422842580c5451280e41c1c1c0c2c2c540b0b240303090704002c81180c00701070100c1c0003e8440c01200042012500c00c03442400545d070380303030b00381680d0760800c0e5039070343c090303004840e54140d1810400c0070141d2012500044404180c0d80308408600c0007682e822400c0081c0c0711108101c00e150308640345078811a07051500c03400038503900000528555282c0140c59140f400d0f42405414450950400d0300305821a40c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 27182029 1250 27180779 27180781
    0x10b070501050622020c010b0411030f0a020a0c03080402030c0909010c090b04030c050405060619020307060b030c03060708180609030a09050907020c04181406040312110403061a09 79
    0x100010558018820403642903007003100156690610b00c16602c0d00042000780382060340c2e11902844065040707200b10708100e650f5459204010395a5000b1001200b01c4140104d59074188500030b40400e000062524448600401040110b43da02c84496040c164142c54034815030307281c1e4030000303040c80d0504d5001688202c011080c003000381d0042d40b0500e6101702540700c2d01501541c0c0d05071011700e40124031000d450040480c0302045a41803581081d0351012005040d140b070012003031030405040c429013954000503400861203034104003042c82023040301242100101800800400003d55401c3c00038012810442c200e00450b995944800d0703400032055040c0e003a22043c1c07500d05180b0340d80e41c111810141c00212650800140d80c00c2840c40b260094a85c3d41c098502241030406000c081c107d0324160a00b03c1e00c41c4520303040031441452400c890f600c41ca201902e16401c1c6410000d00900c41d5241c0440c0c458070f00003011820650102c00c48040b41d91012022440700c2c80c401c0903244c06a100400030b6040b60201e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 27183279 1250 27182029 27182039
    0x181206040c050406060c021302030603030c07080f0c0d0f060c210504020f04020403031715040509060a050919150f05010303050408060c0901080105010516060606181706041b08030301 80
    0x74864400b40d078020384080202980d01c4100f100c07034407690000650003100c0b00c034224101240075002154088800b80403a4648948080e60b00e18042d0351354003c44894200006850707003002d052164514202045681e44402e09c2c0945440b0401000010004c1074140d48030460100c05000e11004c9111105001e0724254180300c000048000d00411981244190301c2018800c25900c1e00388242c0703081d02d40541e00c0c0c4040480c44040c1103c41f10001c1c00d1040f4200d00e0b100c010f00701da13595000c1c89100d081410094085030070550f11410036590081c0c24020141c1007901807541244510301c0c482103c682000d0780c580c5c410350380f02c2201d008000802046002c2c1c3d08010000c000c0c541c00c04c00400881e550030b0304840326984c81700c241c500036014102c0150300085407400100315a610680180a40c1602006a2251000c41c0e40c1e030f420445909600c1100840c2500501e03c1c91f000c0c8070040280200036401c1d28100070305203201c00b643c0781c00b0300420081a81e1030303c3c041681e40011021018001d0300c001000c82e680d1356104c0d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 27184529 1250 27183279 27183293
    0x10e0d020618121504260301060306140d0809040f1d070e07020606030601031403190207081b0904030311040305030a0206151c02120c0603040c0f0b03070518120604 72
    0x2054034a00512000d03100024050001401081445240104130306540340c50341c9040040c1c1e5051035181c041c1074101e1002c2d0300c44128000450090084d071724001101850014103403008501680807602c6841c00c01d2110011951440c11a9285c84086400050038407034001c40e800100f00501200090003610f0b0400c80d500580000c0c00c0c0f00303840b981d2034101c80958603000126950001194841e4040c3c0050004100003074007208400d00070540340042d03e05011610306500031880c6402410001a8805601006058401d1010103400700356980c080120500c05004990301402c060001002c140e92007440000b91003044050350051a4007809403036448060840003503844005590102c0b001040c070307110340780b01d29014400740001c0074030300c58880c2d40038096000c0204000450f000700d9994002c410f10a9170b00d0399400003c0d44900e200d01d01c0703400110705284600c40107541c95040108004400c0041c0910f45030032009903600c22034402445c1030750000130804a41380258010b2010900d1041800303020400100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 27185779 1250 27184529 27184567
    0x80106030f023102030a090501020d06031101050414060f0705030d020d060e01052215060c060c0302030609011518060c060e0c06090402030a2705010f0605010e010e0d0206 75
    0x2120852a0041644950a222194508416030761070620301c0840350050560017550740a1250800005e038544191242d42c2642e001d0404501d809680e00810f00800078008003580c010f810a180941c14241400f85000e480445020140c2c031902c0d003c2000c581c000100750840d0100c0b80d0040651751106040f030342c194042d412a42c01091160b06145003c00d40c0c51003292100e04031500140100175124020060141c100c100030507004c1115103e0102e0b01c603110040304004000d040980e10300c0c0451485042003802c849005000d00105070040040c0000c3c1e5689046440c151944c032606451031103042001912182c488030f2403425010302c200d60002c1e415411001e091811401840f003404014003041000391516100108164040e45c02e11991407d810a503010310780c0048403410000720b143c1c01034500c0344e480c00071106d00c107012002c0d498020b0800102703010707501c00042d000d001030010b9400c08001030030000100115504010503040c0c2d41e1901d07074820102e00c01940d005003010355228192003e42e2a1810 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 27187029 1250 27185779 27185783
    0x1230d020a110708160605030a1b0e09060906101103120a050402010e03070b0d02070c0801090b04030f0201050403020304060525050106230a0e09100510050a2403020c07080106030f 79
    0x40c61400059468000c0382a9420f403640310b40112226045ca6026102c1c0c0e023014102c3c4081d15a00c1c0c40c1298141103c90104a0000168841c5025070503040104218418000c10703050194003208148812a11078288050b120603a5040c0f203072080360005820340c914002d2403140c400350b0f41000c0074040800360700d0740424010fa000ba80e64040400300182407603614010351056902c2c1d035408000c2e00f240c1c1c800c164054032000c0d00c11810160059520079030942910011441943ca0900d10400c0c8000c25400c19541030b140d01960000703219516207920041d450f805503109510a0000c0000d01551076456068450301c084440d1030501c8000106003000c0b8000e0145000d00c0c1100400310440603010b00e990f10005000c00802040700150500b080203200c00b141e8003a00300c20592143d416110709118040c0a0780c0d128050340c0c4c4010070440d2805080203800c40f4143c1c00b241119500c0401d5402680310424403442c0012141000b5076100c00440c1c02d645820901d60008101e946069004810400c102002001c128 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 27188279 1250 27187029 27187033
    0x190803040b1b0d0e09010608091e01060306060306230106120908120906010806090f03040302100c050d030906060b0c0d0c020f060a05120a020301080a03030e070f030f0302010609020901230d020a11 86
    0xc7c0e01c650041e80c1905040d9084012507006007070003040010005080f0300003a00040020910581d82e95844042e20120b40040752115180e090540c0103820002d200702c22008480d06020040d4517110000d07110170520030001e407001d6104d01800040c403a07603408a5250780540e0174414040e26000c0001d5844400a000780c1c0b989000701e5020604281002806483c101d003001c0223985401d01d141d007046844107ca5401d2400d0000005444010800500440028500d0b584004c00c08180318505401200d82e20740142e07801000600c289185183c0001c0c0104400d0b80b98100030140d0f900d0343c00040c000020b4000400d030b11540000351800b00c1c96000b4041d00344103207480c000c0d441945400b107044081e400300340541c0c091980010701500100e407090b00510846414841942c0b000da4850a0306451540c2d00d400c183c1d814808010f450082550900c6200018001c2c848110305003c18240002c05003c5d55424005c0423500040840344003e203460100c0381c0711440040e0031556800e1120300030300041a0011020b040b8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 27189529 1250 27188279 27188281
    0xa031205031501050c0706050c0708030a050c0f0106030b0601030506041e09150902060307140412030306061b020a05120c0909010516020a08030a05070e130b190803040b1b0d0e09 78
    0x203500a400366601c0301c1c5240c0186c00f5050500303204907925001484034900c81e00c10b09200091100081c03004040039807495492683d40d03810840458070b00030086000d9480c42e0703d08801040483d20344c82205800c07034800d190100e01500c0e04800038000e4130030440c18030004800955408904107280c4e004900b020700c200c903264001ca009941c44000c50340c035010041c1d080001000010b030345622540c1c040d44092100d00e1103d0410f900c035844500303030344901d0208601190b9103c1c1d0034015541c0207030540c4452500d416038100700a4540e40825222540c92150b01d000791001c2c1c03000205107109000b040564000540088a81c0c50608402c90103003000f510000e0b44104a8546410824404207105003000d070405141031854a0b4a03801c2e800070800140b001d07080202c990008400d40d625010000d05031500c0c80c4021954846083c1040007a6600002229103040a07650400c21682e002c41688c085901c0641d1f180d44500720301550002c006d010112580d068024051454051078204010314140c8905955032041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 27190779 1250 27189529 27189571
    0xc030d0f17060604120305121e01090b010f050903010b040207080d05060111060601050304031b030201060906150c02060f040f030b1005060a12050402030f07080303090111041508060a03120503 84
    0x71981c01900c429400510410081c0700042c0e816454050451291401514100c020f20250006003416614014240400400036200c0c001e101c0103180541134501007009498103150002e071910211510b04010300c00045a00348982c2e40a600c010b07800440a0425540d0b0b1401c2e00e0201015032040462036505403900f004201154400c1117100c1e1408620f0740244029290f000040d101c581004004400700134110103c100c0d0303540e003035918003402807003038002048507424442c09a0030344080d03411141106480800403000203500030300900c0344c10340507a08a940c8040105e4421503621a40c0c016070402991041c00000b00220b00e011507202d1400460f20b841d000b600d0720108111071145c141810009240c042010005804a80c4900e0700107200404840741c0020703c91a8500309140c0d0752200302590408800c001150000f80200360b030480b40e0340807035803800d03040520700340c02000c40543d00010403e5010020b001620b92602060146400801042220142402c010407690088918a503521130154a80603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 27192029 1250 27190779 27190817
    0x1003270212010905070605030c04091103040c0501140a030203100e01031b0b0306060301090c020a05010f060303090b030c070b0c0f0f03090c011409040c03180302070501170108071401020c030d0f 85
    0x1034035074400c4c0075115043c80c1c120119010740000e8400200130104000c001007007404c40c40783c21010091b81b9181074030b03440e042c02c20740d04014460340003c2c14030a54803220b002c0603c4000403504d9202c0c89040c010b80381e03101c0d0b0340d0706019241c041d084000900b850b080044141b0803540e40c00395000f856101c41202c480c0d160115400d043c08190b6a0315000142400140000c041540141d00d81e103030148102c41d060b08103074603080d082d114026144003541daa034000c00c0c018198402c0ca07000c0605003e02c0e81514500741310007510005c1c881e80f407010304100d00340d80100f089030071144201ca801c8038000c0c50068540b861400c40c0b0f8015842607a08401c0c0d4030a400d031041155001e102c1d505071510320031102c13500b801015018400a00754101320101050340d079511a03c1e100c1017016600f00d150b8084d40c020000c040c245070015050b0010070000d0b82c0b140466400400c4480c0c0c00181400581c0c070504c68030400b11030b48900607854101c44401403035140c000c0e1035454180319130011281c4989a21035507100650300110540e00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 27193279 1250 27192029 27192041
    0x51b0a0501180506150d02040b0d0b04081305040b09040605090708061e06010c0507210602031914130f020d08031501080c040e06091f0321030203060f100327021201 72
    0x580c1106c11901403401514056000040300000541007400200706a030320080081070482c0c0c12504108045510003500710302e4200d81c1e015210540d000c12900c00703d400003541004000b407004103010f03100e20018008079010f001c910300419583d811540c1c04c1c2080040c1c1c5a00e2508a140f074082d075800ca10010354150301c12409400c006030444080c000d0a410404070840d044000c0101c1441001d0504030800051024401144618041e440140580001802540c26a515000348507010750404081c0320a0120b00003c00c07941e0703a0b008030340c4140d030102403003c80c0d9001d20100307019003041d0f0044100102c0d01500001880b010400742e0f59080941c0c1d4900e88403503c0d00960103450241c080d00c100245090a080074043e4205c0d44c074440b50306005410031007030440d40c00540c1048882c400240038104075245110304130045080c59044c15411403400070007003080c24282d41c204134401c0c4110403c3c281030034000d07840840444108548208002c2c0300d45448000e210f00b00004a015501d400a40c6103100c4041c8540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 27194529 1250 27193279 27193321
    0x30b0a05010c060e0c100c060b0f0105040b03060f04090803090114070531170105061e100e040501060c031101090b010e04050309040207030c03081303051b0a0501180506 74
    0x4404040d140c41e044010041c01694080170f10440c04140c040c0d130340300d03624038803c256160350711004211079180110540c0d4130b800c0714a002d80d03c2d0b104030208aa0b044030903a000d80b4000800281c4a80d50f102c0028411703101c640d0388a800c245130005030414091954002d500c80c911800091181c0fa01d01400c807140c1c03000440305100003403428003025194085050404145c808041c15042c0104c45d03da1104140d84035a44c049030900f0095407004002c24000c0c042d199010fa000c440303104c40171031f142c000609a526054080c610030710300004040e060b580984c0c4408690080034008020130760b1260809407501d0060350040e804a43e000380c2031107641405010741d07502254041c180852907480d00d24400d2012201920444040c0010f00540d0f10b5601d6034409000154020365624a103031819007070151042c40040c02540049461180c0c00021980240c02c81d56880b20300a6088903410081603110705202ca081c1c4001d155500713011042c003c00c940c143e8038410303180c01030081e6074660b100c4422020b0b103202a03142c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 27195779 1250 27194529 27194537
    0x1205031f050114090f1002030a0f081504020d091709210c0d020d0b0c030124080105130b040e01051b03161803050102120406060f18150e01090b01030b0a0501 69
    0x148041c42c1c0f1000016107800080908803159410759103002a1903e040c1c0803100006134004684480142e0703101a00341d213a05d241d4103050b0328a081c624105d46400403c580d0481c029500080c4801030050194401d04155801030300310030814002110400582d0f009aa84e580b00f4610700c0844125219560220960002e50000500000b1a94401e0120884090100340e80c0705021000c0d4501140c0a0300c00395224410000d00c0300c1ea00e42c10700c2c000e19180c8840c038603181e000450303559200400c150007582a5040d510100c0e42450000040b56004c400f40c040c80d4242c40c1c00c242000030340701d00c502054000900400030000030305d4901846d0302203260940011115a4008815903002c40c411500400094040c8455041a180e03c3c0361a40c07070307142c01c4ea800a07a02c00310500c040420030003807000030711811001c0d0000032070f410042031600c03038082511032407814002c081946e50b070601c400c412020101000203200914a5800b590b0b56003110100801800c41c00c94040ba0800503190762500d0002d2089042e500140c40d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 27197029 1250 27195779 27195797
    0x50601050a0e090903090d030201050103020306070c0206030f0901200327300c0d080106020d0e19080601030b01031109070c080d0603050105160212040503070302010f0306031205031f0501 82
    0xc10400148005040a00e10740410804046c2940707485000e0b003005800b94001090a500d14070600d40b5010f0014411010000d4900c0650016610202202c1e04038041051003e42601c900c0e02e080c2c01010004041c2800400d01c1d050107d49844000c05940b01c6e40514001601c1c1001c15001d030802080c0301e04040109810010404010710502074003445071402c941c40001c04105100380b00c148650184400060540c051b80141c10250391001815015009620180c010101d644030081d0801024000c5c8600c1490100002110281090b465000a104607022035101c2c0d40d4038149140803060a00084da00341c81200540c0f02141801d45c1c0c40c42c0110710030303500c2c2c1100c1840d0741c481180745e800a0000807081c689802c0008085203090007018081c41c0e9244103107103040542c031806450000304043c80610700e5000e0004200554011903518105ca0702802c0012501038902c80490040400343c1004003a9040e04000c4501d05030300401a602c1040b0540d914110411014807803001c1c10390610a003800a00005 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 27198279 1250 27197029 27197057
    0x20309030a050d02040506070c030605070f200a0209010e0f0c0a020c0d02010c0203060c0a0f090f0302010503100803040902210f18010e19020906091501030c050c03130603050601050a 80
    0x80d00030040310400207001821725031964001042603000310010307580340620300340900900420b40b1031180c2100030350500b040c10322510b00001d08401944480c900c1400e4591280c1300050301d00b8000070f80f142d60300402d034144c99a15060851407290040d507d80035545101f80004180c0c000e600115204180c10360020558201c1032800c201008140403c1241004102482c400058a040000c503000d840b2095001d07440b016601801003140034815030300f03c200a40c1c511304100c406a030750301650030781e0707020700e402542c80d962107611084d40b43c2d8070b600803c440e100c00100010002c49035406444806888150389080083e2201e140c00d141780155040c072140911540481c861640e58203440c402c2c0d84094002007906000c030740200b800e042c0151101c4011080c000000c400f1030ad80b070b032560f9601c4003040300c12001508190086030041690403803c203060503030344d002001e01140100180c3d85200f000c103003102c4c1c0d41d035002294030007902c3e400d20035940444c0c1007401040181d07000340d09840c032000c2e00d9601c407000b8600e54 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 27199529 1250 27198279 27198287
    0x10605030c0a0917010c03050a090f02040b0409080307080403180305060f190c170a05040b04110301060e13020103060602190807020a030506010f0f090b0108062e0909060504020309030a 81
    0x51482d402482056035000403103851070030b0000d0180780708100000307a00b909511b024042e0303500201590411403a120304100061000d0042d101400c0c2c054400080301c280e141c002c18010710311004051b10340840803007013014084e4400d50345031040340309a0314800d601c1390f200d1103621442c207c2c0c04028416007190001034102c021414200c2c0d80010121400d016120071207545104607488480d404001031407030041061040801c0c6500c541055242d0303410840b41c90180c580c10010b0f6030291000b058001c5c40c80d041c1c0307440e54094100c84041c1082d40d401072071a08010694048841d06007078101d0200307007450030004105001041071130ae00c040a00784120805450343e030b1540281c3c40104220703840007800c000031001c2842081182d000c4c044900d20491881d0a06170411700c401e02c241e000102d014141040d10380c03280d0348011100c3d041442a00c02401c40803059042d00681050581189080d002c540c2820401c00c0d40f04918404440c15010100559a00c03001400180e1004a0704110365600030008681c04c0c81c81 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 27200779 1250 27199529 27199537
    0x703090201020709021308191a0c07170304030314070206010b090a0306060602030714030703020d080a0f0c030506100306080d1808010204060903060507050a08040809130e030a03060b03010605030c 86
    0x305105030f6803200d440b805940c2c12a004021200182c586000090040950800141481c200409a8402028220f40e10300c0151122240c040342580d0700f41000c1140c041e494410ba88040d644410040b4070b403004001810380d2500104c406400281c240581c40348444024815207000d09a650b0242a0a03030030b1021640d10782e4450021160440322000303001001c518a40300381e00140050380d000d1b42d56010030b410f0100350ba2088400324011508100701020000b90009924100c0c4100c50506c3e981955448a001000b007a00840180500e418840c02d401030340e42c941d1016100d034038100c0b00c0d90110300103804114211040c83c000c1c0328841c0d10a04030010a680107110501d528854070034200d681d6521450050301b641c1082c0d0000740419406c00e01482008164010264010f0f950304d4040e0500b1281d0400424002010300041c04444c00003580410649516003441c462440e40c0b40b050185d42c3c1c0c54124107507250710100341c20740001d01d0100045070030712498007104d048581a503106400c54031034403040001a80 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 27202029 1250 27200779 27200783
    0x2090105040b030a1a06240a0e060705061306051e01030611130e2502060612070504020a0c020f01020601061205060102160801090b01050102030a091a090d050609010e060609070309 79
    0x45070500450014040c240481010780011801e0505410101b050010511006100485800810324203c4140c00301006543c04031460349800c0204513652030200340726108120f07014146000301c90410201191403a04508042d100c0c40e000c120954a610305001c10401450480302440424401000441c407503412007031030000006659071130030340825034080000e440d41d403081400c050080b04100300504000103002040b090100c4649005c0c04c1940c0081d214100200600c1c03152414009403848007d08100380c4015140150045684840c00c100103050b140c03240394224404c0807503120b210340952012030494102d40c904e8456419a1035203884550146c10020456411489500d1a001544100c2d0800c0b0004007140800004d081000b410002da40d0013050b0411415544204601500540e103c8620700c101d600352100b0071030624101c0c2065940303105403140030b50b122030001c401c4418004046503131070081d4814802041001e040c04045603e61000302ca8081c0d006010f04000342c0124001e070032a045c400c0c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 27203279 1250 27202029 27202033
    0xf030a020d09031205090105070c020d03030608120c160305060f040f02090403030c0e04060806070309050304090c090501081014060903030c010f0605040b03030304080d020901110102040b070c09050402090105040b03 94
    0x14603000c107044201c03185110300f900090f0441078841c204800b24460280c2040080d4002c3c0418507044201900c0003160010003401032005000324820305200e0f07403144028001c500e040e40d0b00032110442c0d02655410003000d07407415001c1c280729100c0d480e1524681508072a4040301034006a603c049101a1140004105880c406203441c01c81d0010b03590490051303c03d51213600e001804490035000101008d07054079102d40240e20f000c1041c000e400e000202513500401525010a650b0070900c1c08a0440c00b50781c0c40125000d0078403071411740d10340c0c0140d1210281c4d002a622444c840d5940d007a01044d620652042d031202040b081004100c1e414804000c2c80424809070031249440403d840d17060031280254591051556110001c0c01585054085ca0048040c110011425400c040c3c40d004c0203807043d0481a04241e5000500d00401d034095241c880c2d61700030100003103490f16075494480d0740303550001c001280c20710700038900840c100001d4802d081c081c60300a80940030036828001400010820610800d86c18 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 27204529 1250 27203279 27203287
    0x3020a0803070c0c0b031003021201090507080703140316020103180f0b040204050a140c070c0302090c0a0f05040303050711032a0f030606130506130c0206060f0103110f030a02 77
    0x11030400030045004100760f603102c40c1d6070071140c01c10403480d28643d00001002541003007802080307541010f00b041942d80445061900c2c0c0300640c1054010300c012600100305015842c4005503080000c1541011640111001c9044941204542e603c03881380e090701101002c0300759003140141d440313540482013130401d08509450705015522085454a003218044038040461420803086040070701403590081116581402042841c0c007800c2c3d0221001805651003d10204124041c03007005910390004680160809103141044215492154403d8000e01c4c00704010f6440c0514240c4104201c508494141d81c9082c1010781c16546d85400d0b0101e07603051641881240b04030300c00201a02041038420006a40b000380039411300043c09840080251083d1080d048141007000940b18154202d41c0c80704072141c0000c150390303810005840c5105050300e010b01549841d09044039141c0000d1100c1c05180c0c02c44800740808982c0340110266016a072503081007010a00056440c82c100c40065a040480b5040260030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 27205779 1250 27204529 27204533
    0x60f121401080102071505010f030f0501090210020a031d0a0e04061d030406030608060705040312020f100c0e10020715050c0307030c0213090c0b18030607110705011706090403020a 79
    0x584280c0010407242d6001030400c0400200380382d440e0304619106c006020703540c50b0010007000d014451001038260f0000d619400200202903006241c500c2e0f000381a10f504a000620080d03603611007220890200c1c4d4150180036403d8444003801c018130800520480c11141030101c0b005000001038008c0351010307100c03401c5c088c5c0070703103005280d100d4590402e0095880703a26000006050b5942170f44218483e820000601600680c4601120284c03600705142c48501701c06034808130700e091aa00108026802211545101c02c030598000c0300180765180e80740c0240e24101340400a200410302032980151348a110708019410492070011101c540c41e0829500700b8820101040c2542e100550450020f008800c09000b1490140d007904010a03802804020b02c80c0c1c16900c0c03000400050150300d03c1401c0100740d00d18004540448080f00c0e19003e400e03a00142800c290103000c012604825a11901901d980440c0742e501c1140c00b4040460203040c1003013207403514010f00860746006401a01140546405100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 27207029 1250 27205779 27205811
    0x15090609150606080f0112020109080a1b09020901022503020d050d020f0307080702190b07050610060e03030d09030c0203030c0705090705070b15010905041103040605060406060f12 79
    0x1005405016008406403503948881d0840d2015040742051000c0101844180194143c01506591960124044c852807600050300c880342280e029030a07502c06d00303000d1020071058071092044644640c40c04450140c48543d4203050703000741101d940c0180d00201c02c0031100f000f00c1c07580ca8400d04059501300f55682e240c2d008105942c609880c01c5d500c1da4070580c400c100142d81001078140d2407a10714003035410010281d41d0024248126030300070b03200d14103499606c158813080390548401065801402a50b445091602684803441111070310301105210200090700c03802442d41e40c00c1d0b800b000700510b10305014640c100d002419080000d908100800c420400181c03010070042101103104001024114030b02000c2244c202c0c0020503442c200f001c01d100000000d4401141e00e034014031640030000c00b04a651004840e4040c10741e015a911506058130451000200c0c00114041c0f4010201840302d5616030007400142e514900c41c0b4000a01c09410b00380d8100d02c40e8540715078441908a010403849545400d00d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 27208279 1250 27207029 27207041
    0xc0a030e0f040f020c0d020601050d1218030f020906060a09270c080405060105100c080c10060b1804050c030601050304171819030507090c050c16051309080304150906 73
    0x1070f0075660024070650000020000c03804400168801454690b0414000c2211541c444400a01c016040c520100170707140640d90104107005200060903c0a5403401e1102580340e403003100380c0c002d490171070105581d8200f49007142c0e081c004a848001e4038030702d00b41044520b43d8100858070b411800006110107220302600500c0d080c019503030303902c982900f802d00380380c1d0912906a101500c209006021140c0305900500035104a03504000120749410b000c800f01820310b083c40480301451071a042c004540700e0382e0312000c0d0000c00e03403002c8002182f200c2401408211079060758854807090003403001498a6114500a46e07115102d20240700300c9401d440c610300741d030b50407442c141005c1c550904050340300c608044000215109043c410702400f6855501d420303803251301d640149502603446494443d0380d01e0089003211000621282114044c503400c0010118100c0c02c1e020720ba100e010405407207240a50b550041d80c0e059074216985600d55111035a0301c07100ca400b4802224031786a2151140c2020466034841c45c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 27209529 1250 27208279 27208301
    0x30510050f01080c01080420030d03020a030b030601030c0527090319030b0a05010f0509030304030503041403070b0a0c0c030209160e0d0b0c070303060b0d0b0f060c0a030e0f04 77
    0xc6060308007550305440d0241c05820241d442d901c805401c041030707a03021a0f02d542040e0040d0f01d022003100740c00aa07217030000074580c130380740c040c030903803d80d001e05640c540c3c02004260202d40d000c00503d090034080640704d074030030b00c000f034040085924148681d1410b145007440e015501e0508440d1175800c02c60b01c034070180003111407200c2600301040c141100644411200000e085610303040203507150160000c5c501004900a003410402014001a00c80780101e00b00e4000b0b40008007203d8030b895480c07820b260b4940c020301500c0c1407182c0c050b1003c1114180000c41c0d20a0b20307141d04040342003040d036040803507914401c00742c00d803502e40b42c2000020140e02c0d881201406502161348008010b0b84084c00908140c00c642c581c01d0080804429107400303e001014003e030072a5400802c6659900301e0304045028258940092014100000710140540266440500400001d841251504094404101e039901904010b4041c40e0401c907088000a40306103a800503161005143c00c3c011844c8901143c2107685d43e40031 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 27210779 1250 27209529 27209531
    0x120106110d08071e0905040e010603020406270f0b040207080d14090309010c060902040501080d090b0a27180605040e0a1a04050a06140a0e1b19030510 66
    0x220340c100201032101901e81a40ca080070680350a101e1401004ca100590328006011034880103000040d1084100344000c3c04000c00501181e015544140d0080c5943d01c8202c1c800c0389403c03030000d80100300c02c4050f00c80c0b09140c2c03420303603c0c2c071801c104030000380c442008003c0c8072039076410340b601c020f40c3d0310320181503074a01444c1c3c042e450b4251081d9000880b0b0a640760043c4043d1101c1c08c10200c08000401c44000260070f03c1d14850410b901d2406101410920500a41c002c0c1800300108075088002148452a000c07940e40003c0940e852515881c035208111000d8001400b12070b2440c0b0240840c03d407440d400310092900a041617440602480d94001c558140000d1038a41000b00094541801001c9030320245001608001c00706603200d80d8004a01c0600400740c0c491000010b06004062080c001e00a400c050140304260880c1000b440e0001308564003410a071500d0f45041d04c1003c000b8416046081c58010303404179042e12030030402c0c0051011031140ca0707041400320220001d4020701036141c8010103400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 27212029 1250 27210779 27210797
    0xb0a050702060f0103020f01050705010f02071202060c0703020c0d03170c03010602010e0c0a05090402120a0321020a080c0f0d15060f0206040b0103020910050d03200703030207090e03120106 83
    0x10000b4242203018280e03090081c212801440076070385000e803002c00e0031000d0904e01d680c0c0260b842d266016104101181940510204083c0140700d403480c0b81505807400703a400d660f0107640381c40c44580700c1d002e82c000150040e48005611001801d005028014050003428180110861800c1c80000224201c442c644c1d40c1e440800104402e81e02402030391412260741015050490102000c12000c0d507091003072034422280040464150b4441c074030111032041850341550740c40d4405040c05004440126805008100406140000c0b50500d1013174031210000e50351684901e84840e038201c801604680801e07185110b08010001101c480b5114a004107008803100004003841e00b50042c128010074600313181903410510410000880d072002c1c1030f06580d030450700c1110a80f5180300e090000603081d00140c1e000400a8514000c1c503820440fa603c0171032030114000c9801120008207038440c2803038480100564445c0d0402d00c005125030708041c401c03202580840341014001d840d5a04500d00a90018010902040d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 27213279 1250 27212029 27212041
    0x10507020d14040303170a0207021206010302090a05011809170a0306080705010503010e070c0501020904020d020904050109060b0702010e1912050114010b030414151509060904081c090b0a05 83
    0x40701c0c2c5019a0450031828a0b01e9074401034011803241a62029004c0d00e2800140300300b02c03d80c103549480344c01400a0070724403a150044c503980ca10070301090f441200100d000903078840b20342c000c081c184d074014000e0288a9504203484006001e00000c112179415400c4030405140e0601405401207a00c11742c5c0210f00503182644442c01c1c25a41d800c034504019080005016602c41c1c80da91030b410207101e14003e01004038a003401802130049071507440c5d0141c0001022544554142c01900c468030b01200c1c10405c59a841800400302c500030b20481410304814041c0401542c0201100e40d18200302030104803007190f02504556203074004d41c106540c1c12451450301018031000f40f00d9003c0c00c042006086150b5410080440c00321700008100920b0440b154100194040c1c0c24012008020000380c80c400ba80e0a052907c400c21070040003004c2e001d5082403000941900d4088c40250286401040c0c66291035001d41c0f22042c096441c1040c0b1003083c3d1200044400144a41c400320b2040c40024400200c1e42401 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 27214529 1250 27213279 27213287
    0xf0a0305060402181002070906090c080601030b1003020904060b280903030c020603040203030706060803030703240e10030507060503150f0114030a0608011b020c10080621010507020d 80
    0x290025000d540b042c01400002d0444d03181a0300790020807100c0039103c0d008a14200e203031808541200c807280341040340001d44a032072604031004d9450345884411150380c41070011012035002c01d200e103610044003404c1405050003513004103401c90001d807010a140f500c444100d201540821032008039034418400c0d410a4440040301c040b010b07402807030107441640c81c58130010090322403075401921460001001c41c086590400444071030700e500503018050f060f40c0c0c0381000e45980013100c4c094007003400c000f07030b462130926a4204205400580c000344610300d414000c0c0320202100043c00340001402d2400007001298007042000c004280c075503682c541c0c2c1d190501c0054107820b401a1450300540e4090380c401c03403ea030440e4440740401d801c0412581c8a9880e0407881d0050300c0e044c0c0c0840d4140d444c160000803e284052012042050303da002c45100100c0b050600220501d6200c0c0403000441d03480100b11945842c0f99084105544418540e1f036413650741d002c141c2120015603180c1e0150780705800300003840ba00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 27215779 1250 27214529 27214531
    0xf0906050105070b04080307030e0a030e030f0708070b070606050607060921021009150c05030109051e04080702030106050a06051b0601080a0201050306030f060c030106030b0603100e13080f0a0305 86
    0x10a103022801c140c040e80c0e403c80940320150000744106c0c404000620058401d03840035001000400480b004010b45080282c6401002c40d4418041c0c005c1c0b1200041030307500010040111012103004001592802c040442039420201d011141c4176150603000030b0796a41c079800340c4a9503024890020781c240e81c03031611002c001e07440c100c85c0f076891840340d114191594000c520320b40b028108400100b80801c51340b60030f01e03550710740da00d403c1600352030080d4070601240d2240c0030703506a82038044200000e80302c02101c2c00800005101140b10310f10000d0026000a4204001d08a03441c4041c0c0081490750f01d61001603030078515504880001600841c04c0250b090300100d8280c0d0000010300134000550400012a44501000402a05009000010507041d440402100a11061440540d505414000c2c0c000666500a01c14000007a041c04011101e600e01030f422240116050038040078450300d000c41070035020b10000c204c900c0140b080c1c081c80c000b01d410800108011492000380a80c0ca039414070015007243d40c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 27217029 1250 27215779 27215789
    0x110d020a0210150b0f28020a0201030b0f090712112b0504020303090613030c090903020f0f030307080405011805030903010606020a110909030d1802010305070807020d08060d05070f0906 81
    0x1c0944070810050142d0030031a00f942c4a4030315426520380200100106100410301207811861154011000746c03030f4040340752000d0500c01d07a818480ea204540822a00303031440f05035254030a429001007503071180156102e0440c085030503008500f00714482c0740208145c0056030882500940101102c5640305202990180141c50754410450350901d5008240e0b20f000b8800030f94002d507030000d100c500003000d40c903c43c4011944810901d42c0d264541a00001401c4415411005403003030710010144000003180078115a40184015419980d9000e4120340c1000007420a81e641d550303d22008204030510792480c0c1c20f0038007820003503548039500d4007410b003160600d81c0003004540241241800060108040e4104010102e80030015502c0301080141036201e44018a507445180c08404031404240129094406000741c900304101d82c0d82c4103081c0c0f2504c801b107900d4401030704142c01200d882405044180d4011502402170441d200b603603541c052400410f41c00c505407081c40c2950820402469000b00c81c040c01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 27218279 1250 27217029 27217061
    0x108010b130c09050f130e010b01140c0303040303110c06090717010c02100207020402040e1f05040212040b0414030a030212010b0a050708030a0b0a03060b04051803040306110d020a0210 81
    0x10182c2c1000516041c41c03401307014842e4804100c01002e070b5580070458002c200c10392004108403ca1590f00c280200111008240400e41500032000725086443c152103070340d00010041e61941d03565640840081501d0000000341c1c440911210030040f0341000060710580b460b074011302007a420881c003111004407141c0b4082e82d0f613040002803010142d012a10303845007900d620000da242c1d032162000501a000b80d030884443d0143e000100140400c0c001c11002805c80c00c088042005511042448164414070b81c03010074a240c2080030030001141484425400750044d100790300220044010541540e1000108400080e00854801120030401900740e0062508030b010514204850308041e240e07000350540544250f201100003180c4207a0364010003001070740180034409403074407864124010442c0c0c51000780120300d020002000c0214020880d10a030b08148011410301e450350781c840000e884440091a80e41c030b0305106482e44003c090014140b234080e23a4000c0d10764002207428440465000e880115210 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 27219529 1250 27218279 27218291
    0xe010603200a0903140a0506090601140105032413020f120109090314070303060504020a0512090703110402071104020a0801030302153d060806040612050304060e01170108010b13 78
    0x8035801143c482c00701e9901c03201c02c1115210040c86103051100d07500c00607045000b00800c020a201c03020078111305036409a031964241c04058401118203007c2100c240e604082c2d900c105480e030a4034076640b044107910060030130760b10758410401ca02c140d0700700c1c6510844941021036082d914454510b0040d002d4a02e40300304100d502403a46005045800e4154807100d04000001c030320702454441c2c0c1055010f0f1402070415596104030010003000d641c80a03054150151500002c1180000041030b64000c1704d401400241f8282c0ea80000c00c030007036120040458042038849152810f64032240050094001a9242c1c04140e43c514100a03081c149060810036210502c941004000700d101130050498854141180345e412001a1030414804010784003020385207080340c0c0029182c0d074800c08003441010700742c0301413007826030f90210703005410400390f8010519002444288030091203610400c00d1441c0524003620052141c052564400b40300780c12184140c1d440d039803d4116410100b00691003065040b10030001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 27220779 1250 27219529 27219547
    0x60a060b0f16020d140303010312031e0c05090406030b010e060d030f05030a060302030303100306060f0305030904020c0703080d0603060b060309060402040c11010e01050a050903070515040c0e01060320 88
    0x1d184149541c041114060710341c00710554030368206008015602480010b030341c04503130700070550382c6c4c000b444100c640e00c500d00300600c0030610074014407810180c0e02510905103905a00840c028000b24454a0308101c41880001310755942c60052030b0040d40909491485035050900c080c049100040c09940a507407071032180700c0060b520494450544e0601d10b02691281c496007003401c0500030560020b541444040103000a200c40480e240080302d01c540010040c155030b0b0f0701f00d451203850034800680b554105106105142c01e040d0010710540350844c0540780030540300c2d50b0781e5040b9000a00c1f80200c0556511090003008028070402003001e108548050651900041490f80c03501e0080000380076a4460300303c100c8943c011107104d241c24040b140203001c041e80030903400d4003c10003190407000050905010500402c40032046070411500300c17000d402c408402c075030412490745019208580b1003019410004d801014418058040c05042d50042800c2445211072920b2103e446031883c2041030070400181 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 27222029 1250 27220779 27220807
    0x30123040b060a0509010e0a0c0f090902280203070303050603070b090f01110303130b060a0f0314070f030812060108010506160f02030d0e090106020307030503010501121b02060a060b 80
    0x303446540611412256a110008140d00c168103a00007500b2114800011138901070315501580300c1c041c40300301040110f0900508480d050408915840860300012003840642411307001010000781800400ca84401e60b0000c00d0900f0b400e00c10703d040141c0012460b00308150741070042c940c01a004034024483c00e070901031044418400c40d80ca0500c209001400c41c8900e90107040c0101c0c5030811002a0b90f140d25042c03d403810100c207064411144a40004009144d40c03410529543c20340740000801c0030800e0442e655482c40c884040341c040b44600c15101d0014521640907001c0c03000c2c602c00c0c000319403a040d44060200d002e0001401990511003114010310881d140c22041c0c80004446c20094000d5594606281c41050002c0ea4040d4040c003403401c14100c103a8000c89100c641100c2503031140c1c80c81e0b03a00c4000f00c0c1c0f28098004002d00144d03082004101c00d40c800c000760b03245551007041c0001d4040300c04c3c01d842810700030b210340303180541c0118007045082c010310310401d80246400030b40c1a103401000f404102e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 27223279 1250 27222029 27222031
    0x40b190b06090103020a0c0609030e03010c03050f0a050403140403030f1205091f06030209010e0708060d2111060405010606110a02033a110c0d0b0411011404060509030123 75
    0x2c0e04066002c51085105d40c42001400c0000380c012000b0021004241001040c081c81145501c2c0a9820220000701c1c0d03130300c03c1c840c0620503489251841c080383c460384030140c0030740400340094040281c04c1065400c4a0242d0300140000c0d882038684503801e1041010151040340c082405192003403a2004020681002103000404a4191102c000280c0d154008a1004041a410207900412001c00208190416005060203100c0070340314405669903110401c004a08480c0009100310640390141d003e01c00e000544444801031400c04007079440350382c00c40c44d282000844040e91103a450300d004001c0f02d6041201580d034038030814041c02c2d1004858000c2a529081410806c44440703c4503400d140d48400000c0240e07400c88144c007a034481c0c49104000030b050380c51000300910940601703890081c4074a01a144040025404a1203101e10380e695220a07003125000402030741403154910302010a849104010005841070340c0315543c03203002c00340615085031500d0b415981d001c14981400d07581ca0b50305001c4a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 27224529 1250 27223279 27223297
    0x5070c0f0201230a050c01060803030c04030f030c06020f090a050a050102030418021312030206070318061e050a090c050603010308041a0408070b030a0e010b01091203030e06040b190b06 81
    0x1400070701140142d00094114580c0401500703004103005813160fa0203801800c0101d20040280180b540700c01107251039100c2600d540445041c20001040000d148543c070422050103410034404010a0307841d03507403da074490207911546000c001039114080c505420390302e0241a003990380383c1e412400c081c0003079564800da00400100c58010203421207864859011284401c4030b80480e56a002d41c1ea81104410000002e01140035005050010720014400c1c03240ca44603081800503101034a80310b444032801040c520300d0b0815800301400c11103030011900d0054500a0405203c000b5081c0c080d41014034802200d0340041d4490f040820040000c2a41503081e87d0503148034a00d084000802100c00b813001d4801c81e804460300c2c0c00f441400040e00050a0081c52180107001010300804190a090301d00300c40c98420b8841c0030404442c0305000d40d0150b440c1030841140b00c1c0c180005c04881c01001d051408004031402c40d80c1c02e414404020601015006004075641030650900c5842d9440002403a903003e03842e66 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 27225779 1250 27224529 27224537
    0x6250e040b13090c0902030c0a080402010203120c03070e01020105040803061207030605010815011509061412010305010b1002060103050a02100903080a0c0c1a0d0515060307021005070c0f0201 84
    0x10005a52150312000407228018400800001900c41c803101801c3d900109944420240e40001030451640c0212407080401c5402c66203804e0b0485c1d01558070301c00c040e1099045200a001411040070800702860042c588520314980724545104010a043c91030548a070441e4109018400056020380030340e50071000c100c51441010441900c403070301c0c000641d07002130161414000001280c910110b2a040000055071700c004031030380ca07800d020310508041202c0b81c002038020b070000c020b5140b00c3d00140c0d102601658115151500130109003003256000c0e002580c16943d88c0c0c0078203c00d0300d003075403500d24046854005040c0940c5142c49480d15604440c8000e03000305160310456480307500c110302a1001e1980074100503110321460340003d2140c000321800300d61040390002c0106e0303480c3c00701d000c2091004105501c01c0c9001200c010b00c0003e4480502030752180300059030016a40e03540d082c00345100780c446038010525071250110b0076043d5800507004405221300280304201244250540c80b180341d80a0030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 27227029 1250 27225779 27225797
    0x306090503070206070305041d06090f06010311040303030b130b03060403030b0303091c0201020f0f0d050705010b03070b0a090905040201050406030b0a0509070903031106010e160e03120c0625 84
    0x2402801e5120b40c00c00207500c8a00010504c1c20150000d0250003550528101c0000c02c0361521295a041481500d1403540583d03180d0000e1742080c06030400651011043c900450300c0c2002031003404040e0440e4000320301003511800c40032840c0c00c10a400780d40881c0031040c148002c2408102207901e4603000392010b4100340d2035604c198100d86003001102e551a0300900006200300415003001c0d13000391a00740481c0140200d45405020800000303da000414080f0080c1000740340f40302050307a4035413141d10115000c0d521000c224a180d03805015031002080700c8118036540e04611700e00180ba0924503000b101e806c40c500400e00002d070f40d00a058409880407030900180d0700c1c50010002d2081592544203a034820405410088215031055941089910a48450911160b229015a00c807034007401610308801c40c000001e500c0f40045540b0707a10b101030600700f0008010400000c81c0c14050559204c040d0700c840080d902c000342c1c00c02c002c1154000304034050000c10304000e04c1c0090500c8025803d00b000c02c80d800c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 27228279 1250 27227029 27227033
    0xc0e01050f09090c041d060307060e1906080f160203040b0f07050610080c24070804031a04120806010f120b060c010b09010e040b010303120e0607090f120804030609 72
    0x800b150340c48140105602c03140c2c03030006109182613000d402103d03480704404080d0321401100f15031550292400501908099080c000202d952605540351aa844002c0003a10a40d00904240c4080901100e03600e0070b43c03e217081d607860a000040038010865a00c089102d10b00d5856021040d0387c25a607544002c0c568940013455464124003807040044e1aa000c0d400502c01c0e040c905c110607000b2917130030400fa12001040101009091500b40d2100d00702050380e04500414030085900810b015071085412900742038032912040c4911a003410016a402c25003001d201c280010161203494000070303494205454501080002e0407640045c0c0020300703200801c40000030390012030f0001c98841b00050f06003070300d41500c20403550191920100d0f180c09000001d0000c5503031030354584ca06d03200e40d42061460140d07900e1580c045036000204105c501c0358507550100200084000d01c14240a1107040d82d034204014207022080320003100c16032150013202d101d0090000000d45107400d903402c5035000040028084068 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 27229529 1250 27228279 27228307
    0x803130303050d0902030d09060e0402040f0b030c2206120501060e01080405030927150a0303080a0b0904030206060405090714060d06030606060c1401090803060909011407030905010f0c0e0105 84
    0xa0f44002e46c140078002802c1c41807503022a04104403011642c4038500f1036100c4091104905c2079020702c15101140401c14040240365800464100360365081d51840d102e500e60743c8408402c0c1850100790080d560350400c0000d907900046c02c1c2c0a4599010040045515044d006000c00c2e0b02444d03058180400500000d00b40318082c02030b103044c440040c3c24482024003000c507081ea669040510703240303140401c0000c94030a001c43c6100d05046107000d0b105080d80d5003580c0703054402020040041002503243c07295001d42d9200c2403c030601541c41380d002004941415803c020035100010541381159024200400a1400c99900071420fa041524880e50702c0c030b244040040038204503000605006d050510001e0400c0d48480d03105c00391805000d03001910440003108600743c4034559009060254280007083c880c4ca045040e698020512000016001890301c111510451040310143c0201c0d586200d24000c3c400b081c052068003e02c005820002c65802d0040508074840c44031790380b8100840071540d80388800746 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 27230779 1250 27229529 27229541
    0x50609160c0c15090b04030201050301120804030204140f06030f1e2d07080609060a0b06130303030c0f08040203070314190804060f020102070215030a020d050901090302070803130303050d 82
    0x44060480b007a41c480c50f030030002806103260500014000300e000210b0040740c6050360300340c03a0f0580d62285146d2034288444a0001c000805840d0440308000c0040141c1d00c41c404c50785400c520003040c00c81403414241c034140d0700300e000b4a094003a4109000c0c42c051740c440030601e410030900704404400b44429030083d1a213072218112016007003001c600118074400c940e83c04c20f0000c40b03011030102c0f078046403100d00e000d4980c2002d4401c032082c0d51252001c0381d6030100540049980c4a03024080500305907144400c0030340c01c00c00e680141e0100b41c2d40c404440b40140d0000c9407501190060519420904107a804030366180c200d8800680454030302500842440000c0c00804e26850f15014820100101400c0014660b4010312615011451420024004d20300600a0f256842d800a00c80500500800000c100300d80c801014500c0c91a802c2044610040b01c901c6407502840c1351200010300f680302894040e140500303a403c100d1040c2d00603c2104000d003071040c020401e80f9458a4031380e0303c95940c510f80720060a8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 27232029 1250 27230779 27230783
    0x3030108010e060c04180b04090503030f0109051501020303060f010309050d05030709060806060304020f121b1302070206030c0723030c0105010b040b12040206040308040e010906050103050609160c 86
    0x8a842054014515840e503107030585510742c582882c04103a6105a2040410158000c00e41e44610a900d074080d40303051201820100e0005901e076203460440e4001c40b0703004840f00401c40180810b03503441c0300307280e440218499140031303900b00380c40041d41d00d000c0240b002d44210034048165010764880d40084014130791140403990750100e9010090b000c3d0300f04940d41d03c0010480140054014890740205004060203002070307140d038665030240700c0d801c030300301c811a6045443c0b0b0308001c00410080040c03943c000c0c070405141e146004048208000c0c0200c1a0130560498010310825000da6140002c032030f08010f180b485160340d5100381c5028984406000840305044000b0400100e00d60800f00090810a20402c020080c0d030380c0b00c80c40c1d41c045001c0e50084010005060242000650001440c1a042400202450705259485c0c0d03889149602503000342050303090110040000010901800c80980b0007400c041c0300910708030012800001005240c4410b103074800140f9800c10f07010300c1c03a041d455a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 27233279 1250 27232029 27232033
    0x405060316030b01020a1e0609080a02010605180709050616080d020703030b0301051005040c1806050703180e0a0b1804030203090a05010c0c03032003130312080405070e0901020c 78
    0x85800c10241e0507410100d403502021074103100c45800c0643c4081050745076580c1c07094507506035142ca14100c02d15010154000c995a07581e80d4010310209014401505c401d01d46075001251290400003031084200304580c011040c3c3d0540420b21081c9500109428148e801c181d44d1107403680e07512003040308940109240644004800146102041016001441d4031802524103000510140c0c0525088400c101c40f0010405a91141407085e071034a03400c0715040301c030b540c80d0003070320900000307810b106050f0b80d90f0121010030800158241015007002001e10500b1480c51310400361031070905246a2000c00404001d402659109581e8140c1e543c001010004e80102843c4801407403d4a80a035030707503108401c0c2c10320410f05010b0000d640d601c41d0418140c00e030f60080100c0850351644c0d900b542e480d550080700e401c050f07508480d444890b410420240034901240d00d00915039900d1400d2908410310360020030710030007000100304004204002a80c0d4212803100011400ba9a030300380c5494024014114942e00b0341c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 27234529 1250 27233279 27233281
    0x120f091206020d1d07060509010320040e1b03060f0604080a03030b0a09060302030a12020111130e0601050a0f1404050a03060b031203160c0314070b070806120a02060d0204050603 78
    0x1101c240d9002d400d90703811041080000040c0340c01c40c0744000e052000b00d40c1c01c2d0b60224409000c03ca211303c001e800c00941c1030501103103a004440403640058544059031000203000710f001c11030507241014158001d1604a49103105595020003042d42d844001c20003409007020b00901d64464403010110340040c1004000e95004a10510b40100070304a4805260701c034640010020541360068400c0c2d104403a030080c010403100501c3d0355800088400c0004c40c000b995665400c608801044000804403541401c44d0700b89400e0038980d2001d506c4d00003402d0941000000d02050a8080c2c10180e1005d1401050400410800c490060412644141e0304402d4002007503407400420051660404420103500b10261041c0c9090b11407e80708900003100c08001c403060070241442e60f14042c4c0885100c40e4001e10381241c1030124020364050345c2c1c0c0006800c884c13440300241040300c0326134060201500110100c0e03a2001c1c0c000c5c02d0313446a5884120640103481031200051010101c0a2035048900510700034001d5926 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 27235779 1250 27234529 27234533
    0x1205030c071403130509060a17071205100f05010b0a110705031006060210090c0506071712060f0a0e0c0a200304050a06050405090109090516030b010f05030604120f0912 74
    0x60b0b0300304c11006200c03848803140c0032882e458400d01640c03240c5d0001d400304084070314202254405030003000400213036014201020403500b84c1c0840110b01507000343c1c010f003245900a0031076412030b0140b00007072006030300d4280107000184d0108200e644004207490b001d06203554190302d0300d0501005500660349032096012a40300800d86802c0340045032650740a4900200f07222818a0a036038203100d004203481401401880036140c4480900300345800f0340001516060a50340d9548030380e215507107030301d10405228104000f6141c603084c0e0265440c0d0980305403c00624100b64902660001341071441e03512000f291032002148030b0110b0108a83c0115200302c49082000021a12907100e0f0042c1401008607000100f2074501034800c65003240d5001d01031480d540c3c64444d1400c02008a0982140c690140300700c000100c401e8140356074041c6010f0700d650b999651410468812641c11540900d0083d0055820440071640300f40d04081e04030081d05010140d40c145520495a24800da0084c0400c008546a0f03081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 27237029 1250 27235779 27235783
    0x130e0703030e130e0703020d03020f0703080304020f011b060209010309021302030a0e070b0906030402040f0e07050a06030c0e0904020111060106090509061c1119060c1e1205030c0714 80
    0x309102c0c05465141c00b80c41691108420744440e403015016a6010756010001802d21683c0c0d110040e0181c816206e1641d004c952442c00c244440d4001e4800c00004021304c010751038404c10210302c0c07035004d081801c01000d0500c03100290048045014118a41c0411040c5042c0d01a07088507068550082c02c108040c500492074400a41080e03681c0020710303103821288040c1c0b80c0c1c00030307000c02a2107a81030034a04001c44001040002d40c00100126006a101d140e0350030b10714031038080c401903d5a8003000e8070f03100b4145420b0144001d110380c042020142015084582540c0100b100c030074008003943d54203030300e964a00042c0d9440c075849400d65124441c3c030303000081490b40950007106442c4210b90b01c400a841d09007c020109081203d00d540d9204d45842010004042d010486005000074040360144051045048032006a0b5484000420800b000c81c1c4100405c2c48114404054200c04000301200907443d110800d1801860140a00c44004041001c0d4250031098403012a803280500c2400320b034a5402a03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 27238279 1250 27237029 27237047
    0x905211b0f0705090405030f030703060509010305010b120c01050d020d091b0801050105030a02011205060102010603060e010231051215040c18110d020d020f0406020706090801020901020c130e070303 87
    0x5070840c00303200310108003482d104545900880e00680118104030701040c0c42d03921640007802c15030a059444000103003585686510500942c052800014081440f00a00c8a00e00c100e112103103d640103115040f01d9680c00c0300a880b4451404a001038030795041d81070000c014120a40042c080901030404801c904020160171001d45500c040280300c143d03602c0e4181076450741042802400b28400020080d00d4071407590082da4071000c144008100c641d40c070f803181d50440c0d0280d803019496940000341709034140c0351405000328600c90340f05e1000c01a1021a2400c03a0103180340601c0744103c105401140c005201000706a181102d401000f00190904c2e1800300f46204143c4100d40949500040c040c80300207a600c42c00c04210400301c010707498440c284c01e140d0001e6206410381518290700384090703d15042c61101510150502c0e80050015034200309014218007425806944168010401d2101c281d90114130b4500300c185c00c0d01d1180c850080d1040610142c8000080720a01d44112040002450b9010400e9 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 27239529 1250 27238279 27238303
    0x60609060314010b01020c01080a0912020d090e0603030702010309080d0608160506070218060d08040801020d110a020705010509011407060914030702090408070c0e07080103030207090905211b 84
    0xb004206140900300e4240e4248103e0140942c10854803016154000c240440d4007414600000400482e80ea40341803a584440e13130b0310300050344044500244142c1000d144406000310080c0400f00b854640c2c00a580c0303110301c001c02410551900d4102d820000c1500c260b0b510102981d8062000f01e895801d00ca541c3d0984544040c814040d4200014013410004107c840aa4016165070900c031094442801d60b11405050550011507012a10010400300070141000d05865000076075a035110f04018000d82d003c038004c0302c02108003009132402598000915408452007820701d01e07203030003230311005980108801d01e0396a4000710001d8480100407003035100c83d4040e880f84031003454409034910016524001d040c4004d411a0030100481c0c04520010080c002c014415401e04603482e40340c10070850601801d940d8000030844080042c01050380602981002e0300000d00d0810a8210b182c6607541c2e07880c2400c0b008103904440c0b202481d28121084211042c8420f0210b8104048602102d06aa16040309a503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 27240779 1250 27239529 27239543
    0x1205031204031e0c081207022404060b010e011d010e060c0a02010807050c0a110d0503070b040b06030111181201020a20011802060309070e0705030a0e12250606090603 73
    0x1240030f000b406081200180c82d0040e600c5d81c2009500d8042d201e1141005c3e1041c0d055102c1c3c4400100b0008003510036131034400b211109030b00c00d410300780b0303182042c0c0c0d503082c400a051207070080b00c1e1450759902400c0045507860740b003202c24555200341c0060390b0412020f810302e81c0150000904040745800001c050041501c00e030f881e8500b80c1c2c2c801d00100c613903002c0d400540241d500040600000f0440440850441000080405460215030384d82c65140d43d010010407545941c1c0d03003081005210a000c11141e010300250003e00c08500700c0c0c8000b050714801d4403200481c0006040350801540c1750041600307070047c59903001715921508810094440c40603007404030407a52160350100e0400030180190400034001a03444001c140e5580e00f08400ca030401824200e803841441c0000408040c1c0c401c250f40903804c1d686816507030742081d1174100191920390380e45d502c0a0344480459442000107104071030040e001d40d43e0083c1e006d4400c4230f08445d00845804042d080718180000455058144d60207403046038401e001c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 27242029 1250 27240779 27240827
    0x110702102303190905030a030917070b040c151707020a0209040506150f0a06050915030c0417060601090509100305010f1b02070e0601080a0207022d011404120503120403 74
    0x2054804d941804034002d001b9001440500c031418000c2e08460f42d030a105488030301300380c544825035841e140c00c54003041e5150b40d1160148814401c0007803409000c2c00c9901c04100c0c899400c0e4901034495030280d1703002d0318694130360000200200d1080c084880c24650007041c0c000241858240596030740000e544d803c6c0d0b41e1000d500c190034503103400b140c000e07440c80d0007816a0444518000c02998650040003666400c2648903d80031040010900114844c4503403801041d215410000c072682e2440b07a241d4505544d902407000e00600d40e800940e81002c40e001100c40c4c0c250b41c0d46100d50401c0394005580020001d60805404586808058104e60510381420709640c045401201040303a46103a98460088030070b4220000c2000e95100d0760105503c1500c25001500c0c4c16a15408248902e8482035004420a15425010034600c4012484070305207000b441c200d019400d4241841066105d28070507000c4101c504020201000401e10a4440140b41644440701c2c600c1c00341000b61840d15a0f085000b26513084032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 27243279 1250 27242029 27242071
    0x1b060605030d050903070308250b070201050705070203060f18030a0206150102060115080907030b0403080a050606040605220801061706091903050d14010902090f0301110702102303 79
    0x202030328412480217004046032440d41d1281c800c40ea01c80103185030214100c030304001b04e04240d955456503145c401d041410151921140c024210340c005040702007004020000303580036030780004000e42c00060750b2039696403a403507021146183c02040380b040c69141c08007181100034290040b810a10030340c107822010846001d1007004a8540f00d0900852102d10304180e070f1180f0440c030032401ea039400240402151159a01d80c0c45600c3c240100312402c800043c0c2c50010002c0964050142c16005402a15500c6c101801c050001d001400b070344c1030b136007403c40521000c0c03c810327180c0000780801001c201000f00b00194680e0301c518580850300c5090300341407242e040480d40c1c0000015403042041c207149508102e0842c10341c0e04640070342c000d800c02030386140c407507120030b25110304120428024480c000c0700599500e03000d0103100c500c20500c00c1c0c151003a45062150700010940302c04440005604030b98401c050210b40300103035051444000040c0c600c500c0090303807a041c035000a000310701030b40b07000d441c0c500e12001003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 27244529 1250 27243279 27243287
    0x140a03021b01021e1617010b040c080c1309020d0e061303021b03011e0b030c010e0901030314130303020604030e1c02011107050d06090210090b090d031b060605030d 72
    0x109255900507444020300d1100c200000f00c40d02d4a50180074140c411001c0c05a1145d42d000c0702e6600b00421801c1007160703440c20500240301e658103070002035400b80941203000c013010341030242c01000320021007000291004424001020b01c0302920f040c1c4000c40d1910340765041d0b80c0003021801c0c001d4000340b190a02181d288644d4110107822030b5810b81c0100140c1103003221015243c00d040540d160903640764420100080d014480d0a52000d00c00d11001030018950b00800d86001904501d20741400b1014810b80301ca03450343e600e0a07056a815050080d01c0200d4200c2204082c4a000580b101c90740000c84007008055020806600480c002d5884089000c0d46001700300813541040d0304410314907208140440154041c23850b0704c01030b151820640e00d900790f1350000b0620f42c42d201041250b52580d500c450340c0442c80c00c0c1c0226440d0b021a80f4025500d641840d42500c1940708544e038103071003003d031034030f00c00105881841d1055940c25410469000c9079a1860290041c01d07042c001c0c248030b401030a0780400d20340d01c5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 27245779 1250 27244529 27244573
    0x4060506240f0d1b1b030509090403020708060103030c03080a0203010b0711030c0411040306060605040b0406030905031e030a0e030a0219050703080319140103020f010e0d140a0302 79
    0x80d084804000000050182001c2e0780300d000e50920440040c4000f2001100d10310426440c40440350168154824075000141035000035000c240104840d042e40c480402d510400303454044a00341c4000d065500d80707050076442c011440d4403070561841044004001c1540c00045410402e1007a02c84820a8603216001d1081c2d00090184ca40b504105100800c0442d0f081e0310580c03002d0074040c043d00c804002d40300208003030324030780c410784180208005810410812548111401403685242c81c43c142030501c180000346205900c6100c080585a105a600b4091b042c4101c85910300c45441c0f080d410540709540703003507070b030402c44e91001036500d00308075089a1400401110500348041d4080c010140f040da8080c291b02e02401010381c0d031841110808400036050500460150904030030032981141c60b01d80310300a9401103140100141d00403401000180c443c10664070614009003441848103005e03201140ca0040307100e001500140310030f000c41c603021101042c000c554a000794252030100c50b44440e20440c2c001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 27247029 1250 27245779 27245809
    0xa020c0a03080f0703090305010e1e030702090f0c040e0f0402040c09050604090225030305060a08010911060a2304080d0813020d020a0e0c0301050901080c0307030b0601020109050102040e04060506 86
    0x4000c12510300096840c80084c140c50b4801d003001d40d00c49072292201401c4803584004c1d55800ea201000d00c0040c4030200040e0092291090011480c01d4299400b01e9000d11000d13102d0108480604003042d83c85582005843c040c1c43c286484c0c1d0181d240c580046281520b080d10240d00540c40c2070160400d48d84150035601c265030015140a107054580020403000b54041503d245005401200107880c401d9542040b54401e030007582c0c0480c20341007100800440000302c2c2c0c0502c07810b82c903201000000032003240c3c04a102c144125223907501c1e800c0c5000c0a070b0f18181d0303103500b0f1103c6420031002050076030f000d000a0001c2e240d09000710f07070345440003031019620340100381d51141c0f441450000f52070041c5052441c0d80203044c405403180b000c89544090b60142d032401900d00c0643c800001c4014091424015001030040c084e160040400100c0d02d80032a4845001e03000c003500d803610000014001c1d0b4000d4100e150b0031940300700215510f684d122040c040c0484241c800b220424100004503102e49040180392140513 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 27248279 1250 27247029 27247043
    0x140a0c0201120504051b0303040e011806050307060c030302030709030b07080a0f020a050301090902030f06040818061c050402030f0312011706091002070510090f0201093215040602030a020c0a03 85
    0x21b0413203000c0f422003001c0c0242c09a0500c010080440e11410ba203a070b0078002c01018051828407070300300b0465000c1e12007a410950180d071007c041001001e0313100d00707230b4004d6070b41500740141e0380d4551260860748091103030005895400c0700001e0040d9a40d01c0910a4424264540d0410404c2880b00d045820b0f40b0030242d0b08400150140300600c618a065440316044032b10080c102e486d46855240b612341084e01c12102510100400304403003c201500100d44120000c08544141c50624505040c49011000320454200030781d50f48006030454404229a4090322210300031a80c98030300d203d1040140f0030b024040c02c03049103550038001e0b82d1040001784080c00341003554040d01c0c84000c00d0903900c000f5082000240c40074415810102810300345c1340f15202d5450300840000524001030300015011920507441040e14103102c07100c031421032102d06a9040015480c0308011507040a172000216030010b1580b034483e070703840e0000d000200503400100506201030b680c0c0a86403040c02000800244151503c00071b0084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 27249529 1250 27248279 27248293
    0x111306050d020603060406081c0f0906091404090203011803020114060901120516060e01030c020d080615092e170406020a02030c0106090c090905090a02040507140a0c020112050405 79
    0x42c0f90580240d6030011018100144480d0344110a52400c0c03981d0941404d29801e0041785620b4a5101e14007061075040c5042c5001960f280400040c5942038501c11001d07000da4143ca80d074880d6941d50054909107800074000e00c0301004500d50403542ca269480128055841c00003500d4142043c1c100d07013481020014200e900742c0c3e1800b01d02c40d0031b00d44821821101070080620301c0c0c1401130840c1e034020103401541d98004150850b030700050f007202c15200090042d548000d08619407240d00211842d4005000e59621910314802a68441c2c0b134001c201d80c0751350005107400310401100c0c510b00203181c0314a4100218210842c02e0b6000d441d680344a440c001c541d02d03840400503010030419001001600e10510403680b030048101207150855409811460505407215400c82103075034402d520300c002d003480003030070003540c28000502540d56000350b03030003070203031b501d42001800c6180078500d5200b03804024403290799501200703034005006020341c0740102e01140700485c081c80207407824841d06220b1580f1500030184c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 27250779 1250 27249529 27249533
    0x41404170403060c050406030518070306020a0903050106030b0a11040303050703180e04051606020d020c10031103010909050607030504120c1103031209071208030c09040b040504111306050d 83
    0x11984502014a158030030030007002000540c0303842031030000c00660340da40740c03920300b8418001e081c0c2e4400b605200c0140550f0700c3c13035842d0000208a00301240c0d070042006a8410490400381d55005490f40050402d5107044d0002052141c403085480c45a9020a420040d0201400200002c1e0046010180016006000d4000001e0040f40c2504428541ca81c0c80744d070703032070340e600c00851120700485003207071a0341005074803480a28012420b14003070103550000d0828062543d200039a03440d0303c080114415064031402c1d22a0b28085c0d440b000131002c034040c0c01070f41c0b5a141c10208014100350a070854041c4207610014480e180300b40701d114021517011020000b10810f8003022a041c071155001610241080e02d1807103950303034040004003150080f03210300000910702092214104400356216082d55000c124100c0001a400ca08681d8003080c4404c80c19120064440800d0042c0912240039401514100c01e120500c40858480340c0608812900b6807000c900180c824010f0f83d58600c100307a0030503407811507400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 27252029 1250 27250779 27250793
    0x6030e071403010902060a0e010e01020708030d0207060b04020f0c06090705090a020307030608160603110c0312090a050d0801051905030705060c03121e0f040c0b09030a02030a0501020901030605041404 88
    0x65010307004002080b100b05640000e000c580c0700300450b00101d070704007110604a50b08603403803030884c1c042400941b03401d5140c0000340d030316031103007401c00405550b0014245041180e135600c00c1036442c03005042191120b1460681c0c546541c1305515501d8a40f052200203a481d44001841c5800d07104003404925182e2542704011002c0c2d0400380c0800103064580c000859286410440d03908120349440c00b07854902e01d08a07001d0100c0310b03001100c0038003641c1040149001d10b000070880740914990084c0c08129510008010308001c05148000c045020b00541121744d01d9000c00d0031810b81c0c1e0202c5685c503661b104580c81640c45c40f0740e8401c641c0c06400c0b020080010b0301c0d0403001341000000710019245400000c002882440760222805090805150045e00d03503440340d00c1000d03900506d10318100030182441c1d125115010041d02c24079000590010b503800d16500c1c10b101c440c1e800c95028080fa1007a00e00c61603e03034080d4001d1440c4a0000380703000c138002950f00e800c0c020358183c034028008410681d100c4e0b883d628 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 27253279 1250 27252029 27252059
    0x6060c02090a0e0d14071502090a0605040b1603021203010e070f0e03070302061e030a050405010c02031c0c050705011a0102060603070b030411010905061303060f0212130c09150f06030e07 82
    0xe1180c424008080811201c103417002d45003440390790040c0e03104d034600200110032b2856001001006002d000030300014036454120381c1c000c507078840c10b0700144801d4a4100e16040c1c0e000e10300302c403109002c000003810f1280d80320114014840c5071103203611403002d01d00445481810001d036035030640c442c807020000b6040800081184000c60b0305110840e501d1001da506c03103980280c41c2104c0869554040100b880713001c0c803400e2000701b19403020b545000d40c25244207450113087c0c8a00c2e44d07030325550070503150050b01039411034043c240d101000380448000c480c0032034408150f410b0510b01500035032000800910f00810030a0503a03403040d0a2a0840c0ca0b40c2d110701c03c109103211051414041401004201a512280500011104d0001041c4014154609a4103031751007428400c02d400d00601c81102c03139101c41c041301640000096282200804c0704c2c03d1507400940ca41c5d02860780e1520300000201c01c64410348e2410151041440000c1030703035549820840448404520141440d00840002c1c05400d070752044003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 27254529 1250 27253279 27253307
    0x20d0b0408090a03050a060f0603080f090301020427050705030907031106070501090b0a11040f030609150f0c0206060a06080c210c0304020f0f100e01020304030606060c02090a0e0d 79
    0xd0b0b0030700705041c0c04240010080d401c251013560204607181e04018160140d0b42620f00ca440c1d06200f458a903903030340f04050148110b0304c018000e01144a6001e0b85095048d18000c0551388811000480307a00d10b0981c44101d41200f00000e2800c1c200081e4009002e8811640254141c000600c0e0f42d07032444c1c17924144543c00c4200664842c1b0208189004600309008071030030a030080c61916203604140c20301d00101d0f4041ca4a800c50ba200c00c0c04101f1808140716850401c80303030070000c04108521540327807100c24080c1d10030900715820315100001420003859405060303440540d0302120301d42d485079420080c2d5030100b03114070400106680300040b0b1540c080380150420042e044542030a1001c54089601c031890b0844103078803034800c08810001075103400c0028260050301544e410350b540503c07801265241c890022580b041c0490082e01c490564400c100721401140c0203107007003094507260340c0e006204208001c0140c1c0300d098801d011030041d010a1003600c21900170b0303400a014200424a0a5600b01101c081e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 27255779 1250 27254529 27254543
    0xd09030e030609010c08010609050f01080606210a0f050903040603090201020712060b04060603021608031017100b090f0412111b120a030207050405090f12030702010501050d020d0b04 80
    0x40562074404115050055815000120740005040341c02001524164010300420034214020011521801e0103071441d004203182010550390340402080081c810150000b2074980304c15151350705020404281802101380c1c03001441000e500500550070384070b05580710701d001d400410042104c0ca01030390200038400e1040c0180c403a02da903100d9040c0c1c1304c070000301c0e0180c0703170301c0d880c2d103641c81003403074548038520280666040031400c2890840c40342c62601d07894040240f540034004040352591007a80140b00003451820205044a2042c0034401d84a0452000b100707001800c2c80003484952401400c903610640d0b611507202080d07999900c0d9545005054a90300d418003c0c03120240581c143d0500000a8803042c20303026003020300c0248188500120202400301c0103420180b440d8001a9000c0341240450310119000b02e05a01c5002020b8101002113010030a82d1254050350f1110b0446400518420516500204147c0e0f80e25414002500c28640c8001e5008a45501000000c0c8010091079000390081c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 27257029 1250 27255779 27255797
    0x1050d0f0b0a0510050901031a070e0a031a070e0d0b06040f0501060c0c09060b090411090607150608010515090a0608010e03070b10061e030b03010f09020f030a02060d0903 75
    0x1550120300805a40081160f9110b2080041c070541e1440480d00500d410f940c5540503601d141c40c1e480800c0c0c500e8400001c50100076021402417441800c480c45552001001c42c001190350b03240400e40b218a60a00301040d527241400100305502801480f143c3c10030240004410056075035515600c3c6034010061a0b2040da00c802c40b015007155445168040d05c001d44801c0b040f051542400720380381515601a0302d00030f007851402c1c84240041e1040d190600c000395008910840d01030b00b032000c580151004150002004a854400c0c0a200a4601c5000038115000c01c085d580340c403000fa0a8800c202e900c0303003c0c010000c001a900d030502080803036001c071800ba40081d0007525000b1250039120081345055946d8408618441400a020040d030380004002d0581c0700c102e4504500034040481121242e80b030f0407071b1500c82e000440d019422565070408014000c11454010f00d0042d070040102c004141d0140d4680155003c0f28107001030741201c0b0070b0b00100414106040d505940001e0245071000310100081b6403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 27258279 1250 27257029 27257033
    0x3030714010f0906020a030509160504230702010605011103070c1202060d0609050105010f090e0112050703050715030b0405071709011103011508070215010612141015020c060301050d0f 81
    0x302c1440607051085a000d46d07100806400201038400103400d0091340d4200d1840e0948000858200502700c0d0b60a80b4041000e120107680c1c9101115582010b0440030200010440c0c5543e042d4444415076000340c0719124441402c031215641c81c003503400d0042c0401c2d1a44e009115807141664442c058a1008101f04d1404202c1e600300420740b1140c2d40020085034031000180010760704090580b00e0410039190030745030146031030500303150b0070010710032041541c00005c02401030040c180107120141d03410104841605503562407020175541001d50b40c40000c0e10748584107800780381c603000390381c01210240d980141d0700c00e441007a80348001e00076201c00700e20f6584116568203200c01101844c0201643d040d640c031904c2d040c0d4006003940600411407030864014840b100003400390030105605484035441c150f03209004c1f001c038003001002c0300030415180014680c20881c507801040102410340d03006002c885400f00d5660300581e610f904410055030b000b1024001407000741400b103c2d80d80118000d0040c4807980a150f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 27259529 1250 27258279 27258281
    0x70b0c160b0105010e120c120c1207080c01050f0904050726040204050615040905040602041211030f0c01020703060e070509041a01050102030304170307020a150e0c04090203030714010f 81
    0x1110044803035007001001002690703007041805408401c20f0302c4441d1700c4110059400d03101c0c605510048d228520102d1030001c0c80c030b410005c400382c2003800390440402018568038603948042e203100e0310091b48035245080c80207504c00c00556a01003044020b141c2008034800420003c1c2c000108008100329a80960500705540c0c078800e2202e031440000c0211090030280180025a40000c014a00030400041c130088031443c10300031a0204d81e40ca080004030342d1258038040b0081d2081d68000070051150030842018494034051456501104904031201003a00401e0903440b1f401e564880c030f000da001000100b000c140b5a40202d030340d80094005440a040e00c0d2070001d0884d01c01940c00b601d145070b14000382500540c41c00744950150000340011811840d0996070a440c11400380600703e403803e80400070400c190f0003041200001540019425202c00b10f0906d00c100a00d10a60b00b00014407912111800c24141485848240354000c0c014500e0480e0680f542c0c000100c00580c013543d690341e285208051842d10b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 27260779 1250 27259529 27259567
    0x20a080d0c020c0a0302030705060703030209060f09030c0a0501081605040e0903041e0b03340809100506031002030c0c010e0c013515060f07060c05030408070b0c 71
    0x586240020801c40800380203160881c0e20312294003400c1450403d00c0580d40000e0a44100c40703040350b12965032203503450704901078011b02e00c6203500080007091400e481400300014002c1040190122000417500100b0401d0014251241d603020030818030100d0000c80c442c0644008111440c10309030300e400e60340c5030651021007085884000f20340012505100b1406910001c100c031030100c200c110522130405041201c030b4400a8102c9103040b02c800e0011503224402104072038803804140d840c41c3d14140740100903104030000c5034066224000c2080007a03c00819200d01c1c3c2c010030000d0f00600c400d507540704d01f0200951010b8000724a03da018822451810424083c07014001c80d50400f4000300307050718001400f06408020300e5000c10700305040c03514101002e0480c043e02c03502c45010100301c80d150a100903c0000b442d1030300c2c0d0b4000c4400560705103408101c400800409201d6402008071100c00b01d011201c07070000340d60080c460541080200041100040c11980000070b50041c01e00d4120580c0c518109100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 27262029 1250 27260779 27260797
    0x130603050a11041409070518040507090801020d050714070507090f02090a17070e06060304030c03140a1d060307080a09021c1a240d05010209060301030f06060515030a0c020a08 77
    0x7401384d840450501d0400303950400b90341c1c2001400d108a07031840700802e980c1d4451641c01166500b000481b580e03c9450800000c00298000f103580d03040a548440141c541141c4120214520800706680408810101d03901d55401202078031042e8140301c2944040c06003020020140380d001d128040d20f81e036a009070700c402804c05030104440c4403c000440360401c00d580c2e0015009003000e1040194688603141141c1d4842c0e07251900da90316a203146000d8918200803089049030f070301c000c18038414041c7c10010003a031910740c1d0703080d0404400c0564204102440101e529800080a20340032580320705098001c40443c41c402007250f5207540b1546149131242030000700545030580b1000d1841002c3e40c003075003125045044402503403500c004454266044049042ca0140569103e81a00c0b050200a50550701b16030310013800c441d5603583da810456101c07240040c080c1c0d0410f144c018001024900f54014168000c072804629081d65185d6100000401ca01c0c82c03e00c0030360182000002c000388201008200ca11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 27263279 1250 27262029 27262049
    0x110a02030705010f0522050106030503030907030201030608010203010303211b0807030f0b030c0112020c0102030705041715040b06030c030a030207060905030c06030a020912070e0601030c05130603050a1104 90
    0x303000340c2406401d4600e0103502c880005d2420040c0048005180703000c152206400c803900d403d022480c030300940100803c0e84042d081c1d000c048140b042c240d0020944404680c000d0707030240065074940c00102c3c201d100c01c1c88010080342c14030040c40d124a4a81c900b40c40303003082e012030018071115a04104403095443c0d48114000841c00410002c5045d018031412040c4c4070313030010030040000c40201007580c9490080140d8103006c1803002d04080510281c0440d02c1d0b01f24500c0096481c2d0800c40d80180881e000b07400340604080c000a440d64551a00154050b541807001100380980e132160b450340c000ba400050021901400360410084254500f041001c940034841c0e40202109490080c00509001182d00403074840d400442d14808075a444034142ea8000c100f00c0c400583c1d91108900050315040300e030740d008050380030f40d00c2c0001d44011181c11103032081030283c03000d2000c11041d801c100d89078421544200080141c4000c1401040d03c00c0c0d201030307800030103143c0010310f050207168038a03800d80140d03020b40f03240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 27264529 1250 27263279 27263287
    0x11040902040e10080a260714030301030201090608070503010b0a0302040308030414060c04050102030702060c0109050601150f030c020a11031f050a0c08040c03170f040603051b0a0905060d110a0203 86
    0x4403d1000b80320050201c903020f00b6408800d513548400208402a00c03107142c1807002c1c2800c400c0000002160203061788659a030101c00c00d006000c41c0c8a80007480181c1c040307030102c3c40010341c00740920186445800c05a880b64550f0b030034081c2513042508a142e1603000c1560a0002000045074100254002c6015100c0d012140104a44071072412400504581040314180800c00441c1d8000061b9020545c3c126802500c4102e07aa80240c010080c680c8041c00e24801c0d00000079002070344031036040601280356900451502d0441040d001e030707083e1246100041e4000720560300810001c0e00c001c207020074000c040d01d0800360203a030f0000c0701c2740110814014281d40e0b20b0074040c0240551081603410701c801d050030100c070701e0240c5800c07001340c00e14440a4000d4480022840581040b074040b10612290b00000b983c440d925100010b000b0031003142c3c00942c501d09110030654902c02d81c8156428091696141078903541401d0601245410179280d04600c079440711540403201c00ea040c0a410500c00d242d0095440d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 27265779 1250 27264529 27264541
    0x903070b090a0507050301270501090b01031a060307060e060a02160807170c0d14010209040507090305061b03070f030f0f090b010902120412020307021002010516030608070911040902040e 82
    0x41040c00d80c0020306c00d178580040034401700c03801c44883c11006015001650b002800b401c0c85400340125038002480090610700200810580540b044004504c40d2078600e059a0782c1300c01d1650302c1d03140340241404524070800412080c94554018154001d152050b90395500d9440c901240f400b0345a04805100d4200e5082402400300b01d2404500189c46031000b40840300c3d400c070100341039000440000d440086101d4507605004000d40441d400c6c2070b000b40003009203180c010b000401040782400122503a00600c00130900c146404800c0c45c10388141c480c034071451612800419625036030b6441140d018551690320000c00c80302c26125484030401d4400700030400c4034091402d44003200050b0015050144180b00d1204180340101c05035078000d031302002c8541c0c001e05a40003649035021300c42c4002c4d403100d1100d007a14046a81908110701906628000303411522160100758207071002809a0060382e40304500420644a6503000005048481c82c86240303055107139181d08041c0d07032150300520640070b0b9060a20039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 27267029 1250 27265779 27265783
    0x8040801200d02070f1b140d031707020109021c0c06020609070303050702010c150c03060506121f12080c061e0a0b0112020a110d030b0102060705030903070b090a05 72
    0x801e855190a18150491a203010311800b40a00702515000590124078a420000540740c282c0342241c0010080442404100072071003a280c8a00407002d02034005c07001078100f4205240800c901030b50607221001d16a040c81e000d1200501c00514400031592100305038405602c0c2d032010700358070045410b11441d5140c45410b28904c204007a5002c401190b0008040007401400802c801055a5140c50f00595030301041c001202c040c5141c0e900a4021028000054040c105941c01100488074988051003103550b00c40400405000d0080314030030403805c00700004c400d0b1801c042201d0210310400d00700b40040e5100d1020009298003120226180100090340d21662a420000141d02508008070410207501040c000144030b080607007054969a140c0300044400d0703002e02c1d60020000090b071021912600d9140001b000c40c05003400c8505240101002091902d05c03a0007002150384041c1c00800445c1c03641e07501164964030003403854006010900c4a100065008005c81e405105804010f040031582da09044d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 27268279 1250 27267029 27267041
    0x6060f03030415050c0c0307080304170111030108010b030d03060506070b09030f03130b0f07090303031a1203071e050d08130503070308251b02010309050d0215100503060a02070311010908040801 85
    0x71f2195100003c104080c0c070002048805441c003845040c070200400b07818045c0034041c07881d04000300340d4012001040521056000c2c0c071000408408032a510b40455509404131510790040710f411110030050340e07001c500316040c803e4104411b002202d10700002c650102d041c60b0010f98846a0b40100d840a0905100c4030000c969002100c8409402142c01c004074041c042c1c0c2c0b898480181070584590b542404601120f24084562001600c0c0d50785401c4684119500c03036200000444000761040400440207451038500707004998000000c0115450308201034503004402407045031850001c0c40c1401c00248144003a0007038030300c60b40b0303450b1b2141882c2c50300d0300c00c41e4201c04120003c4001e210307034001c001d45d01060080c1c072075810240070030b500c8401d03000407000307000050000ba00d207200b4000702d005012360014400d0b03075004650401d10310301c0c0c6640d5554900041e1a02c28140c0c1a3300c00d1010403030881c581c2d4000c0150034860300708400d500302d556000e14250f500e095802d80b01041c000c102000b4140c0207008403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 27269529 1250 27268279 27268303
    0xc0c1a07050d0503010b0a0e030109020a08010507090602032d07080d1409030306010c12020c030601030812070f0f030f09140d02010b030a0b1501110709020a020d03090506060f03030415050c 83
    0x3e5130a540c100f41e000c003001c0c0070701c282d03c0341003085641040c4001c2d02c0a5000200f070a401400d11000e00792181307c03840c0607000a80300d001c000340041000151941c130101c10b1751500c0000303205564003000d07651012010a80132880000c501c46081007000006040714008013100390800e0340c08105503080c00f0010b105441c0060400c03415410400400240d40e0380f2a91540400e58050800c1c40700e8425494100d2030071098004031a05031207410b00200a200da914040c01c5402c2c1c032080c003401240c0c3c98560495200912068100204000c02d14401d00d040c021340040741c240015080000d52005982c030740c40c5650102140c400801e4005904ca2051194203000c0c1c03070b80412060f0010203d110780c1c0d48e40d40d103507141c0082081c5100418020304407420381c402d8070351024190f059001c03140065210200c0342d00035031200030700c1005849407041d80c540c00c502a010316140d15401138003402c4184d50310010310101d1048503480641c1070200f04030100d40644594142002d4110036a5101c0d140d4400740311092070100907a0359 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 27270779 1250 27269529 27269537
    0x504030b0a0b130e060a0c2309040906090203010c05040b0d0e0a08180f1f03020f0c01060e0f0a05070e010f0306030c1e0f050306010303140403201017070c0c1a07050d 73
    0x2281440a81184242110f10035102d600750105410b03410231202801a074035015070003400d04404a09115884e000045014000ca008001442d0402c0c81601c05201e1751040b009502004d00c2100b00024441d40b2039000800b01d0b5054640551f56640c60095550107070002c01c440036281050940d640c00c0c10150320b83d030004251035281c003002c1002c0881c0750160151119078105900064100b4699013840b0944400c0c40b100002440070340e17210301c640f201502046403255440001c1c280042c441503440c1c05480e001d52245e4841d40004003541b001112134440d07960303040d000e03d5101c801c0000001d1003010168010103a41c4c00e8202c0030a114182607a4900c02a40418644141a5001e00c40c5d507a0205101e4112545800c2140c076240d141740c0300c2c02031400341da84085c00d80985948600c40b44624580011590981103406940c3d540c105541550001c0346c0c5c050300301e1031100b584001143e09014602105010780588842e081413a52a44001d00f24444e45030341c0d103090103002c03401d40b04002c0104000d01c408812420 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 27272029 1250 27270779 27270791
    0xf030c36020a0207030b040c03050f030304030504030609110a0e01060906110c06090a0e010602060402010e1915020f030d090204060501230304021f17070f0504030b0a0b130e060a 78
    0x301a612440c0009100c124a07a0001d200481640200300c91001960301c001c01c01c42c68506400c0038901d41c11244000e44044c000d900c1058a60300c000f008880c803a80d81921403505080c25510f85900501c24024100c1c1c82681d101c074605025640c003130040c0018241016590580d604000000b0a560000c0d40954203000d40104914254180480c212100e00d07400d40d80982c403608410001180041c4541c1700c2001611010004102a5404160180300718000c2c1c8a0800300741519050014105640c0384000d07a03107040440a021816510750210700f4149548100c0702e03501d8214074a01c2c1107070722070f102600d4101c3c0d403a0300741310450505000d0900102401d00b8000408000340c2c904105400301c8160320102840004001011540c905040310b220500301225a00301107607104020f40300c4814202c07203507404203400703001440040c4509110812101d0590328542858910740c0c5174101d0010203400c0394001a260f40740898141c032817060f003c0e82001034040201c1c0689524400908014015080c014a0b0342498 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 27273279 1250 27272029 27272099
    0x30f0c03050d020304050a03110a03080f090910180509010b10090e07030c0503010b07030203070b070c0b06030c06070b090309040e070609080d08060607061103070c0c0f0317070303060f030c 83
    0xb014203803c42740c20103c41c0f807520302d0540001d0700380040c940004103808808140c0c003460b01c0005010f00606003041d112200c01d500c0d00303100100006013501c030788180d1480c1d020b941072007608a40c2100350042c0800c000401c10700210340010310300c9510408000c0019946400130820070459003806600528075007803c105040340214003c0540c4014000c4062010000032550f042502c20011a4602030f0021517264681c1862070008092003026141550f0000c54280403403401e1901188503200304400410031490007005a0300c154a80d071004000301c107940400e004c0c0c60b10545603070085007111010000900791450420720003522045007034211210a60120010b051400e4100c030101d500038004403031058035880c00d481c10b500a001014103000440c107001c024009403030340001c440c15581e880343d440034102c0740d101c4d203403182e4240403440041d00440d603500403903010101c804018003045e8001c0c0380104642d40c8030100304000080a500407903180103a030000b041103402c00f51810801105440e00507440702850 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 27274529 1250 27273279 27273289
    0xb03180106241107050d080306040b04060608060d060b0307030809030d030c0e0603130614160203070209151306032f030601230a12050601050306071d010306030f0c03050d02030405 79
    0x4100d446062011503c454409032904000c000b0041c0f800512030769150a1500e0b02142c0c0e03400a542c4035010f6800e0212840541c50a40101d2059410b1940c1c1c01b14182d40740010844680ca00e001c2c291130007991a075400b0340d0b41c3c50500c6a000514022410746585044010a00d45000200080041094070709401075158542c4020300610100341181c4280d01d0b80c4400525800c10402900c000b80403070300d4454a4001e41403801c2300300c1e125215056910b011000c41ccd900c00da881c2c3c40749010013944100c200001400305c0345544400c65032084050000c00070003444045d403104440d040e4000b4ac4401311a0310300d01407100f52403808105103440c0304040284200019004c00d64070201809140b400360b915582c2101842010820b490f040303e002808010316958507420b4039201d00502809580b94080d2400200c0c01d4100007400342c0c01020156101c0b0683e07148035038001040750b441500541050b44070800000030410048400320340070700410800070103616500d0580c2c030f00780181c131784c00b800e5401c140020003e1f5659 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 27275779 1250 27274529 27274589
    0x80a0209100f14120307060501210503030a051f080c040b0429040b0d0c03020306010f0608010b090402040306060608090c0f010e04050919080c010f020403020d03180b03180106 77
    0x25003c2d141001c10503d10014200614032510b1800ca8070001c22000c0a000058103c81d040301c051030300801501c1e61a03e501c140c8489046005411a0b01c1000400c0c0207445503440380342d01c2122900d114942c2c00d0740c00c6045a01406562040505900400d0702c2c02091405100310100e0b640220b03800c01c48082c021402480c007101c00c0b102040000e40c1c80001d00c1860300d42c1d8121000e034480052030304516508914150355491038600090780640b10380340000c00d010f5003900020b0203640c0d207511050003aa1030100303903041ca80d02c044103950300140c00b07100004c001881805020080c21f91500d60b42134502c2c016443c1c07840c1400f0221811b20400c601d000141441c2d17000250152802c00a41e0046400c0d968004041e241810014500710740b072034102c42000c18409400e019103d0001c4850082c0f0000ca200d03186082039000e03d00020b94804030100441e00002d000c0c038031280078401a818484103055070303042d002601c0d8004448800b416490103206960031030081c42607501824904005810b0907081055628100c2d00d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 27277029 1250 27275779 27275789
    0xe010309030c021e100504060e120a020904030c05030f0a030f110f09040e0d11070e09102406050406030b09010f12030908031c06060206091002030a15080a0209100f 72
    0xd07141c901c4100d55203001c845540c0040016101c04410305c100070005000798000e204d2040002c081e00d400703104520341031452034049854840105085200d5400304403141001800803801e00c12080d90200004409102401d45111000111600e80e82c50b494041d042d1800140028409803500801c4990661250305031254001429003164841c1a01c0303000c980100025074282543d44512160030905641c801504c0c0c4190040e00b05540c80c0665030090307055031031000d41e0301c141541c20040c1d841c8801d03111a07009a00800001c145205a0114500c0c610115012500032200080c400a41805120340500070402c3c141d0041e54510455894141d1618008079203010b04a0b044510b54100c200307042c8960300e1000900100400c4e26a00c210201c046495484100c54691120381014000240d00c0c0c004945107200d4403075800500f415884e200c1d45503000b58401401c00c0c5026603250600490798107504281c00281142c0d400520b0b09440b0b80c01040424403004181240750903501000303003c2007403050360760403c4078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 27278279 1250 27277029 27277039
    0xa0504050f01140a0e010b0a090b03040803010506030402130504050606031e0601050f04060e0f09070603060e07111608100b0402030408070f08120a14070302190e0d12020d0e010309030c02 82
    0xfa5640700144001c420755200741e10400c444400800e681e407820004040c0401952140f1541e681e0f140d808001601080382c01401021051004100760304060700155441032004004d0440602044460401c0b10300942e02130381c0c40c0d84a5010001141803c2203402c00880d420703840c182581c05421101980c3c1d6005006081c0140501804240213407a00d401140240035040c10143c018503140d40210402501161180d08500c00c00c140000d07042d0181c0f044c10705468074440c0c00001c0f0342ea81007050340c0204010110310410300c184d184458042c1d2036801340d440607201c0342e406001012034002e030711015207101e41840703845103104005010020b0840c000b2600d541e580004400c0700c45d0418184017046005c0d081c41100e80b1a03c03c41003003d808415400540c8121601401d081c1a0320390319000c6089001e02850046012580c24807000341600590403c3c107141d40081c181080c44080d6510031a50701c8034090600003507400722100c0b480c0d558000d000c82d9142c12013032038100315104680e1002801c80420040190090b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 27279529 1250 27278279 27278309
    0x90f0a080d0905060705031f05010903030503060f04020f122203080c04210501050708010308090d0609150606020d0e010c0308060d0c06050901090504050c0304060203180a0b01050a0504050f01 84
    0x200040d500081c02c4950400161140c0d40f811700c1e8081c0083e41300301e420344d515004c03000e00c401020781800819403d644040c1e450340511400c40c0d80c1a1807a5101074022030340322000f8040c03004156240c0c0018072602d210300341080d844141380401e840c8a0a03000c0c003001100407404030010303c101c640071400030036103400d45045030154035880d18544981c072070307134002201114070280100c2004c5081070010340058890340003005903585683c1d048807012002e00006000c090100b01401a42c42c1412001c1000e0b0700500000a0b40446c076900e40751854a100d24009000c1d49455040200b945c0611250b074074041c90341031070b1945000702c0b0002000b044100c0c1008090103095004901c083e00d0310310252000d190710905100841b500c407900913142e500f0030094140059034881c8007144c0c13410700e4094240510f540000310703400c503221940c43e00040e42004062070701c1201c00155032486154100700c2d4218031130041c00c4a10640d410b00c010700c0085102d40c1c0015010f14108000c0c8540004134814490440d110441c0c20029 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 27280779 1250 27279529 27279547
    0x30b090f061c0506090d08250e010509060d0905060105091603090309030b07110d0311040e070302070b0a06030c170312070504090c1e020a02180402010311040603020307020105090f0a08 81
    0x1810300421025000348104c03020880d8040000a00284151680e01c1d055901d07501c5441044d22601104145c1c04035142104801d03429902643c1316a2401034141040d60800d004000410340541099a00f50941910366160105006007032101f6409010141d40b59406480c214050b1042020100426000c250741c0b00396001c103041c030400034440a154072201244441c1010000285100351040c0c440300c01e8040c01e805890703071502034859281120a0805180d013082e1418046d400d00000c003c1000e41810307001c02101000500311098540300d01008500014814118144941180b003d03070001d05507903000d29000341c80041c1c00002e07210440714040e91301d4243c4ea41d140040b1180c3c082c6500c403070348042c1003a030b080000300e0700032507500402d60f01d4142003585030281007006c0f03903034500d000000703900300d50800c410821400c0d40d07090043e41309006060114195081c11076000e030a178040d41c000d40c0001d40c04001d01210340c0d428061503400000c20401417100d4410450030640703031042c0500007041941c0005030191 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 27282029 1250 27280779 27280819
    0xa0f0f0606030f05030d14100306020c0106090501080d020105010b040308030c03061f020c03060c0325030204050303070309050102150912160204061401080c03090309010c08071401020406030b090f06 87
    0x6075501501c109000040c40c13801c90703525009507008191300c80c180350020400b00c1d410441a4418580c010408002c1c91544e200c0c1e000a600403640b00d4215501d0f140302040240b0140500c0d402000d02200400e540541c01c00002d00716030044e00158283d8208000410104003c80240d9411448a100103560f9132034080c0002c10789070202d400b41c1520040c0c0424070407000c0d0040740081c01d40e038080d01591260b03585ea4091411500c01241c0320071205107542e011a00c985400c411080ea588000d0030010b160548034400a465500045002c40024112050910065a050060103203503040c400d4000b0b070500300155840d0700c13600c16401c2c00403840e9000c40d20340310b0002c0034040800036a401400421545031602e5081111048a55095000c00c1502d000728501d01c10030421244218100c81c061414640030000454080c00014001e81b100c0760180100320100b0407000749003000348489400141e4a03444e105000e4191100800120301c250022020060a4006440c01d01d074407001c01c40f031240480d90700301c80040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 27283279 1250 27282029 27282041
    0xb01030b0904031d0604051008270615030105041106030c0918070207170a0209060619110c01030c02030d02030402061207030209040f02070f1101031b020a140a0f0f06 73
    0xda010310700c1824401450380209040c04a05504070003202241286410f00c10786104900c15150880c80030701c0000341c1c00d480380d0b1f007813504494290306404c40c1900040750050050094000030442c0d40050703051000b00355036441d22101c0d0362415402441395191030748514400401030104203008150000c0010a12046c140484000c0003009000541004880da010794940b00c0032a8408098811000702060799900545640b000c50440c90082c20301114a80c2801840742001e042a41c0042c1c09001c160900f854020100004095680d00d40e15103d492001d000d02c3e02c40707003100290500d8034001c46072580544c04021118019009100565a5199440492a58426000c4506040e0385000c04c0c0300c0c40303a03410340050040200844091003800c6203051030000300c3c46409002407582007010080800501f020741c0d0412130321814100000d10001c2c3c403d4200c2c00620b00e00108005800641c5440304005e145403900c0d089110a030001c002500143d5200740c2c400e0b544c5107028000c01004008181000030710f070818 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 27284529 1250 27283279 27283301
    0xd150903030b060d1431050705040c030c0f0504080d0806030f16080d1418030a152406090608040606050a0905010303030e06060901051203070209010b0c10020a0e040b0103 75
    0x907550b0031000040c3c500411a511804184c0c0718450007043c10342280441000b9086c00010b404070003840e100c003100c07021140c1c4080444880c0a156000600c0d07544902c80d906c040c007030a4038003282c04101d044006010f00d4811441c1e105200b41840240034602d000500c05401c0496814241101d031100c00029280c03585d50703018500144070f104d5112500c4582c1c10314040484035081c040f1010442a140c094641000c1204092035540c02808448036a0300d01d00483d040d007030400781c1901c40540740b0751100414105510740b400340103606c880d900f0300052107024100b0080800446928091810483e00600700b008620551040002d038034086030600c07020303521020050134001c101804a40c0d40d03e400c000501400d200a802103840c04000b46040100428101d100e220000c129001d260f09050410032542c6466030f02d2032052006110140040c0c60350032030fa5003c1d06180c0110f64941075081d5201e441d0141c55040c0c614014010700200b4001e940050803001c07540404c80d0045944c0160300c004030004c00d10140c030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 27285779 1250 27284529 27284539
    0x60c09030503030c0901110a080712030605010e0402031302040504060209030d0804020a030314040810060f1d04150f05090307020f060a0806090711010c03060306110703050d020c03070c03030206070206060d150903030b 95
    0x39a0270070401c00009e00090388a484d4100040622000a40440c0d205108150124001c000e2a000c1c900c0c0640c010765000f80203800c0c160300307080180c01080c125802110100c5d0750641c0060303d01c1c3c491404110750030000d031007490042c02134981540030503510016448001c0c144801c03503403484800603404003580d002d030413640d04031200a00040340d81d2002e408148204a01601440804542411181c04481c0c00100c46503030460b06488544d610788071900c80304c079600b45641c0d03030308100f90f086600c0d40a800c3c0a41c265500454690750140100050f802014030b225118010801c442d15413030350841c20030f0b944000c0469602e1050341d9114000c0d605c0a6aa07c0c81e100294070700b03001e0850440c2c16a100030306480c028002006150520800861180f0a41d075014020400502402200014940041501d200000107590030715229980e0040301001903041180542c100c0410002201e034100911035001004641040c900102c980311006510114840c44071516150711004c8145802604541810500602 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 27287029 1250 27285779 27285793
    0xc0a051501030c060507031d0109050d05030c0c060415030b0d0804030605040b010e0106200307020d0f0b06060301030b01060309020a080601080d03050f0c0a120605150304060c09030503030c090111 86
    0x140c204405024081182c00c04000700c000f06400d44204156001d8651644503400040c5c001002801c40c2003800a01a0400000c03650101f00d40c3c950f00000c41d0348030711071001991104c4c0c5680086041c8070f40e14503200c2c003540c420300c4204071702c04801c84140840b4096050000c0c20007040b41c04290510350052000c1c004640000d000803c01c052940418400c50050100c00c81e280d0300c1c0c5020380c035005000e100b9140040c1944800e1021030000450486003c01e071101100e1904542e580880d8460440c0c000584103c041c00c504c13101409201e0040c00d51041d8102c9440d450340d070550f03445510070541802031104040d99444200215100e4001040c06040c42c00e04841483d82c5d02c0496980d211b48034690440001d0600b03001c40d80040038103000d14010001d49040c9400d08042c0182110344002008850206075102c0c0000070342a15201807074010ba692160000ea84c9203840e0801c2000e95000b505500200448070f4800c00c04240080103803a0008224100c0740d41d141101801241c07040044c2c490100b2a0107000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 27288279 1250 27287029 27287053
    0x313030b040b0702010c08150307030c0b09100509030307080f12090105160801030210080405101103100503030304020a030212030702060f070c0e010609030602070c0e040302070f090c050409020c0a05 87
    0x484a14801d0b4441c2608204964420034101e007aa6503c2160b50049482403010640504a5a110300810100502113035405a0b80b6110414044003d50201811203000121103415042c498401c8171032590324102540780525140104c4c1c2d40340306900000c0c1900a0205a55880103030382c404940f0101000e0b0700380072203401c040080a00a00e02603c14401c0700030880410f0415600507031150741201d40051000c45100400300056507507900003041120306005880f16200d4252041c800c12480000340194a912440c051464100501d0a07420580c800d600500030400180d540315030b40c6040d82c0c0d05643d002d00b0589611fa10929500031100001d51042002c10340d8210f0024000c040c0a0150044409400c01d40d500c11070119108000c0c0641c41c0025802c0d603092000c0361168008091403403058645144156950080e003800781b1094070200c0058002e0402002001d071520492409407000c590108030390500702c0b0019006115603c0750004154011407002568070050124000e401e4101041ea2103080c600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 27289529 1250 27288279 27288293
    0x1b16050c03010f090c03120c0b04050c010e04110a1805040606021f020f0703030504020105070204060b030a0f06050604032d0305031f0e0408090406080712060b030a0201050a0f02031303 81
    0x1162286000c0e610701100d024088445000d03d404c0607402481c9485068250780f20100d502203240803110502c110410f15400050307000e40714911490082000d410000c1503030340010007155110000c1031240781802e8216004081c50021283e40b22160b0625045040c51a548821000c019600c8160320034900100041c8558000c2590f28240600310203048042c814200310604078080c00d5405a032040f014080782c00000d02a030711035038020317005044c41e44c1010b00980c001010f42c2c0c1c19030402c241052000c0b041c02a503130700c58000e006050191805c00c5c0301040c00e0001261150060740f0000c0d290080e482e07002c140118a0000070344240703410040304036030708100f03080142c00b0703034020384000303024480705911052207030b242138203440580d2403215555060780c4560300d540c45a50042241c03135600c503030b999600003120312040010700001e2102c020030304c440c089107050800407102c94000d854001c0e009a0100d000507a440411502c4885017410300c0c04562581d804200c0c910300501d402c19862452400300031040c07040b0b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 27290779 1250 27289529 27289543
    0xd0921020f060105040c02060105060d02120c040501020609061b0f04080102030f0603070e100501050c0312042d020d12050d020a02010906050901141b071a0402040507020304030b1b1605 81
    0x180000325881640c1e50000d0204035012046c014006030480c400501c17042c0b070320784003c1c070f0003945214000d810301120040c090400b02c019507481c25003400000b0104110b50301800320a034003000b0743d0b014040300e14020310007405042020100c407075a000b0001e2044190035040b4255006452104001c40d01ca1070b0484911000071401c1d28580e110744100d903070002c4e00c2c03404204428400e080034201000e8189c6010011741d190b41100300c0800140c0028040c030300387c19410f0b40c1050b01c100e00580203220298000310403e44071f200008072041e000e80451015002580f903102e68503501980c46088005e00c0c10041c84220b583d4000d0044c0c46c02c0407400000e045065540c150003085d50035015040810250f11100316440c01c070740c0402886403246203000c0019a6485201c072072030b1300d416071291000385480c0042c1d8074501099103030b50000740120052014801907040c01d00c101c036072000340b03400214036050940e1161038406c81c00426800400070705020b490031050401099176040200500c10300301078061450440d4580746 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 27292029 1250 27290779 27290803
    0x405010605120f07091a0d0b01090e010204050303030606030a0902030a0510150503100b0105091011010609020a0503040b040f0212060f06090606040306020d1404080a0e010e060d092102 81
    0x5080c05010b81e2440c1c0402c0c81d804555240c0001c1c4101c904e03016106002d02003001090080c03684031555295540c0340c4100700c20601d84a41500c050540c10407004d2812140782000941c15680706000c01d0202e03031400011070303030003020803554903031261348000d200c00140c014210000c3d010b00132441c2400400c5030000e01800380d40400c110901c06040c00018a00c0c2070b50040c455180d15030312040d01000c188103903078020180004107150441c5040040703808110084111481c01c0300044101e0345590f00b0820a20452010301081442940340101406008155000c00b03080a031000f2590008142000702003200e040b801c0e03074058400300002d0300e9580800d0716480c1c1120301c01c102080b14000500b070351400712109032180360002c02c1c49040908503120040290001c42c0502d01c840c0e80c2c0c104c0f08241d038440c1e07580c0c80d102d01e1003408215031341c0036000c000401400c4d05006480c18400502c00b040120380e541c41c00e5582d100031604002802c10842e0900040010441c100c3c80c041a40a00d00c42d08251350108182180b04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 27293279 1250 27292029 27292039
    0xd081206061306050304020a091107060b0d03020607080a020d09120e030a020102060a0e072102180618040201020c120705031506060f090102070315020d11030f0402090612060405010605 81
    0x264511052100511550442e00082c0c104800248401409540616046030015242900154580c0e86a0f002c40d50659200c54000e80046449000c02c24035004c1c084c00b00c0010f5400c072007409001c1e07801a64074880508940b05100b004800203500b68501e50540d02c2c1181c01080a2104201508040710340507282c50400c0300182c40f0003801441410002450004540e06900900303071995051f002000a080652624001c0d0040e0307100003400490b583d900303c807c030240388840c0c91064800e00c1003254099144080045411000c0c0821006580781c2c0c00110101314604140c100719a40c51004070b00304070742412000d510643c001009a84940d00103241d00544509034122052100301e907179161059a0101c4600e030b88840e04200503410150100d0107020700303013418011203003129120b40e50401802101d814800a50398045500e804403000e5006406868040d11115895410030003000f03800044001d102038054513a080103d00030303444014500328405a69401e030f034200d0500d803078414086d1100b403085612030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 27294529 1250 27293279 27293281
    0x21201060609060e0f01120c020c0915010206011502030409020d06080a0c030c050303070f1b05030307050a0501060f1508072003030a0b1516030516030807020124120206090d0812 78
    0x43e0805c0c0c01801c424510585444412941804811000e0000841c8030402c41c09401c4c4600e1040d10b4001800b4005c0f680444540522202d00000925080059100b00e07081302003c8c0182d041a9004422a800c0d584080c0c0050faa03440468180005083d0390341c441222071040c80b00321000d0001a0003108140c0b442009251201d5545034105a564095428064503c003066045003002030104108119803101d01d0800032025552480042c0c15a00041801d0343c507504415144410401d00b03114000141000da83d1440d099403e08041448140e801007002d010300c40d150b030120300a14050003c00c211442e00b2002d9540c8030b013840c0c6641c4c5e107c0e0802c3e2661140300313041c4040c0c600f84d481c1180d0100b160036444040c86040a2030020004013225035444158180b0004008884454001c02d501e80100c900070b407900c00042c1401d4000900716034483c40d06182c42c0c2a130b518500480c0400c07a020030200e40d82c0d00b051412519242c0005501803043c40178080c0d100c0b4040d2009400c000340d00c001f5003807a41c3d05410445107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 27295779 1250 27294529 27294557
    0x17010b0603010503071e080d080703060608070e04020309011104060509030f0c010507120306050904080702100809030f09060408010c08041e08030103140a050d030506130204080c0d02120106060906 86
    0xc0360100b0301030941d064220400c241300c056104102e50221034002c8494444a607595444282014402c2c0741a1000403014410031032082d803d4010840107000902d0448128030b0400c00c000e080daa02c22080510540e000008a10042d0003500700d9840c2500c048000b0340d43d0b03a0b84450143c6198010a009030003800390745580c55407000085186a640ca40c1a151207181410698bd071500d5000e4000401041c03581d43d03071000c1550744030300d020b0720f218a02c10300b01540e07a8003840c010000230800300304858042020300d408001c2c4100c400700030741ea00350001506454450750840c0000d02d06000383d400500b20780d0701e86031310006410fa0081c0403d01540c060310700010107810300540c90181040100006c1e01099040004100103042103002480030750039007081d14a01e5402d41d80302d5042c45160a450f4001a0f100c1d03084c45440d00c2c0c19250301d52407150245086142c5450b01c0b030302d03035141d11040040c00c2c8106000403103c0159210071401010a2085400030007040b5110324001d0a10403103805410000f0b1540303855164 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 27297029 1250 27295779 27295789
    0x5100302030903030a0e0a0609030509090a020306030a082a030a0e03070308040e06211b030d0804060b01020a02060703030204140a140907030e010906140703020a090e070c0c17010b 79
    0x40102c0401c009503186070360b58502c0030043c0241039407000081c030440d010340000c108107109029104d4400d0303072116039076204c0008000705920041c000d540c0382c62040050189540c0c0000b654403045a0290f12280c948800c4c103c85080c2510040c414440742c6e52010080240000100c02000d842c00f05888420540040b60103060360391100c0e000040110000300030611000500c020350f240d02803001400030146800030107404082c2c06040d180c90070305504c80a80303c4100841407462400141c415030081c034000f880e01c00010940070026101400a41e0743d11100041039100780051003407690050081551010a454014000c1d4818411303400c10381070f820a00702880c83e0012900003200c400c183c004172a0b03007040b03080040d9260701800741d90605660f0150041014402e00820394854040c60300052104503011000010324030003400c44040500c10170000c1c54480e0040c0c0030b40291410394020001c0f40d911010203071000b0b02e01a20140c50380711405000079070281d1250140d040301540800920522400e101071007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 27298279 1250 27297029 27297031
    0xe01050f0406020f19020c10080705071704081c0207080606150904061e0317040b0a05070317010321020607080112030521070914010e041d12040510030203 68
    0x1400c0009001040100e0020340292999079440e1108900d840a1103031000070340514030141c40c001d07803c1140160300c10718003880030507141c0c2c2560400c80b4444ca04010002c0403445040703c014401560951140a507206100984000d4400041242c034151504c002211141292181c498014441c01e98080b070300c10008245240140c50240080c0c02d001f40249210407680c020754140c03078005503a554002640c0383c3d01254821103201ea5034024010310f00f98280210041c2c26840000d400078000c00c01008400c100b0421103034149401d00d02b07561103050610b0201c0382c5d2002440c8100400100400120500c030444440c040544201c0080b044680c40ca128166100c0004030f84800110f801c01004101c403c9401c90050704144c46403074250701c1c00a42d4040c81c1c1098223001001034800c07280c0c508000000e40c10204140140c417070703074070340500c200c01080009001803d800e10b40760080d42c940e584159500f00c010301e1005074212681c1a103400c5141c1c515119690741007441280e20500e545501c00c91303a10b000f8401c076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 27299529 1250 27298279 27298291
    0x908190c03020606010e03010e0a080c01060605032e120501050a0b0405070206071404090e06070305100e15121b100302040521070803030a02071a0f0708100803070609060e0105 77
    0x280011382c0e83c150045d40e860004110031500b65498105103032038000700340b003e031441920400c40a81c07601c0540e00c4080c00c540c01500b0072028170804006004840c042c3e000780360404410350720310a001410038054400d100c02030390300c209092a10142c0e908200b02064204c1c03440b5030f05420301048090038003070400042c1d490541e0024096002200410510b9100394401a803800c00303205454505640c1d0751480c406c41e02d4440c1c070311501c5c2c2c00000910903100c2e0706000300794000982d09000d445540c1090804a07040030040c224140c1030b02110740020203071310340300c0c09803404440c100141c5485130382201c400703250742b6149c002c00391056030080c0030882d0290184c03090714140c60001d0302c0c490360002d4280700c6c000e82901c600316458461007900d0002864190070001103118898400c00035803035002c2450000c2444010700580000c985120f81006030591741008400da120146150103411501c1e1224554000780d0f603038020820034000010701ea014082c858001543d9640b2620040084200c1c0005007400ca0f8800d0f103a03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 27300779 1250 27299529 27299533
    0x130e0a0c05030609180307050a06050601080103080d0b0109030c080d030c08011a030408070b04030c0b010f0e0f0a06080105010b07020f030a03050406050c0f0d09080129060705010e010908190c0302 86
    0x807607601d0908800d01a4011000c405140b0b294490300c003240d11351f030030401e02151035500017140701d000c1203058061150031050a007045001d550440da1494010700403000d45000c042c0d500d841e803080582c414010302004540110801c924076485282c0b0f182c440380840c46c2a004242086100c880e1284503151082c1240e08032840d210740090846810308245e80302801c1520002c006100340c0c1c001ca00c001c0301c2540254400d03200c0130103000080c07400c1740d05603005922070032000b401084100000c1e507001c070701c0c20345c4000000c810600944d01c00007210014440c0390401c443c15031808002081d81c5504100825486000310ba15400d6500d0090406070b41321082e50380140094828441040a103002c1c0c0040c00c4030801a07400d4a81000860040a2800b040480001c0004202160400510900307118483d41d200c1600c07403d030000703940c400ea0016001110004c2c2c03802003600080300c405204082d40a05901d407030a0b070085c420031b0000d0509184075000126002d142c5448651100c03070b42402200c03070081040d41900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 27302029 1250 27300779 27300781
    0x20705010c0201030209040e01060305070918060518060103050c0411131a07140d11010903140f0c060f060f030304060207030b040819030f0c0c110d0314130e0a0c0503 73
    0x44541074a403003812810315409000f99584c070358550240e01815640e01d400000c0451550400d82e181c00da00764400c1a15918124a1a14903440b038400741d01d40381d40101c2d010072030380c5030010300011150300c0a1204400c1d0081c04000b0042200100750b41d80030300c100710390038030002c0f5502000d007000e40b2030200c58021540820400304010f04d41aa0320941e40c400e01618242400ca09132902500f1080029141d0010b40000b21300c07105198200401d824112020741c000c0004c2c00503503901030924a00301900140201002c1130b40324001c0a04012240000741c000150303103ca04141030520b41080041e5480303841204005081d5906003400010f5801f107440c02d6008207405e070f00e1a02e9140d48080054030582e0440010014070743e074010682c02004401041e0781c0c0c00980098400303111812641d00e01603000801c040e801c07002d4041005007401607228030382118180c041e605a8607082d90701980f40c4804044040010400c8036003a0070329000c0300b084407101c01030420150b03502c20042080398400c0c500d6001080080c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 27303279 1250 27302029 27302039
    0x810091709031507140706020901090b040b1204050f0a030c0c08030715020306060904060303020c040f060503070e0c0403060504240c0507030e0109030b2a0403080702010c0303140a05010303030e060402010207 91
    0x142050350403503001d080c15100700005d80b03030442c002c0d03004050079254280c001507198581d5034405004030080c20003500080c2818103210b07001040b0312519003030101801100002c1000e10406020f2b42c1a00e003807104c00c50b0022100b03460007600b45c4050600c2500d0b9100000300000d000c0d4030100c1181c55160f0300081c160144041d00341c11800039000075014039000034041c826030724a40c54a201e018040c5019800401c4008a10800c100a40307044c003003604a19400c1042c200010b0b20000351074400c1d01c02c2c041d200001d13a90346140448080c011035002501d00d900b060140828030007080400400c7c4004d144070400178024000040041d039003844004000240d040140d4000301344181c50107000110f0500d01500400e50f203448a1001020542e95074a030028248417804419a28190125600300034000403070400e4516110403d6a008400003c0c2c184501c8084403010984680c0c40035010580c2d0507222611814101007110017460700b400b00320082840c0540c080d10321030000804c107209640c16401084914280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 27304529 1250 27303279 27303313
    0x3060c160b04030212031509150907030911060406080108100203040308070e0310060e060f01090302030a03030e070b0309010b0108071106010603021b0304120b06240304020604081009170903 83
    0x1c1050f811030040340940300c901041d00c0c004501a1a2240c0c9456140b0200030802040d540058800c000c144070010404010b501c41800d5a81d0015040c00c0000d4419024108100c090442e16601070f440140060302058064201e6207150503224100201e42d40303011112140e80480c4415500600442c0e619000a00c9081c425283e070a17a05401405a0350400440d07a052000d940d00741d040504400c44c0c58040043d2800c1103801070001d140c1c2441d007048074a1454011a45900c000e0354068100b60f210b00d4070306111a030411038a4020028042c0e01980c1e4646180050f00030b0044c152040c0c001401200425499480f54461503080d002482c007421645c1d00c0c01d00d007a03000b54005003c00c03540060b03080c01c00d405031406002820041c040e880180f141c2d42e01a1a10307856030301c2c0050045200310004018811280100724800c0d45403041c4841c036540d80d031558000545103000356400032502d449125a02a43c881140d00004842841400040725280c00044140780c1801540842501030340102c40f9030200440c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 27305779 1250 27304529 27304531
    0xa03020d060f06091a091507020612070206160806090402010201020903060c0d0501140913020102070504060b04150315060311090603010303030905060105010e061606090206041e0501020703080a0807140c010b03060c160b 96
    0x191301f00e00361804900740d0100380c3c02d070001c9440085105110080101c0581c0500225600080000c3d00c50f0501a070328201410041d4050003543c041d180c03000c005011a4004d43c105e42c040c800080c00c0302c1d214030b85990710559035403080d011503080c81d0800000142e024005244c103140c0d03490007082900c540e901c000f0041c4500360402803d9045205002d400a13264945123382d20160900c0300790540d580342003030742c0d90a02461b4142303a07400700b616001046041c0b6142c45108005d0711100e24020640c40910100d420340e03400b038841c04684c0120008000410581c16038004840e140c81a8151011030b070b40c404c015035500e4000840315030880700030407c151544181c10300707941404d4400e82e800240c0c007032180c001c224644c02c0741c5c20481c1041603c89034134109440800100c03004040034402400590b082d07640b000c845014050705602030200c604041000140504403101307048018805c0107032903880544141d40602203164800e4040d01a03070022034040d140b02c10460391050000c25100c2caa00c00070755a41039025034 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 27307029 1250 27305779 27305809
    0x3070207320d141005060f0901030b070201020403060c090513090203070b07020d052e0902030327120717030403170c0f03030708011d0613020a03020d060f06091a09 72
    0x46000306070340010120880091000380e848010809002510208811030317602400c0740e80b0400c9800d42400071952554242030640380c0c801e001800548614800b41d0190160b82c03c02040b06081044d03c2c0d81d0183e110b2400001c0f03407000c58100d8100d031059215103040f1010880301a4150300030081c01e1280c40c1a200080510510280112080d000359440311828128402c100c0404140e550f00300c060350f80120454036141d0003401c602000074100070380c0001d642c0d210380401c803500c0c104030034130784061901043c07a0302890b00d8000e48440c0710348000307110b070f13a484844501903240c0d500d0b40f04980d1030700700500000342ea0070f0380d610030a203080d101a03082c030181e1260041c1490802038841d10b14140301180003840030354007404041c0c40d1512154140240c2000e18510081c07807425448490b81009116940c0d00c1c5025002410030100507a01d5603050b80840280c402c062100542c0d5080510001d41102c440d801c200c211000e66803000010368449024810f580c41d0781450303001c032000501c07030946186040900d490003a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 27308279 1250 27307029 27307039
    0x312030a05070f033c050a0906050f09060f041a04050c0a142209080711030c01080408030a0e0705030a030c060e070807030809030c040905030d11090303220803030c0307020732 77
    0x500460b201c00b03403101110b8200c7d00940f0740f0030510800c505805402c1d044180329a2013411854208a91503488030028143d5203944420300114080c080d0100341c070201e001244448006918041c10441c1d0764006541c16180210303000200059066956000154a020000d00004446408150036070901d40b0b554101a081070b0340c0d82080001809402c02002890f100c0e003400505d04048104140c01d001c0c2100f912818080030004100c00119400c04699000060440015212644201c1350340340030307440e410590b05441607886000900d500400e00460283c402d00c1c05100e0001b2155410751920701c82c3c070941d000c40c0e120310014400200400050010500c01030101e40700c019030340000605136454440300761503a030400038040340480034900420240c41251000c0750b14100c11400401d41d01d210f901141d0b03e4429030f60070486010320700c0f00c80140c020000103007205d0300c84c140003c2518031548180c82080c094400c48000140d00c07071341c640880f201c4444100182c204102d8102401e65100007443d007c517840 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 27309529 1250 27308279 27308381
    0x10f080c12010e090d03020a021f0f180c060203090919090203010501060309050c0d0201020613080d0513050c031203060409110303031f0e060d12020102090a171203041106090312030a05070f03 84
    0x41c10840c4140c60555404c2c4ce400c10000140307080000d0180c149070848070454000b00210360384c44d1500d580c034640003c0305a0f5021490102160716000600f080800250305500300b4000040e0320341e064000d0311070f07680141c00303803160f000740304003001001130340650000e0240c2c0003003000480903081c100403000341a00841c1c04034038100301c410340c900845108603003020101003812041c406200c820044209502c206900610400034540400103440c04001d00d00c5204585400d110001c1110441c1c12480c0c10001404880d01d0b81040c0041c080700c031550501c99542c00360310210004004860411245c000d0710058200c0f60944c0040e250740b19101e4a611404c020b544d001c01036445151503143c9002c1c004c24004070b804900130b4102d151603003060190881c040c0301c07400510521001c25030b070000d40345c1e0111044480542d01d030040d401007170030440010501c80b400d1001104101002c0d03055006103210b0b2011b542c0b01601041d81d80790640c01c40d940c0f2130382c4480080e04404440e17040061403800001d00f01c0649094800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 27310779 1250 27309529 27309551
    0x405060d14030a08090606090105130902041406041407080403030209010e06030a06091b09120c170606040c050a0c020d1103070b0405040606090302010f080c12010e090d03020a021f 79
    0x704120510400314640c00000c4000703040b54001d040703a8101c0100300180c1704034140000020340e214410b00800d031168514101c072140d005829031003003010690140050040480c10080c0000581c8121500b83c0034074201030072150072070100300400b44a11681d031a02062a1640d03181140250080d5440700d05000508200704a1643d66001851140018000204141c1e05290990f07007038503842c0d80d5a42002d50b80c101c0390090560090a1082a602582d84414050800342010490203206512000c00e074482e6502180081c540400c00391700c1450140e9061101d03000c880300c200e83d58425507240e0701c0000d04521031003005107808000170180c00d02420110703248010200000f42410031540c00b4046c00c0b94005010003580c00c0c6409548020811400c04204c03152840d00081d00c514001d41c50041005000780001d1202c103030782c9007958603d001d0451203282d59031710340c0004080e040f400d844d154810311440c02015a1a8424002c5900440c0d4941c0501806500207864814115040300684a40c41e250541e01c0ca03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 27312029 1250 27310779 27310793
    0x5030424020903071401050706020d110415110c01080610120c021b150f03090a120c06140c09010e0d050f060403080708010b0307050f1605030301050a080304030506060405060d 77
    0x1420000d0301000603900e51082d41010310b0728185910040002a002e44e690440b0b83e000f4040e100c2d01da40002c00944d0b80c0011902901c01402d41840d40610482e01040100700c1a00c40304c910340c182071950321100f104280c1c01845580c1c40303081c4941180042c007c800059034508118a003580400c01c00e0609800c00351a2400070360a903032085015200503402849208151301001216500640054038a03591481c0c401d81301d90304512611040040c403003000804101100d108005114800343c110181c0b146000001c00001c065100c0000141c0e20343d8113040382c152094000048060007100f2500c0d200b85400d1842e030041d03401c40302d0100c02d030b64000c2c0e0482105021038004e01291401c03c101202528480c9009e15010348414005401a030410880500601c803c0220f0f100712a01303c0e00314109a84c807103001c0c101405682c4100c200c0d03a80341501074210394081010000145050f44c4003200c0408881c0c0d19403126903500e006a20028205a0010000c01c026082641c0066003051018002030021501074076458 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 27313279 1250 27312029 27312083
    0xa060f050904110903070504060305060a0209030a1e0b0601020606031c02010f0509010507030c02030705032703030a030b0a12020303030105060a090816240f08090106170c0f010206090d050304 84
    0x3c0785a10340011524068070341441035901510040320704016150440c4c844c9586c0300d02c020001200c65600040c02c0f545640c0800582d02d109a100201c400c1c5540d10440507049064030903c21a0166000f1000c110303250b00119100d4420b0001400401c0d14261100b00d141010f101c4c1c0303d0400540d560f46408114628650040c40e00c50303072110300046030608010300014110b03003540160302e003150014020071b00000c13804011190091008000303483d0400902020888440d6250000345d4144000035401c264260181c00030b02c4801e0f4103c80406015942e418411214420000700941c1900b003080140120b24180c0060000c2210034648010305949424800d89400020349504008889903041088072090155061880c01c10031042c0c41c0b00f0803441c2c1c1001d07081000450801080c440b4403000610f030410309501200040107940d00740d10b00b803026903080e20b07266140b00f41141d000d4000c5403519200d65000040c01c0d80155002c10003800c1040508200311807035000a030080382d01c1c500b403071400c0c0c400c41d400d07101079 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 27314529 1250 27313279 27313301
    0x2160305090a060306030201050301030b091005040f030207050307060c2a030507031718091902190809010c2111030a050a0e0703080306040209061213030f09050a060f050904 76
    0x40c540d00c2070441c04200745038600740e01100030541408410320050364000e0a50341141d03480240082d40c0e86039402110700f01400700064130b454034900710801c03080c044403152281e000381c000e409940d115a25070060641714407181c0200004035922460b42000120b80801c0e80300c403030384024016003903400405c00345503201d1480e82c025a519803050303d0900501107840310454142482d00c2400707240c407001c000d012509101c4006010f00c1030178610000b8820328040003050b02c217035074076001c2199038a13486c40c50711803000385001103280050700d40c000160800a051080100c40482a01d9925002e444035648000e4000b100c0f04010842d6116208405482c404002a45c000c3c2c058480c0865a80341c041015012902c9e000886070060717004240c20404281603000701ca4200005650242e41d0f40c00714000f1071505d2141e0b402d58201c186800d42004000240143c0740007442d8440d40d50040c0c4803e9940044460f850140500e6601105403103040103039500a01030400c42d0f452900b442420009402d00083c226540700d054 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 27315779 1250 27314529 27314537
    0x90102120412050d020613020103050a02130f15020a020a0306050612010203251701030209061c0804080c090106170a1b020c0f0303070803220507030303020a02060a0501060c0b0a021603 81
    0x16004010303040c4030700114041c06100038074152606041f054a0306c4c1c10b900001c0d0506580da404201d0641c85601114410009040c138822036075512010f20b2285c5105120701c051542c9100b08284001d440400c0000c03d494005210a45907419615120020306016000581c413142d40c1c0398680c000d82c02030000c0c40c414181900d0300390041c0c54030720710020601c40381380340101002038003002020040d034901c10140c152074040e0750000980c1d4030400401e00145260b00d0300c24803003c106c01041d013000502c6009009990800081d12509910300e001d0000383d180038060003011171090450081807802c1c0e1030160b54803480d40c40d00860a20301140d01c00154441800889005800c1000c40f0351090414058103145404207500851400c0705584900195020151007195680e40b121220741000300440400c0c45544c0d0048142e403807a694a2801800030741c095081c0364050700500307001a421116a210f014101e0b40c0f00c1d12045074075409070703035440304403200200a000c940d5820b1010190180540414400041c842d0715 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 27317029 1250 27315779 27315809
    0x1312020109051501030210030c02030d020c160504020405090703022101031209060207080d030b060c01060803040306180f112d09010801060f0302060d0e010f0b0405060108090d050901021204 83
    0x1409400e0100c1c03000030400552401c070040005843c2c0c440001842d811f145400600c01c1030b2031070100d08511508503c088082d0000c101c10143d180003050304125821151041c03038480e55a40144000d90055200d06c45c1e10900b4040000d001900940003403869441805a841070041040350002d907400302a042178400c0314450400495280d00609000b000d01402d00082909a04c1c1001c5156504244940c50b0304241d1126210905610b50700b00755441d49120a0081c00025100c50240c0d903640c000744015030f0b4440c1403510b65004100055a03a8418940113a103030100440182c032040f41c040c080e000c4144e000b66815005819403003d00740d058032840e403031048500002a400040065480b0180c120b4030590745001b03001c000c0100040078501c01c60390f065800646580c40200e20780c000301482d003d920300a5003449848076159000c1c1c3d1100034030400c00c0310101b00c0c0341c90701001181c2c06003040741c040c520396020034504e0414a0041c2d011300150881403044458214583c004a107031500140d21910f12030001107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 27318279 1250 27317029 27317033
    0xd0807020909010b0a0501030e12120601080106031107060c050c0703080a0f02190f140708060a0f0c1d030c0409080c071a0708130e0403020a0203061e06091312020109 73
    0x11682e0020a54402409103240f4007002900b28900f6100b4141859641e41c50840c80c19070070b0040c210021207140304a0303155a070800300f0310501070088511030300040c502c100204003240684241e000d0f8544400005007442583d40d98007005000c1000103405104041c400f036140c04104018240c0a1445208415210500c5074000341c0101e0350918650b0035500041707040b500d00c0120088240045801130340c1e503081d42c8410706200c064590401e2902d0a03a00070f480000c100000c00081c0d142c0034081d80501003012141d0040000100c890300d035a083d00040c001c0340d24001b8000401040c9040701c4000707082d00c909200000c0014111010300400b100c102e0400b00d03134001c2d101018001c1c0b20040030680030081020407012041c0f030303407445045d500800e01c2c0000f04a01a0302c150340c00754400908462640c0784003e04160034040e40c0d403400214102d11038480c00b00014075103a0711089850040145100d00c1d1415100c007420454880d400a00110307000c0403e11424000c1000741303c0f01a140081c0e034000065680d254 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 27319529 1250 27318279 27318289
    0x5030f070e102312030417120309100c02100903030b0a0b0a0203070b1009050903070b070e031b040207080a05030a1404020d06020309070302060a050406320f090d080702 74
    0xd0200c10b90110360101004000766110b906000c0c01100c2900b0f41c101218100007540d20101e042d11510b0b644400b14003c58041c0075500c081102e001d001084541c456642e00c040b105a1204440c4401e0b076400028007014141d00300d400c84a05041e040c0140e5100188880c070000403102641401d6001907100e003412a480d050181d600005000c450f607107a07103090012000030307540307104105000b001030102000042d041c844405141002e00100d800c140060708108100c0342e40c136044200103580d48607100000c9904240540030030320403900081c0240200c100c0315080c00000825049000b40c01c02e03001c10607040050203510040c000d000c4241c40300703501c03820244410f4003203512184100300c4000c616024400965030754001e0a95117503018034056a295504600341d41002c0c02c65000941044000c1540301c1c940d50860003410664175030740da40ca401034881c1c420750a20f49160003e100500344141440c1c42e052a0a100207091440f030448000303191452650200f6400c106080b41507464100200303c5a00b18501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 27320779 1250 27319529 27319531
    0x12140c0c0f030a030206160c050a0305030412020703050c010f090e010806090708070605090d06020904060905150411030105150415021b01030207030914040608030c060702061003050a03030c03020405030f070e 91
    0x1c1e0020201d0003004d580180d5640c4014000000140403203142491503880352a045d40b6455014060b2200802d2074a030190151300705071012206c04ad0a074541010092001600c0801c8a070403000500100c29141d0041d581c0110222800040182d580d0340071804000d4404024000d09000d00107014030f10345141806d00b40540c80d040506145c124000030080513600c80e095550384041240e800e481050f0034903140001b071280310801500719091480000d80f01d031013540441e01c244000c0708001a0304910404000403584207000007101c40364140014040740c20000100549500f14410182c5000d84560400c08114600000400103900050208192400c00100780781c1604080c2810341c24202c50f560040d01906d0103008030450320a50011a141da0365070781d000540201016000e9030394900135190180c0c2c0703d5208648520251181e400032910f1580815520021690085d0151525002698085014120a01d11031042540a01021a20fa5001d0150080705032201006004080c900341458000c068 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 27322029 1250 27320779 27320809
    0x20f030307050601090216120909050a06030302031626070201020717213009060105090c030603070e01090207050706030b0303040b030a060308030c0a03060909080712140c0c 76
    0x20030710000740000c000140060640d91109405a1500c21001000710050b182c00c2015000d1426018015406500043c0420039503009207410b00c80c03943d4500741d0310b040d0380d0a840010300603801048543d1440200c3c1c00d5a0108900c211541c003041402c482c0501c8a060001d2020544000001054021503070108401c6005100304801e201c9417021001c0300d552a0300751081354081d00d5100c0b221001c074815a40c02200e41094030020310519011211155410103c0400103081d81b5409041c00324540d01000510301d8100d4100070030543c0590381d030100c50032458001030807864243c400d000e00800c0340c800c000c81c8140a050450b50040e00d0b1600c605001e031829040c0d0f070206041c07600d44005044079440100440c2e0903504c00541c91540c2e1f80b1460800c80040102c1e40c00580420000700034482002c1405006003402c03c0c1554051101c2e9446484503c00c0312003880000380021020013402d000907488000c0d000c0a00301c030341400c801803020a4010b4039198000c444c01e10231a0850f081d100168038007e8100c40c0c102c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 27323279 1250 27322029 27322033
    0x3090f0105060f09040201120f0c020106090509060118020c0327040b1c0311010f0b01090902041d06061c060807170a140f0106030302030d060506030f0c09031002040e04020f03 77
    0x2c00e002010850203055104018000e21515000400390b90146c4042d440c04428403000b0096010354100c404018070000c3c0443c0019401c00c400041c110110b400786d43d010700b00320800382940f42d18000800c003528001e6450142c0c2e068080c040f1186004081c40036103080d03d0b42040c2802d080400941c0c94101c0076084010341d00c01c1e0315141c83d8056039194038a000c8044400c0903144c2000c50014101a2800d81c0060122074181d800c105490b1000c80b0b494101829548003a2140325105460b0b0f4215001d03405940100d00403540c58203841c004410440e0a8290807000152443e840d101110b80360503211412520400c0c55544c81c0d49040000d100c0c20000e1a0040403120900200f58011100309512020b1000300039216141180c900004101c0a219100504200c04c000f00481c556a01c0d0294407604000d9900c82c00070315110f0f00080301d0030319504684c407403101085070160139500e6025144480d00031a10268152284d581500c100144e0307403004101401c200790405c01145850b1040000302c2008140e118029 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 27324529 1250 27323279 27323281
    0xa050901140415090519020103060f081002090d120c140102121602070e040311070510120507030612210c02010c03260a0c0905030d02070302040b0402040801090803090f0105 76
    0x144005160300903a00001050901c1d0f43c0300034407009088905005011405100408114a860505007120b118400e0701c6c140071a555507128608807210314400c242094000001c01c0d03200c0e40c3d5950080029000c01850041c801200e519003206005039200ba15002c150700305400703c140811490501c00c015101c40081d0700d06290b404010390114800b4001c40300701c50909030b445102038001d201c51f0740504000c4820350518030309820001c2c4405000394540113076004040c0042406d051140070649902e196451740100142c3c040104002000d00415400801d5690500840e50b4203005400000c19401043c004503054101c01c540e0401203105041d06090203c09901040180d070407940310003000703030503041c4040f00b01c0301070f601e81d036404d41010010f10050b0202000c020040c0919405281d4584043d694444040e4442041c180d6500c1040c0003c0003580c0864410001440c198200c0300540e40f0240000d82069981d0b003650742941ca00b081d040301c152502004102c50031000308903629641692500a04c46 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 27325779 1250 27324529 27324551
    0x9020405060f07020d17070c0f0608060907211a06030403091a0f030c0703110f070902090316090603020102060709030807031b0b150f040908251205030a050901 70
    0x20302c00c19101c1406054041040701c00e658038400640c01441e04038001340320b00c2c00310a403203061950002070115084060710b040411500010107041f01a140c2c1307a29403603a540c580d5001c214940a00a100c003042107102c98140c03c0103c501d84c88083c121b503c45202107010700900000000701031503c1e142d00e028a0050040001203a407203020360085840806121162041c444080340d1948980c28140e051343c00008207001400c00000e00030015140261b55000540b207034092a43d88405030000d5070801580844024000e11080d0b80c01003907144401130844282d4a2095440501c4061a501513681c5903501c6104109558060045c1548001c062610140180c11566500350900403c04080c08200c2d082c0381040c3d041c43c0c85298a030302d1a130080621403240c5041c092802e1410300c0030760110300071003030040c101c4a1410103000d10400180d10a141c2810001079049484000821030000d003900700e1403c0b803a20200308201c17008a91203089540d2183d503481d0115506d0103891026146540c56072612840c4d400f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 27327029 1250 27325779 27325789
    0x1005090a030e120a080405041404050a021003061a040f06050412060203060609060304060504030e06070519030c0209040b060405010f080a03030f020f040605030405010506090702070b03130c081609020405 89
    0x5420707a040c00d2410741d40c600707000441d8543c140b1100b8003240c0d11030b000400b0240700c0000e0240c001c03244101ca040c0072206420610b0000b51070180d50041c041d0344141400d800504e084251101c50341400d02d03000803565590407000c44e510f90401c40000f480345000409120711110b0383d50500c0500b046040041c9030514001103103403003503000500035003401c0c3e002c404212155101c108441e80494003c140399102d0411b8288400207200588040740400c40d82400d030485420300302c00b641c640703075000400341c81065490b20076102c856074000c600b1030411221f16507010040e580d1482c0507002c2c5018030b011203554a410703002e0104035041030300202c00900f20f07410200107042000034006c008941c58640422803501e1451410041e0280544841b000756011038082411580080918850750140001307102c2030300c0301300a111800105441e10170040e0803e500500400220200441d081059240c80e460440320700d072a6440000120341240700203401c0b62041038030034843d0b00707818400792080140c2140340501e0700000031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 27328279 1250 27327029 27327043
    0x170c0d020612070207091a1206071409040f020304050609060f010b0706020a0c0204020a020a03031805070b03090a020a031a090d021009030908010603050a020a0806010b070303020d09060c02060702100509 89
    0x201080c80c2c1c100c001502c1901c02d203c0100208081034003446424000241080e044101c01482e40c05a42c402d41c4440a48000003402c601501541d243c02c00320148681207060242d018405c0c60f5041911000360003a05030740d901c0114480d41c01500070b42024142000028141074010740035454007640c0d1801800106c0b243d200f215803c9920100042c3e841d011628165440c110900d4003940c88be1012942d41d40c690b4010800ca0076844c8240c3d820440c0421a003000a045821441c019000340d012034001e2082091034001141c00c01043d008032001030500c1c0c0d0008104151580048078429401d613940a8008010703400c0941002c60400613000301c0030040c00080da11002c1c0340c60003169a450360008070a15001cac1d08100c01422100000b8012140c0300e04089994030040c500880c042e035035013040003400920104d4660f06070b6048858161138080c06880480103504492803c0300095036400340900010001e1103034841460380d64014000500e01484040e00340304954200559140c1408108605010b000c0380e20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 27329529 1250 27328279 27328297
    0x80c0402090d0f06020a0212070f080a12111306021f0513050703060b01080c0f0304150b040e0105010608090106050102070506131703090a060c05030a0c080c0106170c0d0206 76
    0x688507026074000845101c0c0700b0381c015091220300d50071032003409004e800a0190300c1c2c0e0341d021584141e5114120750b800f403045c0c44000d0620140d0441c03400028040c1c80051000c421a0b00e00743c0315010304028100202c43c0403004540c00310714005001c00030020011091002000d10b400a080c40701110b4250720480c40c4900c441410305503850f000500c58401c0f0507144d61071300f9040411a0005520b07850198001c080c04001d16000c1080b40f0b000801c401944000c4039800441003c0d054210f4a942d99030302c422014011040b1441921500c4060b000e8507a481b5031a0440c8180c000882d465142c610040c00100b0082c1004081e641007100622190360006000360803203a041d0b62040da9000d2615040b040200650060411046c44c01105003055800002030641008100c401203c0560303a0802a2003101920034012701c260007d10030845028050a400c2c08924000c0d180c561821008507801403c44403260050002e400d0301141c0c00e40502c2d010005e02040100580328040c40c11482c1c2c00007040c1780920000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 27330779 1250 27329529 27329531
    0x603110409030908030c061005030d020a060515040f0203040201090e01050a1205030f03090a051213231201090c0905060114071e03090501030c0f05090d05030408060117060c04080c04 80
    0x320a04043c415000c9000078240c03042500d07211a11360803d02e45818061b104c036045642c2440001c10f9600e80865144180c5006800508400c1101d5a84401504004104030b111007041e842404007600e95004042c00f03035000040041c2c0d0b03031400d48000744c580082508521418482d410040c80700ba01e950410b00f00b136484608950340d200820b450030519520800040310b8242ca004018801d02c01030000e600c48181d8071070020b5031750000140054000d140a00900c1d030702403142000b82005840f01c0b045504080e00300400b0300baa1006c5603040032922a48640310100e10356076440403403a050200e2058000003904910000b8403403400c064000900c1403e2040200c501d0b0b1100041a104010f441d4403011444440e0f07182c0d640203080d007810301800b01c0c20700d8404c02c0e021a0500c1c0541c3c80e814454502814a880e40c1d48695061440705c0c03080c003181190b07840003207e5030b101c10480480c882d4010001103000b0480402e0481940711401c55050a104001e401c80d9129030080c4802e0014aa0100c4d00390a03080e02130358 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 27332029 1250 27330779 27330791
    0x141f050d05010b0418021005090d0201030b0d05010903230403080702061c0c05180f09010b0a0c08040b03090c0a0e0703090c0b1903050601110c1005041703090a0906031104 75
    0x81a40c01003c0e920301c000d50261504128100c03011003442c0c014850390081704c5444080f841d2000641d02e5200e001625984825241200d000560190303000b01002d0801411070044452140e6802d821500404015804652030b0254021566040b802d14030460340e100c120701d0708040ca140c4e00e41443e0700403018028850380001c80c0c40c8129280c41c044800c100010004240100c82051502900c1e0785d204498a282600e5051280c0000d410000861204010090480340307450303103803800c0d0b90155000112200c0c20014070480120205410001401c054040c80302007a0f030700d042001e1110700d40711811080f980103506100e82000460040303c0c04135031052040c280415a0b200b20718010440c8291504040701c41c0b400810b59802d80d800061458031410001c0e2420496031300e4000040d00d0742180702c0c0a03108e0550100c840403c4508007803c021464400354145207051948801d44590040c51000744001c1c161310114040c0854a0302c0e1080b100180360060041040504580303800c400440007003c460301440c0c07101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 27333279 1250 27332029 27332033
    0x30b0c0913060303020c06090d140111040303020f06090a0b010909020102010b040c0c03090503030f04030f0c0806070206040b15091f05060a1107080705030a120c0b010603141f050d 79
    0x1408564959000901180801c030421103100c1c02001240000c3d401440b4443e003002c1c2e20305005007114101d03400200111f541c01d100d0740d80d8003517000ca2001c080c5442d5403506002c0d51400080c001800140d44240c01a00d0074510400001c1c0c9000001001101d0a6001d0307500400800e0b1080401d605664240c4070129480d5002e00041c0d0240043c0f580044d0040d143c580781d4000c00750301a1107003c90510903582c4040c00307650742c41019a00d0150a83c05040c1b864100810000246402d01d80b1300c481d03100300b102d00d031801d40e00d8804a007000310441e148005600300c40108810050300001c05580701c480d81620030300e510002404600000c01c0107203076048800041d0209441c1c2c20450101030002c0c940184017aa071000285401802003000520b101010700c0381c00784c041114440868002c00b41c1e00080e008105018150720b0386980301214080c0002486901c1c2890030100301255120750182145840104100c80840414008110001c01450901507000b46482c2070403149540d41040f42c004590882e40300a4034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 27334529 1250 27333279 27333301
    0x111160309051f020f0a031e140f19020a080f13030602030703050403140a020c12030d0e070f06030207050604060209060d02030a090b0a1b080702010b0607060603020102010c020a030503010b07080702090a05060a080c0a030b 97
    0x241941607040b09c020862058502c03e0800909142019100005604036441b606980d6103000200003401454103020443c7c0c1c6030f0b0b41ca4058031021180005401b66a40d807901ca602c100e83c0295401ca000035114820001815082303444182c6480400980070f14280e5400c00013500c942071175000301d100c0c00c01c040d041140007100300151505400001000c019020050f2801561034030544103100321031010110005016009109641015402102510341941d9965400000794084c540300c5500002c184103901a8080e0b5101441c401d188441001500d14854181200504030050450404606110150004030960300200701445d1017400c0c0401036442d066400d81c0502045007502d90001070103d00c1c08180900c0382c207c0707011030b8000c0e0020040010000000c80e22040300b00400750202c1c40400040060402d602c008085103070046407c00e080ca00d10b41d00040c1d901c1310a4800252940d11102400010b29026400e040207181c0c0c179000b041c1400130b1b100414003c100303600c0007402c60307000040010b40d070f0405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 27335779 1250 27334529 27334547
    0x5091201020c060f0709030809040c0912030203040320010f030c0207050411091503010e011401031404060b031203060d06050a0e030301030c0f080111160309051f020f0a031e 76
    0x40a00075902c803850b921500b952040101c41c9a40c1d00b19804001ca081d450144042000b56034106008500d08800761007400060501c84106108102e0740d98400164845e18140000c0001d20a6000d0b45d5038514600b41001030f401c01a140c090f0002c00a244054142c0c0c0120551003042e545060119a4904004041c4d00f0b10520f42e03c072603003182c140b5010f1150000c550000b000c001e0300840d5144a82c007810f14448003140024020014030050010040c000a0804a003034164030304140743c00304d0f810030070716140d50804d10103480461b0465220fa401198070f2600303001c60344580d0b0034640c48506518014001945144003004050708c0c0c40c2d510002302e0414245c640000c244608103004a07580c9507500e1900d0701d040890341c440d080651181c010f01140640c4180070301406810318140040c10071015420360904068024811070a101d4100341c006019283c9001992003011451442200010100000703030812440d81002c1540d904040a032000094200007a400801c0c00341041000307440d082e6206a910082d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 27337029 1250 27335779 27335809
    0x1c0e040f05011214061018150b0306011106100909140a080c100915020f09030f0102040f06080c03130302070909060c030c0f080106080603010b04020708090901061d010509 75
    0x20030000040380000d0100390f9161118810000780040003000742e0410303202c0c401540c3c44090021890010440d04035800c404800e81242601c0002da8200240318040300c0609550000c900c1c0711000c02046519a00903030f0240b43c4c02c040f030016040905c0c084100d6001200c882c05080a02c80d50b8245e05000c1c010b4141c010003643e141c2400702c2d641d94400e8140390405402c80c3e40c00e9001d070b11032141070018025841c01541d0000341d001c45a0030011122010f00d0020703410070928840d2180c4140142030071a64100000d0700300c5054039000603a20343c2400d003060280342d0300e03410060511074124188000b00b0360344411a0341c0030302480701c2c01c405002035241c202c0c140b032314952188107558103248400c800d01840d603102e10800321f419241003011400f17409003070b1184c01e554004100400c3d58000100701040c026403116600840090000910b020040c000508a810050059035070800100301c0c10035a04050301000d0140c41542021007401b0041140040d11420340000e0341c1c100b00012500c01d010341c03a80088042041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 27338135 1106 27337029 27337031
    0x210020904020d0516080a020f040b0901030603080d0608010c030b01050306010305040c050d060608010605030a02130b0301060905010305010e0c040203070c0303050c0903060103050f0c01021c0e040f 87
    0x24200d880d4054216030204204072945080d4494540f0070105c0c0e409908240034013040080c900c000050043c0e101c10301c104040702c030200400c41070f030f02210003160015940314404001200070342002d40c001846010049039000d04c2000f2078000c2070988600c84000c00c100f10700b0103011002e45203810021400300d8020400316106500c01d402c070951146c080c103240c5444a48e02c00c081131140107920350946002d6982c1c1c50a000c400c07804e00a110051408400a004044590700042c848485140d000086965202140b9180391820f41011005101c2a44200300e00c0d0303540c0c00c049000c0c000c64110740c2001c1c002c02c000400107192034429a4028410340e80d0303040b1075004964095004150280001081038010300c64012107690402c0080c0c00781d8880c802a003200c450308041c451512501d05140c5055402a09035120070090003020201001203619180c03409070300400c0030500500001003890a51 = true := by decide +kernel

theorem cover : BRFrame.Cov 27158279 27338135 := by
  have h0 := BRFrame.cov_init 27158279
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 27158279 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 27158279 ≤ n) (h2 : n < 27338135) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
