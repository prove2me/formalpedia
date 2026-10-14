-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2928
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:09:25.099987+00:00
-- url     : https://prove2.me/submissions/9946a3af-8358-4f78-8d6b-33da5f956a5e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 526438848 ≤ n < 526618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 526440098 1250 526438848 526438853
    0x140405070b160c0311100311040b0702151b07060c11090a0e0d0302210609040b0606040305060103051f02030610030c170a050603070b03040f12032c07170a 68
    0x72600a0703403070000201803020b074860014030103541000080d441543c180c4011101c0c1c50411016829840e00b4005160410b0103060403000e00c442181d05541c100c001c201d440e1401400421011903a00c08440c240d0200080c800c00c6007075424600c0d0600405030011240d1581c0c0b1a0822184c121120100400702060b00c42e441c210b0303251000c485d687c410100c0d40c00082130b8001110041c50072400340400c4d00800da00140b5220036540e84481ca00021b40780e4100f842e00c5041040118941d4440108044c0c020007440e004240c00f90b8542c000c680007190400c003100d000c0d50712803c160392076070150106801101080c4040241d00c55141c02560710501c40101422001d008502064000c0d0020404402c2004904240c015284208902460040180c1100041c1d2860070701c05041c42c102d201d030003030001861300780b08110000d0301c4c40200c0701da00740d800700041c3c410810b000000d90242c429054025961408000706002c14002c9460300c204001140c070840380015038507401721104504105808007250014000f9101 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 526441348 1250 526440098 526440119
    0xe06030a050a02012102070311010510060801120804050306010603060e06010e0d14030f040e0402040e0f0a031812050d0806010819020c030c031606060b04050904020f030705150a020114040507 84
    0x200d40c2c0745da0b00005001c24980c468004982c4030300da0840104c1c1803940b05445100007445000e03801058180820001c0703040c2390303018181a805105124100700c1c85054042000003402c00d40e802001d01808071102546c44510160140100380201c40d1000740240020319558415106080140c5000e401c544441450b034a4010403074210600b103018900c000c000642d1100117045c01040242950080503000d41003920402060340c6004102c009140d00c80403921482200c0400c200c8695985410440410b108000e60704a1103920b96000f841c4000b0001059400c1c4030020414442d4041c0c00d03501d03585580d540200641316814180d0304000800400f0500541000300c541c018101c0071040000c507800e042d2181030140c0ba641c40320f00f00d075140c9040d080c0d1000c200070a17400707828003521501e00001d08050404001c1804039000803c040c0c803452494a45131410f031010301084000c3c140141c50840d105403480019080360b4080441600150720344000800300c8002c40c4503450185500c00c006c0e08440345410207100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 526442598 1250 526441348 526441367
    0xd0b01150521060d0b070c0507090204061b0c0503070b2d0301061d030607020309030609060f06100c06050c0301052b03030c0215070309030f0305060310110915040e06030a050a0201 79
    0x2504000d0701c1c02050b005c2610120303c1d07803081c0500e0340c400408074118501706007404001d900c10301c204c038014803050141a40281202e4404c040c590145010f200c2d00b8103000c080e24801d580800d0f018062440003044100c480d1000300841c0318603035001c9010800d22161100c3c003030400e600b003000f024028001480303081d114056079160070300b011a401015035030078000a801c160083e00e6820240c0c1c00095032038000d08003400501d0703100820402a041034500a16140694503000308044c0c482c030091755042100ca4001e0000340d4846401c02c0e810400c1740340c0600d0060540d4020b01940b0710411025058054541041d45240c1400582001c0341146035071a03034044d000703000d02c040c0d210150302400150f41c1c1041001e070a10380c410030450390b001c02c0100f1b4500340940301c90482c0020508042c10f050400800e074800241000c00d51210070b10000d16880351a02c0a0000d00400703180079030018104903035402c4c1040c140080e000b50780d80c8c160282d140303445071000c0590f00d0106620003040750300a0000500907600410526 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 526443848 1250 526442598 526442611
    0x1509010801052107080105011401050403030e0d0f060c0c0302010b1207030f050307080a0e04050a06080c010f1e031b08040c0e10050405040b091605030304030803090102090d0b01150521 81
    0x10030f41c15100340100d414500700fa04404001c0c0e40d5500104091a100000c0c415203d501b030803e1890701e030440e03c0003844c1d400d5112805000b0b8024040d0102005405901008035a030861b0081014002220005042c1591000c0c00d9006600f052a070914910f005080344040141d09002000001c0ca965541201881044401d44013800280505070108503500010034038684660b54507844405031a0400c811610042d2134041820316141d01480711210001c0e10030f0b1408403d0a00398480c00c0c02c85e108840c002c2c1c0c0700454038505042442c050a60366015049070804450100c00c840d05030070546800c8030a050b0854002d0f2060351a00c200b04020185502000c1e008a004401e031101c5648401c04142500d1080e1001c440a154460805c1500d800502075002903243d0804014029458280007958070f024600001c0d041c00707000408101049d200b5811a02800320107040c1900404945c10844038000c2d007482494a07a0900800c60300310341c1c2c4500c0c103c82c255403c103007600c02100004004201c54490042c0003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 526445098 1250 526443848 526443889
    0x80115140f04020309160803090a06030506032a01140f0f160c033807050901020a02090c0310091b050a030b1905010306050f0a12020d061a150901080105 67
    0x2030009071103c1c0001d600c10701000d8005c190000c6c03810603800082c16182c1c054000f0303400c2446007402d81d54a407030034401140c2a1303150204007a1a808002414222400c20507944642c1340300c054002840909000320200e0f500b600c1e1b129200b0b400100c000300c11300c10003001d80030b00441003010b43c151148003809060040d8060b00c140703d004415036148007418980b41c10a4800303100e80710800c41c040c019001c01050900d0041000c2100e44070050420100c2800034003641c003841004200c03840507034420881d0700c20564005240400904015844000340d9009844a81d16204503420104200046005103061070008410b00112a800360740b04540640100e01c0704010903458103800e44195880c030090118070048a19440160341c40e05002504540311540a01e015405045503894140d4402e0b0001c4102c507802d02c40d0f0300d0310030040c1c40000c00410400c040200003038900410700341c0c039200f000e2217140e08036400ea4000344403036182c8000c400c40d030280036605400141c5c00c81c0103009030308241058000b9031091502 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 526446348 1250 526445098 526445119
    0x30c140303010b0301240206151201050c0c07050a141e131a0a0b030a0f090803070c0209060a12031103040f08031c060302030a03050a1205010e09060108011514 70
    0x14941903900a0348922040c010100c01848000c9803440c903091007a030610744891110b15020f0300a5180d49000300038514844811400c40c507036860301605240c0281044c0002c000609d0014182c0c480c1d50003040b400126481400c40c0407a540c10b0007402c520903030b2014414083c140d48942e04000c050340c0c44000805101c0034032000f690300c1d85c54600d903000e140c00400c0340104a800c81c82c40000e00d40305880c1c030328911421810404003c06000e48048a0300300407051000310b030880743d079032604026040d000c02c003c050705400402c11007007550101404245038402c45d04c02e55aa01e50008200007003000f40554499000241d810700c0002307000f0410031701c2e001d14080c03c0d03901305640c0d12258000c1c50786a911407140c9800006207014840000d03001d60000508070301003044010f00310303000300c0e55400c5140e100030103000c0b001a0008585004881c00061f0400154040c0040d44c0c545800001038542070380c01189500c5528004240e40b0418000d082c8007200e40590020042e01d0021182a005140341c01c46030810766521 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 526447598 1250 526446348 526446383
    0x1b0a0309091e1107051006051518030a0f110312190e102d0512041502030c07020909011e15090e010c02071d15120f0105061302070f030c 60
    0x1c3e8000700b000d03050055140d03030381402d000e4100020440540e0703d03207107042010300641c0c0e580350715219542d2020b0300c11611007a0b07005c1c1c4148203516002029500d0300c81d080b415410460035800e5030340d0451180360b600c0d00ca140a0000e05a890400001d00a4100c1052044803010320f2641180345510190380780500c10228010045001314181741042800114000c1f241d491407040425070854034810f600c1c20b00e40d00c03880f40000500314000c001600c40c210b4210000308051007092101180303400703100d500841d943c0c1003801d06d0382c40951015400320b002c5d05c01d000001314819818810b02544103882c402d059042811458000002e001011124400c031105801c0810291b1562003840401c50030ba01c00042c0c001c1c11960301074a0100241d00806150310500d6505569492a018590300800c17908407210747c02d0313042c4002507103248603065000013600c508824407100c103605403ca14080e900c00d4a00d4500340e001c1040752004d0384030321a0b02070290020543c03444000307442820001a840d008102c65138502c5201d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 526448848 1250 526447598 526447601
    0x3020f030109240e0a0506060d080f0307020d030c0e0a09020f0c100c02010605090c0a0f0c080a030f0b1206061c0516050307060f1706040605060f1b0a0309091e 70
    0x140341da008900004102100000311600c60b05600542c41c00017420031952654406584100c010401d5008504004400d410000004280c40c0c10781825000f0a44034900031000079592400b14210100090615142c8400c1034040c4941408550018150103055814107605001a6209110046d590b59040120211035441406416158106030a0104803ca2014030081c00d40380c403600418131940380310060000c0a0781407002c03140c40c000c0a05001050b500340300c10580c0c1c078540400018140440000b082c18803181e140c0e01200100301c4108040180401e0b030b0707081c080e22000d03c2040c010264005008103101e1701c1c09400301045100c00031400000d4469564425041081c42041442580e108031030901c1f0074a028003403880604428905901c4840c0d18200040006010080c00050304e0f000c400442ca154540340c000700d0180c8005002680d5405221802902691016001c250f81107508a0400d0340030780c000c00c12000c10f581668518060900303084040000340028840c004071141120320540c03041d40503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 526450098 1250 526448848 526448873
    0x702150d0908070b06040e0619180516090501061722150e121801090e0c0912010b031f0f09110f0102280206130e040c080f0703020f030109 61
    0x201a016203440303542c5888130b0007040213420548910305211104030480d00001e0b035035601204140105074240c4001094400a1002000c0c00008404840141007030110000d881e5030351003a809006002180d4482a45048400170301174040059120221072a5400d07a0000b075075000380ba001140010403031039402c5048060b01c0a60704aa2074080c1902d8505604058030030b40c502d0908800151618200c0d10540c2754072803044005072a04240400e035088001d9200b10b5080c6d0160409090035605130410054103c019044114174601c1880040c1d00300c514001c042c000c0f480040c90107001480708800340b901c1c28696045071f03142d0112555982441e250a6007050003001203603400790343e401c441c0d03201d060184645038400521503810b55100d10040b80c4440e80341c80c0401040c115058034014081c2c440e1002030410700c595040503000d0758136080c010540d90100f01c09203000f0392003081080c00e500c2d5144450303601d41c41c8101e1801905d030043c0030100007505040f0700f080c081410003130000030080d5103541c500c05480c0c01e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 526451348 1250 526450098 526450103
    0x3030207060c032a0201020712030912051c0809071220012d140304211701080705030d1d060702061902010c080903040b1905041505070506010f0602030702150d09 71
    0x304c000344006551301031203640041c19030040d441d00864515200070703041a250388a80585054605285810f21a0034070500030000300e00703491746028100c007080007000320105880c2a074290041450000b241290f180c50f401e2883c0d404072544628002001c4031450902450300030b68144035030940a503401c480081242c4d00760020001001d07566a02c0b01000411480c0341e07030342c0c0300c445240400030f102c0403c1440040c21001c0e104131032081411854000f00301c40200c0c03060961640a60280c0002c18559404641e41013515803d40c1100d84001e6884802c6800302e89481421018050490410015040030001843c0e41c50014260628001651b9120000c6008450490005035520080400078a511241d80e0b134200021100840c10503040c402860310906c5500c000688242c001061200c006003d141960010035031000707903480b020500603000d8420782c841c050440e0030380100c42c000f01d403090091004200f50b0704154000c1d42084155424807000c50305400d41c215007840184070840900040780103000d0000e1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 526452598 1250 526451348 526451417
    0x7030c0c0b030114102c040f0608010b030622050717060a150f090b04140c120901061a07020415090608010b040c02061f1505030411010903030207060c03 67
    0x40c502104518504e40c840e000701d00c2100d0252060400a5104003074115170b08a02c0c911004c600000450141050030100e040c98206003025144544406241d003d2022201108024429098a5404c2540342c001c1200e503000b407440e162a0381c80e072a40a107050b49500510036030803111044c1c0c94050819500d403000d0010100c42d84210100103803c039089c05502d10b503102001e46240c0b002e0500e8403104103111030340036220f4000c5c2e6803244001181e42d65080b14650554048200c25507007000060392031300340d00401d04501900c1c504c3c0081105030105104c0c450844a01c5e24654880803100862840e86901c0000c040c0d038000d840b0203090314030f9072540b1840c10088c450b00800140040c40c052146083d180301c9500309110b80e107000401020603070041022940003031005001c250f4180c01c0200c0404804581d0003940a44c50040c40815106800c080198040e90050801070981c0c1c0110004483d40711140c0001001a004a00308008881c06080c02d54080e40c420308200c204400350080a603010390b41c0b40700f00307041d94 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 526453848 1250 526452598 526452601
    0x1d06040e070201020708271005030c0a0e0a03030314011a0a080903120a051603090809190b040608070801120f17160b061801290d02031305010b01090501080c07030c0c0b03 75
    0x3d88401414140c1c01105071801908c1490055010b4064040240303007541e201400200c1700070043c861100d104214100400381401c540d120300b0010000c02e580b038449290082c05d00b0012842c031188001e1011100903145003070349000070380c403012900c681000e00000000d220a020086484128500b1684606003500340095145400bc200f2200c282001d00444145031030708403040e020600c41c0e812690200800d662945035904980429000955075500605142c84045404100240c1c442c1ca100e000e41c1d0b0a550388800c80e44c96075080132070720700d041800802c48a075040745140060740000050007020b059261031030426203256204950b06074210780c1110000312030710802040b860b240039201c00508244004121960600c0100f0f9030500408501d81601a500120850350a0042d01107030f0120301c520800703540701d0801e00421240c1d0000600304442039402d150358200d16501c50890041114016943e20400e9100d041420140d584030fa2020380412001051007030100d50401c1d9464002c061040d21643d49 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 526455098 1250 526453848 526453897
    0x80a1205040b0f07110a0605180303040b06360402060f040b030a0f02041505090a03060f1b0f0c0602070206070b07020a110901030201090e1f08030a1d06040e070201020708 75
    0x203d48000c10042c00d00121504842e80e00600280800003e80d000e04005215164405600e40f901d000c00c0d060351051000004000800038a112282c0c050705003903416007825030301c4181c03529140500103450034010b07208604d10006004243d41e041c0d08a0b001422051528050010111056000d500002801c0c1e030f0001c24403003d90303858403519541e440103540446c200783c207002c110b0503040d00344460740c42004008620104140d403101846402560705c00d43c10031120300702c07007540c0e809054000e64003003d22084503003078200d140c040c581080c40c1d809555605698240b44e599080c3c001d400480b0140e810140610030400081e02082c822801502190010842c90455250500f00d01401c0923a140c0a207514500410050f604404134105a907405001c0d1040d6589802c24140d2101c299040c0b2500c06042c0080007a4405012000b010a00d42503522600600840d0417414062821603031480c3d0019010442080101c00c0c2c1c0c090b16401c000144000362404040340c03280c058903048242100304084012030440700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 526456348 1250 526455098 526455121
    0x1216030e0d0e1e0d14010b0d24060311040c0203070501050906040b0109060b03060f01020f0a08091008090703060902011715040c080603062a1c0e061003080a1205040b 73
    0x3d99640c402103102c3c1c541090040b9600030800c1c036009021480440c42540d822030b007034000c2c41003a000500340f1401c00d51641424290f0f40401c0094010042001501c401140190302500050726040a2440e1115a105c02404000e01d800020700c0d045020500240000400c01c3c0103482c0200e042c60020402418035041041100506a02004c40c01d0300c0d0003410040c1254507825203074818001c848940c0d210390750384010303030900664111802d0203029000028040056403030181070381403810340d01c00b8405002042c0170356000d90700f5185440c96500c562410400507200e500070140301c51061400402464803140004080b2900b03a421082c600714103600f105e1b0508080c40341d10006182407a01d40c5040c00c066000ca03448800240070420064045000203070340c0d00170726035041c2c02c11021a0030749540707866030440b420002c2142030340c144401c3d0a21440154145000640d070707015441450a540241d49580c2d81d1203c580d00403854071003130080102034204405028030940744600c0c000e80c00103103985040201b907807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 526457598 1250 526456348 526456369
    0x605070806010504120209180d020d0809010e060c07081b0f10110a32190e0a1e0b04060e0f0402040f120606150504090e031216030e0d0e 60
    0x2810080300348005c0040709442481c42641540540d503010345921501d43c650079070084c451000480d40305203044a030a00c0d2703001a0094203010182d0fa41c2c80d240c1c440604103826034618400090b02c5030b00200204400c2100c16004169652048120034a800b5800e02140781d843c9015016030290380080307480304d142c0c400900c1400003401011404001000b1055281030007405250944420882080080301d0005000c400e00c40c0303599000c0c001403181c40c0034061581c590340d2144405490100004010301d201900405d4012034109005100e04005030a0011040c3e1500c846607450200c10095400000c01030002c0004101410455540c140d10344166024400da40d8148480c80e8081d6104101c00c000d9249140d0f4140d042e10700f0340410f07240303014207424080c001d80020f81142c0e4070310295081707a00c0540d400400a00403100358880501101c400005425124091095003821811182000802e800340b00511801c0d40c001c2402c0010f440746443c1019468428880800404200700ca090001d40e4500714013082c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 526458848 1250 526457598 526457611
    0x60903050d0f081501090f120303060b0405010f050703030b1f0807020715030906090203061810110d2d1e020f07020d0203100509010902010e01081515041206050708 72
    0x3400c40b42282c0700200041c1c002000112a03108800342140507038890002c0400418005203400c00d090340300c1143c00c1d0300384250708045000c28038141c40091540082d00640f012203030144c50f400c1320100810010746155102220880416075141005401d5030344201d82000500c00b074100f8280c01021510000d815998042c003500700703560141c2c40c2000090303582001c100b6541e22074540416000341500d8028080e00040d44001c0d414001c000030070256882c22440d6041d4030f0350040464607031508002c019030880303521075a45c0075444010003010826664542225056015180004c0150040704030002450200039003080406034940034a074108446605450300031385043c110441c0ba100d58150128014490030200030301803200700b58050150f55041c00b004150355a01b800c140403518100782c0c800d00034840484104d021610b4041080d03695407048204500c0340c2c4580d8400c0a480c054001000300680540b4840a03010310b007040b0108611100200c4810884e1141e071002c502030400e01c00250031004001c141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 526460098 1250 526458848 526458857
    0x61620070501140d110d060501050a0e0f06090303120610032a0302093106050105070b101802070209062d04200d0c140f0d15060903050d 60
    0x242540904085120001c0341d00c01d003021144901d00d56040c0c049070241c0031440711035034941100c0400d8a0742000040034010b80484003001019201d03c0191064051095a000028514081500e490910f0490701c5811b60f002805a400d04a483d07001078a50703803214181841490111092210900744011091300140640c14144110a1000e2444a5100041c46d400c90003460a681600c404c2d80641e04030f40802d20080d01500400c41c65042e0f106044401444102c1c1c0309141d62040011f14005100e05070903243e05030743d607a10342031507511100140c0401510b1740240d440d44135000103021441c1d804800700c540400c2c01c00344e1200700e00d0040101d503510040c404c82c001e40c03a0008011000701184415840e9001540302d0850380c2e07180703002050080ca0180c00d208400c4152080c4c8070400c60380c140143c0b41035015488244101e280d11201101c034414088608800b4000074401413212980a8010301510903040300c00080e4004641c0340001d924059900150100b40d10350b40500c240081408030501c1c206c40c5041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 526461348 1250 526460098 526460147
    0x90b01030f11340305040312031b110708031303020a1208070b090109020306100e0709050f0d15050109150602060f06010c150c0305090d11060f10080616 67
    0x10b038046103102d000294110303015142291558030200240c59200310101e419020f84200075480d020344154001d0106694869907455001080c80c440d000c1c4525a80c07411011034039008254200b92400981e4a802e14454054020301003503034841000605000e22000000d9122f50740381d80148042d0418541045100b208072aa43d031001ca04100101c43c00544d00030954222a0750b080a164018140e081c3d0081d41802070005000c24090302105d10426070314100380e44140307501d8800c019142100244291500320b0012107200c815454a1014020103d00032801040c80c40c409039400001c84400b43c1140b040346980381c400c82005507844c156040584218001000d0600344400440541038000300128100080a4071756410000c4d03510140030400314207201400038003108130000e400703480c1c101c40107a4a845880c500101451290310070031020007580c0064412911010500c0d0340034040180485144204420005132892040050740d2084000c021000d004000510000300841c030b00c509a044c1c030b044240c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 526462598 1250 526461348 526461371
    0xa060f0c181a0c03130306050f01090c0915020732030304030f151b020c03190b1602030717040608150f042a080f0705030c12150a090b01030f 62
    0xe40d82d8035242c442c030042512590300d110749528500c07515110003001400007000004000d1142c001a005000b54058600d0513a2214a030004a50803004004002150344404205507100384004d1580c0410fa403041e600441d4481c4080d101040300d46000010812950344c0702c1011030550a0311000900d03040740558601441c50302c1d45c0611081c0088090000b05260014842c40003c5034004014110005000080c00441000294403002c509030034501034014403202c0c991003444a040342e44025840705680b01c1c03540b1103003026141c5030b2400104805601c403c000480c081580000741c01c020002984602c0e641c0d5050480c01040001d024114011a0303080d80340350701d4a0356480c040d5481c4500e0a440010b0240c1441c40301e50b15088140d1010100f074400b40110140c13142d8482901071007020400384520341516604400c84a9101c03c60b20b01150b5041886010b441a01000303c88e500000c260152034000603a800009280c8030880c5e10070361489076071712188034007560580203100e90703007442d01c0c41004011801c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 526463848 1250 526462598 526462619
    0xa0f1b050a090f06030f060b04060608160c0c0803030c0a02010b04050103080f09180a020d140402010509100e0603070807030e010b1e0409080706091a01030f08030402030a060f0c18 79
    0x14002d281c07605494902076070300c9860a40c0414002c60300040d200d55050030300d040c200014100e14412038010390900c00080350090041990b41d0003111400310200d804441d14500310344105403590212242c0000000010b0f100e8004c2010714052442d606003544e03140d04500000e8212000c02c00c1443c021800c080040010488034010340e20812104400b0f107560b4964040021042000c10094260001d00d0506100e00e07003ca0b035000c0c103500c2154030010840d40e9009091010307440b8003110000d000810810421601e420302506421103040c4904081c092110b8540c00101183c100300c59000001d030441d8200000c80364140900384e004035100008200c05860706000c40c0f2071051021140138a0810020080000d450f203074001d030700c0319402909003921610380c0e00d4130101400c82d07604190341500c4ac490103c1a18550200d50504980e4080c040c0c0421264540d107000c803c0e00000c0090368140103074465100410300900a41c1001e404c0300f00d002403890740444024280108440e80601001d280940034802c807010b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 526465098 1250 526463848 526463869
    0x10308030702030d09030203040510020a020a03111f02150c1306050a020f0a08030403081b030601140f0d15150503150d1505100b0c0a1101020f0a0f1b05 67
    0x41a00aa92a981c4480a80c076620819100c160000d10f002d4000b018568040f010340305482c0100d6203034481803038452003266100c070100310180d40060340031010030000310300710f442900258018014140e10f654070300a640640812207003100c0580c220044c0900c41e541c00c0712502d80d00100c00f40d505401c00100d141164800c0400c3d028000500ca0001100d800c0ca500804c03a04945103106000c4401c190014641502a5001600c045000c90480c0c1d0101da403001c00354403021041d58085184e02d00350b80d1014011a0040c402007003500c0c40105c00c014808001ca076450003001028503610300801c102081340e421210013103d55014003200003240242044d440e90040841c0c0e0001e10542c1c5078800000c5800004e5020000c001b0018000d56180c060040a50f5158024a1041145a100b045c0d80d0b5034454801c141c1c2c0c42545440001070700003090341c1c000240c844155041204e010320440e5030010f5102400380c03130401860b0080d182e90400e090500e08110350804514521745600d088080c3c2d051501000c0b5920003107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 526466348 1250 526465098 526465103
    0xb07080405011506050c12090d06020f0405120f10050c0912030f031f1a090d0c1a040305191e03120606080402030f0c094c0801060e0103 60
    0x11002003400d11109400007142da4070b40d040c0704590207640d144c000e41554401540c013545409880303109840d51000400381d90178128040d0030071504010551b41c0000960041c00c40c02c018010600c0045000e44880f0070302160820301400410f64250384e0300041d07180c800c07041c482d00d8201d030034a0104014803070800107481610200380c0d04d20001282344000c150440c00380814010311a040403041100e5a2001d00540da070000c45e110b41d821241d6105c2030281341203070704040c080200c55030801a40f502d604014450000c100e001e91851098a82c9543c0345e50341880b40c41c1078082c2e032a28040713414424032a0a008034400c105508004805a2003141d661000d264201c480d6240d09650750100b8106040c050032442500c03803003001d400c1203425100c90300030307003094415602640070b44140303001550681c8000554625070340d801880c4200f590344080484060310804040c0307032441ca61004c0c1c503e1030a480034440400c110301141100c2c0042c034600b40840c00c0070300e040e84003050a030306005040000b9000c0390b50843c10f594 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 526467598 1250 526466348 526466357
    0x5011a0c01090b0a02120c09061e090406030b0603010f0e060c1e0301120308070309171606060306090314040b0301060c060207020913050f150105040c0c02150304020301050c0301030b07 81
    0x600d80c66a80100740c0030102074600b004030720800c440328105038010102d01c640c2d52851006900c86035070015030b5005240c2400e401540401511800d0350801c101442080f00d44603050303160404100215054403415402114080c80040034000c06190a01459546605400782081481400010665a9031014010300c54401001605032040c0c2c15206011080030000c0d140c055072943e40d40107142440380400d40035000500f00c80085060705220b4018261a103820070361084c0704804d4590103000607070203a0700c40041440a41a14800600103000305002540503c0c0300281c41621424040c04140c03403c0f0261800c004200002d101030544007040e28190b50b001d03c0d003405000010314003080207106d4940d002e980300400d1020801088031406040f04103510801c00d446e803080c05210701c2c95540000e001c0c1c030007a20062000600ca282030580c0030340d00340031031458502402d00d695000700300425604117500d81c420500000708801e50809000c1c86403c00e4003440e540f0b16643c55902c4d550101100609a0300402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 526468848 1250 526467598 526467607
    0x20f0702060901091211010e15073908060c0a0c03050f09040e0102030402030c03030a1d131b170606030a0531020913020f060f040f030309170105011a 66
    0xd902c20351903000501089000c6802e8003c5d079040c1304500d14240b288590000781110711422550610341d600045800d18460072600b070240c00da0724070360342001c4608560312842075a42507003100d40c0c1c418003403444107405880c100340c2d00342054240d500384503000303000c0f10f007100c1c003000307401911540b00d600880c3c9560076142480c0c4990050215030200e01c18000300d541d0013030400301d00c44d1090320190300442c0100d02c220200e80350414100141078a0340079131907080000c03030b01000800100b0141c80c10700a8035910b006200300c0b1400d07856907042c3c04480d261200286011b8001c85000741c1160081105039800d0310080d5200220724000c00060341e18407004160750301180e11840032682940600310850715002c02c13a28601025130301d0f003550700106c0080401c00da00c610b442c1008981180c1e9800342c00c2c0ca980e03802404031252681c2c0b040c02e1107100c0c0e101f040d038142c4401c0208000a080c0c40303400043ca0107140701c3d59134100024544031a9000007520b00b43e51604c1649070000401c21844100c0884c09108080c21070507458 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 526470098 1250 526468848 526468867
    0x30601021f09120f0e0a0305071205030d05150a06050316140c1f06050f0604420801080c1014120f06030f06011a0d0b060d140901020f070206 62
    0x58880039400030030080c4140c1640790701c82c1e00500052000c18017a5100100520300c1800c1200b510300610000c7c19581101d4020710805001400d4402c889001e0301c200ca240c03000100125044910458130200b100c105005103424614240b800303807005040c07910b0000d0031801c2482482d09007198007442d800a11100303d4103036000100c9c0c281541d82c00c40d141c00a543c48844000017841ca8554140f00a01c0355610b040710110b640c0c60451003038414490080c2c28941014245504007500c0742810303032040c8610141b0b4140c160b604444a00e401664070741d05480448030703000603001500011041e0040d401301e800c00e2508901c1070719000c444151287c40d61401d51a0140c010601c13008501c600400300501c180c0b030000b0000303611021070300b90740100c43c113038112a0204e01c42c2e0140d0b51508c00c02c0c000e00000c85240300c690034404514001030184d2002006001541d40e00d01c030001006544a075115031081d549076a51160b9054240c40d0302e9502c21042c0009600e4180c0148103450b4a00c01c00308000c0c4500400b0a90b44a03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 526471348 1250 526470098 526470101
    0xb0105012c0a0810050907151d010e06072609031506040e1006050a0e09030f130b030f06100905030c09040c0e1e010803070b0402040c0e190602060c030601021f 70
    0x10659582030304c83c005580c030b2243d4040c000c11281100e05108110703001410700200e14600d650a0b81aa03116030300030b52001102014031125401041c1007004404a81c8490b9032004001c7c5015849090140c1d007200c401c40300301c01e1170001002075066014040c0400301e2103450208504420003a004020200c1d543c40c00000380050203641924100c0c1d00c43e0104040c0340300280e501840640d070381180c20075079044d958400340ca109201120041e09541040c400b208a43d920030000d080c030052440769030a00c2d1500c6030044405600215070328500d4252450501c9850b050903010000751a11502c5d00060460404010070754a040d500350180c01040381400080501800419003c081e140a10301d6180500301144241c140da903200da42e80e01610182c800001c0d5101d00001201d2403198040040c40c3c8d5503550380c007000010310002c01c4010074400c01240c0841203aa507070124040311060480b40c801242d0411000a151101c000d000b1749441030200f0a2003120b030380006140c886203826411404914622614410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 526472598 1250 526471348 526471369
    0x90d030c0203150709140603010f15020f030a0e040b1813140d050403030f03020c06042d03080910180209091c050421020a050103050a02120c04030b0105012c 69
    0x301c11191030350601144a90045c000c20031078020305102c80c0c010400c007003040700c1c1d4802072040c8017007080888030822111205c0c94643d80380030700c2d90060300c41c030482e041c00c003e05591203c604500003490861a10a0300c0c6800e12030301000c8030094519000d400043d803c0d00004540244c01c0c11004080c08041908020940c0d01c1c544800f80c0070f42c1524200d030f003100c0c80900726810a00089000c1141510550400361192003a00c6c103407c0401c0c002c04241c0c84589510138920084e031060f0003009a1940f01241400340300600c5103a0324802c0c1d4030a8054079041c0322590400044035900200c250a021003900a010420170b55102907404a0b060364140d00d854941d540b800030151a1800980e0800c0d550340c3d0880d4100d0003400483c0c00d200142e00071b04821011200200d812504000d5114480f400180142e51099010701d9000317406180062501304038800e00f000344101181e1a000d001000a81441009604109940103007800e0820440203908107035116010125104052142452418148050b507a81d08660 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 526473848 1250 526472598 526472623
    0x109020102210c030409020a03050c120105010804030908030309070602010c11122b09110a0501171018230f010320100503060901141008060a0f06110d05090d030c0203 73
    0x103170b540340c0e990fa2802010713400001010340800c0c540400514030407101c030100d82e0300207503440c00b4103075a0b82480e00641f10028003810035002c210f0b40980c08181c1d0341742040154000d1011500404d00320780ba28800038250340e901e0404804014449030708008103480001e0b640400c1d01900102d503141d1244c0d80c100e0b05603022119a04220350f9801900c1c587d00103450748102c4019028880802d60364081e00180602c011f514850240001c0000d02c0c051424268140c3c09074001c40c0754503c601060b5500d080c029410181008041010740c0d0311805e402e100d0380c0602070440c9103201b60341d4a0100b89081040e048680c85c05200141c80c0c41c01e501d501c1034000c151914108030300c210050240240001c8450011b00d13980003110f1481c046e042980000c185801000311180440e0b01c020002c0c00c100d65815030494101a014001c1608012480c3c00820b14040d0034040d00043c0110f82d0b1902c10f006c0d20000c1107440c10a2a0308100d0912004100c050a1603c40c1d01c40307611843d402d8200340b941041c0520200e8600300c40c44e81d07070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 526475098 1250 526473848 526473853
    0x1a100e011211160b0a09080a21060803040509100f031b120809030f0109320a21030603080a0c08090d050303070f0302031504050c0f0d06090e0109020102210c 69
    0x1155421408101068821401071540c1602951501d45d540111121040094020036060202c4002980f06a240000c1d824814144101408401500741d00ba52225040b04500d40c00102d07052150741001c1d00c807254032090301080b4042c1c3c646404400c0d84051300c00d00014200040d24550502c005d2041d603000c000601814600340a028942e00b40b0084581104c11214442d0103a0314032209041814062856010f4000c145001081729204003031000074940a6440c403509015210b84070108014000d0882c060301a034000c0808a0074070003e9494030b00310301c1c054030a261803d5410300100ea6410143d540801c00340c10200c0c2891107038101070030b070360050049a039031080e61910040100b10010010b14050283d40d1140a02d1000050b41039069020881d0042c84212803400403405505d465081150440c10b101c191618144001159401d40da00c001403856071107440c2c81c8208240c0c03480703200d04103225802c100200702c60561342d80004e490b003400381d1302e003411103608500340c280c2284c000c02101c41001300d0504 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 526476348 1250 526475098 526475107
    0x50c0d02060402040c05030601080721090f050606150d05040606210b0604021e03060d0534030f03030509011e0509070906030203030f0c100c031a100e011211 69
    0x400075901c1d001103404034040ea0800c5c1c00440700c0741c000c40c103803801140c050b1502c900d6503848a0045502c0c0c501403000040b01c1010f41d4802c1c00b10250b0748a24800a8000ca0b41d80725503240a0810303c0c42e24001604c03942c05008a113850985442489041d60a80c51580d00041410303101da083c8040640103e4004038480410114215a00000c1e204108012407003017456014a03aa400e007004200e02500481c11f40960540d180650a40e400000855200200030590602ca01c0b0603101d582c43c0c1081d602410700610300d0a52218071903214840040c45c0340c001a041101120b02310356580181404440f0300406050701c03000840e801d0082900001d0350700426001c2071041c041450742200141038190307041c00e101e001d6080041072018070b9000e44803d032500030b401146084c4141258220035845184540054003401c04800c030401c1c1c00780100030420640da900843c9001c8480100c00c031030301042c500d040c41ba040c400032405045800003002c11405009081c004500303001d4080001c0079042d80b007007aa100d000f000a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 526477598 1250 526476348 526476373
    0x5030a1227030807031802040b0a0905100906121101110c1f090b03132604260115090b01210e0f0d02120304030c050105071115011212050c 61
    0x188411886400303540e407101c0f582c5400b0030503011a2107000f0300842c1400c802c10190050708250b0084031f51002c0c003500c1020203d640c1c2229408861007130b54806003a4080034001c100c00e00c15802118044d1400f0840100048015910a42c400101546541c1802840b450b401f031990000e00100030035034006400900e581d0400d40e80010301c10310700d03074890340030808064010400c215244266445142e5032504020700b4001038071040400c0405240340007680d850508224403039a1000007400062140d1081c41c03071019600c0a6022044100c148581610307894140010042e10346401050304481e1040b00008000c00c0c0d81d00102d500606a0300d0300c031200304620354800d5180e43d443c6e03c0705103c0e40d000401e0703600c5040c9102c446510358510600f05d000603401281c5206502c0455001182c106120303081c5808000080d075605402d45108840c2103003c2520900c12042c6a0014031070700d109100d9410503039405605018419559040840014000c200341304004003421740160122038401200500b282c01c100b0000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 526478848 1250 526477598 526477661
    0x13050703030503190e07060507080d060b0d0605040b2b02150d050c030f070513050d0b100f0e041518050a0201090e010311040507020c0607050307061805030a12 70
    0x4e031000070b0b00380501c100c000134860403071052002425403000174103151854894102c48607000100242d0f00d1400030006003404490520271840100501521281c642900d140107000722045984003c0c0290b0510035003e0003517642007800011b24603181d1002290405c90242c9040442342d5020083d0400681c215a1001564a0001d8042c60b1401c01c0c0901030340e80c8080050744c05001c2503507040802d90302040424078480c05907014021741c980440c5d01d07500303c80d60340c000a451040710740c00c2920140078000c2800b10507075007480940042c12209114004003454461a200d440000400241419180c11032480c0041c40307a8215a100d01a00340e1243c4000809040c0640c95091002d41240451141c6000040c06550480103a0403290406110141d04400c5414807002c0c0c0070081c198000c41c0105591200165110000750250600070b0006507102c0055143c42c1c0c088034100414041504901d41c0021b000501c004101ea01080d8107180540b8031b80c40f01d210b00800f03070400291014050744813002890320f0f034141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 526480098 1250 526478848 526478851
    0x1a120c060d0603060617191e080a02010b0609010c08030a09020a0807060206060f01091203020a02030304091a0a0803190504150f1707082a0f030103020a09150e13050703030503 77
    0x100010082203540d91004074456030b41510211b003940180003840704000390203c008480a0040101044404c081e40c2c0c400c0700b14810483c00c8070b00103000b0030741e021402d60922500d1004013058804610b40703810756001811010035840014100400000011701c140d6582e00a4854194081c04541c1c0a686609a6503141c4015000d810014480c00000500310b1400003a1700301804010303161510501e05140d04050702028442c0c1c245c2c154480d44040e84016201007006100410205da00081c0540c540300b4002015204000414800c1c0f40029040c40231032000b10480c0c41c243c2521045031150741401000b81c0e001e01540d1b01040308103641030113041c00c0603008004844403030183d80c0c44040c1d00042c941d2500b0f81100582c2d10f0000101c8200000d680d071940030128200c105020304c106014030301c1c45060007030194401d42c0d4001d808440440108214149100710901410040c401480781210346061804503080d80e01c55642c0340c0d081c0b0745c00f094140c1117002003030700d0b403c0d04641030714140c1e6281c0c10b015156500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 526481348 1250 526480098 526480103
    0x50f04090503251a04020f04020d2901030b0604030b0c2b02070c06260a1404050705100801140108071205130c050a180c05040e1005131a120c060d0603 66
    0x1311000344039004240c880c5442594000c05841c200184041400000d4000c6919000695652401134042c1d44081d08078090700040c5041050141101400045c00e80d8406110207010b07080c181702c00e1002640d11600035038800203004500d912205a000c410f9284403a030380c008842c50b0034426542500c20007640040503080e00074401030540070795a640407101d130701009032420301007002001030f14043d87d29aa01c44d07030400500d003030101c0c0e202050740103014000c80a40701290544e21080081084d03042ca640700740041d00980c02c124105625001c049950319072540206410407000310009074a040c005c000005803951050400c1105c0e190001c000d54140e00c41100170f440d0f020a6030030014540c42d089484005480e030041d069030014903045110300240c119000c95600344007040c03201290450035096028440c40c141603409414615000a00c0040341550786502c001c9821304191402030074140722451070700c6106072000744031049681d81850416041d03650940d440403000600301c007000d105030400400d4a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 526482598 1250 526481348 526481363
    0x130b0c040e070c1a09031b0102090a1e030b0910020c03090a1502030409020313020d121701063f09060b04020a0c080d020913050702100501050f0409050325 68
    0x21242d800a407102036560200034000030094a101c190b142220f40519049a1048100e03814125608101001034446151801c441e0394042000459451b043c4141001880304c940c00d1b40c0c0c3c08100308041e00c0e4800c1140405405c144041d0042080741c1c100300a07044038000c601500b15241c03441b20302c6c456141da1211310300e0b5101d440c2a40e00414203804840306100310360030030707001180b4003490200c01300081e401c007c2680315203034044e4490304050b0b04c48000301000a845070034180b002c00300c110030240c044100d400b215a94004108c006100403504041c02c03115000d42403402c5c540d010030620905600207a4403403408011103011a208595030300c1504107100d070500c030795004c1c070000403c842030200b00d0240040070000616038602c44004a20402c009114a0008a00152402440030003103080420401801c0d07560380e988400304021198103000001c0f0401e06000d003402036500d0080002c401c40089040c0c00e204550722150941004010022614480080354038400c058a0320450314040c0c21880790140c4d07140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 526483848 1250 526482598 526482601
    0x30f0403110d122d0b15040b04080d031a011101020c01091101090b070c09051b04081506090709090b0a21021f05030a0221040f121407020603130b0c040e 67
    0xb1012a586050120846941c158a8008100b04c10010300b888824094011004001d030300c10050498000704007a010f4545c0d1595140d10301102145405a01084002050b141011502c02111800c40140c00c046092902441d40200000251300a02c5494035086140d032800d40000704208a2215001011000b601c0755017900340c1c0c41c02e03224410b1052050003440d1801c4604140020b0701c603540090f030000700045548107a0b804000c66414a580960000400e55100c41003042460055100d0a54090010340d0b613880a400d00c04405081a03c041c003401d400d07a900c480f01030246031900420300d030052050507043c151025440c116402002c6106400343e0181030324011061404403041c02030401010f030b47d52001d10b5540d852007400001e410168840d030b4101c2c100410011154426110715010b42c1c012500f18106186c1460050381c0b800354407161805009082020050401011041d00c45041d01a940d1640da80c1d6460500411040065070007801000918280001c00450030302a205903101e103180b01205 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 526485098 1250 526483848 526483871
    0x60501090b0c031e040e07021609020901050a0f030b03010207150b03010c080106050a031103091605010e01020a0b180d081e10090e070503010e0a02090105090c030f0403110d12 77
    0x74840c101085000e0751007000380130051944000340d003403c40e0711000302c02d04140d100c4070030b001c0008003039a0000050b480005102588180b81e860b460051041306030442c5402c0c5100006005070040451032010b1205040c1e500b1038681c082d4122407117256000f0002c40d5151034500d40842c0045048110b00320151030700300510081e00701449503040d800e02a45450380c042e8078010302261564401c8600c4030070551540210440d01d603100b8080d501030700c039003400340030f600b078009600800c0c0940c99032240f4100300b009044110b40c0d0340c0110b80c04d03000e66000a03041d246e40d40c8040d02c40715024104a603000e000d100e095101c403c410b9004044500403841e80300140f0148020b4505880340810503282003242c0c4014010030007c9400c0c55004680f8a0b82d498181ca8030750350744400003400c498840d054000107406c0f40020708110300d40340303940301c0c007601085580c00c1c910b0034440c8008030386000042c840010420000003040c14035014841c62015020030000300c0d400781c0030601c0d0007000514210001840c0d21f041002600c00e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 526486348 1250 526485098 526485119
    0x50609010b070209130b040c0501020d0906080a0b18010303020c0a080c06030105010c140f030301360c050f0d060f080c181f0902071b080c090402060f030a06050109 72
    0x4036000345428a05003240c40d02000181c0e4000341c000c881441c8500c0d405c500285042c2001c9100c1c030b0143e42c040c89618903080029040c96524100c9030204200b0600034044650007081c020740202d60760304001981700c48040411100c1c0c4903000415100c0407181c00000c201a03000409000d00c02d02a600d20b5100c5549001366035039100186d80c5240c0c011024001480361b03500c5801c5141007603000d000071645603109030b0340032410100d54041d0b45500350000001400a4501101e6980c0910003414100d0041d43d515462680e903092640c007a941e249441300010f5a90b540b00d0401d90700c4008048100583c0e850340740710007200810f002c0c0f007581c4502c8419040060700c031030302083c0d00d511920003404c0c0342800e0003029040300340500000c04801100542040c99284c00480c40b008002034145200c0060fa103100342d013418001e14900d1400c048003044a00030501c032a0fa00401c400c560074100755005d40480e00e840c40011014010b840f50b040f07505a01004010141c6a16006441100c0080e00c400030030984907014800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 526487598 1250 526486348 526486351
    0x2040906050109081903050708130503011a0319050f100507020712050a15110703031a310b09040503090103060b03010b0405120a080705030a320a020a1e0303050609 72
    0x31558001c1521700207103410403030710b038050188603281003490712030381d59240d24190301f2010300c020000c0e40b201410300050a0034070a0311650102030f04100360900100000039602c50701c0c0d00c02601001058903000d42009402c00600d03100305100350a560080c180c0000100040108698000052241c2c00001406002c400303c1c072060307160050007a08000c5132a445042d1681004960390103c59900d0314070740030340c4ca03c0e200070740304a0344680e8010a400d100e0b6440c2190080208007580c2c451200b200502480c0c000400307030b481d0301481c20010030074500301014031000200750742200c0075000845003082004001c80403004201c4600240c03030400503240c540401c0134117400240a66480300c40304110501140c40c1a501c500802900c0000300e60041010b41c1c1c81e07240c3d03900702c1101140c040c4d001140c16480c1e180c00c603040704039000e440315050420365040c0120b00380b80c070031040f03400b0b00c500c0001504450701c52003030103548030304e541100c0a10200030442c7c030003d4112066140950000e440c2c14042117807440c0107042d05 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 526488848 1250 526487598 526487609
    0x120b0f0408090405070e030f0703060e06070f08100305011b0f02060105011b140109111302031b09030a0b09060109110903070302150d09050a1502070528060f02040906050109 76
    0x80c141140030080c40020013010340003c0512035030109a41c010340e4208500349420540001500401c0e00e14a051002e980c1201900d01d06a0407080810888c143d00403c500c0b01c00381e4174500000c06446000c141d880180c80e0b604042c000e54203102d2000509000c007060210340ca4481e94680c40030f5405013030100d031218420300a05001410001180400100b4602100141c03800341244050740310701421881e00712001d00108540d000d822031500c1c0f803e45000c945645032030140700000e514500d4165103e402100320880d0300200c456001c54070324100d0b1000c100c0d40210641c045080086410001030240c0c1c0c800092295600650406c040f08009402400c29601e070740da4041c0c01024024116820004a00308440d401c900d0920b06010900f41c1101138000c0109041c002c002500100310641408850030000d0b541b41c060080c0100402400108001410717820400310940e10070108462584008a0540c101e9018140e80e0a02d000c0341c103003c00c182d004100312040b0107010007415503940015600d00505100e803 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 526490098 1250 526488848 526488863
    0x30903020a080f1201090c030c020f0d0c1509050a120c020a0315140406060305061506091201060b0a050301050901050a0b0a05160204020703020309090709140d020f0901120b0f04 78
    0x607000001c0103100540200c90950703074210300b4071903000d01c0d14110420990220325426221034000c5078942d013521811100001d079202402c071100c422100180c5c0c13808142c1504007084078a004400c2803000704e841d0340b005e00300601030a10601d8014100039585844c0e500c01500d04003031600000c10042c0c022103e103080da0f42d019000301400f614540303a80c554803128404481d50300382c4488140c0321060070b0030082ea100314801c00c800511617085d0f09190b860100300410382202c401d022204031510350b4992040c3c90741e11004950b50034038001e881e8001d501410585d0302444c40c01c080414980586034000d4043c6058035070030703144500c4a82c3d9441c10441d8000d1180706540f0100020002001402d11910080040f00c804405540f481386440d4049000c90380103070420380040c0c01c00302da0540c0381c0c5020f080954001a01345400407100b8100b40d42420311706508000144607502441a100841d00d40803a1410b03800d20041c00d00401e90394901c0119040c41900400302c1d07201c9210030028a100000c0c021850103a03800014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 526491348 1250 526490098 526490113
    0x2090a050f061912080409150801050a020f1605010b13091716020d0c0b0d02070b0a0605011b030e0402070c1a0a0813020315010602010c090f03151503060603050304140103090302 78
    0x2051401300c40100b4145d450080400c00801c41c1c0100d0300580280b20210080c00c10b0307403842c04443c1c5003110f502414044c2d03900d00400c22046c0b10008041a240300306e6002d052012518682d04c1c0c6280101f1449980300e400100d440200612500345901c03403071506000d55080d850703003a0010320301c10380c0d4425441e80388148001011400023604011802c810f1891252120512a90301ca10460756a90880d1419462060300000d00310100a15003141c2500328810b03007404d010850a100011344011500680011208442942c10f401e140c40b4480352a02103601500c215582c03859400c000011601501a07490a130025441c84503140d048001102c982c04526514290651280101d0301014001c1070400e07070b45882030041d11850541d2890303409000342295000014058030089000e400b82140e48c4c050a516120322400b0000705d251650714882074000c520740002c3c012116002404244201d40000d0300203441c00c4404010403c00100400c1074035500c295088010620200443c15a1003c0744000c0c0140c02000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 526492598 1250 526491348 526491359
    0xd050706080a321f0e0403110d1205070909180c080d080a02030a0e150105150a120b060c0703050a03120513060902040209030d021c0903051506030a02090a050f0619 72
    0x2c0095421111241c0298031154103414918181c0d44135800c07000303600c08a0000c2c84200368010043c80f042002c0580502500c6c050504044e0090b503c1500d00700e903650b250000607100a04c2413580d18003408098104114815509560000f2180032603011241c0749106840421461030000325038180c11141e5076000b44580d81c0b13001d140045e400140418040a0307c404110341107100c10720090340c2c0b6039a0100f10401640c5003408210200c0358000420260b64820002649410351050381d2400368035080801285074411300c004680a44240003a2244502413076001000700880800c14031540c1c0c1c0a541c401160808810961080711400e6550540e4426800800e5000400a400c4000081d00052006041c00700180129082204200c0a100141c114448903540300382110010003240c0460300e40b0445c101d003944e441c50754800d1000f6030215526490780000d0020341d02004000040b65000d89000d2840c10100c038080b0140c0000d0343c80ea40c0700b0305c40d200002d2603424405e07001521807c00d516040034003031404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 526493848 1250 526492598 526492691
    0x11090405010803040f1a13061e0302030106140723060106030e0c0d0204051905011d01080109020102150c04090c05040806060103110301050d0303060503010203010e061504030c030209060d050706080a 87
    0x2244503c2c07001028400c0b1f0402a1031507407154000c00307075915003044945109041c1210140001c0f24541858810700052003030591140e1140e94541110351800c3d036070409070a0070440c0c0d41e00345005203002c5180b2688842e001c0340200e0403a0486000341c805021b040700501449490b23008030524980c01206441d40c880145c03a1540000b600050a0000c4562490701408103c0688000760440c00c0803508c1d02c825200750544603003d081c0185682c00c0204684011030b40006e450b110b040030381e10345004601c5c010031040306030182180d000b400d40303c070100300e4107104110180c0190003510640549024180000f0260b5009000d10907a80300b00718076080c0345030300300010004064503250054040540c3c9034404281a1403d200441c06400b0107103c14400c4c1c40c29004212108034170200340303d80c5980500c002c20000300c2c85540e04080d2503040300c9908240ea40c58000ca6240a503400d405009440368040c001106500945250301030841128107010f041540180d6503003094001c5c0000e0200d400b10b600030944c90291 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 526495098 1250 526493848 526493879
    0x10b0d0c0e0d0606050307060c02180c0c0102030405070f06110d080901111602040c11120a030902030a11031c090e04050102160606141804150e0111090405010803040f 73
    0x103040c81c0300c291805402040d03501480401c110741e510350b10f2601340b00914081200380020b0840e0720b00000c1c070204590203d007206c403034a00030210400c4501d02040c520900c020591b010303130000b50001c54891520703052460340c40d40980315140c4e01030742d18907005c2403081c461a50b0010b4140d05a00400545002d00811030b42a0402404d041055517156002c0c444c0c810344a00800d44080c0780c1c44862003114203401008100d86103410004203000506240003c0303100c0214019580821002c000c580300c00e80140290040c1c014035900a40c94092281c00303104006044e040742220350403e5003241c500442c1c2c640740c41c1c06505d0b080510000301705040010043c80c541501d00541c041d119400150500c0e900e9000320f43c07044180c0300100c410549811041c402900d40000c0566094811143d100d51030343c088030f0182a00c48040d20107440f6010032500d6482032407164010500040c4510000c2215032134031008102950030074a030140c8264240800000c00d690000161015210506003480b0071501e007076008c2d0b964568 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 526496348 1250 526495098 526495121
    0xf0604061503020409060602010219081317130b0f0403020f0a0b0309061b07020f04090c0b040803040509160807081e10031406040c2702040909031106010b0d 69
    0x200e561000c581c81051505010102450b600e0240c1c071282060040c5054503850307040304045a2050040804046800402e084014010308180c070194032080b15040504812400141c10425a0240441e01c2d04401000300f415036001640c8019440d2901da92444030711500d01e2412a912060109001615011a50300c0c09150300401052481b0781c1c134401d0540f9504102c400480c0c5070045010092110124850700c11140317102c01d0752510340714072030740095484200400e00d580141d541c1c400302410090348070000c00140c042d4800807a182c50391200110340c7c0c0c1d841401054050541302c40403030002c4e03180c00e520001c11925522600b010707589142044655050061820a4038034030191480a00500030700c400d4010394055000b05080c40c214182000440240030031003645900403820031001c11144181d102c20b4400000103040461070f0301d80d85200c0c006100c040c001c800342c800100082c1c907aa0700d5000c0180035101e070b1145900d25041048040d00c1d01001d2081003000c034410081070079103400340e038801e07100c007407 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 526497598 1250 526496348 526496351
    0x70209060a0f1802071217010b030f01030809040b120105100905010b09010323091506010203190e03030919050f06180609041d060103022d12010603151a0603040b0f0604 74
    0x255444a2500c03c5121b19080f012403041c0c42111010702181c00298003510001d03028034594284840c1c100c407110030510002d0641840130484916590361f9130049144040d005220000307818524441600030301040d107080600103030f0b03030200180d461002d0042d98100c41a1082c2c4034107100d40c07400154040d00311105c4500080d4490422060010052031041e402140403000800029119801082c0d038414068192030640d1300c28012008050091750203c500c0d0b84d401d285c01c007041d0b40c10001081c0782d03001c0c41c1c1c0c1c8554020a400003c07444090340c07486140c00c5a2044804107618030801003440b0161207041e02c9841c0e08010303034041c01c0c101d08000d001842000e0014000151298104003100d002444908100340580c20203c01001545881c1344000f50f401e148941e81060520001c00d01c01d2401000c21703519001c0d6a0b03045d080b9410500030740c4500c004540050880320b14242c1e0f0301c0488010103014100c0000b0340b01c540d02041240c1020070949100c0ca0784203000c100c09403241b0f50346c48405c910080c800c42c1d00a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 526498848 1250 526497598 526497607
    0x20a03060f091e03020601060c050d03110408100509010506010507120815040606030207060507030b011b05070e070819020313020909010e071214010b0a031502120705070209060a0f1802 81
    0x1e202c03042201c040c10f400f02d8030308100d1802864000e06151060b4880010018409102000b20f036001c10040c05000c01820001148071528003010924015580a40322500425000708001d0645801051080c00c1050080045640c0c241c01075449004602d00078240720171040c4280c94460054510381c1d046800c0d981084103a64a200000e01548c425800201c00240c0100740070b010400350340203050f0009558102030141d42e4100c40001d011a5001c4800310306691034078694002d000081c4044009440b00724801103242c5004600500341d00c40542e103000042e00355900032500c00710507100742c4e4015200141030078003800040d000c01c1030720580070717008002c55541d4001200d4801020400c0340005c01102811040b406094106450025165103052041b6418200070fa00295103040e0420f003a00d138065a10450300b420780440ea402170084196081d40c8800804c14002e0039034014025050076442204c0e4041140d5482d42400501402c61283c0c001907035919009005040a0290344501c61507820801400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 526500098 1250 526498848 526498853
    0x3f080a0509030c0a051012020f04080c010206181f0b0d1b0902030907030b1012030c0c06020c0a0b220e090f060c030604020717031e13020a03060f09 65
    0x554060428100420000290382100303007010300c40c0c841c141c2c0d82180d0203002d96241201151101c00d040c90484104200b02004c2a01c6090b1076065410002415480d591070380d80704e0f608a40e0b076020144c89540548500800504100b014040768001c1d01860700181c92045501040505554030f0480b8104495031201e4400202d030720359104141c4d075540100c88141300c04950080500c0006602c2e002501c1c070a004100b001030507140050604c0c00c40e40d10220024003a6100031300c0107021980e60700404200003201807030030240740c0e0104030b480219014445c04184190b840f20b050342d803421038014494001c1c2000c0030411119900e40040c08011116080d03004112641001406249034960000082000d84405100c484001007060030590910f0b940181040e0030100b40d4280103001c0100101d00c03698000400804001c640605901c01d1001818000d49074180720200c1034800d2142c070044910340107420300080c680024040c0841400c0d40203071410366914119200c010240c82941c0341d804bc82c40c1c44a41c41c100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 526501348 1250 526500098 526500113
    0x306120807020d14151f0302030a02060702041d06040b1608070c03090f0b0d0e010903020304170309040e010b010806010e10030905010b060304080a030c0215060415030b09010e073f 79
    0x1045c0d4001d890f0710701807410101c101d03841e4000c280d040c04040c40041007400161000194040c210390110340703503500d61083e44002406454100f02104040e500c04288502409000801e2405184540d042428503668044030080070003928000341c001500070750104203c0780c081c00301030010f00e00a103400344c1c8440c0c90380001c1003020000d900401402c440011010714085651245103103011068000f84080700b0305850083d524001c2e800b80b40d6010301b28280800c1c0000040003101c6003c0c902500500000c000c1209140c02805110b501301c4c00700d28440c0c0002c5840d0320404004000000c020907052800c0e9024a040300200b48800f412500f540d626904c01f80c4a98032800917622491007014402d640d00d0811030b0003000e60780040c142c070003075510060003548444c400c03c15481d40000b040e200095002d0120021416050059002904111360b2906000c1c0100b810340007140d840195900300c404007a6540360540c01d41004042c813003410300c83d6a070000c01d0700030300c07805108009174010501210941c5688550780d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 526502598 1250 526501348 526501363
    0x2030a0209130314040311060d0207240b04050402010516021201090f02130506030307060f15060504050f09130b060d050609010c08070c0c030305030705120f01060306120807020d14 79
    0xc20701d4070320a007015480134261403005640c0c0446030519145a98103061310b00702202c814440c1170041100c500c501040d03415030760000d4102803280c50601400b009030110522452a26501c4da06024000041c2d08041c09028022581a5241780c60102c4c0c1c0c0d035401400c0340010008aa10801e48120401c0d100c00900514030528000c1c07001303104807012481000145002c0070301c1c5030041420007040181c02d40c3e0102c02d8483c4203821100c08141c01032161101070003880c40c80090140c800e201e42d004610180d0150203041074440030355460195000c50000c100c0b0550b42203d120404140e058603140014248412480e0040c2c0060f0160110f84040d548407030034564111901d40d480e81d0340d00c08002c1203642c0600400c0d00101142410520900f00d915103900b440d03018000941404000030110b0380c041e00c650112201c020052021002c141403800b0398480f166400c0c40360f80b0010742054030111305808082c61200700c4582c844d51046c903002640d428400f00444041d4207488613800f04078456007a00080c0000d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 526503848 1250 526502598 526502611
    0x11e03021606020f0a110609120a03021c1b0309020a0b0c0c0d1401050f010620100609020d06051816050f0c0a061a10030203150d0f120318030c02030a0209 68
    0x11358075800b4a41c1c00a01740d00742c000305101254046018080c08000116440c1629448490347c15511442403209402034443c0c40000c3c2c0701d400124022181070f04043c0d00a109012400c10144410701c4200740031001d41d0566200a50720038190a020481c1c01e042d0780081140009007420740d5007030b204810000d07000c0311070464117850140d2060340e02c0e80700c407000303204541d4813000c07904801400c0d50514400502c001d526010130003850b00040380c401c0000508101c030084c01c0449100610056445030f254101070342100000c4896582443c3c0085464a4101141c2183e50b400b120000c0d919500c88588220318240e84c11000140304040042100c80300e00903000341000c04004c40280701103065450020112514480c44c41441d00d0317803c1440c0040e03036561032240310080c03a40c900545c40351070b612042a5042e410101459200d4810001001040803460740c070700d9524081c009450041001d00b106a054a245046640e0803d652010000000e40200b0b0301c0e80981e800601181c0c0c0401ea00c4d8007240d64000240c694 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 526505098 1250 526503848 526503877
    0xf02040609030b0108120723070b0d05090d0f050d0b0303030a1d07050907030b0f180117190b04030c0609050f010b0f0f0d02030a0b10060806011e0302160602 69
    0x42c0140100c00010742d0060100b000240a40c0f4a64102241d0601852200400c00e051141441864581c9112094a4100100180c4800c0d90395003500346410f0303011140301741a0b1414000000c85460002c204614040030340d0f1541c440c9095660310858050380100d0488414a035258100016510100055446030b01c80d1000062807500c45e4135881c0e80d0075050240035400350320070310080c00103403209070006402c420725080115426001d000015283d20b900244075070040b01c00c010014464441d0103409040350403a2607461401c3c201c1c42e021548400900550b040251a03140130800041d0220f403440c0c0e07000c0d020303240140d244400ca6840c6000d81d1a41e41c420348241c0d1058080c071503038880a00c500710b0319a4044400b600c405c94a140428149400103064038407a50f008a02c500070b54a0a01c0421a003940c4507004910310303d0010712034501050103010f02000958420000f410f594001e2021400b40102709843d00700c01105040c0c114042c1d80306200720105a44045590000109540040c00c8200020450b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 526506348 1250 526505098 526505117
    0x4031e02040615270e091509281103060709080d09030b060409060b03250501050c03070b1503100b030c091e04110603090604110103051e0a0f020406 65
    0x10402a284181c104420803044441007008240d0800140c20f14030911441130201c114208080760102000b03039100f8440c010f110801c0011300000402c1d502da03400c1003044080603c0c0c4541c4400340d0755a100314a4415804c460814100030310000842c40d186032446100c82101070f21030742020030308000e03055070b0b030f82e000c184d03904ac05000007103040c010901e000005181c019809031643e00c5580e18100301805060103140e0f6010400f081c0300d841c0d00640e882003005000c480e00d003500071a040602180303103003881c00c1e41000907030b000c40d896125100b2680f035001c088000750308060458413031404201d0050442000c0309202210032070b25403000d00500311140b2802c1780004140410034181820003501d540f419100f0b180d0b04082240144103000005480010004280455611442d03d075017003404c00440030b94400404003c000700d22100249481c4154070a901c03824541a02d0401941510320035240e01600d001190034080c14044400141c582c020640e00740842da082c02c10207424120b034070540140c0c0005a0750b44 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 526507598 1250 526506348 526506353
    0x90b0702010608010b130e01020c01090f0506060a03020108040b06030715030f180321060e0c1b010935030108030c16050a03020616150e0d030e12030c04031e 69
    0x104103001083ca840003031150080090006610003010441070081658600117003104502c00d6055400c80c07586c8000070060304810b4100320b43c0400b40301c00101e515114020005500d821301c07210602c2148d5041c1c480c68419204ca0761a02c2c41c0d40c600800c039580621801400003070043c00041d018a041c5482e4400094100030b20444c181a80c01c0700b45950b0118400007000400130b94040d0141c55900440c100301680c0c21502504e420250800d644011000b5442405201940c80c94000600c000d0050b00800d0302d455801ea0042400c0c1c4100300c0d80a0180c20032848000e01c51550280341c6601049401c60b0464210584d0b0b00c2401c2ca50001e03000319980781c2c408a003112070f20000300202c4101400c000c040c4503402d8a4400001c00385149404024064200802e0060b50511108004035072568007101340310b04030800c2c070040d8005152100c2d0303030011880f4051207542da442c044d204215401c50070002400d2042c1004890141e90380c0040c10301d84100404100c00408a41001032000110309600440d08140140b030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 526508848 1250 526507598 526507601
    0x22030e0310050c0708032509090c030513020f060c010e03040e0c19031802100f0e0a050603151c030c0b0a0501060503060907110708060604052805040510090b070201 72
    0x10080103110a15200502240c0b4607031005440b081a44002450f940e1f40da000f04400071064040960382114040d10740007081141c001d8076402c140c42c801c000400201e00e0601c0f080b8241e540030b4603046070b1294115098409802c094404941d40caa01604051800310280b034035138211481742d480414603420100c0c0601048a4103811076800480c01d4151506002e210b00c50a20301c1e030f05103183c0800385a981c60b03021000c40c005a09103200980c0003801031305902c1901c2005010300b072207415010009418942100014134002d030017502a2100940540d04680e03904c408031880c0100b01d9440da42c42010185407007104012800001c14980c8aa618001c03100140c1c13030158801c1c6006031000980500b840c00521000f5402010780f5840081159010312035150000180c0e03071000700b0410015140520040810b80d0100021450300541080d9030400195480b02a1074845000b08031401141c83e1405903044c0c5414001e8214940250103041640d900c078440d554010101d81c102d82089852115181c200850990213 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 526510098 1250 526508848 526508863
    0xa0929060f09010303351e0a0c05070b04230a031e050324060406090e010f050f010f09090f09031106151201090b25050408120322030e03 60
    0xd8600540e00d504603a4043c1c5641d05c6c500980d03885c00303000051442c0011558092130500c0031010128085810601e6130b841400c141c0382d201070100320b0108086040e0a4103886a03118031417040d540c141c00c1410b59030385c02c1555280038009403026005e42041075890485900c064030040003080040061402510340908050002200120380c8903240c1c51800d9101e0300042220340c0410140020100300b900904010b00301c0c58141e4156810401c00701c1d0203d1015009050041540d40d0101d88801c980e0360390750005081211801131541140c24181d043c0304550246c0018600a49181440c1c0c0e500c9031180750100891f1042443c10703034110380303543d440c500f495044000d00148060280c05018189408601c01402c00c400c2042140900b032601c0302000a05029881011002c1e13002000c0742caa400d00848030065003a078855010105440d20404405050041d001c540442e40804040c0507842580e140f9000075400c01050992a9024650140a08540c2c0084800e80d01c3c843c0e1203180085c4010400d0500d00170740c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 526511348 1250 526510098 526510129
    0x7090608070c020a03080309100c020102130f051e120a030203132c07030b0301050429010e01090507050904022d0901350106020a02040c05040e0a092906 67
    0x10340720402c805a101c0c405600c00b80c94000741c13a550f580c0c4504c9045490006510105201e4914100384d410345c1c994190001e01c6180c001000c89018180c880148000d004131a10680c0d5001401c0702d81e00030402c50301207042540030710050012202da0300b40c1b2640c83c1080005101180183c01c0000c15281c8102c0805070013000d40345280e00c40500c034400d40c0c08a060f441a110064015469000016084501c2030304180d49696002c0c00a2003582058a02030700005170481c00824070460601d044914003c1202e032550480b80c0c0700740d214416901e0140154010700019140c2020440108250051a02c80303000425144c4600650071080e600c0140102c024464002ca0400010004200781402030b070380b01294003500c0d0f038102c0c1040d0341a801d1148803e407030390400e000082e00c200072200010306070f60007188500003903000740c400340300e003a18290040b02d03c0d21403409185103c01742c51000c40c1e5410035079801200b00c40e10070b00c07510345582c0c0d540c10303020a103866140001364503140203c10004581800d1000740034460 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 526512598 1250 526511348 526511357
    0x30d0506123f1e310b07080301060c03051216020f1204062109050f1504020a17010e0610080f0a24180b060108060307030c0506070503120709060807 65
    0x404584503030303500744640000c0300007030024500f0b03800021200c503007114181043c00090f10001a0b0150043c401301003482030341050120b40c200009407940ca4501241c045682c44030900b441c51b8202881646d51424450b4107401300001032040c40080c100040f41c290003100d0f40a00c1c1ca03588252960300078076107c00c2c000e005405412522880740792021504c180d40580d045400d2a0415514968050990b5881c4900c235404031410724090009011021414034030513020a4156907e9a4100304402407a000694000303400150103041080340741800b40c008444800030400125034601c5610710546040026100c00840e031212200411201d1401c100301c1c8a94007101c1c028003801005501e0f45007101ca0360b211109582c40098808190b085d04a501082c85e62480c408100d0040015003000d1026035030407900c5501007010344000c82d402d07203000111801142d5021040b203440070704000a101042e0040101140d551205000480c801c06131401341520850140d560b42d244d1314540040101503d002030403040610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 526513848 1250 526512598 526512703
    0x180f0e0a0206041404110406030c0f050f0412030e0a031101020705151602180a020702010e1806060d021b0f07060f020705010c020109051309020306010603020c030d050612 75
    0x60b112081500c00302e8039401c5404100c0c01000740442d000d030000c40c0700900418000600821603d4150744400700741c9106a0f21181285c404900544241c80354203a0100d040006000401c2070050148242e031040744a80b81044a895040300403510b0010250021100700700074010400e000e513410054840180411a407880c060881c078100318060344504941c040c3c024a44d42c0310b480c1903403648013540000d00d01c001c0704a00d00d444d14041c140000d40040a0032400141b602c081c96042d40390031f2403403010010040401c0a20350b100d2404214107640b0040322903d132507400b84410340c08010106d42072500c2546030000341c040e40c203600c2a40350a0902540191b001c3c0448002d001000e151700003142e1040d62001e0030101c10400c0d003070005941031001380c1e1003180d011a0045403115407404d103030032070750941d031099003162081d90f2144001d50503070103604502d030419403080c004051820141c0d00311a0700042e024000344100403c505d041c03424900540c02e10860300e00003090704411010b020f508141c3c1c03c0e89048400d07824 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 526515098 1250 526513848 526513853
    0x606030a1e030e15030f07050a052b0c1709010c0207030305031b0c0a051b0609091503071d0a06030c06080a140a060612020304030503010e10180f0e0a 66
    0x110091464803802000762148081018000c800040d0224401001042c468900b024100e14580c02210303107544440d014400b00d28614022402c0d81d0002c40f440d1509420607003107a1807142240404446030b441c0c8000d2901817022501e16205e54070800c846581c0c2e0f03806c10710240880300d42c0b50300050214590390b03151540c1d50b400541e02044000c16240d03d0300d8440d6594135070010361201d1030702c201352940d50004000f600901d011000907651b000e2031f108a042d01d086424041d094000482c42d14102c0c2d4000200b00000d500031710b0b11409540d4060f0700808800c1c6010002c1c00407a261540c02c3d0070020340420358245000400000c401c400f98400d481c0002444018103640d0743c24000703905031040c0001e1040b00c0300407612003a069003010907000d03c940c1c0100b095141044000000c5d08580c81044040303500e003402c00d400e000c5c0600072284203507010b0316410329503442c1140060304080c000b000911024000c0c2da01144940303010030818824803108d800461840d50150801007100c0300c20314500041e510218a5000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 526516348 1250 526515098 526515113
    0x12020a020709051f230301050a1a040509030a0c0515090604020a1211102c1809120705070b040609050405010806070806040c1809050405060c0f0d0c050417070303020606030a 76
    0x660f580f202002190750240b184900743c00350840c403001d5040d400c26040000640c0c1543c461400c00ad4440c1b40606003a03046005d0000701d580c291307107148160300100296110640602c00700044248944100c07060b0b0440d92041c120390301c00684900c001a002a000d000951410070301100240841ca01136030301c000c1c003030741c1c0f410350844807104402d004000580d40160f00c070780510074241c00d0401c82100320240350001201c4000b00008803000d18418901c100b44528142d55a00242d4850300700d64009100a04181e04004001c0d0010340040707da82c40f40c0703070001c1110100200038200812550b1604500b440c241000c00c01500e0381600842c4040e40030000300003040c3e911244050b00720009480014884990840444400803524025000c20b800e0400c0081c01c4071855001e00e02c030728050700c00ea0740c580d10744100780074451282c0c0c030080213045000d01050b03440e4020b41c4d00c030511404017070070840c0c50b0960315034450259080045050714035400000c820000e141c0c0602ca200d6100c5000c42c00f41109440c0f640e590304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 526517598 1250 526516348 526516411
    0x7110d0203160c05060703030504020102011a09040b0a09140a030914010f08040503040902070302060f10060519300605010206010b071403040302030102160318030201081612020a02070905 82
    0x42d6a0070949080d003040c0b00e1940e4844020b0b02d00500382d9582e030301007418041c010b0541654201d00561030414021501e420b051050000c1240007810103c0c0d540721070305e4803090b040001e40f815a0860742c6110b51070000380f0284442c2c000c3c4050740702414920300d41d428081c04103e03076a4803480760410410808141a80d02c40c0c00c10754008100e0500348d20a0b103407803c2282c50341c002c90700218811880008d01c1020305030005801c51041d1400041805076590310498100b60344035512801000c69018000000c050403580303032415640d2001c2c5001c2e0000032a0dc001600b54101c03088400190300d10940503a10300c40124080d841c0a00401c1c001032925514050354242103100c1c98402512498000d8910b1109030070500441d402190000c009540b5070380d4050440e118124065030840102c1e010780c01c180d00b88a1642840d004403a01615001d095a072164000c038521080d01058000b0000ea000840c1a5441144086c01901035a680100451030820820004a41c0702400c011801490b03000403400400321445c404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 526518848 1250 526517598 526517617
    0x6060f020c031507211802040f020406080103020d081303150e010606050315220e0f0c010503040b091e010219031a2b0f02100f02070302040e15010e07110d0203 70
    0x1c417409200156440207844403408182900c0d41040d000c1c6180f1212440c014404034001c4504008403001d01829108034030407407046c0000b040704100108007620700311003000e40c00c81c00b0361300c658500b40c52903c560313500000580084070094080c124030304c003481180c807030000a1300440008010307640c1010f0002d005070100030300070307080354110390000030198507060100c800b0a210442400100c4842d42003180c060201c54140c409079120300644c0d14180390000170511084001a120149140c03a01e8036550000316008000c690144200005500c03c14801e019010021518100050321040903a054000c00c0044154180425081c400310701c0d800440305400e095401c004595020f074142e13a980c42c0104150100f01c03505030100500e1006014490060414000eaa10071034081007813402007482074820600d44281d1100680c0261000d00040c142075000480c1660603c00325250114008050314400000741c04c42101000351000348000b03070f1b0b000b40c1c04030b030782900e40300203030065404c00e0000954a0240240c03c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 526520098 1250 526518848 526518857
    0x417010c0f1b140a060e0a17040308030a150e041101030c23251505010b0a0c02090612010c0903170306030d0e0616050a05060c041a09030f0106060f020c031507 70
    0x1040007683e04116000c08154009400c0c403500580c0c045031038a44d01403420542d40540d201c100700781a01004404c56082d2a809480c00c2e0550f2a44445d0701c0040c0808107803e102c90f90100404210509001600c0d445030f40b01d910095800c4004c00001805d8415001819051055500e213a5621051071081103030510110702d08030351103503c400d0303804803075480700c941812003021610404000c0c00100f0528403100741400c0e209000d141d17a5014039096a20541600000180030241c1039001498640403040d0407520003071215580e40c0c0300c042c2e21030031070b40441d0603032001c40c00d504420801c2004205180e80001101e980c0e150451400b00e000c40d48403030802c01911304000e4900700301ea41e25030700c00041c1c0e072681a986c0c00049565040b441c2803a43c030103040e5002e540038410400010000d140c4403040318103482010200e08400101c000c014040d0380c005810301541030054075140e82104c2801d2240100418550340c80e00750724000203001a0418280b40c0c1824001d4100200103a00d5014546115400c1381c184c0c40d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 526521348 1250 526520098 526520123
    0x8070305031222151a03030a0509030c040507110f07050d0816080a050c061305030306091b0310090f060f06050c010b09040b0609070305040201020327030f03030114010c110d03050417010c0f1b 84
    0x641000710cc43c2020b50f2251514050021165000212007a102d003401c08035501c610003c0380e1b00b55108038a2085540c000c0b282035806c000500034101804000d070040e858034a02e4080c81e502c0b221140c00604000000800125000410900400906420956030311040d4002d58503a21034030384922004213041d00444110021450385032050400d8035506003040100d64136410605c1c130002039210603100e0ba64800d4200101c0000c027020621402c4103c032002c1107070031780c0e0500d0320005030f07482d030403c081e01d5826540c0c1d60390707000a41c0c490700e08051086226422074492813402d90100184124003403d85000c1514060030040141d800000703c0340000074001d640001a4025818085001ca40210340da1b014041d0340c040c01e0422a00101441c140d030b801c189251025000748004441d501030100001d01103c10160740c1c43c007a810300428028a15000b441c02034075240d1241513050752018502032001362695101c00100e0b269038080f10741d920088032403412014413090a6040c0f009004a201c2c0079085448880 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 526522598 1250 526521348 526521367
    0xa1706150c0a06020d0c0e040b010f08180f01020a140304081206060403060c03091e05120f160c1505070203030a031e06060801050a08070305031222151a03030a05 71
    0x40b0800d6101c0010f555501003c02d00f8801390078905600000328a42c2a2988840d207070600a03140001c2c010323902c0703400c1c00310343c503504172411040a0070b60b40303484000407080c1e2011502404168500c047e6100090780d91442c84000901e4404205000350b480141481800009140a8116903540d00c0071100100c1e04d0711040300141c0248120b81c0002d1446140c1401046079a4041e0031038800c0c1e9018000e02d001c0c0400317450030039802c1031034680014540d0b00540150203042800101400700c21512136240d904003200c000e500c00d464141d24109882d03170f485a0400b0070500c61040301c08001c034007880c0750a904240080d40804e0f90b900070111110185900c40c00e4400e182402c1c0b185070000c4007000c40062000c640da595010b01240c3d03080c010680a03621055000c2506040040c00304100c9030f00c01c00852500242d0040c000741004050222445a81c070381c95110004444284603a41c070b00c7c000d145d0161388030005045041140c6018010190401440d50300c2c5034907a81c0801500c0c40e01d0700c6424003075568007000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 526523848 1250 526522598 526522603
    0x4032405010e090105010512030702090a0b0d05150916210206041d010504020a0c1403040b0714010506100905060f04150906021207110f180109020a1706150c 69
    0x8442421a45031600018142c0c640e1442d450081c1e203d0b000800c4540d80320818411806105070384c3d0240c070b80c010030080d030040c141035242d1a880400340c1c0d0009440740b0908005241000361300700941e400d5100300303128040104650b4007650030108150050070403440d0884000401308803481025400c0444105840650b80b2190225201550092002d40e4403a11841e5800500640c140b411346941494000031a0b81d042c41c0c402c0f01d103e141c075a1551000030000c2e030381c0d48420203226068a0520b0009001c009400b01d40b405c09008614801e50368002054000e00880d404c545c40101014031680385040d0b034852154004c13090005850082d01e0159482401c80c0f4100003030300c100d40c425401400320100039812a9404440751094802c0f0f9800e95550301a10320640b887c81c060304001802591903441d900e5450716100c00e0b00e0951410140c00745441a4050b0040907842e07009a01c200c00351900015102100d0b5403001d0070902075510030394204064100341c40410030540c901c8444040c07501c4001014090040d04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 526525098 1250 526523848 526523903
    0x603070201140117010b0621070507060203070519050a091404090f05010b0f0105180405060d020d060c02070f0305060a0e030403020619090b0a020c1908010e0304031a0c0403 76
    0x10314001002542c4d070b0a4802c101c0c040c0c221032010300703500c2e000f60042d07585481c40840b104036800280c01c030303059151211100e01d6010702400c4030302030000030400080068142e001540c400c907116280c0946030300488107040f0760a01d03502e03052410001c0030001e410405410580ea0000e49215585c03040745684c06d01c1c045001010310040182442c2240b44441040080541007900c0d460415100e60ba040f40405005640c980641c40202c0b45400b60b08804444504160b030080b41d02ca00001c0401d001d00b421500441c0c40c40400f41c406036020307502c48008420058040080303c0040080481c856040c520790b884460b03e92074081c003200e80280c5c5406825900750020030549003d142c009050382d59408070174020010025022407500089404442d0029401c41c00e841a1003182c40290060021000e24100300031101c04c0e0350300c031480550340c00a030125842e1400d00c204a003481d115001542d445095007001e02c10380070451640a040750340130041003104441c40c1c5c242c80403680c2c403003c05540c0c0882c5400326101c41e02c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 526526348 1250 526525098 526525121
    0xb09101d0d0f050c0f010909050c090d0f0c1a2205030d050414061206040902120f07170a020a050d061b050306041a031e010e01060608040c080d0c020603070201 70
    0xc030079404100b40b209030100104040e01c2141180c0c00311011906216180441d921228040780c42c621003000345100c01d0b000f440d070207410031000c01c2c03929a0030300008401c01102c00090700c504211103400d03c100005c0c0901d18024041d220454011079600b6000714000b40706540820403583d020500650b4500502501d207009084001d0560301c482c92150002800394000d403180161042003994091604d0070240100d03240c10b045410001690707602c51040c030001e03007850741e0102c0e0861008401458044828442c940500460360040c042c0301d8500429541d51713442440c0c144036503411182e803e000698540f2001801c59100340c4041459554a00700712005040c0d40301000c0a00344500f9040030a50383c08001144151000c071001c00c82000b280260082d0b10081042c41c54055100310a031120b540c0c641010000c062040400110300803c1404105095414951003540443c0741c1d00305000810000b000464042c1c15100001c15a60402c04001840050350880107802201c0010124030303031314400e4102c000280c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 526527598 1250 526526348 526526359
    0x4081b0106051302030f16080a0c022104060f032703140a020705011205040506010501050904060f12030e19090b120a050607110f060a020d2007020405010b09101d 71
    0x29581c0c183c0700103548229074412100e000000010400001c89450b412460400d81d81da643c241c0e50070341c501e00244201c440520940c8682820a504100100031048103e0b6140045586461030040c0152407983c8091400d414582020074481034800354845031084003501242140c440e15050a0554107901081145030b00301ca80000c0380c1c50b0340703500090b441040b9482a038644040000742c00c7c0c120308a130401c0d10001c4c81604107400400c001d42c1300314050000c10a004000086281e0781c5c80300700012680541c000000044001400e0042c0354100c27010421000342502c03a0403402c10088500c0400352801d0196115a0f0f035034400e442000c1e11a1121211040718030301c00c652004c0500d0070513541e6080112000d000203002ca081950928a01284110781d600c802c00050061381c80e5060301a002c1e4210070703082484940e4038055941d0034800108040040000c0341c40301a51615140148810307203005801070500f00c00300308155451a00e54805221400071f6a1030130102600698801d054441444025280e100b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 526528848 1250 526527598 526527619
    0x6160b0408120f0405030d0b0118030b01050f0a060801030b100f0803280c020108180304060507060b030105010b0304020d0f020312130f080705061b070f0302090f04081b010605 77
    0x150907001029694500c500c2c112443d92003000606074020101d8000f8402d40041c0f0150380050701d550004100d01005040c07c48080301181450700000003283c1c0192400c0407100e0040000c0d007050789224420680036114294540c5c140714000c0c001c07420612004084403d90400100716100c0c660a42d000b038040307003101e04c421603507801d880c50ba00c0d00024807131070070103202e00301c4a50000c1d0040c603000345c2c440c610b48440104687c00d8006542001c401000c01c0c49803a4103040d4040040c2c01400240090130781a04c0703198458105083c44801c0b40e185c0c90034940281c0c07400005008018117030060b00d900c82e034101d45580140055181843ca40b079010f26000303405110b801e14218100420402800810a03100281402250b458443d500420101d100d40c1d940c40c1c0000030700380402d003003010091403240c0405810703500c105481c51410745042c10b164420705010001d49810300440c500080b4880d00302d600c0c04251509070802d5212040144a030719074501c0d110000148458440400390050402482c1c01080080700 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 526530098 1250 526528848 526528853
    0x409080405100801140f0312040602070e01080609070512031902060712090b06090c041d010510020f1e07091a040516050a4d01020a020a0206160b04 65
    0x45800c5030145910810380404110009807080b03007a40d04944184a41240c010280f03024040b080fa1701510740f43e018010702e030192840522050082000703102c4c95000701113403807420458134082d00040c1c100b094035030411814098601800601c80c41510703400c980340400306240000c1c85185102d11143c000b480400a0340700c20740030760042a03052250300c4513103486450800c1340207100d04650205030014000707140100400c0150514003034081c0e1050285031990b20f032a07140c03000c07103180e070022a2480b007600e10848010300190410004002007a43c4034001400341250580300c040d1a0411056041350350a145040000d242e64208103420050081e181f003004483c4c19510b410b8007202114080301e00503810a00031911804195007090020036450340c4050500c5808101120b042390503800701c0c81403a0100300061211003072100000315204600290804030307003155407820030460001b103034450b50b03074418000c4682c83c503004104603400c540d0442f00c135641c03100c0d001321581d1201c3c1e40900143c03903015000c041004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 526531348 1250 526530098 526530113
    0x507090324060f06020a06020a0c020a0902071a130f0302120a0c060b030606132a03020903100501082e060f08011a1f020a02100e150906040611010b0409 67
    0x50701862640240a043c1d1074400c0e80300b03256203c2c810440180d208281a601048aa5001e881101c0051501d001c041e0126000110302c001c00b03801c860340d043c3d4005003003020010f1054184c0e0007005050054109840d0440b400c1c0d031034048559001d081d0b80308071101030701050300c203100008001590f002a65210900300d0320040103c0303d00381c1e0489105140648040b070903c2c000896901c10580240f20f4116072502c4a52040584001c04031040d88441601900442e6401c2602c1015a80207076070700161111a00320805140480d10064a884c461420700107011465022610351070002040040c0a160201000d4010410f9032096000411034503010b000b140c0311103081c800804544440c0c0c000e01400d86407190074050120404045940300443d605101c0307510060040d4000f004aa0340182d80b0030a84c0f607000700302000b0301c04c080c0c6c60001d00049010340b21843d000b00f00c808902e08501c100e60404840e800450b603a44954004d00080c015124060040304c1404d40140d441000080d00611608040307140c01034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 526532598 1250 526531348 526531403
    0x20f03100612030e0301020f1902100f020315150906070201050d1d0706170a0929010f170d0c050703050d020d0e01080405100b0a1a130b1c05070903 65
    0x3000034400206244161170b050003992150141d00d8449440c15120786c1200e0390b9140006141d4040d402500050100d901c024407442c000c01d0a50b0402580c0c03407800f91108403a42c0044141e09100f4442c03201c0b851080709411064405200003a50381555032080d42c00140c400d402120b1b0802e4490f81003001d58481d150382c030860003544411b110100e50b8060389500090b00c05146621811580c803d0f260001146000250402c00f807440c003440f50b00c0b0303800c0c6000c07004111590045001c0e240b18041030380100114603074017460300000c100c82c140601c01c01404140e280e0710b60700c1a1440e5000c2020404840303003400018404e040c000c40c3e200c01241d0030111030900103515210002d1040000c24054420100c65501400c451407289500074081c154203084051140000e00d0141c55490f0000301440e40404c1c10890282c122144c1d0300c0076142e6584a52a455203103400500603004507000f1075092000c050001400109029240700300500400c0383e503142d9000712450042ca41c006000021400740d1203940c42000100362 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 526533848 1250 526532598 526532603
    0xd0f020405072c01030905030a090611010908072604060309120801030209180f0706050903010f09080f0a050f0708030a060e011a030c160b09060a0603020d020f03100612 74
    0x18466995207480560310701d0364980c1e443c41102403081000121a5074016103070380341c8074141030001c0c0e0f00945444040c91500030380d0203500801c18407441441400d410071140ca101d800c04500034842c422459071449094080c0c908010000b1040e03503c900080350440001d403e0090b804400c0c0c40d2296078600c0300a000e00000304041c0c40140c0c003001410303d690f12406025040e207802802d03000e51521207408003040408070144000141c05030703c0da2908004010302c400b400901080e5100c0e0703140c5012000309801c54910041d113010103490000c980000803805000c2c3c0e4414108400003035140c0c034411009a60601c1841c2d10301003c07810014810040100e004060350183e43e108004100290304d4005045042e0002c0c001c2e0700380e1000c00c80d40b010010708104010750f400030085222030304004600007107450004c20814226454100c030390030041d01c04010007414be8400708004090143c2865038010411000c3c480c10301900a1428105c0510315840c1000440c0001c3c0c1c8104007005441c0c2d03104018212071015001c02c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 526535098 1250 526533848 526533851
    0x21e1b0a09111c09080406181a1b0c010c290c120907050618010207030203033106090e060609120609010c03090804060f110303040c0608070201020a0212030606090d0f0204 75
    0x4101500300103116071150145d200095920b8a801c008054504d0700b0400203078604801105008502100941900010921010215030300c03002d4840c400300380031803032a41a0600d03134441d1406c1c9015a038403c0c3d03007100d595007001c0003c2112080b0542009050140010b84594122240601c1183e6a10b41d008011750340d4000c80704100d40c0c69000010f40c4850442c41400e0b4481014043c0cd10840c0c0d10901d40c6050150500440d42860707034a41c04a401e64001c414084550004407200c01c1e01d645034800180b104001030800d9030300260030900080c00f9002a0b010b0400c10b04420000180651110f8003240d0b90745000816018048050505169881c107044581751055400c2c07890303007035045000e80207803c0c02d82c4d8809001c5003441d04008044502c0f00341d0707208490801840141c8440301010a000842c00343d40110343d078620340c0e8180b0130050149100a40414110fa20420a0720304441c2d010440c0b400c06030906c10b4403940c80d1900d10029146002e4907100c20b038800c82c00401d2004122142024521240c402d480 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 526536348 1250 526535098 526535137
    0x180f071a0909010b0904140a050403110d0801030b07111e102304060204030b0907090b0901030f1202030c0f0c03010c0e09070507030210090f0201021e1b0a0911 70
    0x11810400e01450748034a42241c80c01c40188138401100c00a00341c4a01c01400001e0503074840b0394041d041100a0300c6204140d660b400c00d0100341035114080c02d02c0f0940c8540106547ca480f50001080b5641c14407000d1300501c0d044c0d01040301c0b01c1c07107981b016040e401d19104490050398140d460030041d40f8040c411007034600c240a009214031300c25000340c42e416401c018902407442c03509166030100d01402070084650603401c00021000845070b43c1414014071540c4000e0404508001030030048600e60040710344202400001080020b2032802240c0b592a07000703900c014204031429050345180100810503100b03008441e8040c5014100080340c51071128100d00078403c00440c0181520001290100c46030818402c200280090b030168009201e094424411102d444070300c130b01c6070403c940781c0d444102c0701c00480d900c04d80250740c0c1c100500c105c64803500c0d824001298040b0903595960550009200f0350121120380302c0c0090b903551200500410b0400c1c800c1c020004807000e007440d1907000440f40804404c00c1c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 526537598 1250 526536348 526536389
    0x150103120908070f06110a0221060109110f0705070305030415020c0f10210f140609090c010e1903050c0a0f03030f050d09060e0609150906010b03180f07 67
    0x1e0900204ca070701c8441c102d042070508200310b0744400780820048052242c60281001a00ea03000f02d00a990348032075040c1001e071544c2e10490f052a070181d101100e5a4100614148803e94030300460340d81c922140243e950381d5907140352480c100700700750b400038145d40008900020026801c61031102c0302005035003685c60340000c040811041d41261025150051201d1014041c1c00e0300600d10482c4181d0003142c40ba2103000c1c2c0b2181d0509840060050700702e255210100142003440c24130060760880400c0b508801e03280341800c20340c1d5440e4040800369042051441c03844189072210240303007901541207281c0c207010a841e82003403599040c02d034480034040c1e0031140000581e07809964003c005c1d80c0d0705998460070f00c064030700e0071983e5422140712001c0c0682d4a01c40d02c03001407950300c20355048006000145c00b0600c0c3c4408480c0c100416460040c2c40e180401c0700f003240180700464941d0555105d10342064403601c0d00b82509000c0c0000148602c19445544251503140c000082d5003822180103c0c41070700700c0500320 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 526538848 1250 526537598 526537603
    0x602010b031915020a1704240207210504033005040303080c0a051c050703230a020c150717060103020a02060a0b060f13030606080105010b1803150103120908 69
    0x40c1d20141000e03802c3c2d080441d520f9030344e8005001d080361518040850002c420f84112003181d00342c400305c2e002040c6486054044801110b406140842e0300d00031800d01009456107a680b60200c01a2011101e011070071812107030040b41030340e0186401a446a05100d07168507106104020a0542540802c1c1021001d010318460000c54060701c0e450b5940c000d041d00d814200e0071040d08118541c50500009001807030708008608006050f40403540008141420042009400c0303a070180d40c3c1d0311006a035201059070b0328443c0020300c2e400280508005a6031090072007a9802d091000b003048501400d020306106000350711943c00b142900348031030300e0340c1e10743c4030440194100d01c9841d60101c0507800c40400035940080961041514503405041103182c28450455940c085e03204803015003028914020600501c8958441d003c058150f0500800641d414004c2e0509240200c6032001d002c40c03961002d010030b58405110700c410740341c412040b100c15561079140044500c61034244c1c040000d002d8080000d51032200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 526540098 1250 526538848 526538893
    0x21219150b030f12030402031e0604150203010510050904060b030c0307021018062c01020a0905120a08160c0303210501031e210807021b0609120c03070602010b03 71
    0x6801400c4c00c110105000c800c0e0b41005000307a07030500410b07880d048044821103000181000c44000740429180c2803403ca550094a10301d04001107105100510640e1100c202d0701c4192903003820103d840350350704000a0050600f50700041c500250100500c0403400c5d410000e54003980d502d800b907031840d104641c0010215410158042c21041d02d0b07240120108445501480c0d03000b0310b0604210000703030307403c6030400e41d0506003000c09000d0b0350025108010551000052010701003c8034103995001a05041a036074001620002c3c10524000545040210107002c510031300550240d0951811a038a04001c4e0580e04a01c07004441c07490080d4a812242401d0322481d030580340e118106440f41c05240000a074005040002200c86e45801d00007141c910a640e28224841c20300c076502e4000e0352420820090800c401d1030b580301179240504000c01e0166941c00103543d8046400d5800000b00f0008610807441c290b050600745405001d074000100b041503064110320104501501150340c0300700a6512407514008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 526541348 1250 526540098 526540123
    0xc090904110414070f030e0609060f1f0e040b070804051b06070f0f0c08120909150d1109100602100e0a14060406051e04021219150b03 59
    0x540001000100401000350807403101070400507101c460300c01ca800002100391915404114803c410700c4446606028410585040902405080c1020381c0d1142c0c1d50340014249040c0f001d02c000020707a00e44403c0d5001036010342e81c45484003100d035403400e20a41440d0150340a0700d183e02880c00141406000700c40c0302d1b0195038004010589a08051904800001d20300d03c1c6690100c4100314041c0460b004210700d01c49103010365001c41ca07a021500d800c0d954501164000156030304051084a03114a8040680360f00c000241d5510416659408051807001c00d803146041d4404c0321070117000241310000075030305403001c2c05035500449915000c5003103595008510802c8016444403440070049441500700400031003510f0300700c0700c05600d1a41c865180c0e44220f01c014100f0390040c01040140702e01c0d80030319504070202840021a20506003440844148010406401a0010000200d5041081000d421090b60b0754080e910403250360f141804441940c1200c803110030781085403440d11841c012620540409 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 526542598 1250 526541348 526541359
    0x40303060f0f1d040c17150732041a0a0311091005070c0305030705061e01030f0206091503090a020a090b060406140913090614040b010501200f03120c09 67
    0x1c1800100803d005002002150340d00000f041c0019502c5030248014094201c02000e49407440480c10204050b020007400c00041040d03007000b5811001d01c001a0f4040b0988440013000006880c596801d03003031040d41c0c0104105c40702e40d9500d2480d8000200030341104480b45e913003402203104180b1009054054000b8142c1d00c0700241c60500075085c000d1b002041c1c80d512402c0141d1000d50f0b2516001e0564000c41030980b1b141d04420308002d410f000540c840054a000618070340f000354119150301481e48407001000307000c0d0720300089020380c0c0d0b40c0f082d11101821135000e1442c3e07501d1514100703403a100c00c01070004a0185200c0c820108130422580a20091a400074015508080c5008801c58682121800140314000104181c1c0400d03140c89295682c50300c42090045650f003807510340340084401665210207c160820144000283c1590600f0b04482c02460415215070305100139034602100205d298903140f0800c006481c00c0c01010018000b0038200d00e9a0403105d540720b8031400d05138450680c00c1933015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 526543848 1250 526542598 526542629
    0x705242a0a020a121d0d020d0212011a180c2b02090a080102070c030305030702190530040603151e1802250f0506040303060f0f 56
    0x6035a4000140c10440c0150300340050401410000c00c00ca074004900c010060b001083da01050260003400b115061141d464589120101c04400f051146800880148202d85100401d41955074a1003040d41d0315800070704408264910682d41d070700034924100302c0762510340814641e200b00d01c0c11310746641c18410400b00c0894550388204104240307602c00314290356000b1085110320b920620080c2e4a2211009601c00103079510002e000308020681c0650000d4540da004000c0a03000a0410000d10304903a81400c00c0c644a4032114070581c184401080c0e101d4103440403580190501400240c0c00400410f007030400c0c006052000e91540c412440d6075000e0210220420040103054866401111004034034003442080d1605c031403041c000700001b00451b18814280314020302c50b004000103040300070200c0400451074103200d0b0b491181e00c55440718407449010004411242400b604030b09104c90180d000060316260300e000d15018000f08240e018400120300c18940115101214200c1d00007611074190a03143c00707 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 526545098 1250 526543848 526543861
    0x5030a0206120c12040602040915080307030e01111002071a0115080601020109080a02060402131e020309010b21160b12071205070201020d0e0d0905060a0e030a08070524 74
    0x480140820042d03140402100d03880500d5410b52500946c840e040242e5244e1030213420b50192110311590740314400e900c6000b0030600c0000030444401c3c4d94103091003821010b9480058400c2c031a081661221409513280d080020f452aa000340001880b50b045009441d07200340c0055260f01c401d000b00c044410115003200b401da070041d078200d64010014400810014004d03a5171001581210f091b01001d80d01030f0b0305120440c036200f1038003007500f00450010491681113a2440c54103210a480060001c1d5000000c103809200079084207640c501c0280945204c6c440313024880c41c81440e00e580306d0740a0f0040c0d4480d40402031fa203041440c02c440280381ca603404c1c80e010070b00310b1240400c080d00d40c0d01401320075040d07822101d00030b009441c0320b0556600016101d501c0f0540c65000e03034010300d00b001c41c0742d000020003515541d0000b003d081922016240540c492101407010b5a80705694461141c0c1803250014200070880024002c21405102d00c0682e14080360804101c0512100091030140ea00d0985002030390 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 526546348 1250 526545098 526545127
    0x31e0309060309010e072c070801050607150501290901090e0a0207021005091003021c09140124050402160206030703060509090307060b01050f0a030903030b041d0705030a0206 77
    0x4001c003d80000142c0068921810b62400c40030fa841b1482c4040b61800505090b8408002d0a41701d080031100b26290307240113000104100c105028079880ba80e0f01041c0c441c18000c4c12044240400c0c94070760204200d58483d1000e104550742d00e0003c00e501101c100c1100b0140081000384c50b020b0b00180c41d00c41c90107080c0003e1a094000080c24803180c4d690901c610390241e03881c0c1c10540821029030b101c503540d5071003032014002050501c0c0161000d25004101c0c2031100d49190400c8074240d100c036000010503140b03c0c9010035078880b541c10003071041d41c02c044400104084072a00240c0052007800c0a4508940d40c50500041e805445141ca0718450519020805410f10034015a8000c03954a0000ba00e60744038400107807a0141030328112096800330801c00204100c51044200f03803042400c0041c2007041600011140e4452009048200754980c1501400c142c0250050524010010000c2c004e6034840000e0040d0f009941007a1503440c030418030005124240030a8100189030041c128030b240c200800030140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 526547598 1250 526546348 526546351
    0x8010b1008190e1c020f07030f0f020103110406120f0c02060a0509160e0612060c07060f0204150e010305060103180215070b1821040315060b1305031e03090603 70
    0x280e902e07a200401448018001090140fa0b1a0780440a0b015801c50003850a0040381c0c2c501c46c141d118881c14008200b000d0600300c000340c1c0c00700081c1100519880120058002070740c1c0e40c0c02d1034102083c00304000d50014000b001906402c6800c0103140900254440ad4440e0034071100056004040814084a1540c02403076100507841c044a056100085c00b01400c001d60750301160941980ea010b00550789001c5404d4190000044020301d03d90038051025003091040a5009148660b2001c901c425020f081d019103009110740080c0203255901e41c1c4010f0124814800304138002482c100008900d580203204081d2141e041036616201d0070000e0b03092003104180da80c00d94400c40d009200080004403041d00040c030400d82001a01801c084a507013440c5001030785000c50911050fa07000f052921001c00c0300745c0c1c1c1140d802051401d01e4410781d8031040020072407908140981c510020300d101c18040003c048400b01e401c26400c0b20660307090606003100d550401010300c00f003508100076241781443c0620256 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 526548848 1250 526547598 526547641
    0x50705040b090d050303070314010f03031e09030501090c05130e120f070206071b060e06030f040f231510050906130218040c0816081e0405060108010b1008 68
    0x88504080d071511417440d041241c01200003a150300c2c0158601030312580c610300400e01000c645c40102e08641d005440402140780c242c00d09204204842c0b8114032800d00c04c0d0007140c00100070007084280b41004a80d0100721300615000f0782c0141104940420140300d600328044211000d44084120328565010550050004880c144024460400507a40c2c02006102003031007100781180c14010000c160310a000141c0c8214148041601101405d03110482160360001004d490f5224580e20341c03801a012703d01000d0007400e42030607641034200001140c0d50280c0b4400251045408001030400340c0c00e1400021180400884c4503000e0411040c14600005a0001d00c01043d490062149999550480c4c11007901207041d00020034030f0400300e080510540882d9880c41ca4454070b40c2c40c0c1445050111500b01205901304540100000e250510f03119800c03119062082d00c41a09007818104a50b44410a02903804107500c0d10511224900d054100402c024440f901e56880b2940d43c3c00d1240c0120707043d6030b001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 526550098 1250 526548848 526548859
    0x111002070f0f0f0509090d0509041d0c0a120c030209071b031701051e090703060b0f030103110d12031107080f071101111b03100e0d0e04050705040b09 66
    0x800d06201c00c22401010305001d4009050385460080404440c3d40d0541c0240e00940700c40302440200c1e50003140086141c081824256951002d540c080740040c406041e020100e130240380140c034138401c2c0101c2c08042c02c2d24103d502c480340c0c540741c41200194845121000f080d81c460804c080005052030703960036501c0140c60806c0b121401142c828140100c0c0e144a04500242c803c44503411a51000c00c0e8035805414280d07001c40400d15601c51204201010b80a041e02ca0502c1c1000100f9442c80381c0c004401928032003041c9600c84680d802203140035007082c00100c81c25020400f81003c5414100c1e031000140c2c0e00001c480e0301302e9890001c00d80042203c1d028280368048100202e9000c81c581600402c043e02102c00510b5440005050000903c138450075400e04103c1c2c1d84e105043c2c0c106000940c03046c002111046442c006408100007444c0003232100c00b1135081410084100b004020205450341c03071304860f44410100c03031005000c1004441086500d840800d20600c414400c0c142001c01401e0080c1010f40b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 526551348 1250 526550098 526550113
    0x2100f0b0907120c0503060a03030e151b010501050d0b0412090f0611010c111b010c0f05070e0a0b0a03030c1509080c07060306030506010b0306011b030f0f0c111002 72
    0x4140d4580d000c86426010460364029003d008400d0700c514010512503142c62425810034100007070b10f058852201504010101c6603003031255950300c4030b4080280d100640c186d07546051680e4440c07501500541a003a82d4a007100000300d90500301008000f01d45c0c03141c070b0222a9602e684d51030090508080803107042080d8800d0120785016100014005047c05840e100c00c10445020203600395060300a40c1c10811000c003500034a002000625020082c1200c0c5004818040d170600403a106c2d015400050319840007000b00c00240140802c5c1c08003a60140302c03100d880d41c0d0307071018070809840c02c6c99121500030303069000030400b09106064002001c0e2240b4401c00b505811401e03990140c6400e00e8081e0385492000071105102c11003080b10b00024003890074107000f02891511103a03150041481003102018000000807000d81c803a40300031440240c4806448141040c41c24001c1254483c40b4850f8081071144040349602401480f0410086038044001c0030006860410f00c01c040b852518508150302c210359 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 526552598 1250 526551348 526551371
    0x210f092205090615010e01140c030f0409020703030b030d0c06090206040308190905270702010e030a0509041422170a0206090712150209030a020a0b0a031a0102100f 72
    0x40d14081e00102d00100b14034100b413010f002449980c00c0381c0c1d070305128155181101c1070760401c030181d95110b1401020350b2100c800621107070440c4203480c01d1041e481d80000d004502d03c07078290b010b403004038020740c0c0401618031341c0800d0550f03032074100580c103001c0b404003840480000e1031504448501403026140e20708082e940c4d80c80c54140e4200c0c10b00b85d00c0002a005044034416801610304c13004100440d40701100c0c41d01026400d901d81c0d080360910601144900000c0e1090303000350800e04110041c00304480c1c1d90400800001ccc5150040681346100e68107040f81c400458403e00016402000a000c140b2220250403983d000c1c022200c0c8000c9035807010700925042d500d0303420b1024040c101d046030040e00c40c51400400d224180020754001d00c641d01803100f40d501c0800c4540f809603025a8408400680c0d034412500068603005a00000030740c4500d1180d808103000d0300110180c000501503450a200460040d0b18580c00c001001041a0050380660000c1c02c0710307009074101021554008000103545038414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 526553848 1250 526552598 526552601
    0x20c0a0c06050c0c030c0f040f1506120609091a070201290a1205030301062001020324040608030f0a0315030605010816060e01050304060e0f210f0922 66
    0x2680040085080880c3e40c519185007449051035600c011000750920f162200c000925a20072400e00030f009540e625403c07000c5003099809618591500b460010350346640c0c1d00014032140248840320462410000d0000b0348034518042c561800d45d21030340c1861518140540880039640c020030040456403910000f04240880810610a41c40800c0c2c04010025044040c85401c460b82c1d40003184003110a552800881e50110603a410b644282c600041c0e8441d03654100c00032041c2d842a0181194400401e05c05060201540240c0301d400d80b6080c540d08030030b0300301000110ba840d071003010f103142c004001e00c1c01900480c600420fa0f00c14942070000e030036803208505a0404c0081d0304210f0751150703280d0043c130040404011011209840c0b04040b030160b4184800185030040150710380e418424040040340412007175400240c02090360318201d030458018241750716503985d10b1901480186003c01441c074141c854001c00c448000c0c3d00100560715040ba014284054035a039812300c0305c600900d007450000c1c0194607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 526555098 1250 526553848 526553873
    0xf0507060804030503072d0f090e040206070f020a0b0a0504260709110d02072d0c0902070807050a0507030212030a090b03180601121a0f04200409050a0b01080309060706020c0a 77
    0x9036502d01140c0101d041009e400d4081c160811812048490100401030b41d4076001c0741c400d00d520105200302c4010a20100c0c41220b0340d43c101d0303142082c0200d204914564403802401c00c41c0c040340c020580305240b4140003d00321a4624051303c10350030404042c062501c458114820100d00c4041041c600070401c20548220380000004454200c4401d84041e0f90b404844584140c0e1002c1402901c5c08560550795550303001d80b94414100c3d0b294002c1845824403508005543c142600b25042e0b408008861900341c1d1a0318840c00102d00c14491411309807032103600001518170340c100c00d40b600491107040158420064200030551441000c41d5544124454801c0c0140784c003c0a0b2001501044152450712021159100840c104003603c0b0b0401c05c01003c01d4040c0c01a001030304604804a408040c52100200c5003040c00c6660300241440e22b10300c1000700c0050f250b0b806602071360b05148103903240c9100c161280719003000c140c0d0015041c42000c0c00f085840d4002c0c604000004101e401594150756101100b902 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 526556348 1250 526555098 526555187
    0xc0d0507080c0319060f110c030306011d0a090b1201140f011203051903090501050709080c09011d0a020c010c050a0e04050708010603020d11070f050706080403050307 73
    0x41000704811001005901002c1c08110058107520300c0c007964400d64843c07426005040c1ca41ca56801d03646003559a404103e01090a01100360355000500040da030303e6100360798980c001220503465207a400020440f6208450004111480d0300345483c0d200c0b40540045030141d0b601c241c3e0701e000064000402d22542d00751845801100a1601d030905016208480c141d00019001502d0421000002d600000700c41140102058000100000e40c100301d008000d8020000c0c81c1d5882c04e41403100090704900f00b1400c030798410049440ca0075000741842000502031080707004801c2905548021401080e40c201c3e44008a060010304140d1164030b0103003520415080840820400191202c099522080e0f44921200a036030510403030604040003803106d0814420181015070100b410018170f03110b508045d40040140b80c2494860449040103460b00c111614200e946200d14400011560f002d5000e240c40740d90152200c900750317510030b401a21804d03c04007039249101c44000b0034041c1d000c82262030400307850 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 526557598 1250 526556348 526556353
    0xf020906030f0f13050703123b0a0f0306050603030f030a0506130c0f030b010c0b09012c0c01121b0c12020102040b0f0d1404111f080a09050c0d05 64
    0x5000b1103c0d801d43c02c010b05980500000211810042170001801d01c0859610042044066441e80011103124074285280703d01c4031014501c036014601503000d00c401c5600800c480090319004181001078000381489444904110f00108001240155102d103910001c042c2c00d9a10385021050041002c4d130048611032072040d6038005002c010301f0480114424040301e458200326805501d40050f00d040541c2d40c040c410540c68201140c400d912a0740d00d250210b901c001039002c2424031403061400380004400350a0380042c03c42c000404d8070100541003e06030007140151641c1c0740040011903080d5a0346070180800f0341ca40004841491820041c4c184404e001d64481001c408a49814a060400d040c941d500f16030041c40203104101054084542c900c0ea00c3c02c071190b540196000c09000f60105c52a02c010344082082013005000ca820490000c00c001215681344c0c0000100980000c4045400e07000c0000324900c002032103014203540070a00c00c50080c821030b180f4102e030000240000b03038924400c89068 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 526558848 1250 526557598 526557601
    0x41206090302011103070e10140406030b03010e01110406050a0e060f12070504051e04140106020f07050a1a09030c15070b0f04030503240307060c02121f0f020906030f 73
    0x1d82c0c20703c190101e40074444000c41c51030411000040203880005c034510b104112100b00c42e5401070140704d4108a044e402441c1d02e88940d40c1d00006402000f1021040d402542816441c0012800600c80e55000501d03004580341000d00342a000c4900d5001001c1610900604c50713106012540e50002908a1206001010f0381c0c5080d110308806541d040030707100106008040c402030205540308000c2c0c1d413503000c104590184400c1d04e000020041c10f005100109200c0403200003140303d6501142103452841503070100c581007940e80c000d11102d407460b0f21526103100001c8400160200200c1c0c02000e18800040c11210316036210000940ca01040392803a10002600003210010000c5404c07031954000344120082041e4035140e1030192051000911a41418007040c01a83c00c2c11b0080e1004401d140d8081c003212982c0380c58002c0549124402c0909a03c6000c000b21035079050000090510342e13080e030080e68105202520003e40c0d000d40035485044169036001e1200e240c0340e464501c0510301c03440f0142e0444109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 526560098 1250 526558848 526558853
    0x20301060f031401090f18050a0209100803030601050304150e06190b0d3f08090f0c10020c031002032d0c07140303040507030b060402091c020604120609 67
    0x44901c09803850705050900394103d515144a0340c1060440d4900d05003c10249008403ca40040c1400401c2c5100d40e8001e000316014000c00103024505280700341c403424203680714407000907090a018030552169500410009203a54415005180c11601c181d180800c0c015880c0007a100340e035520310305c0d1900e5a00080c00c010044460000b5203030400f946044c00c000010b40c0c1e1020403041540c030503001c0d004043c480200e081c44016103440400040c080d80d460007201480e00580143c00e81d0304004030000401c41000b0802e070100210b140005031424a0040041d0348192040c000c038000424151019802004a20b042684003480781006c4101c0c031520054780c9260005002c0008200204071042000022070986400b500c4450200c0d0080d10000e0003a03180c10445c03070a0300d82ca8840790700d546103600001c010300040000008a050540f8416100b06009a4500307007407004a02a000005134814005882400602050086402c0b01ca00103021a80340a8a0700b980f00c800c0d020103042200d08a41e40d0121005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 526561348 1250 526560098 526560107
    0xb01031113031b0f080c040f06050306190204090c090305150408070305030c0405040c02300a030e010e0a12030e010506010c120e030f15062e09031502030106 69
    0x4180301501030581c2090084035100d0120348503800002d0820b8554451a10b001d0b800030007200080903510719105096803110b14580c3c4030180328401c03601072800c003200112004114020641070391009401040643e403070021645c602e01d8005813503100d5642c2000007041040540c0200c00e1841c10540b5034444207403840c5851032030010740102c22800d803105d1906010000d0320303110441d00e14903010310708180c40b07450303100e0342910600c10742e800759502c5031030414680351071a0003081c0304d18a45070860701c1c1401500c02001c01c40210b2160340c920700f41b01e4020800717a84020b00a50001e45803603d490b00005060002e00c1c0000e19100b00300009480d48228413517003240c0f440d4180108075214a244000f40200d040c0740c800a807030303140d0030b4000901c0d100b800080f5003003440c42041e031022104c0c001000c45003010400b49103182c441f8024220035024040e5100080c1c05410005c1c540004410b0304440a8114008250100200600c4403c0b030003c0009503180000440c0e8100c400b4100380510500c0140c0c0c039454031070050b2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 526562598 1250 526561348 526561361
    0x71505090a05061617072a06051303020c01030c020f0a1406070e010e01031e050c09031501080d0521040302151f0612230103020901050102031201060f0c150b0103 71
    0x4a200804d80380d95480c25602040d04545403120104502494480c65025038031000c115914650726034003584d8440c0700903e8486400840d80c0110703400c0000d600c0385140d041d2103040380200070700507034084811810254840d61010007800d01910503100c0015040030303080d0410aa042054402e0300401c0743c01c65114509001d11600101d0904083c0e84074018100041c001c0310724060113505040c0e6481f00c0c11043c00d200d900100303015a511504000c44d10744500b002c03940790050345c2c0250080c03084004080d5807004415081d07051700d410030700400b003490180b4401c0b9202d81c0400303544010380010302ca82c510f40042025407240140e120b42c01420684100c0c0c640f42000302c0b0000e0400440b1180582500c01e00b03004601842c09480c81d07480c00c025281102c0032100003521680703601c1d034100d01c0d070810000001d03003109807000c0c180d038401c840344a01640ea8000490390fa0103001c05a000010300b503001006071300c4c012221036a02c848641416918806152500300380761182184000034a0f407070b40d000c0d481303640e031500c981c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 526563848 1250 526562598 526562611
    0x1d0112050a20070b0f0c04030b0f04060b0409030e040207170703050d0b0103380604030606152a02030a1a040c050603011203030b030102250510090215071505090a0506 73
    0xb6410802e0340e031103041035000080c14404900c907603100814103152a26003120084c1d03402c50141c3c03544d4201a400450041c0046505492071450300740e04001c82d00d002d00900c0049605a502c1005500f005d008000080d400f035032048410040d0003618003002c104050140c50541d0080d2141074554000014940554604050703550405240845c400340d44003012103ea410650625107014003020140d89526404140c500460390001c0003107400000c02209420000c1550a18008903401e0803250348144c80401001d20740c450f1107900e02e980c03685c8400c20308581d90119400202240c461031150748031a08105160388100d002c20f41c41008100a104112a817034004040c113035050340c030f9985041d141c0c04203082424801410962038400034615642d0940684001801040300c0c200740c012400004101e0f180e140c10300316094088c0361090b601c001440d01c25002000d0b001380645000b807000610008155000725000c454000304a00d00c00444403541c450113105805101c0107201c00500c1d820260b14215005110 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 526565098 1250 526563848 526563911
    0xd060618080d051b0a0209010f06030e010e032b020a090e07020724030603081317070b070b1f03050723060901030e1c020327011d0112050a 61
    0x160b400e103030780c0031003290140c03506004082e403040c040307000c09400c0402002d00a98450034220020840562104c2c42c8000c40720151402c0142da005046241e098800302c460500c0903400c01d000698900c1000302e0551968081c680103040d40c1501c079105070303080703030880c01030040010b090160074004140c690701a2600140280000c01c1c3d0b540c5402c0e42c1105002c003c12a1b808008060103e064031540030703800c08009036500030386098032040c1d01d40420280b50902e11406007640b408200c00310032080003044903010b884981010f98034020a42d140c2000d000e40141a80d51054106000c035944000101e0f100b002461141c0081c0c00c0240c58059002100c28418180c00707104030f1700411804044e92010100c4031140004e00300843c1c26800d0074852404c003010307018040c10280c00403803009611036010005010005070450300c48a0f41601c11220320741d155401045501140c5100720700ca0fa68012900c10051800c414500540100440141d1805598042d100c0860007a216500b4584480582d0019042c02258031107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 526566348 1250 526565098 526565113
    0x6130c0503010917160204050405240c0412080412060606021002090a050d080405060703030b031b061c020c1209090c070f0605070224070936020d06061808 68
    0x111300ca03d056030b145084451140000d00b02d05285600e41140042c250018410000ca25003420480d880ba6003201c481040304400d02c09069002c03001c1550f080c02502e00800090605c0d05000d02c94001d40715501d001d6030fa62100303020000d090221301c0a20510359104500104241d8580074001c4e1500048500194905005001c504c40c00e840316400131003190030842d1502c54040860619000030710440e0486500201c00040941c20b046d00354000d204084015004c036518500314038100c0010752001503a8a40c000801c03c4861307505d07031688150050324503c0b609e0052500d010304c9a01803403d503841d200105240341c080303143c8000303281c445404ca90028a0282481c40d00700c3e01c0c0c0e200200c061040c0b900a28039981d40f070100d41ca40d80300300140900d00301c7e6100c0a8100809601d04113070441d40c03ca5041d070001d40070250102d02092150280c6980982c0c01c040084800d42075038104504050320b05502116907801c0c00b110001c0380c201c0c041c031070003030110342c5a001000520342402c0000744c0030781d000f210440e4070102 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 526567598 1250 526566348 526566353
    0x70210150b1c09050a0317090102090904020609120d090609050405161b0804030b0f1503030d0b03030c061e0c09010906051c2c15042306130c05030109 66
    0x4640c404825800040c02030b41a8050302c0c001011814400f800394030410b0703c0101015001940c0701c0240c0049100560a80d07101d81e040f40c2070707208a507540c582283c5144049401070070b00501420307142900806284920541507421460403048030040400100d8440d4100300c1680c0203c05c65025240580b424441ca10707001012035401e03030052004000300500210a079220002c00000220b54681c800c000903a104d580c2d0511251300d50b0161840095081280c012039146441059100d10003c0064040e5003001e0740005107100030a030ba610181c0e0940070400508000d4036050000c54414600c82c41d43c0060200c106402c0840500014145040005c081005600d40e89c0c11480c1c2004440b09440d01c1030752040b0142d4400100d4034071030402180d03181070024044180b030044100c80d0703010b05d004c2d40309411910b900340b46980c2c824405003203800c4200d082011502064111103958500c603401c40d0141c40d801c420251981c6090300c22900c80340c171714058241d00c07002c100000011300c0c0200411030090200c401e064 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 526568848 1250 526567598 526567619
    0x1a0913030f02070801090f15022a0708011401090b06031b09040603021002060a150308040e06120a050109031e050306010f0e0d0501020d0b0409050d08061807021015 72
    0x11400641071040702610140320300d10801c5402e004e004820003c2c405210320346480d1404440400040318980304c80c030803c0710380001d24400c2c0c0c1d04550b01d000050034a00d518280300b441071130780004418a540140f900203d11000c0901862001c2d8180c002c2c6698030b581b422101e402100e040c0b5120784e00c5502c0070414810005954000000d802020000c0c4980d100c0c0008001b80c001d0115030300c004d4014504000f012a21034022805174441c0031440c00a00a4102041c3d505245074003d00008041990510091104c1f4150141c00c50b80310401806003024141d401c0b0cc0c80e442c00508c2d603411121340e03440d02180c40800d54050004079001c0c0c850074038000030040340d0401511901008150034100b2a0810821011078803c001991000300c01500720f1440c0c41d02810403074043d40c0210006003070b0508226195400d400c0c60720603160740c5900540076102c90351050390201c442c0900545503c0c2d0020400035580d04015049116a01a13140343d0000e03e521a0000c89410070380310706200140031020481c0007005280c040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 526570098 1250 526568848 526568881
    0xb06030402130e1507081522020c010f0e070305010b010e090a0903021c03062301020303190b0a0f050306060d021c0203071503090201170402010c0f150507031a09 71
    0x619a000c2566a4543c01c0646004020a03058100034201c0c400d2220207078001c51018042e1071540801e521005041007802011011405410013019440c00030258442e4103038054506041180004100035408082840969610811600c965045210200204642449120802c038400e08022015548090005601741c100174402640d0a0b141c41c140f5081620a22003100040c40b40d480c040010302581c607005008051078010482d074410366690011102e00981440c11102070168000c41c0356954242e552898145034001c04144c203a00c440c0c201c0b400b43d5418103007401074901030b40021201403414080601d068070141406002d03001c4400601e01503120f203081c036a4001c0d0b90b84903aa03200403051002c40d2620b2090740c0040b500001500130301c80d0740390b4183c0004a0301e0b8002d031b0301e03144605c0300500d183c640c800042d90001d02003481c0c00003060000f140c0e0f92840007034a0188940e280900c0481c9031001c1520000c641c18000070360345440501c00140065a41c03142d660b819602e8444600c2c25038100c0018000c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 526571348 1250 526570098 526570129
    0x131706071d04050a02070f2f061b070f0311010314090703060b06090a030516080607050904111207021005011202030a0807022d010f111902011218060b06030402 70
    0x200d0328005000309134540c04880169601c210388404c60011030502c4010403100080d2007000e4045030313080c1004a0182e042001c40068000c106c0c42c035110740c0845140d00c4014420281845009140000850302c40700344d04000190300581741c04003441426400103003140c00c0306510402c1e25444c101071000500c00000e400b4240e07540010b000a01c1c41010300000d855002d03144000da40a50612004410014003090714a8081c1c05c07031900100c00c0e41c032012010703140c00f0111005000030307a003442446014035041c0c02a44c00108c1c2030090504c0c0c00f6039007403280b11070749048038640091ba201c82c1001c3d050b012548075150041030020b24100c07100005600094507440c8030107000d0020303503021a0313107070655a8441c44483d4254008520303640e205858415a2010b81e03000150502060803404010039040c003643c0000041c800040c09043e44060801651900f00103041090307040007004104181c8000003031186080301c00c82c0c1802e14140c80c01da45425000d035800310050900074801401404010f171030301c1c9140910b104 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 526572598 1250 526571348 526571351
    0xc02010e0102030f070f0614060612061507211412190504050604140105011512061a180f030a020108130b070509010e010201091e0305131706071d04 65
    0x2039400c0040345140540a81c02c50f540780001210402c110140c07a102005900c601010f00030300c58255011708103034204031107003600014104040719010301204c01407580107200403c550003025440d0746000058000c41811542c521064070154510000304103411b10090840c41c0100001050316104030443c00361911030502104100c000c20001c144007100c1d0700d20074980480c1046140390904100c0d135204020368059a041d821203c8002810406010b800d060b9080842d0050120000160444070080c026a151107466a1000045014800b1213402401d41d40850005916812182c0c15101c4a1480780d00c107620039890704480c00c049403000700300c46100c0c68090900d00042c0d5110074500c480c50401c440010505020b44c02080070164001c005442e1600e401ea07581c1024000e01c0005a08071100c402c00a00640090603484180c0c03000da251055400303104c0c1c40c0c09402d04044500000e5044a0398020b4980c8074208500304a2151081001c0e42d40605140381115002d8580c1a21b048503650300c9600b5130149 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 526573848 1250 526572598 526572617
    0xe06030a0309210516030b1e0121020d11011205090c01030903020a051002040e011d0a02031f0f080123150609091005040c0f020c1201060803030a0e070e01060c0201 72
    0x50400c0300e014a9103134104c029540c0b010079602c40c0129094443c002107620505000104170421282084840138226001400c1c00b940d0074000c00a902d0088419001c0808c40402038180c0161911101c3d4040103206429401002008100150a041a541004c0c1d074141c83c050400102031400119070755603610078207000890303881d14202213040c0340c03144a028155114541c0003440780c0c4915802802101c04030240b00307081e42d803140f48039205007034520030b95060341c46103102051030020789038001d5800c6421218070001142d12841180b01c1e07280c05512026800c08500420002c8200070302030411010301820210541c0c002d01d04101048440113440d0f101c00d070350890888030f101d44a2000722024100c1c01404a1a0f500e018003202c402ca012030700800b8042c6040c2091000180e02070701c070305409c4080640280070500400400d0080d01000706080980540d00c1d00d1000070a403005000a6010b640030220110304a01700d28140791500080368040c444150102c00100f2885a01881032003034160309107001c03610f9 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 526575098 1250 526573848 526573889
    0x5040c0c140c100806150a0c060b040e0a1103150702070e07121d0f0f030d090602070611070606052202130f06050a0e0d020d14120d0203010e06030a0309 67
    0x900e82100290354100503503000f05440c650b0031400c00b0348680720803184c1403101c00591607012101c0c0501001c040106100326201e50014a407a00129002040a080040e100340c404070f460b407408441c507a081d2280e40c9030181032221420705204c9010120550b0382e011809051a03003000755100454402c0700d000200321070209403254400e800d095601800f00704240710081c0c4505c00c24007a8400568800c1d0b0512459000c0110a03002081420008036841c010b581040440411a8040c246150049070515401c2010b0000510f030741c4900c0301001d603114841d40c1c44e404a883c29504544050b04401d220b1004040441d010b00700000e0710340c1e001c000e03248005d40c070b602e88080c800101c2d0100b90000b442c840590400402c40c035038844040c12030046580e4803d41807022810078050080f00c06007002c1c0d0480400e07101c1101050041a0800b0b000200c40125101e0614648800501e500b08101400020390004010041d540d03d1203011a000101140074011002c025a40680401a036225050000400071406040d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 526576348 1250 526575098 526575103
    0xa15080a0e0105040309061704350c0a0218061005070201030e151f08030403020d150903092606040b0901111c0c09150e13020d0903020705040c0c14 65
    0x400d031107103000a0055007014034001e4500e800b24001e40c030008004e10701081400b0b04280c0c1183c0034541010b9074440700103081480162940582c03042c00c1c078000b5000e8003450f01c2c0c801c010091802c02e09960140100b02550302c10016110386441ca404194407148003800310f9541c0d00b0003403042c281d0407401c2c55641d07914a4401a000383c510b910355a010b502a01c100c0003505500e40070414822600d010114100038502000e2038001e802500842805074000e020900050800d94618000b0328010300d001c131084401015400309881600308200c00080c681c49080010070542608191a5201400a1520030800b0b0f65280c1e03481e907000704007030419082c032004155514004c7d4000c65170110b14195043d80c558586405401050303010340c034140744170b1912601042c460700c00c40380c030800e645024110520480c1c0070a011103458800c00400b9030301c080d540300140d00d0030080384001c1c000011900350200d4039041c141001390400a00c6d41c04a4015030030704505082c00b55202c42d444d0000d030781c04400c100b03002800d608041d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 526577598 1250 526576348 526576361
    0x20a050c011b050114161d1002010204080d030204031704120209060406090f0207050c010e0d06020a0e0603070c03120c0512040609080307120b03030f0703031d24060a15080a 76
    0x2400c652070944440c20310303224600c005220700d1003c1120044040b011001f00c64100349210154585580c84c4040b2001e46400c110003808a0011303c0058240354542c0b55190802854500d2403010a60014040040005a41e01406004000c62032170742050318150511100d440b40d418024801ea0b0540d00280381903455520070005803c18203002c100c0c0b00700b4204c5000007548030510039a0329214200346440d0030740c840c004070301c0410f0015201100028596076990080d4029010020900559601c1c183d01038981e8000b039442881c169440c1521103056040190811075140840203100e418840c50020444e0000112004100b40d8190300700c2c2a612810b200c00201070300600149401000070500c00b0903503115000b410390350710b100c004021141944082664a00c0b5480c0b032051030a20600209000c0b80c040d0b800340d484204804a01c408108030007459500f0007940206401301c20410305034500c2004010300a155110405613201400541042c0019a407200c0320030092080010050008403095010b0f0406d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 526578848 1250 526577598 526577603
    0x10c0e060d0e030327010c0c17121504050a050903090f0103140f01170a110607051c020f07120c0e0402180c031b090a0905090c0603040819020a050c011b 67
    0x70313522810030b00d0707414184544040c1c1d101c94240000c07018800d5464103100b4014121501c0d00e03081c245451503030354a10040c005c05950b5170035400511030543e4072418884468803074480d49490307200b40c1088404100444101402110485160104010a0f100d000040303490904003203d03042109054800120094410300158101d801454803d0200b12840303440500d040e501d12003030034080c540c20000074550312260118080c06102c5441c100c0452828620000c0551071300650940e10f4454080c02c000a42d83c5000c52860010382c42288200100f420600020707000d002640101180b841c581d80300d518402c400d6025068481040c90082000c5541710f69010952224044880b0710f00e20300700c3c01840d043d0b04101c0c3c2001d0712420403414030348030b098903404a43c5c22540c0201206100c5080c290700c4001410300405205551003407442080d4280d031982c000c0d42c4214412400150b403106944202c41506005100e12010340d4407240e8880009803012031803440d4040c0c280b801610843d811840155441c4260401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 526580098 1250 526578848 526578853
    0x405060f06130618060501050307020304051e1f081014060d020c0a0822030b04060506031e07050a06050a090e060a090f0b090f100614070614070e03010c0e060d0e 71
    0x4010508042805025a82407010805d1550f1080159880d101c01c994440068008010510151a0514140f052911202031260000c900000801c0031580040038550351020b8080256a1455201404650003010380c1d044941d1030703143c4003030b1007501402000c3c0b0900c203600109111207040015410703030f64007020840131140c81d8900c03810041050b51001c00c3d840b10400403103401283c50165007080c0380c110b903486900100580d40d181c407204000c0001407e410780c5802044483c5100a21520f1200b802107504005003405529000800c010418140e001c001404001d100d504245500403e0701000c032590308001824aa482500047c842429504204070041c0340091046181002e60f00404116070180c0f0407076425210414401c0c0c03889402c03100d19110304003d00c002c0c0300981c407610030040041c0003845122f043c01029a189003e8a042040014603290b04000f00126140c0c0040c002503d03640c02d5008000c450240c5c140201856180560340d0301440c80020410411134250340210a1024014107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 526581348 1250 526580098 526580111
    0xc0a0b010b070308070503130f06090215090a0e010e060d030c21030e010e07060c050c130506031506060a03050c070501060305100b01020309090112032a12080405060f0613 75
    0x210711809400500081c0d00141c11540040e1710307980104102da01990450003070100d014a517940b04204504d410108603840ea8903040b25500507161427902c01e005010000910741c840d13200905002480c2c0840d0310086003d4034407001000200a500b440541014054a40074003800322400c2c01d41d4034891000300108500800603001c1183c602c842d040003080d40745a0740c00e00548d4014040a42030303483d0755050340a05d8005080030403000d4011000402e070079208030140d0b2007000341000051a0b080c140d5011400c055120b2082140c1c0b86010f2142c082c140b0748100c480743c11400c1c442d0216000703009a60728503042c1682c4602144a681112040c0c070a801c0d484070090146031b0712072800645802c0c0d42402d81850901b03000046d040d56002000b650b03201a000f4003100c0a07a03107041307001c03000c0701c1c1c003e00164188030b04001c03907007015110030010407001030002500c91065450303443c241e080f8039042d407000005c0000040900002035404250b007504100d086c136118459840d10400550620341c11040300b1f500d40e2a011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 526582598 1250 526581348 526581359
    0x4030b010e18010b360a0c080610080a09021c1103190b160c021203030106080a020c0d0c05010b0301020703021e01050403121a04090b0402150f0f0c0a0b01 68
    0x1120a441030000070450348800002c032650310f007a14010714409034080041507040610301c505210b0600d803085801c0c1000381040b058900300165040507142009110f88542030007210036080300309545c00231810b48203903400032801c1200410420015242010454843c0e110b5070642d640d50700420142d01c0c3e0a1a00744c8c020400e840e091413085100003c26010780148820b8120915040b946200360a4000651080c00d6441d0702c95049104035032803800e028014000001e40150725030948080072080f0000003559a5410040050300e4040028542c240c0e560040200c0c1610510100300219040d4a50400c2d104e100814a003c80c050a5550350a80c1c1640c40803885406140d4000707001580515095540c142c0160009503050076030304115000b8001c1654001c2c440d0600d00168000030120001d072040c60044091407000800340e940200c02641c9010011091000350b203171158485c0c660041803c0003902e04007030722001c090349024101c1c50340103841c40810b072010214014486007850301c0d0301c426015a6980c60345d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 526583848 1250 526582598 526582619
    0x203150f061f02030a2006010612050a02130302060703031d070e18060f181b010e1014160503040b071509110d24020315090f061504030b01 61
    0x1140c240e8450003100004000b0070030241492400c81e0070960142d4179000180c441981c04081022202d800c260700340800080800050058034040c220391f50300c0c01f001070300c040f20f920150f03280034040d240d0291041040c0c194161544404400b100e5041e20b107242c03900d4031424194018100c0309800d2200000221b10b9582818001c152101031741d042c950f0b44582c0b511342c07440012540f0000f001c468495031010010400300040408030550204464032040c410280f083c461600345030181140c280c019031451000200c541e0441240d1710907500c02e4482d050340c049403a03401415207900c00340e030312201200000d4840300b031400b0304002d83c0d4664203c0201d9507030f295545c0084945506c000d130140c812060303819905c000021203000b91021030750080420008200308204005024810450894001e03030300000c920400303d19231b051429910110340c001030302d81c03414030038407824019200c40f11031243e0494400c102d0418420003000c0d411000540c0d0102000001c803260304007611550f00041c040f1081340b800013690f000710 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 526585098 1250 526583848 526583851
    0x50d050a06090c02121209120c0d030612030c1101020c0d110901060c050d050f120a0c020c030a080d1107051c030b2b030203090a060c060c0504050108010605070203150f 74
    0x42400402c42d00054010403a161402e03180039144a400800070b07140390352240886c40d80c02c10540401e07070360b8608981203442442d5000020100044c0c000320007515440741c02d40b06103401401805400c2c07200c400d06a0b00148207000c01c076802054100070922500190f4030802107404401c0020304a8566603807a07042041501200d290311384d206400100c000b00d4224400c88668a1013035000000f001408070459043c0e03801d8024188100d5003503c148458060f80c041c484900d4015540c030140041d400194040090507c000d00c0b510500a912059242d800102480229000003001160000e541004d81715442c0e650f104a0b00081d0040c4150710b1403000544100710030f2113458059880c2000841f035484280041180408104014041140c410380b40c0113640c1c0e0103012506100344103032850f110304100003480071407107074010b940001c06904003d41004554841c3d003c0c10012401c100d424645054002451000c05015110402130007003151804c640b01048005441c030b507011042c03111032502581c4203001840 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 526586348 1250 526585098 526585109
    0x80a0f020c0a030b040b07090605300112260702041d010e0304140406030b01062d12050a0b0d030c03050d062d0303021914060103060b030f06010f090507050d050a06 72
    0x40001080c1001d02540088c400c60341c40d0749400781018079800524400d400040041c40e10169100540d00e010566040101e000e01602100980f5040340d81c00d2a240e51580e0b82030074000d841ca4846d2250198102d941a28000b13681100e020410340c001c9596807004500c00000c14441c0e60030412510810100400a1f1099500000580c400404800e0801c8155110752001404514400c00140000ba100b5a5041e078040c44070414020300004000c0d55100c2680c80880100014521a20303011081074940982078001100c000180700d000008400901c1c40c0c0b2008030010140580c804036101050b009100383c0380d01101c08201001201d5480c014200c100703840300d444d10715010101805140383c0e1b00400010701074039055401800c1c48034801003d03c040c0c20b0640001d642052400c622803103c01000c00c91036000e140308000c0480c110058405052600315280801001501322200500403451071041c0c40b421200e94610116075521454010b907140d100341031801d21032a0814041154400c82d0f074012004503003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 526587598 1250 526586348 526586363
    0xc05030d0f050304060b03011d070501030b0f0a0608061203030f0f0703051b09130603060209150315010e04180506010807080d0c020420041701050a09080a0f020c0a030b04 75
    0x96469800300c0310501c80104103030200350140042004207005621040300003801a00014040d01d0469075074000070003500c60300724103500483e002d00895038503006100320440c0540e40141005c0c0e0400c00500c00b000180180c20070820701d480018a80d581d2141c00011030b844c900c003500d5490400c40401115414229900258410f5200205d0042c40c441c1c0302e55840b40000d080300c271801d4040868001c050b40d01481d20301c1d42c000c0b00710708007000c800d25601c02d40d40114810721005a98444400900481614814190000380c0b400e00800a6840080c0b9000e503804109107804803035030f00704400003401010b0946400c0143c404400380c010400000003820386c1070f00e60444c101c454940d5100c1003195640307103080e44040000c0e10551503030f0060030560031840708162905c5002040000c0080356903541d0f00030b9400400c03819044141d54011203000e206142d0003c00c08a001c1c800b1800705e4072240540e20a13a10368104000c0000142c42c0f1661007030002c05d87c1c18070001c002ca191a903683c101030120754815182078800c04c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 526588848 1250 526587598 526587613
    0x3030f010e070203181306140312070305040b030a110a0c05060f13020118030b090d090609030f02060903160b0d0f060806060108041401090c0303030f0624020f0303040c0503 76
    0x32802140700e540b1841242e0300071858410340100f1281a0f094590718190851011050880c112203a809000042c005400e0080104400701d41003610303062a194044100d1201040300d038000c01c0c0e00800712015282c914401035500c1c0c07030b0340c2d040c000104000040181c48520100300000700c1940506c41c62101030050303040703036405c2c1c94000c000c1e981e21038140c0f2440c8071a2103000307036000194090b0764005010940c00340d40d040d03540d0f982d444a4400907001c4903004401c2d04070024002d1400d0b0001c2d240b5024050710314000d82e005095a56a401101051070081c0c07045002060211507950104088007800c003070034001042290359030440c10035940100d0b442c8400c1c10705014810f40f00c4031040c4608812510321200502c603030f4a4040056030f804801400c140d40c4c1c0c01009220701d8501c41d09000709901640300f110f54a4140b861803c1c000c0880c0d084044090781a4102203081008006001c80f0700501c540d01c8050811030000008160b11741009803407005050301010080200340a00c0c4201242112826410398182 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 526590098 1250 526588848 526588859
    0x112022b060f020a23040611030c060a05040203100c050412050c150d110f072a0e0105010801080c030a020411090901171612060c090e181b030318010306030f0503030f01 74
    0x924017099480015010280003c01016105100514222500b1000e503450418031090407824828102d4145c4d1803a61203405110071818108a20030350f40d90070210402c4454011034004103244103900c0f4994501400074003c10a00c001030088000e03010004098030340c000402c07060b100c3c45030440000300000529240d10403012400070412210034002c2e07954000d282c941c0c50b40d22165404e80c40381190340d00c680d8203402c00b68010800c900c020064858610341103120340c90003000510280050308040c1d5290403001070090303151400195810802d43c121000301d05011090342c00310700c0307000b031707034129544070b50118000240c1c0000b20001c41088001d0301d0540c1d65400b00c1d20b5400e041c2c8001c52107800d051085001140001c01c82e903501c508c400400524010790705544e180c216500f0300b2402e4850300541a072905103a0b41c850300401c90380c440300e240c02d45100e24058008000903141c1c040c0514640500140c10b1071003415a100b98046400b03150301060784441030b000350501507500e405c100c69003119480c03114000700c0e4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 526591348 1250 526590098 526590137
    0x309050a090b030604060203070c0b0106110607030b0d0b06030f0d030905070504020307140f0d0203041a010501020c0a06052d0d05011d010909060902130902090112022b060f020a 78
    0x1007060000e4010304c115180c41d61060002c2d8401041e80041001c01c06040700000c840b8240c0e00d0003803265a0301d45200f241c00b10b0a1a0410388050002020f0602c0d0140540700c0e615040070502020f40c0000703514005aa442000c01d0921404601000c154040d50700d4803400580c0592110001c140903d080320721054403002403200703c1c13000781c420001091805403030070750043c4a00010039003e401c1c00c002a0501c0007101e580c4061b60015182250590718001c50385e001c0541000c44030b4014074003480106040d211420105022106a01800c0300f0441c0000e090700684040c07501d002c0c102502d54101c0d0303018400241c444462500901c410410303050609000255854041380300030041d20302000101c1c07480e41381006c3e485c000c0c49118003c032000368031500c18501581e9035041d0030020b0010a41e0101c0c00601d14030420800c05416013191160001039030340f0f0300c01741c2c035440c1c0c0141260003001860070310340c07040740900108403000d8030004000342c6c00c203000940d01354034030b402420f0300d146a83c0710034050061740702c3c1151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 526592598 1250 526591348 526591361
    0x20d060f0e04050705100c0203010911090f0c040b071103250605030903090d05100c09090f1107020111120c030d060e190f091a1e040503040e040c120309050a09 70
    0x1043e55000c4203051009181480c3c10107556001c80c00c1c001d014000640c007207401e540504a0a4034808503411045490342410005c4a80c8442c1001210f003017450041c45403181c500450243c29007003040030801500304207449103903102c80c003401000c40302e9007400000d4000c6090f808002004c05108020b0000401e54020001d8034015a1202c000e18144049030040c880300b120038100070380d140c4c41991741c0c960145400d8070508209042d40e5881c0600c1a0034a25400d090b40e014800000145144c031095000f01e800220a40d800f01d90b0910308940c90200814415142c01128528510000cc0010b0b07030400b1f03a4400002448448040745003800326541e030394401e8440000883d0b190710a0414199040d60303011140c0c0c4140021120710300700003850800c3d43c6890f5010180328648503081c0d80700400340416001d108000c5203070000140303100b25491420390b80c0c580e2a4083e03486030401440d03010010034104a1315292400291140710340d900400112410001c02085062007020b00552210b407010074124158060340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 526593848 1250 526592598 526592603
    0xf080f0303100e06060f0a0c2d0204181502030a050604050c0306150f0f070203070f0323010609020c06040c290f090a0605030f06040219050d090501020d060f0e04 71
    0x301c01843d1118101007030000030301c1d450b84002d0400204090344003040203070100544d40d07a00c2405460082ca003400555080c0c1100811140a50f0002d01d07040c00d408100025282e03050364081900802d00c42d005403c100610001441e018004003c0c501b038840c0d1350301452255440404c14010703030b1240c400f40300032584180ca45884d000750070000510542403180c20010410314003240d07540b40c1851421126500d4018120724640806d0002d0350b070040d841c1c100001c2c005016407215100c01203246a41d0b500203080c119965130a800909249858514802c0d484880105150744c0c082d95030b1400c01c032985440c0c100c200c50884828400d418080307000d4090454050f5181cac18000400d001c2010003003541c50035001040503046800003000a840247c4580345004000e10450700d8164603410007049016207004000d10a41c055841444104021120070100f0000306079941070043d43c852140c0c0b0504040c1205000107000e66000142d80110490180d112340c08036000c1c940e9000c0196100c0720020410a13092740c01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 526595098 1250 526593848 526593871
    0x4230c2503080711070312020a0c0b040b03061509040507050705010e060f0a020d0b0a0807030312050408180301020d05190605043b0a050c0103050c090901090b0402070803010f080f0303 81
    0x80032103010391071314004100d81d401198100343c0d50f9654040380b00a0541008016000901d0807001c20010100b104081c0100c5140b0b42d040a00b4190105110300001b05203c0c03180e1003417440b650008040c43d04441c95120040d1061025142218000d8119840ba12044500e580381c00380720309a6000c00700d9138134020450f0250172801ca032205584580a90480140070307907400d5503481002455942c10400d40024205280500001d52840c2000b800409070b000e58019504c0c00c0c84104000110a03d007106c840320f0100c1040d0301d8000328400401d00a004d480e21503142280351106008060103925070034015080d09040a02406031540240300075150580c1105144035031000d410800c1c0e2480c440c6401c254007425440e445004d106000003440d08a6404040c0c0d420b4110a1103102c09580c1405090782c002040541c0501c0c204a22010450202052040c0c00c070741e80e40c0b1000e106143d99070390101c4806c5078201407160b0304c03540c50740c80c0150b00e09004c4c4900368191251000c20f844490340402501d02c2103480c0c600 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 526596348 1250 526595098 526595101
    0x3031014010503062103120115081605040308032203021006060e01140a0c1b14010503040302150702010e070803041d010503120702010c06090b1f080c04230c250308 72
    0x17000301c1080c001a0b1140c10501090203080c150788009080c442c02018903090344400103821840c00392034128098000c000c000740301c00840d4451030b040403c640850b541b041d030196803980d0314205841c00404064008106030768100114080c160700195600c04020184000c0280c00d41e41d110a40f02184000341e654085040040c1003800c040c0001c010702110700181c14040c0100c90035944100d0911810304070900149401d030000c1c0705804510154010a50003820080d10798201500d02a6844111155200d4200350100006640038401e4100031240352100080b50030040d11440c1041d22030708503001c0e400300080a0b9150240301c0d1860340b505412aa0080e028001200030381000942540c807810042c0d045c04020ba11440c0044d0942c8a8450a20300800c050713480d6080c0a1405000440c81105100102851040c188140603001c110326200c900f00f200e00103540510004c401402020300c40140d145a0340800400410b9044000241440394941c4c0100751605d018034100d80b42c1d40c002e507a003d400284e1000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 526597598 1250 526596348 526596379
    0xd02070f03060911180f0a0504022d030f010c1701030f03050304030e090c0315031b040e0c130501050306090d050301030809130e1e0715050f0c0303101401050306 71
    0x280060619130003881d401e020755080380c1c0401c03075001065815504410340f26080220440e06464004e8021924000074012030500f600060300e6a04000e0b081800d184440d0803100c00d042c0720301c1a030f180d0150044d0a071881014040d03600d5000b460b541c2882c00101e448100c122504079451010305041e42d41c40341c9465910405a1002c50705504014811400c0c4400e0075100c0a0960b907805000344034a92800c0142e0390391415141076040c01090401035030080d072007145107070140035058560301c08d030110580d0001030700c6480420b04d915040c510080240c01031500301c00c00c8110b420319084181078880903000c40d1190b0300e80100090f5a10130703806000d400560184014130008a03402e00034500035000415140000420885090860301c12181800e950390081c20787c60b9009200010303e402e00041c9401410303000d450401c0f01c00f26800e110202c0b04c204807000500120960101055500450440c821280c41e0701d40f500c012600c0b150140500402c000301003890718112762003041100d10804014280d500201d0107403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 526598848 1250 526597598 526597601
    0x506120109020616080c030c1b010503070c0b1005040f02040911030f070f0e130f0501061818020c1e070e0411010e031c0306030c050f010f0c050721050d02070f0306 72
    0x4010441c0c3c5c030a0104043d4585007001c001402d809201c00700070f44088c02a445000c4102c2c43d10344d001905000090041240c0d0b0ba81000010903040c0d08800d0108455807a00c2440412441d942c0107151703ca840e04010f00030180140c0c1c0a00180c03035030034a04204002c100c00164403240012160045d003042100300017020075100b2980203107a80030b0b50030b01c030601034950130008442491b04420040e449995502403240c014141c02584c1c010855420817200d0754441c0c2c0c60300852280300c0d0040d8500a030103070710180841c0c0b0250f411911400c0000064840c00d0021050031034030318442e800a400d075441b4455021440c0c20003000d10754042c5500034410030308d0300d010000554401c02c40344880356050081b64403400c0c0c400b00110002c18098259500006e00314118600342c1802c40142d00203500902628085040e030703903048201c01300e40140a0400301140b8200346007051508005400c000d406c00e50092040c0a41421040708658031442801070303a8880b140c001041344d81d90aa03106600c1c100c0e200d00d000300040b4005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 526600098 1250 526598848 526598887
    0xa26060f061f1704050f070501090b040302040b0a0b1c050106031109010c03020a05030f0a11030702011b1118060f010215010501140c0105010e0105011e0206042a03050105061201090206 81
    0x9600b0850030b00e0310400c051041003c8111000d855170f410032103502c2d00c0c1d0300e81401041c3c0a40801d007050040f05003042030710440c5010340d000c02802150303682e0b200c0c0d02998072000c03204001c0822034092650f0b010384058081c80c0200310a41070301d4a0f81018008540d1500a010309600f01e40100c00050801b0b014000454000050340c0c001e50650140c00d0008011401c01e200a0080f00a02c000c0240c1d80e501d6044000d01c000400350b501031319500306000ca1030050ba072140c00d44e007040c40400070591001d54a424803441a00c189030010754044a0007000d1800884408841882644c00301c2d0b41d000301c20192401640ca071241011240d0440d4541001405550300a4140300528040804460309010380e6066903401c5403020b03003140c600000c2c2040104069a40080b003080070002c3c1098403844155004e002a60f580e0380540010540d07002c02c1c1e122140000c08080f140d9000c424011b020003100e9613420403a0007040150380c0316010750301030310503500b80c0d150500800045980c05071590349885201407108410185 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 526601348 1250 526600098 526600159
    0x3060609040207140a051b0306040215090324040204051e04060f090f110a0f140913020d1104050603010903140d06030b01152a030e0a26060f06 63
    0x10303100360380d200c20300c00c0040d4401c0c944184018007010620304030040d2102c5002c80401d08c42e40c0010104001610b840c42c2c1a861410001c40c080e03103c0c901c3c0800241000320150510541c000d82494800d022241e80d400749028500940c1c04010702e444031200c0c103900e90b11141c94000e1410348000498000b4466501501d01c414110b2400141d0b22015514103228614900c019035041c0354060b0030508500c1e140c24410020302d201d9010140c91840c0042c0a1603030440040712a108070030510001c0c00c7c0c000f41001c84101561f005100703009102042c078001c1324014058040c0f5000b580ba12000400ba81014411070051a8041d10b604902041039910744c4010b902c0344042a4080742c035800c000001803c8122a58003030300040200031110100c1210040400300740c210942c8038640045601c0c5044045400445520398052911415a80e0640041a074290a96209044030141c40e60035200d00440044c841ca120300d01602a921142c4070f0603c00d5062078010746406500042c5041200101d01e64444581300400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 526602598 1250 526601348 526601363
    0x4060306090b181504090c050909060f0103030f050d05010803130503010c02030d11070b0c0712090e010e0709080d0309020f03010204051c0f0b15010e010807020309040917070305070b0c03060609040207 88
    0x4410702c0102d030549131446c4044400010000c010b014600d02030b06d0b00b07a031000c40c0c00300030482c92400c1480c059503040b040c031001d0f040c00908104075001d24494011141d0b40c450400060240d075079290401907481d44942c0ca02c1200c207a40e5200480d203450180502404040e05a004504100080c00060f00505000038142c200328010491900055100c0f00900d00c1100c0e400300050b00d9000714100a04560705000244040001d102c2c0b0520410708104503507810b443e0705a00c00394547d03440010070385615651380c10500680c4a0440e00300007445d81600074080c1c040c400d851710030b090040d9070b051600341d0246004455100d220202905102801c00b036882d200c03180114545150700c00952207009280c00d00391030034281c80c80710b81c4000156580214602c044000c0a00e0071059a00e420003009403203000da01d480d584640c0d16894542e051110b40d501c07444804d02c24544050795001d83c0d150213441c950045408480c580036070030008070000803900650b44a80b8001c0d203214a01540001040000e6012260485861 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 526603848 1250 526602598 526602631
    0x1303060e210903010f0f05040302060f060303070605040219140a1a0d0b06040306060e07170402091501020a0b0f06040e07060801030f080705030a120e0d022505060a020304060306090b18 81
    0x145d4580034809881d050f41c03034001818105800d000b414540003e1001440d0706011051280b5a10008211040725400410000b02c548443c800071b14030a1a408018500005044002c900c0d0b4a009a00f0180300e0b06c111100000d0940d01e000d0007214100081524a52003014003207035040c46842c0d000207081250080c40a40340a0f165074542c0e0407031306030740c00030441c610a0804020301c0301e03081112110842c404621000d000d1900e030380014803000c0010000c642c0c16109091202c1c2690081214582565201e41c80280c1c0d450324122144085008580d5a4451803c1881e065a00e0a0219459068551650391004a0303803c5888881a07000004021903241c40200520404a0f1040c005800000c40a94480100064000300142947c500d40600c4917642c100f40802d0918507000130b400300d0095a8110200c11016104401205264242c0d0241c0e80107840016041c91983e808001082550001e44041007000d0b1260050011500c0411149400c14081a864a4103040500c8855405504c240c113a0021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 526605098 1250 526603848 526603871
    0x602011823071818050d0e01030b1512180a080307120608010905011103070c030e0301060302060a0809061f06030504381b040b0706111303060e21090301 67
    0x14000154003e405240754109402d80030310b5a4010709545056a4007419140da85a4a80b02c0e00c0c0d582a10403074003070042c1000d806000b64029001202c900c2c2c002801900841c012541960303442e4071840c841c05034503d501d000200e01a08400e4007914054500c0018005041503688103c2140c0c4080e00c001c0c2409882403669640d84040d0207032070040d0070000c00210b00780c16145091404d40f0f28034440c6203e010801d004002070183d100c0c004a0005400d460405e04080c222004640103203450b41010f500710303000003070040034583c021504038000d1114a00f01ca0080d6100903110190100c000c150082c24080e4140800800d44250801d9800a010310040303003071240d20100348580905540700e81c056281d0858503260820008580c816440450301d16a5008500365180c003c00d54883c901604241030b0300400c51030284105640410f90241c01c092a40c0d503154040010450680220b201c00c841c12400c03c40441e00d01d11000c6800002c10381020b2500c10311842e0f07640007240c150401890940c05650b1400411207 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 526606348 1250 526605098 526605103
    0x160e060d03030b030a0c03050c04060602250801060801051803270f0a06021608010b030c150408030f070605070201092003150a060f080303160807090b0304060f060602011823 76
    0x14461042d52100207140c5145460780c24a0f809c800128410f5240881c2080390540201c0c0f1000400340e09414030740100d400d040140c546009036000310790551720f032032030204804005611107400f9910360111310002c2c0720101102a40d901c21403102181207003081f1000050066100c3c0d8055000f440244041501c00d10324000c908403e56540c808001a442a44004011590070010700d0140c070000000740101035168022039600c2181c641c070940502c651285d1040603110311010b44001d4280c03a42a03a43e07801400381c0310942034008807000d071181d500c2c10001c102e03450300520a1408495200250001c0e41c0312903160130101803600e044194150281c80340f5514402c501600040c0310740e000e001c001480c1d9090000c07007222990740390041c5c000c507801082401240d2402c2458010803200d5480d100e441d640d01d0120442d0720700240da02c80010085c0210910007080143c1d041f1040a6501113003c10030b081d5500f104038247daa007aa80f00c80ca11000071180710104500c00d0141c4014141c05a2402c1d440201040d09072 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 526607598 1250 526606348 526606363
    0xf02030421020703050a020603131203022203030e0910120305180906150f0f040b0a12050c16211701050315190f060603060503160e060d03030b03 64
    0x50340c0c481d200410480000c1200011040301e5002e200030302c2d00350300b141c0e60300e0703a1100c0210001e031060402200050031440013021121201380d003e4000072510710725001c050b001e900030400d550b2244402e41c407c18404500c5032052001c807074040d9035160a034905902400301e8042c01800c460701080766140040f4038003180d103032003902c028070941d40c41c0e41c3e0360341030205486408904882148103601102c14000c4ca6524611740000e000da000c0b5003276583c0c2005403d1048540728020034950190f0300810005151148400a0b0010540d1500d50081036402134040c44100c44003200d01d0035030254240314090b0031640404070311030b40c0c0340b0550080c4503a0961112a20207180d400d4003800000395234a000c68000450b5108150061500782c0c014060317100c4044038000c00890090960801e0001044c0700d40c0403000681018854566042040004603200c81d4010f000e8412070194a010f4418460040c0100e40e554070b00d081151490b0300402c2c4e16441d18030030001c1d00024401c080d8101a101c0040c06000d540600c0340302e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 526608848 1250 526607598 526607603
    0xf07020a210c0e131403120408030405010507031e0221180f0a17070f12030510050f060d09031824031521060509010e01050c04150507060f020304 64
    0x1000140a00d242c00942404941c002082d10b030111018090000e8203c0420300d841940a03010042c1d40748140d41051443c020400035200b03002520741170200340540400158091130142000b88642c0d652000243c1c01d07a061841035018944a020b00c5000451140c0e005c0e00c540c810a04010204400448103148103060903034100803030b24501c3d100e90040000030400d8a10007001e400c007604217000281c55a0001801c910017104000320000b40b080304200304800d0a035074180c4d00a080c1080e00c00c070034400400801049681c0d01904400c14401b1174030303182801d007641c2c801500030309092070002041498405001190000c5040c4040f22500c3c505107200101080f016154001400404100c00c482c103140c0b0105405001040c54034043d10400c0c3d00c13071010310b000c094824405080095181c1c1c8059088106413070740d4081d00f403d01e084140604200e040d0070204d516000e260082c406901c8444021403d4401d038462145181101d56429100307502038030242010310b00840000407140f00c083c140320f00340e03032044504 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 526610098 1250 526608848 526608899
    0x16050c011a01030b0a140d0f060e0c0f03010b0603040f0c0807031104060e01030206071113020c060f0705090303040303030e01060510020c19120204050402120d0f120507050f07020a 79
    0x780e001d55915104040000300100d510007100e91811070b4600f19015090300b580e029101384e00745a41403245000c0b0800c00c080e4004000c21405202c0c4002a03140c80c10040414828814138284030158941409241207800303008000750300c0d540341c5540c1c0c841e0742c3d4001c0b0b100312119520b450f000941d100043c0881d90055000f40303400381c0180d02c070404000450ba1030342c01580c8620b00410041c800341e203a880584882c591300204003082456188005075440090a001180386400000ca000000c9001f1601e580102d80b420079801c0320b610741d94401d80c3c00d8010044030f84d800d03601c203200c1000420310a0f04a04145c071468030000442513100c0011070f04060003c80840096030090300c4400b0b4a0400c8010711460b070740710200341030002d418090594007402c21500041d1003180c855001c1803d6559540d90308120000000031608224542d000c0035160301003582c140004608111081c0120b081e45000711446001c00340c0d1460b01e05203c2096124454122030010790700030b461406c0c04034102d034500f0360701540110300200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 526611348 1250 526610098 526610141
    0x23a0203070b0f030708330319080d0c0306180f060b0d09021201020c0a1b0f060801030506090a03020d11190b220201050702090c1c02030603070801022818090507080a09020916050c01 80
    0x1114001e95000ccc07881c00301014a8403008001009844942480741e100300d8801144c482c046142030070103401c49801034010000d001410840c000c1a41d8043c0110354825500742c5003500c0240300c07490807406540c0c4800c403140c0150116000091030f008000d192070694001c5d080030152200700e1041d07100f01c66003224011500c2c030801030003406010032241d81c1c800600340092401d03295603900203480301d45080c0c40a061205405443c4031180051003200b02241c55550f018107011801c0c104024200f00c10b4560441240c0c008951104040c8203440091250360180c598074600130300741e401c1c02914140200410a169810300003481041e0420178100d540902001001d86c590034041b04160030420f156005408076072040200f400c2c08501150802100748a1441210580341551030545003c0c6c007003030903c50310008041c0003250021403035004600076507440ea200051541c400488100310784020202a60112000e000074500301550124000301c1109882e01e0742c1410444249a400e40b0007070000460503c02204 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 526612598 1250 526611348 526611367
    0x70c0203100e01150e09100e0c270601080c0702060a05040302060706050406060b070c0306150f0602030310060e1c020111010c080103023a0203070b0f03070833031908 73
    0x5504c0c00351000c0d410206840c1001c810300c40d96000d0590783c400e41c0c0f580b181150000e01c481800051a007800c090700032a4001c0e010003007000d04a40c0d0306049e0348451407410100d1041e5200b00886442002c1030700e4050314000707040d000c00640340c02810050040000800c00400140c030703440d0140801d14411100800e241c24a8500b80b8107032091508007030398410040c40000b0200d502d841004048941250000407401c401c4000b0040700c0c801c1c1d411840381150740400c000307105507002006520440030100d042c0c0a042d00c51504030b50030400d2600380c0d03034001d0541226580d901c91101d4aaa02d8a1050500c4580081100d844a00703544a8095044c00b0640c2080100190b0a241c402401c4515000510440509480c0040020411000c5061044400e05420442107440810803400541100450303a0389030400c00c001e068159100715401e90003c5c1e003000200b00784501003103000c00309441d6644451345000c100102c2110075410313126010740c1442241c8202c905052024201c1d41d0040c000c03c10281e6a01406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 526613848 1250 526612598 526612631
    0x130f0914010506030c091c0203030307020d020d030501060e010807020a0209270105251704080a11070509011208070602040b03091c080f07031407050409060815070c0203100e01 77
    0x160300c00c0f03001e1001082001540190072044a40c0488126046031104c0164040340c000f6003091400290103110000910070020f40025020503041c06603401c40706030b446404000c9041c0c8400703100b5a0046922002d0308540c545c0208602c5500c100c0c244100d2f58050034a4001841c40c000650388100e10f58600403624680c0030b01074010ac401c15940764000e01590403e9190b548500544401e01502d00c04180103800e403403481030700080c14801d407401040f0034504003828080f541c0d41c0146144004030349050b143e80d5403440c0c0401c0c04421650000c0180780a6803038401c41200490300048201c071958000c000540014885201920240600000301601c0c1e00e4000d88080c0740c20000c10359103d003032104500b5a0303410742d840344480d079112404208401a40c2c40c1c00d0b800781c02074002c03061250b0081c0e92030310400c00015030102c0500121901c91509202c1150f4032a11b0b0383d19000380b91501e000c41c800710000946d602c2d0158019600941c030240440d400703600210003410803204100041e04442e51604050f00702e44565 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 526615098 1250 526613848 526613851
    0x30060501030f11180310090c090515030a0312020f040803030610050f07061e020712180f0902090a080307060b150a0509010e1c0803161b08130f0914 65
    0x500c0000c0000c1500b83d06840c000e80641c0c00e40303407610200420000141e8409001111510581d110144403e200d20710b420a9541c0c01e074018410402d1130440001c4248503812400340c10020080c001d460790b6070040d1070803140002c02e2000220b859808000c00e80510101e400103200070708001c0055616401d1040c104028180303150082c0c0304200c2d05120b2602e00559681c12108500c1d0300450005405d02c00c100c4101303684004c09200020244003242d04414811002050050141d07181d40f01b9800034844441e98500f0042c41c00340307074204040c80b2400e015440300c0c0d034000c10f40b40314001d03c0701d1000f5540300f000626640c4950740c110703184e5440e02e200c1da600b0b080401454030f02d09044500c0d281403404080b0b0090081c01201025410000004440074140e210b0340300007104c495854543c000340e56100e06005e85c0075402503802c8444c80f619096245000c40c49903461648440203161013142039803054482e54240e8100468440d800080707454001500c60740c0310342c414000e00030b64201240e031a9441c101341c20072550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 526616348 1250 526615098 526615121
    0x5090111070206040e06010c0c0b070506070f020712110a150306150f0f09090f09110d1e08190e010e010c05060a020705030904021b0f0714013006050103 67
    0x428065400107a840d0003e813010b56200c225001600d036540f00040396007141d10b0002421010050301c0102d20415003000805d42e40303016404440c01500c4045085602683c0050f4040043e084200c040c00461100c000d89401c59010304005a1208070383c1000a085000d42c4e8131844140e00209109139055805000f018003e000008070080a009920b0002d40b00300c031f2024034101000484113804600d28010150301014010911f410440b030030350b010f02c02c001401940419036100c031070386040a00c10b103041c2d2034803050103074085102c0900c11407000c410034488602d80002c903601c807014040817612030010300c18000084000d5a500130000d41450014044410030880503040102c1402008081400024100d800c440d00060060b9603042a0800504501459070880d0348240000307060000200300c450741d06c1e903990002c07081c0c87c1c40c80c0d4002000b0341d0f41d26642c401c4820b28010350a00b20010343c046d1030250a580246841c20f01c140401001805001d041030301d0305c00c0b91566540046c0404d5a040c490000001c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 526617598 1250 526616348 526616381
    0x91203040609140d05340302033a08060f040e06010b0d1d03042c0c091314040308070203040b030103020f010201020906030c040305011407120e0718050901 68
    0x50609200070080c5810340105800e42000c580703d109503845050310382c40402d810606840510254034000a0913003100c8003103505003440480401804144c000d624000c0f20390003001007984101040d0181720481044800f16003405001d92070204440c02a035200c401100c965480203094070b0100204219103804296241c012440c060702c95803421000101141501e0011041c0e07502d03500c04201b410060b02003408542d004da00b0407045c82d03400b00d5001000c1c109643c18680b07121701e21412521286c160810f410301c80c880c4c401030742c0e0100c0c3d0304100140003402c001d0000740610400300c1002c8003500944040304140e502e000b400f0400c2009065000c15001d4204c40c844c4003130b510b09441d0014000e17180c0410300005c1d00c588031182c18016168000d604440a1100c0508110303203900d04041401c0c102e400070b2005851303a50030030b0f8145800b4055480d01900c12034890710303009030164481c0c440f90024402c0100e108101e210300b20f0081600c511801080002a00204002ca1a0b14040d0019401c1d02c140128420303154 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 526618705 1107 526617598 526617607
    0xf0109080306090c13150c0f0302060f070306060e060c0102122701091a10170c1306030305031311060d0212070e01091205100e03091203 60
    0x444003120040c015985800134540c451040e41810140c4150504040c4504409951711489840d0f4a241c5660340540c0380da250a0320200c5c40c40700340d000d07034001c000f001a481940359440b54889810710781408154540302c2d01800f02504031210310f11920380880e842038080b2095041d181841c411440104032810305030074a901e8652100340300f00c0c090040c1181e100c1c9041c0f050041303c4040b80d00c01918a8144103680303041c000d6a1000d0300e01c0402607607e10300001e11075040110600c0e80440c420241c5603c10445003080710041c40240030007000c074107003174080000c2504001500d03884641c851451420107010700d04044880d48460302d0690012001c615800784803000d0740542000115080ca00c0c0ca652100e8000382c50189000c88000e000031600030050003050341f0b280507548018880c400300d41c2c41c15101081c00d020b40e6280030b680b85072541701040b25552440c2864140c440710031014044c51a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 526438848 526618705 := by
  have h0 := BRFrame.cov_init 526438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 526438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 526438848 ≤ n) (h2 : n < 526618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
