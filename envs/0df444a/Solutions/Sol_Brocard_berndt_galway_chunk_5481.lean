-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5481
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:59:58.463945+00:00
-- url     : https://prove2.me/submissions/454f2024-d556-47ae-ac08-e3868d4b6405

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 985611510 ≤ n < 985791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 985612760 1250 985611510 985611577
    0x2214092427010e0121080903030307121d03030115031b03090b0f041e031b0c15050c070b03130b010807090b100e0111010204030f050313082808 63
    0x744000e04440c00003181602c64620f0141c1200c0941051101d100c042c0c803134124480c0303040703032046405e010140032085180d03400380040e500c5104c4940d1100f40c0311410113400400d6648404080c000d0001111712a11000804402c49054510141007809550030440d02180145040c4440c6010341f15010440c0521540c5900080b1066001e24840d040640340c091446010300d10546000704a19041001d48580e02040252010194005d0428152a6000340700301e4460b0050b8860071103400c03001c00c100780914181e0921013414203540c0c0c9410b50506041d804200d566841e00d016441c8004c1000c0000303803d1003101c58a0044007540300404251070b513900c91189035200e042e4020304900c907003059045085420180054006103500e41e03100030625101000550b46044007a940080035502080040049040f00d04601516840b031402182e03a1700204000100040070303500b241006801404a001d201a414500401c46050711901d1403c118181d00d848462032045280c0d406034031006102c0c00e80c8103126000781 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 985614010 1250 985612760 985612819
    0x2040506121f0b011d010c020402071e0b1303050403110303040305070e15060a0f0806120f03090415030308430906020304050105070b13060222140924 66
    0x80c04880c0424005444442d01c80442c07203444020148652117545c402c1c6880000a40040d0005107495400d40303d95140a5100d00d50107601484583c036001040100381d03615504c00040c0c3e109100308a41c50b94020114031407031102070102c0c0400d500d615800e550500071a40150352103022681e126540e1009000e089500700d075040314490750300f0796242c56400c040b0202c510f9201d99580310315000c2c00c100f1040d14140340c00303003d0940105010352101004c0b0710810401069415074002591604001e504100a8680f2600c081004060382c803404c100003500011147e0b044050014408440c20281c0f49180030002018080d00c480d4041120024460305d0a4461603c40649940d0301e0300c2082e111003003660303280706622509000410400100f00031898048250303800041003046202000400c0d1114420307a0060240c1000c0c00550030b850540d66000900004010082c400400900080305030004a40400040081080900b0207505103034408000000c8800300000074211001084683e540086500c01c980c036 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 985615260 1250 985614010 985614073
    0x9072909091e0603070e071209120c3c03030e0d0e0112090b01120305040e09010b130e10091b1806170706050a050c010216060b010c0f0204050612 64
    0x403c0190a0104d00328054851a029030a0542c0312840c0890301e11a512103008019662240c4190006100d00c11050004100c2d0303550311044411410060403280c86d40052804901800051807810980710302d140c1c0c0e185140c41015280b100039410140d020b041c03110300012041c002d540228607560780140400038481000e0b6180c8070448a41d54180742199903409002d455513101800400450309107008031860356110345842c3e0300703280e540c0790325444d0340209854410300c0713944034080200e040c106124001c0e1070044083c8140400c9520407800303501d42c0c4000b62071380449030f11004c0350b80610002c8140504800c07090452103100e5951507181202e0055900b003180300720b40c2800320015080112040f01d0804c624008060703d1030034078000b000e0700c50354403449110050200c180000038540a003032010380b8072424a05000b4004d980e091400f2404c1321800039800e418440c04900e11004514154140902c450b416140082d0b00c0e1603143c0041daa000c0402030501c05482282c4103c6070110f14045251198052100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 985616510 1250 985615260 985615321
    0x110a0b0f041d2a04050402040803042c0f0402010c12030606021e1917030c0d0c090602060a050411030a0302100b0103200a140406170907290909 63
    0x42c1500300d03034094440c0074501580010302c1c0e01d114044465006041100c4480c9031901e0b0307a03440810140d800651048105420118040011850b694440360040f00c0c0780c40d03032071a40d0403800c00c41100c156000c2d080500f903002c03420000c0c0c110b9001c0c81840112a8000100640c0b0760b178080b80040c0540301e5400303400c0040c003d0039840441d1203901a2042c0c64900e103078003e82400c5509024035204551419000da030b40d84078040c03500d0515100e100040d401041400c0c03002e5500d0041c8102001500d101d4600d0008200066000700701c8298085210780e001026510089100c2c3c5603030a215a1241c46000b242d54507001d41002d40e0100b40c0c0000d2a907124400165051010a19036030043d400c4036041003170004c400c5608100b814215001703c0040462840c281084010380c0056280b1503842d82090304040080341110b03218150244986564580c40501d14004140315824005c4c50742181030f01c2501812500007006800306121081820345401c02000341c80344100d8500614688960b41c102e0403801044800340 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 985617760 1250 985616510 985616549
    0xc060f0b060d0e121c0e0c09040308010f05012307050c06031003031227030221030a051602120a09031506180e1906090b0708070306140a03110a0b0f04 66
    0x2500b0f49044130440540b0249546604170040b01410302414021440d00500d4641020340d6035010b1403034000c41c00396a90360050f60516415000511045e000b4070706110300d900c0726915075442407040080300d0318404500c1d610790500d40b40291a190240050030f50044011007000791014548107501c08590081c0d031030000c0c22030340c0054881283d0004400c0a050103100e4140c1210624410b02a10460700c2031044a1500d145c0301041141d880c110100075400440000500980700e440d80510350b00264080906440c803501e600001e0764a159420301200d40520110304551010301401c070080003035401608050954444008000050269004100b695140c2040280c0340000a1180000d2600c8040c000c114501d401d0003032410982a07076a0440700746403a40704420016041c600c5041c010310868036842c1d164200342c40080c081c0c2e03a140d00710b1080d10204108010503592441c44200840750800c2c00150803032585404104519079581203001d220344001842c40e0a0014400180112000007d500c403d09000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 985619010 1250 985617760 985617793
    0x3061507050a06020307090b0c010b010e031c0e012f010c02150f0a0902040f0b010e0d05030405120c0604031a060604052206120507030605090c010c060f0b060d0e 71
    0x9444000c1c005502c2001240001840c80e070003180c02150343c3c180600c003943d0301d07020581c8950000030346d1105651203004660351035801408075011a5004c901902c411481c0c0b004684214142003001c804218802d01c0c9250300340d003d10403000302c1c410070001d03140f101e00b01020f008111003588400e0040d80d6107090b600680451000ca039481076200c241101b0401a1110380b42d90307840e071070013810f4001c80710b6545140c100160740724440e442d1340b05055440030400d594100300140a1706880710115000b004045011000907201004680544408076141c075140e942c174818480c900006030304101e40141002402005001c451318420b81d0792046111130b03003406c1d40ea03001801103a0040d4844c11f9080b1605030550411002180b032b410714806100c400004845656812110442d645039405980301d40005006006001840c0a05544040c00200a0490f07203c1140000c180e010342c00707000f9111a03910030344103584412a40001d0028030000384003d44400c0741c1004e810003004401c040304410303c00e02c86440c04c1c5064 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 985620260 1250 985619010 985619017
    0x1b151305030f030a060f060c020901080f0709050a0204080a050303041b0b09010e01020c1e040f0902010e0603040f02061b0c01020a05031e222607051c0203060705030615 74
    0x50003409142003600702c095074090b640014011400e0355454010116000740071040b0240100010703660059a4583c0740148145480e041c4c00604540c2c101c406014030351000001c41c102100d40a00700003600755200d42001d0020300031034110300d4013401040c00741400e2040000c0503500943c080c041c2d020b046040034582000c01007082c4240000c0c184107015644107580a002454008c0c0010b0060380c8041c0380010001d03800e6007980c1e01c4001c03a01c10310164803c2a0400344200071050140c1101040440d00030340001c0c0a070454510060b01c901000400134041200848502d100c1c540d000e0880c0392600480307641c40e0031040c00d03002030aa003440b4058016a0b15880010460341c4035400c40c0c069494201416900100d0400004844d03820410407c0303045080c0ca030205581e07023404401c55001c4555070800c01c0070718207500b80c0c411910390400c000c170440583c002c01082140480784100e40c3c3c81e01850350f851031034000d0301000308003035450b0040100b003014464128000f140f052204558071390002c40347d440759450500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 985621510 1250 985620260 985620263
    0x109050d020615010f1115010612051306110d06030302030d0b1c02090a1e0b010e0d0308010e130f060905010e030a050403080c0712050d12020319111b1513 68
    0x41d84191a0020b500038610040c03031171600c0c0792001019043c1840300e49032000b0030300342d80080203050004012165008084c803d4400c24103070144010300b081000140c00c805916805000c0300d40e00c00c4260505003a01d4200e4406c07044500080c0b000e95901d0030060b48a4100b400315018107403d00000240515000104070054034600c04590070b0541b02c2c0e000d01022403002440c1409860340c416410414048014000c55108034004010400007551000180120200b0000a0080300ea0700c404800203904021641e0649650012050490b91000e520b80a04d111400c00580303048014462030040c4410307900103900032400f440003400b05c0500120070070380d00d00c9070500c540c0004000340001e0000609400042403c41104ac3c00c59800544501c85201c120703031240070445071944007140f41001c85401031414811043c64100850452038a0f0007150220078441045c0c840c5a5540c00102c0d18103996002622402c04040b110085081003040d42541c1e00c40640ba28034113040401000508840b900c5948106800e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 985622760 1250 985621510 985621531
    0x306050904080a1404081f0f0b0603040303020d1104030605060a150219020f030d02030c0705041e0b0d0605100617150919091a072309010c02030a03020109050d0206 72
    0xc00300001200c1c103030038003d25501304031300070000000c81c0c1104100e21140c14101c0d40030700c8004104001041c088440407005009141e0411408141c9a80d505090b0396100d5003500300541e46009643d5101c000b41118030481404900c0428080184940c0d036009034403070141995002c4000d82c84803e13014402d9500701c50000140c2c402851221140c084804160341244050400c0c003046038a800000d045c440e0a4200d01d00581c0080340c05081c42c4410000d1100510b426a010000345440c039403040805000c80c8000a0210741b220000034003a00c4615881e100c0ca034100d4020801c0f810400c030761011131612442000d00007002d10150502488400001c14001d0103483c403a110440786500900294580c0241140b01d4092011114035140640d80682c2c42c3d900e104a0b041d01c41c1c00900c540c0c2024202e00903144504000f00c00d40401d041c81c407044500901128842e80e0241c444000e000100c80c10b13046102e00a4140c0902c0d101c4000f0580c054200c0070780284a03005413223000070000422a51380404680c4a4801c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 985624010 1250 985622760 985622767
    0x270b0405040c021506060706020405060c0313061404090509150103111206060607140f0a080310120201080103080c010612050102090a06140403200301021603230423030a06020406030605090408 84
    0x9803030508010147d5074801c001c09070400e5500c0300000c555400c0800a09825080050100b509100290700600070302500c1c18603001382c00ca40020300049009030302507405040d90368000700703050910420145488100341c0018101c4c660316850f160032a02d44e904083d500031a1075038210041d0090214030140300c0d0b94050903103030031b0004c0d68859a003804a200000e040c0c034000c010103030701400c130103120b6141007038002c00c0b0b103940e68106100100c02c00321744c541c400e800300c10b101e40341d400c010307a88641c00d581165013241203036032500046100d1030700504190303001b2001100f80c20007600030004190058000c01a048403400000c5a8890066485d04e51070900c3d03810301c0340100b00500001e0303588174265030320441c191400054014510003281c00c9900c0040c0318a20407802c03071185001c140d40140d00083e8598028840b0000e48014100184280268001c410809002409103064050069420740c10903000404071104a09075040c2000203501900030b1000190408601060300e0030000132580c00fa5501040c030925 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 985625260 1250 985624010 985624021
    0x7060318060c0c0c0f1a0307171005060a030e1002070f0303020c010f1e2d0e0f0d17010816030845030f070303270b0405040c0215 57
    0x245101c0e0326810a0044400309080400c013842c1c80c4a0150a82ca2420a5036904169a081a00c0c10380c0034100c1509104000b007286013540810041070360301c61094402c0b080c0c0c40d16000d9441012140c0c000d0354210308003141d45410560300d5040745000c2103558080c1c4507458503414032034041e8440d5802c0642405804598500000d02c6079008218054000d0300000d01d2202c00071a00d401e540c0009000840c9080d92221682c0c04802803103a103586114068600c000103031104183d8829074030031b030380d81c2c0c0720260307201c1031280415014002c2c03000421402c07095030b444490300701d030190504c034480007a10500d410f54400419483c1000400700c0e2030000102103448a1865942c2d1400c0c1548807030f020f51180c101d8500c401ca8004086501d04448255001c5050116540e02d18941e072141c01550720584668040d40150074139800c0800d001042d21b8040c904001540e507007451122810142841040c400c41c4112000285446641c0c00791040e00c100f150148002c40480004999443c2c4601082c0c10b01d2060401045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 985626510 1250 985625260 985625273
    0x20607080a0e100c060b0307261207050f0607020d02031918030c090c050f0703050a021608010c1413090b183c07050703090320010207060318 62
    0x168940503160494505034044080307000f600031041640045010a0034400c1000720382d010303100a5880550003032040700e242c0741d45822003081240c0b120158140d2410724941c85c807420711a650720081400096981d4051924241d9610301d0009003000702406a030b004501403034400b15560b036030800c0950041d8205159226900800d090101c0c69205004901c0e47c613440c00225044808000e60040c6280d690040c81c2c00060000d8800c045010710401004001c000051300900381038402254061400d29165601008260f291240c482614850100b01c000000b59845054008161030001681da02814030300c0a034241c01a401800001086c04180d01d0082c00030f41100d5020f0f4414400c001e02c11100038525100f07010642d4001c0e03c143c000d00101c41545070f60070300900c03e0b908220400c0c40120301d000c0507400180c0c56200003e0f21072006c0140c009107960506200700000d1014541090250702504059000c0b00c140b10360300180580540180c401c0005c40714024840e41004504181d01140074401a0f03907460f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 985627760 1250 985626510 985626517
    0x11d160e07030221090a030206130812130209010306020c0d0e180603100c110609070518040204110a020307020f01030221090102070b090d1d1012270b06090402060708 73
    0x120781488921a00c0341c1c01c003c4c40700d0450089250300d01601d400e050b41c1c207000f424540700806103200c00221304000000200301d0800c80301000d01d80d02107c491620340b6803034407100e007207000c0300651700105640002c014000e003035005001c008071702d0b400c5400000c450641500c130b0030584a42030383d10a020080f02c400746400081500d500250040c00d90713109a1995100c8006c645030900d40701c0000300c10210740c8581e00410400c8580140703800008000c881d00c0d003400107407200010f0101140001c1080041002c54807103030030403040c2000d40010b07141c580603002002560b079003003141d003a803288000443c50030785540280b080324100309003144110490605581181071110015189900e43c1d98201f2048003c502000f15890250402c5c00140003940241d07080109001400000d107810030b0401c5e000c02d01a0b036208101986c1703150150030448040103150841100074610440c40d048407803d40c140e040818000c403410580c0452003904061803d8441006016059608440c003e4100d0800c03c060700c0400d0901016 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 985629010 1250 985627760 985627777
    0xf040504020307030210050c154b0423030d02300105120d020304120317090304170a02090103081c090807030314060a03060e030408011d160e070302 65
    0x103e9240542e25400310f40d0084481180c8030004501142c242000f2809005800003125007403064000fa06006c1640e180b1102c00003500340c1611160880d943c07032100042207195240c110f5446125007240a0303174994941e0b8404540480c1c0d001641c101c90010421880a4040c90300c6d8200c009604000554403400000c2d8480005843c0c06109080590f242c04160140d4402200c0e1b4036001340307031551410f020b000e0541e40c00c5a004070f8035089058410102940001680c044480d90400201d429030141000c0e21340200840c83c114a0201400402841c0d00000005204491001c0c0340b0090104154074100d44039286000b000798007000e180010800304080d4806020f40592440e684591088044801ca0881c0e070f068204652020001c5031420505805202d80c0e65090262804a402031421400144002095010003424150703a16480307640090200240c80281801c68003c00c00700ba2403101117140a1075140c605006c52041905a50340d80740300500c02c05c2118004030340c10b40340d034a507400103901940007540e2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 985630260 1250 985629010 985629013
    0xc030b0703060b2208030a0c0b070905030607110f070807120303020c0a03080a0c05160b04080d06090506040629161a04060606081302210a03200703020f0405040203 72
    0x20200f103800700b8000600c05100782c44404000010103443c55003650401d40c2c020318003500184606a006904806200301c49036200101e400f1942e03400380c0603102454250440b50b0036228400806c03545c550031034914803034050040700301c1c1c03202c40040d0311f202d5403141d84d030141d0041508500010080e02c944403050740c3c8214480d040140c10055081306403494000805025000103015805200740c080c428401d41c2c0c072000300c0d0301e081450302d1452014026402181400146400215070000e014013080b442030380e480459002041c80110303911482c81000d060700340c1d4000e00c0786282080000e54040414285402d5090300b03240e45040007401149480d02d90400e640041010305071011000c00145003030035107490499080e503e000c89080c00d01f07140048401e01c1e0003041c1409107007024880420079182003a4212a41110079100300442705040406041c6200101d40c980c3c883c0601c0081050b030440c1da4150014108940e4200080501e0259aa2402c15220207034100180e5081411642032640100394041e00150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 985631510 1250 985630260 985630271
    0x607050d0e011b1e08040803071b0b091f0c020d080a090b040803010e1003050601210f080307111b040207061e050603010b04090203030a0e0109030b0103050d090902070c030b0703 78
    0x103400303208211068020005135072061810407140c55400381e030213180344602d00340c0540d00c0d113643c503410240b001a1140050000307440c4152070740f59011034480c04056005244940908169101541c0c031801900f20820320903c0215215401c45244510300001c1480e600a041d10f10107503000f6039810318050300030784480340c0710b41e062408100f032000c07890b000da803055840c655250301d8540c2ba0f00007044050044880e04010080c05c1021403000249103054a4028900c2504400141c1c075032210249135440007400c50110f02c641e2410b004045014511444c85504c901e800d061445055540390480040c2c11413818081100301c403074138103040c0c1c0039102c00d80c0319070300c001499044110200c0c2100c8101401c11409900e446c00c10115080c00e0154141503101914103001c510803540c0005d44038081c0b1100003041100400880c0c0250388622108401581c103e031445c865961241440758951880000381e0020a401d000d00040c00b5105200b01d8a429400c11409403c0904590380e014200c500507010204058031903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 985632760 1250 985631510 985631531
    0x61202131511011a0a080a050a0b070507060e030d050603031603050d0e0f0a06060b0a210209090708160c110409050111040f030c06020c01080f06010219050a02120607050d0e01 77
    0x920901942c0c1058610000e0582594401c22246091700d800c8000380d60040d07040d26001403000034800300c10640c021111b650603070704c5150445c0c1314050048d02802c02410603100a048078008402850041a840c00074407080e03513000140750780ca201c1c08140150941e0000e0101010921a90143c1400f50303014801140d016004000079140c001030784819101c4d03400c051031250800405200340030013004010405401d0030304000d406065a80e0f03024410356039104140c4500c6901c40c166044a140710700c0200810f1190401d0b00c0010062790044800005111032008a01c220034040c401d00070314280e01550384100f030220300007440060807000d0030499884d901c5104e011341c01240803016002800c4010b0b1a106158a5410884440c10072540410107640000f0b403c03103060703603210501607449980803240460030b88490303004034505031300b10b0401142d403181414200c003000404150151014000c035010502c025a4406181d1165800d40e40000450000c02440d00c207002c0c07540040c000c0c12100d4000080d004c000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 985634010 1250 985632760 985632763
    0x913020307020619050705040501050d0b360103080d1503020913150203150d031209030801080d031103070e18010f03120203090109050d0609020a0f061202131511 71
    0x1641c030708000d600704100708407904451000400000c00345410030f114508010300d001e40795102d603010f05070401c040018250707041e80e003d400c1015401070107020b000d01c04180480304018040705584000b00105900444140c080004400303506a80e0010211450041140482801400821100c118200c903550000000d42d07243c0f00c86903c120403640403002c5a032070618050040b000d0040c40186114818000d00c1881020080ca4902080c0250380ca9036455640342010781c4d0040c0c075205807007400390825121801705544100300a0403516448100d4507261401c90003502a82e42c0d4407800b115000041c800526002d04c0343c1348004504001802c500000c2c0800115450003c000b600480c944100d2840e04008100c120401d030404a842d92001d9070a0075103c41c00200110b0740c030720401d44101e00c0d440e05101030100c580d00080c2c43c80e80c000c0940441650300c000801d005007240c4150004501e50060310403800c03010340215584211038240e4900301d103042000d411001d109035500310041084440582420327020 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 985635260 1250 985634010 985634017
    0xc060b0d11040b06190f051e0403020109050d0f06051f0e07110a05030a081b0c070f05030a170f16030302090a060c0b241302040e0f04050a030302091302 67
    0x60100544014030718090000362400507945a0050004000c400300c0360300d5614980306254124640b900b036144a80e241241d00d4014100d420310401d01d0408130721074401c14100140102e0380700381c8034103a22070b544900308001c4810603000034002c0007a1041580018144c0d5101e5580120744034904a1000c444500d4000030310f0054000240d4007525138240040f19030411000151218500c3c01802c0c031207150343e160b81d00d03801031510040900c40c045020030000c02e042402010000503090255485030302030790703016a40344258030400c1401560450086058180410700c40c40190f044210b001ea1798442c2c42d0051215844148041c81c00e901c144902c0e031030441c01000b40044140240e1300540c5039076002c0d0070019803c529138006401d02424141c80302c0010105010341c1c1d03002c500081201c0014a10303103001c01840502080d05a40400d030803441c01d28500456010344251102405080f2441e618045003120380c28003960302900380d61004050000107031094004080c04031000d444240944641e0300c801c0207a81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 985636510 1250 985635260 985635263
    0x7090606080a110306060706090c0905040812010b0903030405450108150403080711160f050f1516020a032001030c091707170f1e06070c060b0d 63
    0x1070122052100d45409409040840d5411030003580c6142810030029101d442000402001c0c6a110002c280a008440c1648002031801840074046403400b880c02a10070740c0881e000a01d070390000c01c00032803034001c80302c00d4561414001d4000c510341401d22041207000da4040c4034101c001007114043e41000d00040e00d0304c0041920405038200d036000400e240a541c0c0c42c0503088040d056100580d240c0001c1205000150842d825007070404590b221007404681c000121a4115000d2054090608226000a0400c002c8800c200940d90707240361140200410707041001308080e40611a800c0714607800180500510001190280c114141b103490380c04505043c2c020390058030001052004600b2840001180000d040d409280c1040035a082d1000036044c19481e00420198402c0e00a54603101c0d001017042d14090304004076802000c0c0c1d00b40395419940c10901281c2c5160f03004894030b141340164180d607802022201031019200340e50311007108030b85800c04030400742ca80d42d841e81c1041d8071a4075841c003604c100740d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 985637760 1250 985636510 985636517
    0x1e0b0a21062f0a080a0b0f0a26010b090f100801050a0c090902090d111804050c03010c0809060f10330e150307020a021801051009080d1107090606 64
    0x142d504554a100c0740c590240c20040e00c01c200648a030f0740d0382c02045654010082000000c4810451011610701a0040c00c1103420400418010551140c100f01e40c660403a031507600072403816641844142610380a800315600a40c12002140b01000c00c000901d134401400741515014682d58086282920001d0710140326050b9102c04500e01d0f1944151a00054060340c10306510b40000e54011500c9041c020314050044000890404445e540e04291681e007061503100c02c0c04581401c0c10444d403218a1840400d00c25842d081418030824026030801e84614042405085140e842d40e29110750b4a00042400f000e0300001c00003c50500b492180c20b52a042454034608444410104140b4008200582400a1010031012030b0306540d503219108810f00464040103480b5120013005910742030300303008000c3d03000414011002c41000c0c002183d0b4102e90046889441581e0300b080b050300d017101300703005442c800d0b041200c032100594095100c0c4011482001c0c220b5050316960782d816004c440700e40c1c1012000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 985639010 1250 985637760 985637801
    0xd0c05091e0a0e1303030c03110d02090909070315090201140d020a080105011b140c041e0506010c030f2f030405040e030a0207060f0302040308030a1e0b0a2106 70
    0x50500001000141000c1040200c00d804c0058140d00d20201d0f90000404058072440d0301e22040f4843d400201e10140c443c8a8244c96a0680200401a400000c040c5004407500b40020701a1400040c007e401c0700e4000c1c904181460b01d1200c42c1015000780303002641404042c940a0001c0164000106950b102700400184c503044810001003e032401030303220380e040201801d21641c0c06500c10082000059003c07042030741c1c03604501021030619203c03000d00d681c0700345441d40e945e1040302d0032201c1ea00900048402081195a4480103450300324080308040d0018690390420000c003400303504803070920104109071001213100f980740240700d031500f28a4012190070108040080341040d00442c85441c92403006142019421080255600002d00c00c010801900a02c1204074a0082d81102d0145801c05081c0350790f85015151760303000d00142c110013114080d000740c144150000070300c0f43c2c3c0d01d42d110007451601d040f403070011005c88c035109103d1a5441c10b58805c020304005595441400b1a101503e02400c21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 985640260 1250 985639010 985639069
    0x90303160b0a0507020d050a030b0619090e0709050d06020c10060801060b042306071707020f06281103040806061c2a0b1305090a110d0c0509 62
    0x3121a00070340481d902c03030b0030301c820302011580100e0130389000101d40c0303045516480c418004134040c1018814040d080340d0001100c0b101c072a000c2c01c00551032a000d8903140d28543d540e8003a03035034050086074160005107601c54184107525007140c1030b201c818010b80c005810000b82641d010b05140304040300b0300000e650f4050400090f1000e00070a0300500840c00c0c0309042900d001304440d04102088201c5132100c10341100c2078019078986041d00d0031980c016942c1c05440640080013300ca80c0003010580c0b09403460f2881101e01d2130200c08484058107420f1b041c21260140d601c0d400f240c990f085040b0400e1003648410352030206401c1020300002c104040c000c0c01e40d418200203000801d8803c50010781d1145134880c0d21030210b0000d03005000d8180d07210b42c901424000c0143c000400f600203403c02c902c0d2040000d114404134042c01c0c59101a68022140c11110352908990030048a901c0132aa15107101d082c010001013501341d61000c50700c0e0f8501c0c00c0961800a000000600b10480c026060f480610707043c825a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 985641510 1250 985640260 985640273
    0x105060a1202270a0506030606030405070e0a05040b0612152d01090e010b010903141e03090f030309010c06051902030c0c0d0201060e22080f0a021908031b09030316 72
    0xc3e140c030303040c1c1d814103280341440e001c10058480103217542c3c01240d001000c2410007804100d003000804e00e0384c4100345281408504000580390503241078038012608804909546001c40294080310702600c01011100500c100c440c2003008001c00d06080f240c44101030030002d402440c44000c540c0030b001d00c0d0b04031365810b148464044955448107041180e140054178003580c0d0300010714205480d0032400e2115520390800305240341821000c48040e00806a50905084000000113010403410886010100700912018181d83c0d000e034140c1640010400207481010a0302c0e90302c250340010418280b2050b210307010f456802a0f03807054401c603101171400104084c14110500c805454400c00e40300900c4800d01c2c01000c0400764502410b508060084013034036402c0e0490300b022200c0090780c440b4500740c44d00c0354014040001d4200200c20000360041c4145959072841000352814400e5000403001c0c1107840f00c002c14100e0341c2025400320020b2000f000b607a035065500f000034102c101c00c908030140c1040018038101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 985642760 1250 985641510 985641577
    0x6070f020708011a091005060d02090102010b0102061b0d0f0603030806011407111002100903081501031b0809070321031a0907030e102406050c060105060a1202 70
    0x34580d00d0410050f0303c40713101a0b030420465108442240c2c2940b504100300c140100e83e5480642d1240300081c4003044038945802815000f2401d03002004900071500c01680c440908440308040710001141031524000000302608044c00300c01e0300050900c18441e45e04084800710b410503004501070804200e05984c2c0309031105060344d2590301850400d541039031403030014200300a09900c5054071118015615100301b0040d02000c0704038005101101240c01c0182641030103492020403a001d00702040c440394003c0c040c000b00100768007500c0380c68080201d022151250060203120b00b6001c2d4500c0000418003964640e00120444800000c0b0418641e00250456001803444081b03040146c400841c10740d507815000381c0c0864603082c045030010827091401d007441400100c0942a920342400c005031240c2c5a1002c800c660a1036508400d0552910380503103050003007803180c50450f80305900500c01801d000d0064030121201c0d081c80c0200354015800141660000541424024900518004141c20700c0c1c3c0b0b034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 985644010 1250 985642760 985642769
    0x1509010507020f0a030509010e040f140108011e0b0a0302090106050d052d0c0405131409070807120510020a0f03110901050a080c0c060712061a04030f1406070f0207 72
    0x207010f51498000019103600401c0030140078003502180c0c00c3d4182c0d0158010045a003c01001007207a40c042d511823030700500900d50f206440bc0b0070b2038008200b4100520a52041c80f030900c0d8131050400d034040004000d401c0b9602160780160306d01c60000010b856040403203010348582d44844c0d88a00d9595070700c00c1101c2d0028808500c00d00c160303000b1321400780c0300944900b208056a20340c072070f95a642c19014101b4442e40c0c0c4404e4100107401e03041026008242c0c0000c1e40d0b07000102c241c1203151225034002e03948001a001c0e10701941c00c1007000b0001000000301030800d95205009a0304101503404c01d04040382c101580003030210392500700c10215907074184a00c0c0400350490900c6801c000c0d45a0008243d40204010034080c0000c1c080410b1f00c0304a040d09032400c1000041c1200d15034580102c00408003881032500c140e0942c1000404141c9090911210003919050000075050a1464850b8154072282600c1a81c070b2103800358840b4001582408030038426180e945502414000001c00240b602040d82e11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 985645260 1250 985644010 985644013
    0x70c0302061b07150e12070c1a0405130b06210a090302071202060403050a03030605130204030f08090d02030703080c070f1802071703040605010f151e11150901050702 73
    0x19951a08008201559480c036001441c40c003660302d810b06044000c000980b175843ca80d200d00441a10040f02440041641c64418a000d100c3c440e038891803101604940d4011030304903102070100703000c0e504160b02003031507a50a4440106460a0040100301d0503408105590400d4414546d000c5c031300100d0b00140c6801943c55402041105403a440c002d45518031805850603000c4919104001e540d651401d4502644d0020199400551917140c058010309091081900550b00e0045000c4212464826501100c0d000102100d40c0c0381ea507901d03a1391075032002540399444014002d803940541c4013000f11001442c0b081c9092543e802c2041d0351075191081c1540081c0700e5400641083c070203504420040c0181d00301810016072100403503e0f00540e1101c502c5000542d02e5030102c100800d1018603002103040790807400c034000c2c0307840d00c0daa044038000301e050028001140b9400c0d80740c10b05045075003004120040902d0040c1c1c0d6101b50740c50450401c8a006c401d40b030300c03000c1170040c4141d2001c207116840c3c0000d120300 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 985646510 1250 985645260 985645291
    0x501020606032a061c060605071109180d08150a0303020c090c12240414041104021b0a050106080703050d140d05010602030c1b010c0209090c09070c030206 68
    0x4000ba559581d44200310103c45071040094141e443e1600b0808203c00008003413586480008006400c40c85040c5e225260240c2014000250075001d034003213401c40c0d50404280b2080c1041070050091992015020403a545920204601c1108003440f008865145555841c051402e183c100140100e16266212f445000d41c13030300c00c10020f5000240071030650002c3c0d505000726aa4a441074289002d07071803d58030004440c1c01040703c041011034801c140d2104046a55485418000c203000850714808030541214181d0408900814803c620711000904018400340c50b000c403503501011600c080000b0300f5080e90004400d40e082040c280508005440c810005001941c0ba6417106035071400b00b281c40e2414401c03402850b807500d030312040c22a0b480d4413088000307012950750750070001c0d0f80b544884101e80390b50040e99101690a104100c41c5426014140c4d501042c00140d03400300120300340040c0071a0806d20543c14002d0140d160038180c91300c134440d40d440380c0d84072a5030317401d0180c1401c5008114022000440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 985647760 1250 985646510 985646521
    0x506131a0904050f01051f090507050d0f0b03010f0b010e0f0607170c070b040303030e1b0f03010b09040308160c44040807061e0e06040b2205010206 65
    0x14016685000d0484005a203919603040c070342d00b01120011008055400c007030400c0030800c99504040848290340700850f14207581c0b625042c04441082d41c0e03a500203a01000760384000c2c001c94000c2c810400048000243c20b040d1a0700103400c403455101200c003940d4817221584900d41e00014070070907420040e660340c0b0071198034a0014070f16105a0700300130400c000850070240b021f08a0402c0e01c000d82421001c8030842926182001d040c3d800610003100005d007060328590900034080f6000516607c510014012400300004000c00b0001000c24990190340e1403018000303030b03507401c0da010380a68041d46503000c6500700b0710311203070300e1583c1c80c4880b0040c40350074818280026811300f0480c034541c03d50420002d81419048ac0796036446a036200a060f444c00042e410000150140d0007031003100c11980c102c40e50780780d4500d006c1d00e43d00e14030684028822100b110720a0854040c01c1149403400c4001c0c4450716107a107800c688801a000300c0002c0c2410845101220580314a203072100c409400240001c064070701d0704 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 985649010 1250 985647760 985647791
    0x4180503040918060c030f0e0d1d15030f0411030a151e09061a0d02060706020a021e0102131d041209120312110702060403110105040306020d050613 65
    0x60b0310401010940c0c984201d0010003240b0202c4808035400701051100001003800180680b20347c4030140c981a01c1c00e4098485100001800454615940c982c00d04a0b052502c0121031002c42c0000207400c0844a03404c034501410b000002c43c842c401c095044496401c060411900c03c2e403050000b44e0181d0b0014400340041007031240d844d204c0081c271030800300e000c205180900d4003900d86d90f5146280350f414040c02c102003080c941c01200b19603114100074089000034208000c1d082c035a00c0b10180d0051300070059840441e801c0d8009000580e89801240c81051200204030016500141d12200595011694801e54010710101e00010180701825244000c443d81e2004191100075000405403440c404507401441d004d101018000e14107020700310b41d900c50504001c5c007102c200400071442da40c40d103018010507014031411340c3c0340281c01a04407400c050440c0d80325620944428055414040d040c0400400030b003c50004060714100000302280320300300300c02442000144201007620050a10b9500c1800b03114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 985650260 1250 985649010 985649017
    0x140a0606140307021c1d091009110909011511120a0f0207050a170105010b0301060f0516050604030c03020f1f2c0f19050a0b0415050702070504180503 66
    0x1100795415540b521103101c00c1c0d2800c100d80c8070040c0790340e2441400024040e0405c500b15842d40c80c1c044030110540c001c80402c8403442c01190400322080b030500c400c1c000c45105d40d00c00c2c09601d010340030480c502005000040e44592003684912000b8014461280c01950b01c080d6160002c0b4140c0018120705040c100c1ea55032300d01a803a0010b003009240220f041d620b5100f044540000c250140040c8281130b22840495a0420002c41c140d0041d0b00b00000010458202802c890481e0f00c6074ac2c0d030301c417281c0c0004800c842541c0105030089040ba0303078001c9c0401003001444020701032403194988003030902c22850080c0c00e02d80740c044030320040c1c1c105100041d02c401d29054401d5044000d628000b0b900740b0100c05003041501843c1440b03010001c864400c41060400044480c5030844403400c4075100701c1d8248117035111180da550020078540204000c0d0f0005040d079000c6941261240b0905a41c02c0d02d03d40d180c80c1100c1003106c1100050340148810002408d103441086039503400b18164000c2c1c4070180d29005d0341c030321 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 985651510 1250 985650260 985650287
    0x513091b0f050d2301060609051905010302030c1b0319020a030f080702010e070b0406030b0901060507020607060b061c05070e18060a15030903030501060e0f040f0209060d140a0606 79
    0x64040250fa080181d07604410020380403e2001c04418001e041c1c01d14020100c0f07009103408110070006c04106403401408420b0000084041c08101c5402c080045020750000342444003c10f4080c00702280018890000c0c2190180210042d42c80320505a0400c6140005180200541d04500203220110340d1194090284241a003060001038071407a0301240104440041554903000d045804104501c40e034004000b200c285a4052040c23595420411680a00a11030080401d004024581c01800d04030050709503103000d0000000c00045440c0481e015a004078207003d1a0390101c442444e91140510406d60401030500d05200280e0b2420041411748040d079038901c0b85419440c0c00202d140e520411494081c0040f8407480b0301c3e210b802d19001e4054031240400302c010034105000419410b12910714003100e140d0003046501c200005200340002061f40340d10b48010710303800300a940b10b161600d0000b405800f90841d800034500daa81014001d074000094800c2c80705c60b050100c00c010b000d0b40030b1028010364 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 985652760 1250 985651510 985651519
    0x302060610090906030b04140d020d0309020a030c120507080c030a020f03070f030803010303091a0f18090118060b03070c0b0702070e0a0e01050901091e03090513091b0f05 75
    0x241c581c008240c0d20014140d1201c43c03018149580401000a0008424081d40c0300d101c0007641c1d45034103000552114920305a1400503803043d81e02e03028076807003500912086800a00034910003901ea07224943c2881d06a00b010800c442d0560b50501000400c0258500401c80d00e405400c4200d901130019490300c02d00788020384501c4541000e000c003036409000c400000c0c02014180340c0b44680d07030300e00b1500301d400c00d00c010380208106001c006500154400501c2490004400141c90708860340310a001c1908071104074456180e02020385c644944031040703444d001c2c000000924183c03040103003000b403d0320080c1d080035502c41d0003403040c021007641029407070380c0b51944600400000d54448a04900d040c159502c00203000c002e00d01409100301c003da11002c080700c2000300a20965640681c0303542aa2000c14005000000035000354000501c0a580102e82d10b100385040c62000e0b40da10009906042d801d50034103141e5648501d140e0802102d80c22401d82541e000031a009080c3ca02240a404400030f8412203015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 985654010 1250 985652760 985652779
    0xe180103261204121710090c020118050f0f1203010b07080c060c030402040c050307300e150609010f06050a050c0a03230708090402091504090203070909020703020606 73
    0x180148006850b01c0c0c00d90401e0003141d030300c2e25040081c1030220513500040864048003410906910420b0207500c140c00145800d40302c903181c0040807006090b8440c00300d0446d540c907503d0a5803801b10150040499001c1d40c010030018420310500c40c2000c5200200d42d25a5000c0b030106104500c168007507134110b0707030b89503003198a82640b13007855101403207242c01350f4500340110400c1040c103a04401c05180600d000343c0b0b0401000010a0054909100540301c260105034010307040805030025805010400682e03901c1d03182d10720300c00d118100503189840c418030000c1d00307c0c441c1020a6030940c103049601090885481205501d00743d6603000c41d400328003414080103000280e8101a900500458882c0300081003150004260b030300303000340050350b0030301804035002140200030001040401075074003031030700a0140d0f0700d0603414a08000007580001c030550340010a00501e422000c4006014200820b54103402603600c0c5030818000b02920003641020000d584103000d01d07004a90300240321603001d4410707100c4102 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 985655260 1250 985654010 985654073
    0x2042d080303040602071e0f0605060f1003050a1505180403020a0804030f0204060801051509090a050102120718140f1503011518030b070813050d0e180103 68
    0x104696001030000d48000801c0c0010803400d580148805800b6511010005290214080c2c5403d00030f10050312502d41e440070100440e1060348016004040104824141c0080c2d10104034030340041500100805e948200b00425004140030308100b52400e554161080340c00c28001a07154446690503003070f841554030000c3d04050003080032211a6030441112034032241da130300c0e051951043e0100f00301d0185090903000aa041814001d40307000d1056422900c1c004950b510502c040070600609420591040728110030200317500784002d191443c0c00d000c61081c130b450138410240c801d13800ba10ba800244181484108140c03421003140441c01c0004854010111900d00002510f10b62a000c0103048210000300003d185404c400e024000804952105412103640050728081c10034984000380c013202c4420000b4580f10f2150091a52000070071107030030107009190b16600d140c030080d07940d50408201e111400305002d1502c0380d0b0145c4403108510388034203298107560f05c45558101c007800006038003510781c88150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 985656510 1250 985655260 985655339
    0x50a050903101d1f0b0a05150304120206130803060402070215040915031205091201050103050d0801080f1b06040e0f040b0615040b03070c0f0b0612010204 68
    0x8403801001000c441e403410741c502c250001012003010145441c5420068888151004200524061640d0540710480d640302030b86000a0409080700d01c0c0e00151888020809591340d50b0140e016440c146a91903ca00d003915040000c89803c0e0035140c1503500c600e0800c0241d240b110890280240d01c452002d0302ca03220040170401074000d41c00002d5025040440000100c20040007401c120764036240d050100c0c0d00581441c84004ac191300006d40540041e000c444504c0b03000c0c00040c10090b20113402c0307524845101000c1821a039080e0012140750308502d8203002c45c1940f0021484c05810741c040600b0741e1a481d0480643d441542c407080d440030300b43d1740040c40c4140e92644151001042080c038150003c0c035100e94010300c0c00d00300b224200c41c01501c41000c01c1003420b0568403a980c0070045079425282038102030041080d6000240304004004001000600003082c1c006c03480503261040900f070f0003a00f45603042015103c944107150703140b070788180410445a100f560400351201d4160468850b110395040807403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 985657760 1250 985656510 985656517
    0x305060a0f06051f02010c14090d0c0506030a0b10080c030a0911030a1103101503030509040624140a090e180322060203040e0a02091206010b0901020118030906050a05 73
    0x440c0d0216140c0c0b803661300200c1043c000528281030381e000300210300150005888840c085040a03088000078040c003d040d080030400f1040890007800b41c0c503890f66030b40c0c00282140e4822a0601c00140d1142941e09090512010081301e004042c02c008109284c00320a5039803901004084008460316000000180106181700d90480c040144c1036820030800f5003400c16000c030210212070300901c10b151682040301354a100c0e90000381d04400407004003c1c555102103c45400564400b68090344e200300c00510042d509010181c5000f160383d54140c0300c54420400713081c2c41c5c405490441a01400c01c03500618517480030000099402091202d0155110510300811003001a10080c00310b2000042040100740c0701e002420610240d0781c120070a00b5200c0030200e8807400746221b08401c070031486000c11040202900540100e41c4081c041c02241290142150700d03081003a07000d01e02c5190005480a101c2d41c0c21f02030184100c0003026003003030704081d80d9401441600684644400c00c800881c2c031401c094420000c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 985659010 1250 985657760 985657769
    0xa05060f04020f04261c0212041202090f09120706110307270608180114010b04091d0a0b090f01050108030d1d0a020103150504060f030b0601020303010305060a0f06 72
    0x21511412100f0440542d6446402045c50040d0084042818403005290712110b202c40c0074041e00e041d04800200080884401d030b100c40960013180c1d44040d201c000340b0701070001043c4002c1c1c8000700c8280c5005100366044003401c400318102801003041052000003990700c111000d0b049959590390040d0800c4001007420503811076000c10700209200000d0390103508803555500c440030616803002003201e03ca413009a14860700d0046100b0900050341c42e04081000307081c84003840d00100b060100503502580d1550240c0281c901581c020405003d03000541c403403041164007488400b445601d0310011296960311184000700414007000000b051641d01740800040949540c009000e60b58440058071b880750000d204d8010704510380041e0100d04500308800518040050f4050030b12440e01d60011000f030301c00500515500c2044000000d1103444030300c43c100080001d180c24035011400c500d004040e5500140c0424119801440184042a000302d81e05270000310308030000036211086101c205c017409041d0f01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 985660260 1250 985659010 985659019
    0xb12071413020715181104150513060e240603070903170405031c1b023f03090109090f0f0e0102120a0608030f130f080a0606090203060105030a05060f 66
    0xf010002c100c01c000390944040032120050054440b5694901400700c0c06400c050002c40d49264113003064100350b4811450317020403a2101400a45400220f04035004012a1100d0141e48190030003643e02d1401e070654014985410180c80101140007220b03c1b00340000e600380c0300785400070208089030300814001c030003035900001c008080b45541c5299500364100d8401c6901900030a0300f80e42c50078203030035954a640341d400d4641038021180c0565400c444002d5210880c2c009850340280240e000c2d00e41c0c06010030402c0400881d00c0e07440038413070001e035000503100380d00c0640d402031003409916a000f03400c10043d03810368140024810800c00d1103030003505220041040700c0340350030740b80b14259006400a01d5130b001c8007003001030551034915868089861620400010750800d1189144612030440288101030103403816041d0a5181c080308020a402a1b12024030790b07101c80c1409040007002e001c1e6200500035440304509510b040d00010b00706110080614040d1a65880002c20b1a5036405000104510140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 985661510 1250 985660260 985660267
    0x9060903070b0a09091415030a080d09020a09060e0115032d05090c03030f0d09021f0f0e030a03030f09060f150e0402280806190b1207141302 62
    0x40000311190b1080f40004001058030070f001c10340e043c09008005900c261032110040070350b21340101c0ca074542014103c141e4540541a0b401021034800703c00b802c415031403c01c0004400d6550b01c100450b01d0010b61000b860746040100070400f880c0c00131001c5044441c1203041183c05c2c0720030b45088000b440f000000e03440260683c80100c0a009001c9240000b80000450401035602c406004942d2940782d017512540c99442002030200442c0400090300f1040c0d60103002155102c1c045d800140c41b40b00c03110503021038480c06100d01a1701c60b03000016011540c0b0609050a420004101103a129070081c4009130a04d03880c0e8410b070040704540ea01030060303c2d410030700800160f400000e411000c2d000641e4040a00640524042120403808001a004541c01016009035035010014800128080d80c080c881d035000740200050032160600135548103000780c0311840c5c0c0d2400485040d008951070500303540d005a0040050400c14600002c042c815148a407114888100031803001548824803550403201607030020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 985662760 1250 985661510 985661519
    0x501170a0816170f03010504291e0a08030c1501031a04020109090c0206090c03010612021c05061513090302030d0e030d061701050a0b01120903050d1418060106140906090307 76
    0x1310302440c16944125000c3c4807521890308001e03035800440b001d51811014840026002c0d151010a0241340c968224480070070141d03000010b4406a515400419030f60800a098001140140701a06038196000b5a420542d410b541721500c07141390381e01c00d1b0301446d00105c1c040380c156030141d242e10b0002c1014400a0003500100f80009440701c90a83c0c0055441c8240030340b040f09494103000d00000d1301d800f20031001d5840c506400b005000c100820081152070f0a05c00785401249007440b11610451071044c0b1000c6000a80c01803200c800c2d2038007a07601ba520303c0c200314a0002640407040310210000780d0702c0402c1040c0050951421440b56104c4580034910307120001070005100095070a83c090803800800681e0748150641050b00d10055400c0d00082004004007005180c0f43e011040705c81c040c2c40e01508000302010701004440000c9000700c540c190210070003403901040c11008441c814540082e02107545070207070207009602401900100f01001150f84c07900340d220b180070350301f00d000d00808981c5616a075 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 985664010 1250 985662760 985662787
    0x305010b01171909060f060e010303120b0906040b041b0c171e0a020f07170f0705090c0721050c0d030209060901030c1b05010501170a081617 62
    0x4800d410307010901e00e071100d2162a005658951007209404114050204040f61800042003840c604642c80c0d60b84000d24052650288101400340c450b9012885c1c0c04c3d4110f04029121490780c071600b04540b41014420306036501d4980c03045400c42c41c280ca010079030040100000300907028180284044603900543c100019030300c1408088914040c026400e80086140c514200324420200711465014040110044520390b510091801681d240b0580720911908500181000142d0780184444007a8080d24581d85800b071000b08a03424020b0000c1a00342d00c1d0201040d49100000d04108103d100491020300384041110134510b0f03401041e54210346400c420a0181880e00404c5c1200d20b11300c200258603501c103000f0310031108001401089581840d08500044000d00041c000b102c040180380c0c0b0501d0f0f64403140300322000806210300004035456040c0200d12408640c0d00c0404140e44d40301d00700100100e520b000460f01c0784601352103400307000381a608003040c5070301c0d8203810340c80c00100009414203403105 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 985665260 1250 985664010 985664021
    0xf0e0f090405031e0c0a02010c0f060c18050904050615060d0e0d030606020f0709020a12091a1e0f04020109030b0f07030b0d0305030a0e100603240207050a03030f15030501 75
    0x5804071052110391802c0702d0b130300718044c82a041c3c8081d4446e9150360701541c042c444215005200b240c3e0b11224541594410040d50f10078900780c00420b40e0b030103003409013000010503080505026a0562880c2c6400e8071400c3d0380781006030029144c0610b5500a1626460f681e048441b1500345020500a41d5120500c499440400503940b0001034604400403403e07d00c0414041c1c40011407400600c0143d06040b1104020b41c445e0b0020818401c44080809640c140c1d4020a511385000b01050ba201160b5607281c0c42182500030900800d50911203005039001c1014501c403608022a00307004141a0307680d20060310003d2490f0409071010380040100500c400040035114030505240e501400341980305014003a08480030700c8000c0100d1004d01c0003401c01041a84108044213001c0101c50021110811341c00c100d48045e08141c8142182c0e84007c5900034802e41c48080c039032003c4c0c20071481e040c403a807604c0d6220750020200808040c0c85010b410a803d1203900f000c0c07607640c500d40106210590305d240c007034000c0070f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 985666510 1250 985665260 985665277
    0xc0b190e12131202090708070210050112021504122006071b0909200301060b0309010903020f06010f03080706020d06090f0b010f120c1b0503030702070f060f0e0f09040503 75
    0xd00d0074101180114a54003d00480c0c2d6014155012075259400e05562104e07004240c281184145080c840d101c80c1030b402213500802008048185100c2d00f40140032400a0382c0c1f0a50f40b8104040104200b030004141555150f41e402c030401c06d44c0c0c3c100010030b1103143c100da412500c1d44140041520360500c00a03000d811508a01c003005034410703556074036054080d902c0020303025103400b01052040004d4141030500e01a061002800014a07039203c640300c0ca80e40d0829664070b01c4580d52608604200b41d010002034942000202c020407880d80f400030010a06050f0380001040d40c44089650010010fa540542d0f5140404603410301910b9266404100140b001c00f80c0014084c0c04c18802d0f207055402000001107207031803a5182c0d5094200d90700e04130050015400090108801e0100c220b4400035a80303004160301c2e20900182da66403e107810000e16144c0c0e15005149011404030003080f100350004542007440c811410001407044990001452038040d555001d504468401c04020401101100401200c2c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 985667760 1250 985666510 985666537
    0x3060f0b04050a090b181e0103060b03070e1306020c10020a05130936050f070306050601050f03071b0204092a030803011a090d030206070f0c0b190e12 66
    0x26a41c840c0380c4010b40703014064454010106d124448075403004004c00355400300c11400d000380e034200e880c654604840002d0340243c403006c0d6980b01c00c44c8180741c10711103c00140706e800030070300a50420f01c2100070314410030700380201141e50026000182040a0044240c0d16615901c2151a12001d0034090800e6000d0300d01001c20b208443d6010420310200d01c07d07000c5031180d252200d00c02040e108159450300c41129103611a803001040c90320009078007040600492440c82000d800700501d18946681991405400c803410b008003804683c00c1d50703090205680d4010341c1494141d0f51140b000b04180c2000318401e2006e500b150400600304180b160564816100d90b040362000307110000b4010f10001c244640e4000100b401c441000108681c10882c490300c2d061652100e00e4500e00318031000002c00d00c03020950124050382140c0100040690425a02c05d010130450810002c119100c2c0c0d55912440c0740105a0881d001d00300c0c0004442d5001ea07801402d0f4254281d0840c0e40c01d105058441c02d903134001c5192180c0c072 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 985669010 1250 985667760 985667779
    0x70314070f12020a0c0b0a08040f15230903040503060c0a143009030a0806060409020c1b040207150c0e09010815151522030303091a04030f0e0103060f0b0405 69
    0x4411032801101c003c19101d580c0c0a0140c1c80c3c0399110b19a15007822b5083d94000d40ca20b01c203900e402038902c10004101500300ea070a00d42c4107201504119008004c00c02c085540082c070081103141c802003512a800f903112110f06035150700902040d02ca500c22400184400d0030302252001140d03400c074030603407040700011a5003810540454035250794100100d0300a10560000d20880801c180150100c0d50000002011682030a48440e0394800f2030308465140c440c2ca42c41030702862a0850f0003026220040c2081c0c1d000d500d0919070b40c44104101010828078000160f0310560340740742a06c140d816222100c80100318070b0a0303581d140b0399a50340340c48403080c1c0e007000d20a01011500651441c2801d070300e014009441c8484400360000070004907044600081c4621515100d4542008805451030020314441d40340003408000d642014407a51980c030314009071603500300c0c05003c0404d401c0081c40c426010300d490080105401c8a00480240c400f661041c02e228810b4400894134148000107803080c0d42c42600d18002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 985670260 1250 985669010 985669019
    0x301090c200717010615020106151b021003020d050406050615070209010e0c04120303020a0f0503060918010e010f0507111219030e0303130314070314070f12020a0c 72
    0xa40d00036900500080c2e4042e210800140b101000303204000c40f440000020307a03544d10221000f03070806880c00c0d200183d55841042c04102601d5180e0049a0100d140652000d80a24045c94910840d04400f1303201d10180c4088595861094040380e14a6104480a00041c02c00740380242c0074140a85010f4071481c1c043e80c1c0100e03003c601341c0945080540007030090101c0d900c4d002c0c40455030200034180482c00d200400001c02c4101070b2000060300e881c8641d8005960f042d20400041180451007807560400c1000c0041c00f825680c0c1c10383c001c1d000302c4000c0c007100700d00d401ca00f04c450051441d010f0782c804030350815941d840c0c0392040b64400d900c1401d0b070761505104807015400071615110710380b4500084540074807003e103a80120b00701100403903009060009a101f8401d43e0103195410803107000c1060f14030075029000301035211801005c0040c8640150b41441840d50300a00380345080c0f0b800700c00c2c800d80440e0f508144980d1550b000d01281c0c201e0503d103013890b028800252200c040c417105491031540c1c04000107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 985671510 1250 985670260 985670297
    0x9030a11040f1e0f0e0604030801061202030103110415051309060506010f09090507050912060a2409020d090f080d0b01050301031e0219060504050103180f0212030403080301090c 78
    0xc000f07001d454000e100c60010300d825080203241c04000b44c000350741c0c0c80d52101355a0800b00541c40c05240a5125428190b240c40303002010001e013008000d44d81d078014070041000610103085030901500885010440b000309441c040603040f081d0388003540c8480024051a00c0180c00d501034024030740a100d091080741c1e00d100042d10071355080100e41000030079142c820031040350660300c0a90814541e161240c80c4c001c0d05000940300360200b00041c4902e400020502c99040c00d82e2041c0c24111909011024403c82c54010407500c08200e0b00c1101d020980008406070412010f034050b44140303a015407996401c2ca414204650035802050342130a8031454a0703400e0b42c6540c090002e4904aa5005a91261008044018118003802180c081340c1084440c800c0f061801c81c64002e2030040c010658855032034900d050001000c1e1440078200c0c48092000c404050042202880d408282c02d4042d03580c20b10600d987c4000501e580300c2da13800030f40710310b4011001180f00c1c8111381020201d02095981c08009410782800300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 985672760 1250 985671510 985671521
    0x723031c180b0c0d0b030a080901031a03030d0c020a050102040b042904060e012610062a020a03050d0215010806060f010e040b0405010f0911041a07020609030a11040f 73
    0x94030102040000a0f6601510402085410903051020500300d0395200420b251106041045038000c80100c0c0c41e005650f494030070700c0d40c54440b034803015002d0360709003022a44a115802c484405280c8440400d00b802c0d000300b040c10340c4654000000c55441c1e5407040015002d4000d80101403030390046a0007030b0314000d40c20b603246592040041c0000c0c0343c507180010599155804500803410301030342c2c0d034400ca44529810042c88000c40500024209844c00088200c011912600003409014494000701c0c1c000d55a40f80c0c2000c1061540c0300d810a41145000140310804540d000400a10400c4149007407a64041054021040c60032604c4040e641ca51548035100c00c07084800b80c1c1c10140354031340c2d482076600c184012a44000054000681d1801c54000714003075030300c2600b080080b28070000003080358823241d225400313091140b00e200c94141410301569821040c580441c820000c68081507020a56458104442e000e9000030300315181181d103460850403080c03c0c20a0280300714600b40d07103104565014001c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 985674010 1250 985672760 985672763
    0x718061d041203050a09060e070303111f0b0a03050703060c18060c02040f0209030f010b0f0108010620010f1a031c05071b0308031315110723031c18 65
    0x103540b072003070702e40314101d004007001031482030780e95240c110f1000810104d102d1268007458000c0540a00e50450030b015140d001c00c000345450ba544001c07200040365449102e4000d501b4007505021426041400020750014860b0700301411710f00601c0f00010410019900846e8102d5071034507405281c42002039039040c0c0744c0385449000045500c8543c02c0c00180703450351028000c01c1162900504003c991000320b450524981c11039a01c1d41c8d920701c1806020f2404403e1500d04c140700346065a0030358100324004103240003400340020240051100300014080a4219008044107014108003821207080307044820841c07200b206009004181d1700b0340714410f04074890f060b060f00d82e4031090328003241070340c9080703c0c1e0b108104040200900d9403c08030004d180c040c019806000068200100c02134641800c0c20301020380b81e00c0541c0e85141c698030615074801a800e644809030001c5003d040300312840149248114445142940c5000001d4070325030001841c0c018140301203140100300040000d86a0399039a14450040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 985675260 1250 985674010 985674023
    0xa030e0721122115151e0f320d15050d02061606090b040f02190f050d05070b0313140a0b04030806180705031807051c0813030c0518070f0807020718061d04 68
    0x10041582080d010288030480c5011100c1c007103410b29000b1123080d50000f0304140c82a81d112081445c1c003446441c0150081e1104440c03c0e0b28612295002407968807808161524900c5114406020300445600c2000b086030419980031851500c0e00d0001e2200b14042402c9105c6c0c08102c0a01030441006c1d901202610100704000d04110301340010404103031032004007200c9500c139011010484659200c0950f004c3c482041100c0d110010034030300700d84010180066800341d80d100c402c088000c0f8130f1040240340c00c2a01804d1629040d250500410b43c0310300b401c2e442180581c104014402d400b980107008501c9000000e590594020401340d5198441b0032071b21480f548507200c411417884c0c00c105144c0c00401e032882844000c1c80c01290391103090140002e5441500d500006803020000d03030034003094003014844604420080c07881c080c0006400d89072520300303030800c2040c50760000c0c2c0003d008001d01009051b0703000c0c0301c0005051005001010744458010700801c1c0008441203210b1b1800000b1a5009541c0f200 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 985676510 1250 985675260 985675277
    0x41d010e07081b070f081803030703091a0405031c033218060112061406030604030c0501024303050a030e0721122115151e0f 55
    0x80502d080700307a40e400003c00781c0c40070000380000410803030002d6142485004540e4a4800c0c821030008000c0000e6002d038000c0c0c00c05c10105001030b50010f05003094035500d1450070f4500300004e102c0c0380e05018941250350148981e504480720607003080031280741e44003035a0b014403035a0f03070340301c0c66a0581e030001c4003600e16064070b02240240c03442c2884e48207901c65500f0800c00112001015290b00e40242a030100061812945020b001d015450049601c1491000c0d100610307818000003081c1c0e40c0344014405002c00c090b403040001000303001c0d01116185008040d6050703100b401907444079071403980d10456016549180000d40306128a821111490f19016102c050506401190076030140051000d194400c2c003481c50b000c10121803e103010511100c904a803889030141c07614014a04204c91075443d03082c481e10300c2c000b890321600c140c03508010241402d000f00e0b0514501c1d0301001d001d600394004007a030404802e90005041e9001070b0715000300da0420701c00380800c0d0010714295141c428200d0b220700001c4194 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 985677760 1250 985676510 985676521
    0x10f11040b030c0d1b2601090207051614010e0f060f03091c0503061e030c040e031201030b1902030601020a060e0a1703071116030f030212041d010e0708 67
    0x32019550006010f91500d2600907000b00d2401201c8400d94842260f02e8849000040940d11541c42484407803982803012000030a070b140c40e90406030502c00c140503550005280e604003d0180103501444100342000f40f46291100c18541e818400320900380c0c0007604440300c4c9401da03c0e02e45a00c030703000764002d003403039240203074022511000f0345c4018003e101511415003240c0c411520400a000c01e1a225035a15850b42080000c0000000d000e03a0b040c46d456407180c218150a5401241030302003034508450000750b41d180c83c034555041d80901122403801c40d01c850000014040b415100510401074004005035409808100004078001602e0310382c0164807101844c00040c800d5032240344c0c4901403108403000c6000f0340c0d0f918400400e0074150b040d5864404014000d00039000f04900740800d01040103084c060310781802034000a0fa2911001c0c02d10389100a8250906009201400c01c1c0c0741a22680f0342d445480e4204410142181d00000c06a032450600014110704440ca4950141e103186e9209100368941 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 985679010 1250 985677760 985677779
    0xf0909040f0c030f060506030610060f111b0a051503040206030406020f18040c0905181b0d06030515070e0d0611070302071a0306060403200a03050f010f1104 69
    0x80007160350403010781c080340109506140d04002980320b115a00540080e6140030f0081c2c2d440540b03828040d610507070511000c96410014102900c2d81c0c2d00e00141da1410098007250b800d0b404010701c1c50540a030b404481c900b902002c000d11250301c0e00756002510541d41d1000d002104c0c00701c40c2d100258080500101d001450102c00441e00700380940030140c00c1c4158103003100000c2c0e21a050b10800148075041e90061810207001e00101031926040c1104418600700201c0e442c140d070b0282d003000d401c050600103291842c0740a0f0890a040c02c401c0f04580b00c1080b42c0504006040303900069035148201d80d09802448190402288103440940d602510110180c0920100c00c03071a42041310042d4071403104001c0c845070070001e05030306802075008000c0726240004007440012030380e5401c00024401c00c10001c4640320801150202c903404011140145148800e840702005003a1500e54010700b2038200000b80140041c0000701c442d000002001410245000760085911805000f51001e00a010800c1210384 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 985680260 1250 985679010 985679029
    0x260303070503240901060c15020307020316020d1202030406030f020406140c0f030f0913060e060904110d08071109070e120a06060801050403170f0f06060904110c010b060f09 76
    0x1d0012040c180c0f811000980c1d1135000340c0021002900d1b11140b00300340700e0501030301c10a2070140c290852640c245001c00075128414842400c0080c9c2da40c1040004644880c400c10b104982c02607022800042c091400940740e0340184182e00009003885100150b0321010701c01c0b5421500c40d521200640b031a0303449242069000040c188059008500303096081039018402050b040041c44035070756440801404020f06030140042c00c0009518041c0305100007a40044026040042123850380780c5580d852521016041e207120070b05810400f515900c40400c0b042c0005040d140348107011940210542e9030900c03101074001c8032000d0000e00c1001030183c141c10b10044199442000c0302c1511040402e540741d900c20307039146a2050640b81c0d5034030108414594840c0c400c4500703500c4000b4906d402e003030402c505a6409005030401001c003038002c010420589d01c110881e4401a000390003400103c011440e81c201941190301c00481da07508111031302045141400440d100140c00d03200590410582d0800e1080c01c41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 985681510 1250 985680260 985680301
    0x91404020d0e03190201051009090212010c020102090906041a12010609090f020f01020a08092b050c0a1d0f06010203040302031006080c09090a240204260303070503 72
    0x50303081100140c40e100c1c50003a10a20309074903008690310307546014031800c591a2043c125085900d04001d1001c030421064041c801c44203c244049442c40243c00004c840d000c2c02604d90001e503103007410108041e43c041d009420f1890003150210403543d5000300f40400c0c0d0b10b04c041015000c0140c2112884180741c005000e503041072034000006843e075101c0c0f5560040340d00710101a5400400f2142c1c140840c17402c061000c10b010000e03c00340c0012890f980d0780751030074000d81030110700c00c0300081c0c042c1030500051002c0c0710b5030404440e01040e054101c0d080c05510340c00341c551818001c031041c5d0404111802089416040c03100601480e06c0260750b1540d030103c03650340140c44103046000800001000da0b50030020200203d98204002501c2d504e0301d0b01c41c51404082510b814004d400290811050010125110108a070010401c0c10f5201d076190740b201203421404c03004a88030340702140205010350750b40704000f403c4640581d0b01caa2050114010340c0e07a40000ca030014006641040082c1d8001c414041140c0b844 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 985682760 1250 985681510 985681519
    0x9020117040602160305040302100e1e011718010f0b060d021305060304031713080a080a0b040f0b03070503060603031b15041a10180b010c0633060914 66
    0x1449000031843d9801501c1010717130001e0303400b0405009505e0120040024113600d82481c10000c000f440220321036051540c0420401424481901250b034003615141c1d1410780d018104406901c0c040007560255980d140f81d0380c041350700c1c20a402d1030b1070400d40b08000f400e4900510840c14607440040f50f201a6011240300e068000414200040d56160100594090351003030b25a5001c40d50003540080c00703a80d00401860707240400c08480000b0031081c03822200780d524a0720307062041d40d03514038207c005400c0361416140c00c0303032404050020080305603000c2840c0e24000c50a9440301d40d52181019603401f010754503150306420800c910000802c0c140d0018920000001c10795410b545402038040030081c0c00c40d02610764442480040544003540c2d90800d80c0f001600004100b1035080c03601c200c00e090f502000d40350100303a550ba01034920b80e0051701d686026581c0704030140194203002100000361401300030814020384882e0b0000d801035144c0314681090380c1c5942e80708c05445141540030f8006030480721b42140c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 985684010 1250 985682760 985682767
    0x9140114090d110402120f071e110c0a0305100f111206220c03060617190f0e0705010806090c0a121d0715020f0618030c070f030b010909020117040602 66
    0x15900c40d400a80302001c132481c0301014901c0c2c08004003600c808000c10110820002e83c00c842c80709d0640429010007032a16242c020503082031480c445191680151000303500c40c1c1c484400000304030001480342c190b600014410300106002190080c00d55074114685002c440062241c1020b51054006c0145e0080c00100b1202c0200f203001205070b41450f2240003000d0880c2c40d09402180c0c640c15004460007080146402d00502d45200403c03600d030040a8402a42585c01c60030141d0380c0400c54106400c2640054401c22192a149460030342c2c1c5d41c61441501e000c19055000212035240c201c51071032191402c040201d18000f00408116007440310b200c0c01c0c0281e280c2e00d40e0034107044208a1604900419400000c101481c14101e079070000540101c20001158410000b21700c1a0714040f85c5240c100c1440d98591440d81c400d050180e046004680078000b131849087c0d40000c0b80c0d01030140c080200c9005a0140040b40d07210131500c4186c1d82c50300030107408529882001e80c41019481a81d6600c0703800746800605 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 985685260 1250 985684010 985684043
    0x1140702030a08120603120f030a2f030a0606140d0c02073816030804021c121202040f060e150f070312270303020f0a09140114090d 58
    0x226401507444d145010b5900d034200071076418200170003102c40108090309030808042240180183c40000c1495505a4660241c11300c849405030403114032703407280d4441c05500d00540c2009034050b00112032501c40315080c000c0029440380100d508003400c4154011300c81c03074041e41c1601d8901401d0308200e040214410f5140000d000c01598070040000b0a242c026011003a0f00c0d10000507806048550141c1c0e040400c110700030b482d1002031403540c00d50354542031041c07107680e840c000603041c07074815030311841c0380b4240d01c004004011500004100303002140d1540300f4101d00840392001240958010440d00e140003110900000740210104000c0f4071008001c0e01d6019410340c0c41d564030b5080740c03400c05078080c004107a000030190006454495100008400c10002c621920391813808070769a10441c03290100340340c548041c5032182d01100c10319181304105540c0c030358050000400c548070501c100f54102d0b03201c200811180d0720912000c10a02c4a5044407410903100074104031400703540000c00c50300e10482d022881c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 985686510 1250 985685260 985685273
    0x703020d051213030b09010c2118110907050c0d050913060807053c061204050618060708010501030b010309060912030b1009030b06060412050706090f0501140702030a 73
    0x545900240c0340c02066900e1171810343c001803000303080800c0b207905140d180c2100703c1d400109072000c11840c6810130030f401d4024011600a00c0480d010354901103117104180140010103850442048058804100079528054125a5030081907507081158010380340003507a40344108042c0c516618010400202c0c000304001450480d0426885141250802d0104004516150034100250440c00c04142018000b0407140880700b010603000c002c5c40b00560b04844104d88800d41600c1201c500c2d101d0140440c2014105240d56070401c42d0710181241046c0b214100c0408080b800c1c0b401140b00761102c4030075908040064000c0d1800885080c1010707524070400000c61520702038402110b008103400345100c514442e005058484c845600350007030300d280d100e402209520486d51000c45c2d400105041c8103496060000e10300384140e5203e40300710285003da0034140440031408070116403460303da4203406075442d88800382030308161150a0109034002903004110687d6401032a00510040564404826550740c20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 985687760 1250 985686510 985686517
    0x1e03060a14070c020f04150e0108012909070c021507110f041806050a060b0a030c1106160809010f0509070f06030203010b0a030e1219031401080703020d0512 69
    0x12800103407280d03020304442000e90328040c1c2280c0c141c6014800b203c03040c1c0204641030800d003051802161345042071a80b400e455081c039800380058246548440d40d5800300c1c140a40b014000c82c42003c050442d401d070003442400407000c0c1d0300d500505112880d603140142540c5100840340141d800c004403c8013001d05155940c000c25045101e001c039880b0000d54081800158003150300355034001c910b00038041c411807286407440c840040d400702e004207150b44d881005c50050701726a0300c098004400480c25507403640d0141c0125107450403030340d10006c2124015450650302c50080e03e07040c045080169240c08014461072800394070100d0381c800443c440060a6000044401c01c0705c02d00c0c002e0b044400d09005100131141020300515442c079096096504164070179080703105030504142410f5648005541c102070902030f80d038801e080c0b500010340317642d2040408402220200390010001c0d01d003094148042c051901c041e4180e446410080030220309541c28014210740700c01c401d07905480382840c2140c0c5003040302d004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 985689010 1250 985687760 985687771
    0x220c0203040801060b040e040803070203190f171b09040b0d03090e01121203180609080d1512171215040501080102120403180305070b030402030609070b091e0306 71
    0x29a50790b07151400d01c508507511500182c140c4a4104002c200541084001a1b00b041d0012106603a81d20b410b07070103071b203544101e14071011244a00b814032014a5045010409410071270f03180c4811a0111803a244c0080340202c1d0868a120a814580394002054001074080340c0c0025000148103542c0700005540c0c100681d81c120009850100103221041c1c243c0ba0382c60051401c21070752403412807103a0b602000140d2408407a010140d031000c52190300894168041c0b2078a800242c100045031742400c2c00c40c1154071015403240c0f45428104565a00f4100035161421250085a2103000783c2c02644d036860000d1040c1024107550341e09000161040441c0801c4034065034140e402080c0c0d9080c42030a000540c1c00580c8a501c0c20792040c81181d54550f1520b08031039001d40d043c0b60201e40802100000f4030b446640d40c2000c0d045201b80ca802180218003034000b117010b20300807011140d450b43d42c03040255690020f80a010714440060010100900b050101109280c02c0c1481c041000000354010038a45102106e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 985690260 1250 985689010 985689013
    0xa0609020d02192a023606030a030207091104030206030907050103230402010825020102130e13031d090405010504150b010f0c060b101229220c02 64
    0x40e08400112603a0304540061620704045985881c440c050109124011040309400c00c6004e207048215a07031803400c51031140c00a11001c10b000300203581c0340c80940b03c08161005c0b64614030041081d9190004100c2c400980c15401044850f052209080250680540702d035100a028040800103994a41c0611310a40c400d0006003c2d4a140c00c00060950391b2011050642c14024240c03607010b5000061070f15401902803e00c0c0d00e00b52180300300308800c0703048008400d04a0b030f000816211030301d42c1074001b81090650101d5548007140c80d01075040c410703441138480960014400060800080c0141c40e10700c940d9912182002903044508041807040754100c0302203403180d644904120401612a403100340c00b550540c8100500c0c13080c2030000e442607501e80710013000c0c40f00f000001410800140c01145031000301a0402084400301c88004e0268141e000400745607504001c51800e90028820300d040b4500d8008080d451000c4410302400080b880321003a00c81307060174201c1c0fa100344810780d001d4a05454990760 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 985691510 1250 985690260 985690267
    0x80a0506010609050d020906010c120903050c0a080d12090606411e030d020d11031602041112010b03011d060f060c250e2d0a0609020d02 60
    0x6401400c040050b0401001d1002e6104244201d40712003c8150301030754150780000040d142c601c01600c024402100c0100350301c1c0710704084521a40d2011401c021a8428800c9540343d0030018100003405c10315020341e080742e41c015898039032413610494202c0e542802c1d00d0320020f451302e01c9845080644010760003a0740c803690540318906014218540c1c040010035245480103075400424501e00c409010407030160300c68480190300e00300030200c945d40d11408285c0282150711021214502944030900083d514010514ae00751440c6d07000404011070701e4810b1065514601c09070186d08100c014155030b00071000506050000d54040340d04090602e000c3c1068000303198817585000600c00d0000006d48212065117809400c4c0091504d85d81c1240003011000c986443d00d500143d04210f2611041e001c80e541d990680c019000d00356075454001609507109210194599030301d5680e0025880c140c2e450040c030010f1b240c030b03038811620f0a40003039640000360380c540410210364480d060310517a04003810011a041d03001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 985692760 1250 985691510 985691513
    0x60111071d0603011503060b12010204090c030506060309060c07210201200909012d062622110a060905030136170705030d0b030f0706050d15080a 64
    0x50720181d48041e08030020300c0440c0c21620303005482405403100902c81038840b0032040e480d565440c441c2d500c0081c840d00854032151707141d071a180648900130500c1c011038075003008113256042000450b482108544007c00640c2c841300400212a884240242c1e403c0d00404800c5030080f071103851411020405034004982694454040c3c0f00c041000000300403206010800f00c0650b827900110141181c4c640d42d0011110b0b001d109a80500301061076202003580c1e9a00303000325100e6004072102450000b0764424061000d501ca01303418a1101c10742c2e08440188031903a41110b020103085014458a2103801c8030440044030714042146100300f908110701142c1e01300418845800c0900c0340380301c0c4d040000b110200c03849030640c1445003802108690b494481d00a281401801041c4408000c038503181c0c0015a0b840030f09040550300d9800145409900c542400840111403900250540011441d18007178900c1c5e915101003a5040e50100805007503042d1100b480c00c40d20404280c10074020440e000c094403038410f15 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 985694010 1250 985692760 985692809
    0xc0c020a0801020414040209040b03010905061b03010b04032909030a0215010e0105010c05030412030e1206090607030b0409021c05070b031b070218090c0f0105070b0f06011107 77
    0xc039040100240c0c0b040c401042000300a007540131410400381c80050b651001000401d004d04010110b481c0c0540c20490148200000082c249224030000f041810341c003144020441454070081c030414034095000d010a01c007040d480000e41c4502030401c50110032a14850464540200040315000100c3e0400b040d0340d08403070340502ca03845401d840c5022a41d440d43c10300b1032200300317000d040c0289030420222044410400c0010401c41d005064220107525240d400d5280040198911218180c011501d20310141d41d1401d000a54038003ca1901014001d00d0b030359450214020050742982643c002d49803c10307c030140e240d04030b241c81300c0e859841c280a030044260900306d1408240390300000600808004001030040300c2d07039000d1074005a034a20f0070f903552450700000d0b02905030b544203090f0303000030b80f4148096200c00040c038100f902d0013a180f0641300e508881c010764070390143e01e074040d003c10080030024020642030910143d00076014140f5403141111a0070b054030340300c0183c00c1411184508401180d51148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 985695260 1250 985694010 985694029
    0x20618040b040525051e09130f02091e030a17070c08060402092401080403050f1908070c0b0c03100b1804050f062d1003021309110a0c0609060c0c02 65
    0x140f41084d510304020517500c0f0300c0c28188403455401e109004a41d0340701c82d0f908e20500741c013240c41c0f03a030082c0818138000030040005e620000c1528070414010071010031000030403d400c181c0c003200070301606200c43c1c0b40d00c1b0385001d10fa2500c1d024001e01c404000f1f80000030305004025014107070ba64001d081915241c81070003c1a203010745070b1442681003604007002c00400d070007a01803141c030030320b13052105480d03501d01a5014060710700c010f0a4944089030481c1d002d22504021004003481c0c0d42e80da900360300c5034281505d40f0310040b00c024104003110310010f00900c000310025034020700905100320034aa515074903045c0e980c200b000343c2c00500c1900f03c2218140c1c03501d8000d098000350f2245155449060a41c0012003105440c4c00a000d000d1000d04082c800484150035100e40780f501421494180d000214018020b502210045402d008041d03000314200301c1e64400c500b402d845c00b0710100c0c42c0060140d016200904e15900403950280c40d08071020000d03146010303000284c1c81a440f00a403c00c102d00c1007014240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 985696510 1250 985695260 985695331
    0xa0b0f030a0b0a182a260610080a030c05030405060304081e03060f0d0f0507080706081b04030b04050316060209040e01090b0112142413020618040b0405 67
    0x16007044c20f40210b000310100e0000802c411041d000040101e00410000b6605a0700504041103406591a20f018a000f4020b084900c2074040c2d601035a2440d01d446040402401401c1c0b055102480e860006800358070490b02440c010000ca030705103a6140e0004900394800c45013100e2405002c00c00c2c0c0720070b11a00300c484004081d101d0f5020b0039403070800c01007410b8043c207801c1517105080500c40b8100780705003458000340140d0884299451180c5400246e559414644540f4002901e640c00264200050721154100021041c0f6903d203001e1850b1201003e0740c1c4081d000380d80a0104026502d8610702d115104000e1b184921005030f02c0c1d40c00803042000301c030b108000c055030a904011402000402c1c00c4810303410342d40041b0400b581202241080711642d4007005451010b0b06c91000001c1510342154a841c4124a00c1c00b40e120007a81e41d000d8840c549212282d001350001340501016168101d0009004c80e807030000350000424010000000c2e05480c029100303541d0583c070340c41010701e500c882048440b8404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 985697760 1250 985696510 985696541
    0x60f08010501140d0f062409080c06030c2503030c031404081305060f03150d03050307081308071a0604090b01090507030b030d030605030c01170a0b0f030a0b0a 70
    0x541c03521002900c0707144000d00e4207610300000107400c00c41c0001603000c01d24003d00365a041124945940054a070001d400c0c0745d02c02036030010752074520781c00d20071f4030394200b641c0780c610192809030180400e00c0f056030806040d42c01281814000e04882082001c0c002248040740452000424400d00b4064110744034103241d40b080505015140300400000382600350800d038010101c507078981e01c00c0c0b40300341c1c10f0340390b130300000d600103000118910700010000c007075401000160710074400810b20404020a10b8241140240418000d000187c4028015154903600580c80000c440c4009002c0c1e4a6038030a41c008442142d483d01c4120310040040090640554808025901004074900700c0e101d900f00d805051041c0c410180d1910300241400d8482d4005510030040542200c200204501c1c5c040d0240026002c1d01d80607100340300c500c1071551321070a03004422590a42951107191690018600642508100d0765000b140380300e182e44003611308202c200422030246209403524140301c02000e05079004044040d880c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 985699010 1250 985697760 985697777
    0x1504120c05150a020604170d140103020f0406240201090b091506030610050d021810030605220f031707030e190b070f0c0204061710060f05150c16060f 66
    0x1940c1c4c0000d00c40350000e4010001d10320715401008440540d01c90b040361000c1c4070381080c0e10640140300c080f60240c182c078403c0702c1d111620003a0000b400110343c03907032040c050401ca86150058013044401d0486410000c2171001040740c0c40580c5030401300c2101078401c01400d80c0013859583c0b8180b002220550804811006050075051454007000c007100e00e4007800744603600c0616110110355591050417441c3c6040780003040c0764909845090700c400124841522500e0810000036184402210000a08a40a2032032402c1000a440c0c0c60341000181100f2810302200e10040d0b0411150b4800d8544108007030369000c104100300701041c600306400d4000d102d107405d074810700c0913000900d4980640e0f804481842c02c2901050312280031070b0300146d6590080d40141c40c00f000401c0c200344004481441581e5003003110100600081400c0440d031951150f06410443c0d024248401e250a440310700620254510075810240500c1c051810700c1c1010110161a107d1358508000c0b0030380004500742000401e080c041c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 985700260 1250 985699010 985699027
    0x150503030a1d090a1e0203130605060607150203010f060203090d06021c0207050607030c0e03100c030207050f0a0c0f0e070f03061e050f120703021504120c0515 70
    0x5a90090009031810721440d2400802c201d09031002542e009100141001500c1c1010130105008007610030b41d05190b200940a071a008840324002c580c003844044110f83c0001c20f841e1941401000050482e50b40410100152408562400c098001c000b030301002c0180c0c0c951624003100d03802c074510f501c801e065400034000060b80e80d0321a0b05810341035403c11805695032814041d06071620328070285401030703680301081d0181807080c0007580324071400d0070740c074200002c04000800b501c0d0903400e8405958150700a04102e00102465009001481c1d114180542090744c0b6554841c1040344102140741035030b0090a0500a001ca84503220b0010300c00004130038502c03800c0180341c0032000401400401070121480440784401c0c403903801900100040440052491070000c2c210b40c02035142d1003454030034800003089040780e20309800d0065a0805000040008910716400d01400c0d00300f25010586602c414000050314848060b0400c7c04e0358803400010403203a040c4030801049159404c1a0142c014060100b103c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 985701510 1250 985700260 985700263
    0x10905010206060f241e03090d0309060f290d260d09080d0c090b09040b150406080916030b07080604110d0608190f0807110a0b0904150503 61
    0x19003208050700d094510008500200d503000824141040c0c0317546403110701c03001001e1000041c0c445010050a400e501d0201d0f07460043c5a800b040d11094510740041528142040c021791102843e0341c401c050114650300e036400140c044910070030203858000341ca1540403680c0d9040000e070301880030023205e50700448201500c1c1ca1403051004a604e441c1c4190180082d03d4000c1128240c07034519040100c1407245440d285000035040e0000741a100c049420072010030200750240c0382540c01e89001031381041c18482c0c00010440502021403195401006441c2c480c0c00f802200c400a10290505417605003840c14141e8130f140c43c00d11a820301e800c004610610038800215034461150f08607030349181980e601d486050020f4020481045c01d0311860600045951030b159264121004651080082c0c0d04103400060700c0c0180034036840d0006001040c00403d890000e41d0240103030035514040e40300300c0180e210b041c0128854004c42d402c000400303e00810103500500d058020300030719400140380001c0301441c0c500402d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 985702760 1250 985701510 985701523
    0x4050901060f031b080a0c0e0f091209060714031207090b0d230702010b1002210a050d090807110409020f2106011412030f0708090d050d08090c0109050102 68
    0x7030510b242116840451002e8941306009485620b0603100b8004440c41d003100031007000d214502c40000313064001102d400c0c205407441c2c421083c3c400a8a00c0604550b0030018941c420301c02107610640070701c090750114046d42032011400541078015543d0384d92400010414200c020710030000c200707100a0030300c803c1a00230305a440350b442d18980452202d000382c035060402140300c0302c00c00300545603c6c200106503034150002492404142c50003010204810400c0740c5171125100803080c00a070240300741c2d035803802040c000d00100840b45841130a03c030080165409541000b00d00b0349595002140010500c03101d0071105240000171182042403c2c000c1d80172441e080703e0140281c1c4116450f180c0001480c0d0b60a000d2400310301603805507203080d1b8440084001c03285040d90703058003c81c0b401003131042c40c440001c12180001503006007641402c000d541c5111a50780200c0d81c40381c1081d5180d4441c0001001002075041a48694a85900500d0001b0005180c00a0b005146042224050003013000b41d8012801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 985704010 1250 985702760 985702763
    0x60c04050f06040b130906171b030717060712141906122003071d040615060201020315010503010f06030506040902030303090d080a0902090612010f020c01060504050901060f03 77
    0x44803811640070000a1071070040d0b40c011108098005003174480401400c0c000d50603907140c840104001c60320b5110490611584115548440d030150000080c2c0c0106542007002440c00141110596612a041400031904140f030306003c59008409000c4181d40001c00352481058403c410404101100c1e01c40c54031881c09019400d1071000d52440030f00d44601504040064040341d90b480c5101d02c83e40c5001c04c004144440144042810403484040600e07001c00e900f4100c641e0068054640c003011700801898120140c011030314283c0c3c03884e911522408000942009001c2ca400040e100c2c500401d003813072030760361481075541001010030051100502e007180e5074080d02c45c90303c1c1c0000c95540d0400820001c00016101950601c030200401c5803d01000850102c19111607942c08070356101c000c41c450a64807aa103000f5808484903000528904100070031810304003aa000105280e07131725070000812648490211000c0da51500e4003031203541000d01500da00200e400c0020060f0380d1a102c016115504c96010 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 985705260 1250 985704010 985704019
    0x1091202060a2f0c0705030d0c060f05130227070e030c22090f060204260303070f0f030f051501140c0712140102031e01080606130c0201140a0606090503060c0405 71
    0xe41340c400c038408000c46005000090101c602a070580e2401030046c00001d4801c440745410250744901503200c40c001c9034081c40000070b01410f603d085508005889110b0381d0002002c82d041c8010301d000100d0316940902a41c000d44448120030b4400043c14240754441e43c225024001d0300c011240581072002d424807610128400010340007a40c0d01d000e40c0700d10320b07540c070142001c3d00104022a25400382009010a040a520760f44698121030901c240c0741e004c116150030100d005440a0047d09001c0c3d84200c0d5103903014900011542d82521a500c104c400688100d00c00c0d415105a41117256084448000f80e4824501914103001f00604456903c95450140c54a9540400d83e00310070400888039034103480e500c4e10700030354607440c10b0801c24281e902c0c94044000b03c1c000c3c44000042c3e80f540031503d180642800f0380503902070200d103564100a030180c404403004642d600e516109400344203901c40ca0040748455030109510b860020001c1440076140c0003648690061000d00115803689411101245e0f000e07035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 985706510 1250 985705260 985705267
    0x12023918150d08040b040e0601020d050307031806051006020c0d17090d170702040c030209061206030709061215050c0304060f020d0231060e09040501091202060a2f 72
    0x10a40da035800074401001c3c5507010401194000100002e001a12850030248405554840049031307181000c40200740032170002c00200c1d40e642d2007600700c80075100980c50700c8601c01c1c01940c0c600d000c9800445006410703048030384003031020b10303814840c1383c17820203086880340000e682c5034860f0b070907104110040c500c4054000802440c1c5440b4209540403040d017152182140d0741400ba0b03118581d922413901244502e02d883c1d405a001e5010b84203030391071414041d0905041101d10b40070700c244100c0c09004144c0c5481610000540c115042c0643c002409113400d104400b1443c03403400d82c80d1550800950000c0c6402c2004221160100c541507da1150704400c01103401c03903808000c40c00a201e4030000e99901c174000541100031060440c200c900300e9010501e60004034000c002c0d840d03094a0680100e82c00074402c403e400c140b510742411010b42041c001d00000440380d1241e56981e062403001c10794040543c0010003007161880a034401e8411010001304c0341200d64050001da20780f107194103600300d041100d006c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 985707760 1250 985706510 985706551
    0x60518040309060518120f0f0a030206011a040e0601020c03060106020d080105090c030c210103030c120201150506180613050a0b03010b390105010f2112023918 70
    0x820410410840e5407003034074980c40f2905002358544a4020054002d4420100001951020b00010510500d5401c00250a0a040c080181072140024100504500c0b6211500407144e800303201c1c45000b401c1c1500200750407004a04041d01101c0168850340c49031507604d040240d541c3c4a6000c43c0e82c0201d848443e00e40e10070694000780c5282054400c1c088011550b98008000c1681100d08034440d280140302c40c50305103c402504030300345e40c0007009904e001176240404002505200c0b024102801786100c510004500120208483d50040410b02007600f03121300c802c010a00300342081401034100040464a50340c108039000317845124205000d040320500c80c2241d00d03800244100f0250410905001d00100307003480840c94041c040a01444103d4481c03180e0000389040c0d040601507000101d2406074120310801d4807000d141842800081d01503014071400b2aa0840c1c540701d02100c0119a0b2401c200c1c0c80400c040313441d044415000856000b05038000ca90030082e41c007038203070030b52092207034441c0340201d52078 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 985709010 1250 985707760 985707763
    0xf0c0c06090c12010b032d150a060b0c0c19080d361a130f08150c071506181b140f0d06051804030906051812 48
    0x942228020034020401482800d103004030340e440010104403040c4141c0502064418201c5034502107240c1d16a0240010303034403d400310324158500000521121070900c010940072030801d01003000c0c2055000d848402c03c00a20024802c5002070440c0080080c20900c40401c4d40d0765585045120601c2a0341e203240481c0204200010070014202503810799202811602001e000748070381c1d8501203070305809002c40b8030b055403c0c43d04020310b032928105041041484c14515031040031050607030001c0c000c0c0400c542c848121440c011040244a200341542045180080050070040103002040c102c00c1e404051292244001c0295001d86401c0385400c0401c81d031301c88802004003a1a408404800c108908285201d5060740c403440c043d003030101910f19030f4a00d8200407900b0b01d00b10314480350f10840c18802e8840b00501c02001e40b94001088400007029500e40c00003810880908039407900040c0824100403c2640c028658402080c003824200d0503c0351100c6d0004070074510428035030007840e000c21070030f0701c001c0d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 985710260 1250 985709010 985709017
    0xb1801020714010f050610050a080a0b10020f010f0c2a02041503021e010503070c05070308040b04061b080a0f141204051c0e04050403021509330f0c 65
    0x24001820540010711a82c100d0280138000f00741c0c250185400d001400a04203000c0c001c0c9100c0440d680e081c42d0040b0361310143c3c1c5550000d030400032616a603441101494442a10032454400a60000c0400e0030100d40d50030f0035a240410080701d03450406c104200329035081085200928a1401160a10b10701c540200303040d62010740c0065402420b014410100d10343c05141c02d020740e402514188601e884404000f030000c503004802034005501080002c1d50340b4458205151f0070f9125109603040b0b943e076602e42d1800c13178000343c0107483d03d0000001d0401607203030400040c480309011100074411444017500c50909a0082c2c200c200184034001c402c1000e0079100311840c0c012800c824113903c2d120307150003000d8038849400300e40480c0c0030305c2000c210030301c1e02c1b00075131030b92003488119a11040348110a000707000240c90041c00480c02d51140c44143d002c4a84440e02c4148104080e5008241620724541d1848203078070a180441e080d455070030360001162121040c0f10760300c028a000742c9a4682ca450107009264170 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 985711510 1250 985710260 985710263
    0x2091002011413030c061b030e16030b040f0f08090f1c060203100b0f0d0c08010e1501140c0d1409061b0313120209100503030d0c031b0201050f130b18010207 69
    0x2e203080c9605071440d00070951f4011041c2a540c1c100082541c1c0c1e00c103140e0f12940c1d40c00312095141130542c00c0000880c9541601c2d449440b964150324014550340d1120482000423200b141c040c500071814816a0418500580340c0190844a908640030408850b1041f2808208094401a00000091308442503420b4407401401c200503002d58544031007440d43c00c141c00c204c8000040c142404c4e100000c030b030b2042c007255050307503280307a80c0850307548900c62412019052440410305016070b0516076170300035001d80b0141c8500c102400103803061440c0705100a0003548600e405440c02003003440000401d849110a40b144000340c800e0083d100045001184e1950140712600ba10300204c103d0040b41c00d500300c1c0c10142c1c4a038400da41c424500e496443c4841d030302440074006d050b0560300601c40030400d03082913001185503c4050400040c403245404080b0000c070358410f0180d0150f034440050007140840e07020000d40c0403400c50032400003030400c3c2d030340c81c0d510910182c01401c050f850360060103168002035040b04c0009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 985712760 1250 985711510 985711523
    0x9071502030409050a0615110a060504032624120304030f051204141e060d0b0a0b09030c210604120f0306080607031802060d02091002011413030c 64
    0x41915000203580e039000d80100c008150501011401030700140c050703d8281d40003c250800d0101c2c00180480d080002085503103454450140d030b401c0802d1103481081c1c081da00903502d800c0c215940c2d0402450384840c00b410f248003003c0c8001080b850008403001d190b9124003c00005540e04004c1c0b0000d990000c0381c0e0007400450100140c00000c020f01c0d480040f514074414016112054401c03441d050040c00350344070764681e00c0b1014400b03034214034000005445d40069141e818414072514401709040c0d0b00014002d244495441c90904a1440c1200c044401405800c180604d442c1000d80801d4903407501000c02c5020b82000621113592403000400b880c004014a03040303c280e80362906200d59a44008060080072500500145c11424030038000c50090390002d03802846c1985440d10102d00138a0b610381011a115107a01e01c1c4001640d030f110041000d003004031400768a560040040014480c084a03100055a161500c1ea580d07046488424079841380d189040405a440241419210a007010344018243c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 985714010 1250 985712760 985712789
    0x1e06020405060f13080616080c1b0106080f06041119030624050105161b0807180b06030906060402030a09020d0b0709090e15060301020f030727030f0204050907 70
    0x565030608064444e024861005880403955030076101e031a110280c03030344007003400000342e0100806c4c00340d0140c5030070110712450785160952400e4a4040b5000c2c00d0300500f2186d440d4841002013a204020141a5036081809032841d4100f55540e0348803c04d640155a002d003001c0b61210704038030f441410107401150401c9040c007030b04007202c107606818072010400c1c2500300c0b0038a0000c2031551084096540500b0180003030591701081e6103401d0403040d030000908420904900c030214100c1c8090044200600300c0400851001d400c0e581001d081e245424607181c0515818400c0210300000000c2d02034104006490040e80c03030715040714001c050880200c002c0d401200135400c1808212800c482031388503401681d2441401a2079030406000c0e180e0185504a040d4803008a54248094000003241c001c0401400103151980c0207000b103941d50011100b03a07022804200710251601d1388488001543d9400030008409181155600010740c0500c441c06800386a0300d0340007a1100c6420400b4038017803c02480f51035071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 985715260 1250 985714010 985714027
    0x304201c0c090b030309041505030304081501090b0d060b03121206090f060a1a07050703030f02100b09070e010e030618100c14070303110307050409181e0602040506 72
    0x1400520190215810050720100081a1449205030644600c005000e10b1410030000100406400c98960f0740e007813181c0506002070750380c0e0100001c0c001480d200c2e014120b06c07012100004031880d0145c0c40502005d050584010107036a442c070070a41c80f141d10100004580c0d60b22004241b51060413180d0381c00c042c80c005580040309941c19a9588141401c4035a101d041e5220110b42d06200e50544246400c0040d4080a100d040c4c07011081c0c0c40812b1a03511250308005a0b81c4403280f60241543c010b07070200300e000724901d888550502140d03090001405040c0200002400803805a440040c01c0d0020003e41d281114402c2e0f00c100441c4546c2d503002030480d2500c0c103011100404000241c0500300e41071052503004130f841c0c075541c00341a84040720f42d01d50000703022030303072a40d12a03a40c40031000714109075555501048c1e810400c0d0145010b070800341d84103500c0380c0c180700010045034070a115a407062540c0281e1076000482541954140306c50685958003a03616501c0d2480103402207401c003584c081000f044000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 985716510 1250 985715260 985715299
    0x90b092203120204120c241416060c0323060108010b0d0b0415051c050d050307110703050a020111010207051b01090f03060527280b07020d0305090c06030420 69
    0x255460000c1e070541400e180540c1070318400800802c1802300d11000c241c0007205000c0303401303440424000e01590440c0d420381d68400c030854103c1617864020a0341ea40c0103841e50106a00c100f02d200e880704031000c1c2a82440e0001800e456030500c0b490000041c005604103403148a500103c480d408080d00901c24264580301107440c00d003040c040c59010304640f250344041c4004d8000f41c1e8480507006409000b1500343e03c03404541e183c0c4002c0191040c00704006005007040402c0009100550265000e000c4944a0303200041040040300c048400d26070061010101160011a03a000005050035107280142041001644c8003001d981c40310340d0440e0003070800401d0003030a800852040c102071341c081c1e440e040781c200405005207210b90114001d51080030b8521505010000c00102a00b0500300500c0f60722140e0303604101018210b4480005030411409030001039098042d480e0004080c102410703005d04001c0115a0901009001510808094a4420300b103403c41c0d01c0740b0070640f00545090080c9140d5031221 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 985717760 1250 985716510 985716533
    0xa03060e0604021608031b0f0a031103160c030e120303100906120602091f020c01021203310519120504030308060f19090b09220312020412 61
    0x2408040121001a07034a28280c822a03130079030a00c803c0c84200c60002c0d102c0c80041d80006064002c503203d200d061280506804010b4060038091036a255079400c5803a4000742650440c0800c5c0015000034024800415039140c420f40b030b54405407400c40303030319510307414110b0f89248100d4005401080b40700401031035410200096218200d520301088100f540e0b0108a01224000c0c4121300e43c07011120504000503480303800070008010010300d80800b0320184081c0100c000701e184640e0015034401203103d8040c3d40c06015102d0542440400c007801c52400d031901008074a0282d14030020106035000c19818450703a2062501d01da5003100841c3d44c0c60341a65030104d00d903c000d0344180c07080280f10703081403091031143c0200c0301640c0e410340c4d034108140c41d20010302004a05807131040c1d03442020031444c0100544540c211034000c0c480400d0100d400144141031040c0d0080150042c49074841080d00d0101401c02d1000c0a10020340c50b19084c40b02c0144010040000d00540d04003154030701c0c444207511305101080c0f40c1c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 985719010 1250 985717760 985717769
    0x60a0207061107083d06050f012f0307050f0a23190503120702010204061b020f0108040804032001082a0a050919080d1d06030a060305030a0306 63
    0xb0340b6503400c0c4000c1c1c029660a000c0c4504655680250703070000d404003502142c9841c000124040040c0d4541100d169004000c0c80c00040d9061035864008100500d4090740c00001500207003842404007070107100700b80d1040308002c40c824035205880300840560388104101c6c0d4500303801c4410b5500c1868008a102e4980c8601c001c2a83c1c0c1604104070000100003860100c42044102c00003002c0c05050101c0700d4400c403c10342c50568142c0024445a641c0110b640750103403003190b055000603036990510f4406090303010b295106c1d441490340488072400503221031180d2400e0034003d0803c450b043da1913203440030440c030540d0030040c082800203251000d4402c9108001c0c1003120262621040341c0e0703408541c007100040d0051198100320540f1102d555062051005190448440c5801d61805120358081080d0070800340e0381c40741c03148140300d0410940d2800c1c0041040c9005903c1c041d04141c0307442400710300102944002030f1090500001017240b01d80c150340014020b5034014107683c0c59080c00700c0c0180003003415225 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 985720260 1250 985719010 985719017
    0x150c0a061b05040510140c0607121802040f02040f080309131a12030f12100b12010b0c070306050a020304051c0912060b0a2409030804050618060a020706 67
    0x2031120031003480c00215229a4240e61503d00b4980341100704001d08102100302d00510240150100600a050008103038019481c00142854149080000e20902800f900c004026181c150300409405a0644580c662501203402003006001140c81d90000e01c169802100c58203500c1000041c041c00103c094514400304403035a4410441c508216800d0f07426000900003410742c507060301c207910f2501c069680c80100e514001c503801d04860000f080c5445c0d20412221200b960300400308040511080400300103880d82c45001410007a0345022101e9409040c06980605180860802a40b400411000c002142c000030140302600300180c06900951040d5025202d82c01031800503a03803c00c840742d00c90300da41296503880b503400d85404d03400003100c0329034181190103503241d12524500f43d480480c04806004041802c0d216014043c08003007a01c800c5100d800f0034802c2c030641c100085100b00c07040e80c084420030756030607550b00740c2d03000107451030720031440700c0e960000000c1110240294000740b00300556440341c5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 985721510 1250 985720260 985720271
    0x60406141b212104050a02060a1d0618010c1e2d1211030d0c050306120606060313050109050d09140405010e0c0a1b06050a0b01030c0f030506150c0a06 66
    0x40c6200a02c0786260450f0424400507014080d01003151609a0050207402503c0c00920b055000505641c05255503e0000e03800e1b05500824400000b02140c01100031a03072907207000200031692501038a1004598148000e5144075004e01c03009914845010703140d01e800590051561a01c020a83c0c07080405025030042e0002e08d400440003801c80344a50b982102c2d940d041c07018100d600b105d59843c00030410196000c140321481d812150343c044c13008080c020ba1103458403440d001040c0107404607d4220003030940d0110082c0140c586582c4100e0303400c0000d04c058100b505425040c1180949038001008169104e803198580045901030020030a44608000101c220f141c0300040205407002070081d03000c1c0402800c0415188000b15000f4420b0a0450600284007000030488540c4500404404d0354000e0b00c0d6400c2102c612417500c5030000001702420100403440b19804014000c0b12114060700600d56240c0100b035541d520800c1103540c060103c000d10340e6810103c500542c94040c40036003100c0190401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 985722760 1250 985721510 985721563
    0xb0315010e030606040f06030206071a0c160803040807140706030b010f02030f181c05010609090506040201180801020c2a0d0b060a03080711031209060406141b 70
    0x700e20404401c84014002c1a1603140c000420008140401210806c3c9a4410001005072950800303001c2e0140681d84030280051005c41c80802d46500401100c2c1d04042003101c030f903001115107407482686400030100d03a2655030b02d250540030780c8108036024090030002c03400450000f100241080c152203059900384104042c28005460300d254400c903000140e003050040d4030070455600d015010118130740300b400d0000f01901c3c001c208c000410354580d05000c0212028082803041c03d00624000304620132080000d14001c0c2c849603128040a04001c0c1003101400c0c0c2c00400345103010944001c3c1c00c1680003156104c002e0405143d0307600060825007000001401c52030000d0a640c0300c4200c035001d02510150982d00e807039843d0381d0310490051400381e210301446404808291414098445076103d03200441580c59044101458074192007007080f4910020480e80780540c40b0041580c04803002420b203d01c280000810304840c034041c0c4000c140024400207081501540006242070180b0005114848070400701d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 985724010 1250 985722760 985722767
    0x613080a020117100501030f0f09080d0e0307020a090e0a14030405011e02070b0d14010902120a270501060b030a021c020304030203070311012d1112130206130b031501 73
    0x104d40510071032080590401141d4002d407c00220005504000140d4410707901c5c1c04d00448940410070b0360341100103c1c4500300b201d4103100e41c1c411045264021030401650303500203003080c41c1c0ea000d00720341d040c1ca4101140924908020900001c4e034464034a040d400309190b54981e50390041d108036400219402901d030042d4240003000b041d40300c940d50140240504205441d4080d5100b030400260762617a48841d04070302200c060416000c8c0410042c090b07564080900b0f410780c00000501000c8074945411a50404c058440b01484c007142c0402072440d28041c5541803083c0140ba45070701000709500000f0404c000c07400250300420710ac400d032201c21020a40d6440b2140c04a0008503001005a401042510003190040244280340c2c0003241c0045003500740012442c000401230790498442842c10601c054000403039003c4e8040c41041c1c0e01e051800c0041c062543e1a100002a2580c8044000040c2072815500c5200c21100d60b040004a00b0314910fa64815a0485a008685140f940c01e030300030003040325600c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 985725260 1250 985724010 985724057
    0x708103209090d0f050c15130b0702100b09150f0321191b0f0c080d02010b122d0a0f0f0c050901030f11011808031e03010305030a0e0613080a0201 64
    0x6c40c0010300c00841080108100102c0c041d211045440315104101c0001d090001c4c4184580890350141c1080c07091a43c001042c0e4480981261045c0407020400c4030107010300e505880c205500700c55150b01419620301190800d6811f0341c500032405c1e51903080300a90f2120303c0041648030300020300501d2040713680034111040b00c030191800700c5944191540310081180c1c4102000307418008c000c103070011980e0ba0007551904001c4420200135075142d90080b980da00c2c0c04a0039441c00c51005003e49904c2c0030034002a01d01e01d845001c0004c0080740c1118540f1400c00410140300b00740d80c469001d40c143e82d05402c000e4050640101e040340c1c01d40104d400803d440c1010700da6241200d0b07101c4903120900e00e40d552400a81499048850b04020340c150301c000c02d0415035090071000b0801040a5565140030303110300d0b120a444500f22501c42e403020401000012800002c441c9018028940f510316082c0f54400100d0f580300b40c1c043c40e412101441c00100d4034517004511248914401d8803400c0040240030800360b60b462 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 985726510 1250 985725260 985725277
    0x3140403060515150d050a06050a0608061e01020309040e07120309172d0a1707110f03120d061d01080c01030c020601060e0114070b0708103209090d0f05 67
    0x401c180310038801038060b41c20440e00300e09511b00100e096902c610110b02b0315100341d80a800010548014800c03242031811350010f0200c400044000e030450340c080003030740ea072061203526405144e0310211030718005030502030000502480b02020a5541c1f1a00380180145041d002d00100d070720181107880d450000006a000140301c007020400011584949802c8841c41c62403d030f0b941c54061441ca6800040541c48440c40c03030310540305420703220262420700b03a55200750f034000c1e02e0040140c076006840a03500060b0311581c0711244110155103815442121001e071207251b010025440071460030035a181100300019040e180c000702107400f1786503504011800e65078070f144202c0140e0021401444072911035401e13080e10010605140480803484240b0f01241d038032440f01582e405a190060262003540400e00b43d802c100c58043e01c403146402c10091458075001e0085000d94000c4881490001040c416484103904a0061848505103000e00146840c3c000ba0040000040c3c00422003c185502130b0058034000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 985727760 1250 985726510 985726549
    0x60b071208090c06071401060b0307020d020f21120a090308160e06090a210506010501090305070902090a0305030d0f200909221b230d03140403060515 66
    0x390752402800240d074490031046d61010740081031a40c14280034000d65000302149910540d41c0c4c81e080c80f0003400c009040200e201150001203800008000005400030f0400405641240f405810442580b0b5440b425500031a19441903041108401c020380c0004034060080c7c9a0915940d100e601e200e140400840320781000c04d200043d260114140344020748080c18010b00401080c646400d641c00700d2000c1c0420442034045084e100c0d0081000c1400602d00405082c04d1240e500b5007184d90381c94030381105010b40680300d5404113404049603a40c0c030009004540082c01d99a5170400700c200b2a01610b0480da40d641d40904080e40100507540140103c0002545002da5a042c030214604001d102c24002d001c00d02c12841c02600380b41084580105216003a00c078015100611035050b454208103847e9501c001c1f91090341101c214031004003942c0107012079800301d896891008541c5000e44d0440c2041440041403180824040200324207580300070702812050780b0385569080c912003005400e001c8208403080e05c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 985729010 1250 985727760 985727773
    0x1e090e0403110708011d0106050301060e0c0a031e050702010b10020d0e040207061407090b0702100806030708160f0f081f0f140708060415050d080409060b07120809 72
    0x2003842441c00d00c001c01d03000340685100e16501c46015080d1a0781405100303100b001c888a00c40b0681b0248038910081c0025802070083c14948800d00ca0311038002084030006c8080002d448818034440d60000d072030980ca801c5031030140c08582070280000c010450f82e540c0591b02c0c2803c02c170424542040340000c03000b1144d00400f0b0803403210302d040b241100100c03d0035410980a0002c040010b425015160042c440503240d07100070304d4849801003160f005c640c48a070640c0402c0201c100581c9031544134101090660a10a05070344803a8040303441c00505510100083c00b80106481c091019182014110741b01c8100720150203072180e01006821910744075a25055200c00e03000080c0d24412202d50b547c22802c00c06c00903044c443d43c0300030380c142c44000d0350142024044004121480740c110035010f42212040d0303010020510a0840c281510240e401480d10031402500700c03008200b00700d81154050a100082801072a50368040190b15400080045820300b81c41034100710001d01c94001a841066050010030a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 985730260 1250 985729010 985729013
    0x5061905132315010803071a1b030c09150910050309030d0c1103122d0408030c1606060f0e0c03060d020402090301150303030b0301020f0304020f0409121e090e04 71
    0x740070710b1480c403801c0e5030700441c100910300c581d645640c68002c110f101d02071941e5006c5450007101d40b410094241109a0b107800074421030750111303120034800310305821035942d4903141d00303050002c00d01031180e1260f07001507518222589086403401414554500707580e101724041c0f0750502555203000455040900d544103200714240710704150001104c0b000700c1c0c1403001140c01c40f0a0307040d0566120003640306d001003615044c04105202030800c2d0203d444042628003d00c07038040d502410441c8050005070500001201050324103041c0001c0319542204c10700240002c0000c4d10b0910080e003106e00c21009040d03000d402c0000c4c0782d1140304006224941000c18a440c41c1c0d54481003244500c0103500a81c0c01540c02d0000c0030b05a04c3c06d1068000c0c030310568480030005803461900406a03a820b4000d03a00990040c012104036020001c1079039001a8102c40c0400002000000714000b011041d8000d84443d06d040704240c1180e030072008000d41589108a088681094184141c5078152240310703500c034440e92000010f0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 985731510 1250 985730260 985730303
    0x609110d1109040201110f0d12022a16080708060a050906010e10150e0a050a270e070b04031103010902010906180308030718090501210c030506190513 66
    0xf0ba0282c814109881c6d000204e2034014505180c11108121903031188252403500e40c1c2040c00e078403001c1441c0400b585004807003824100440c0c0003a1084500350b6504420b410380344001d0220714101c0d04110078000580396204181d60b80c0340d90620511005001382e80120740007106500034603104000003002040b040e4030b03040401828450061542580f5100d8540c00300d0620f0fa10b805401804ca40350790b40342283d0f040c0380c040081c440c0c4d1580c007040c810300c11017100f006003101c68940c03010700b03840140a400201c2c0101c901c403005880c20703034600780340340c06904004649071420401800a4a000700d04804150201009150881c0c6081a0190100380c04590030407a10b44114010f60840e11101019903140c1c0d178070340e61000310b50001d40740000442e005a48d8206507244c5044d13808001d0226220501244d4541500716062200c005500304440c020703100f4290600621020302802190701c58211013880c42c180482d41c8003c118410a203958a003000049141c229a03100e441e20380f681c00010b510665801041c000d03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 985732760 1250 985731510 985731529
    0xc0512091203181911041d070902090d020406030303150f08061302010e03072711030105152b06051009060302180d080a0807020d0f140909040609110d11 67
    0x114554801e0194010b10101602c2c4e00100c41d44c40b403c00d030880c10107031008100544440c682c4810507030300180a50600b22800145040440d001c0d4030005079914202400b089410b0708460001e074011741099800010142e02d940300017072000c104400c05080e1b5466a910410f40952841954005e901c52004030340b2105049010048070b520505048020310301e460003180c2000080c0d80414468280040342e048808590007015560f900101d00c02c1240c501e9500030700685000600a0a0041c0183e0b00070311503407456a003c40314a200b0071201c400c139000e040b00d5210400d000c0b4126070707901c160030305d08005080d042200c0907020030081501c0d00805503040c0a000c50094209050100100a110003200704a4075402002c06030203005a005070350341c00d46001d02904507172015040c10301719070100c081400240e038004a0f4100a00652038840f00d020412401241d181c0210143c40d0f52004240c0180010889a07a0064104901c1188401c0c20b0351106000c000400c8800307000500f0140e00c031b1050004c186401e84d8034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 985734010 1250 985732760 985732801
    0x3030e01260f0703020708070b070e3a0b15012a060b10090b07080409050115020d02011b0302070f050a15060905070507060c120c0512091203 62
    0x8032096125041c00d04904110140c0c4840000700d24188040e45508551083e030080c3d00781419890070b0307841c0d9a0540544204803020302000c0384980030600d100d06c41e00c40103006010092801614541254200b01d45424041815080015550301a0600d68081c0340000c01913411440d07110351962200c24801514007030701159410001c071020300515143d0381c1c001c0e030b50040f82c00c06084543c0c50300d030f4034142c02100c0c0c01c5500c0038407079000d40a91549556000c04c06000b900c0540a805842e11424501b100d031700d008a0300f140081508000011a4151820780c000418030855800c0725100c010088090b400c0703c076081458028640300c840944041130183d0010480d142c49104c4035008142c1d60340340c2c0c03810034075091070880300513800441c3c02000a54a000d294081c040800b000c012505108501030158800e01e6002809151a400d0038003040340a0b1340301240c66442c400c000c0c0580001080014400e9001c054030464020105010920003c1d000480164500c40040c020340307141c5540c0d2641a5420447c40d5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 985735260 1250 985734010 985734017
    0xb0a02030a0b060406020106030201260117030705192303042309040c061101110d11130305030a0f0203090603040212070315061d0402150309014d0403030e01 69
    0x302d030700860712020020401481c090f400090454203501c00144007102098440b42c01168480e0009081c0c04008070f220304540c01706402c206a030060100c01d074154000d1480c0508140240320400c40c1d001034125441c48440d21951a814000184401c90301d0440b42e0310717842e620b8941c0103020600040580d14802c0180c0315201c41c0300b445181c0143d0001c0c03001d480c111030407502e40f41c1d104403c00c0803e41001c003188030760b04403e000340407100b070700c0030f4030150b90203209140c10030a5180c00f080d400103007411040341c0c142500c2c00182ca50103500c0e07050241c2e41760301403c44000090b5840758041d02e0710f4400300c15504000380c010f02c43d5140d13071943e400f0002d0a0004100304400c50181000000004040c6c0c0203a5900703040034600071a02d17034a46506a19003c0003041c2000e4030314007042c1040016a1401100000340141584142d02c90f203d4140c40f500510300035a01490414007100c00c07900100a07441c0444512050300d00312284c0e105000b5001000c0681c043e018064510248000d00c0007078011400b40610f10320614 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 985736510 1250 985735260 985735271
    0x12070633141305101e061b031b05071a0924220305010f020c0d03050a060b165601031b08030a14030a0b180f07020601030b0a02030a 58
    0x826410881e001510110940d0407090000c021170301d044288081c0c104044174031072002e02e282c80f502416031000c4100c903902031545036414408150080402500795881d03560945016202c500e0302c0ca0303880036a40650310708034804811240c02c05405004a607007042c030180412828240340c00e4460020154510160708221061206144030800300745d04000201050100081440c91410b20134212108181c842c10360500412003032400000005d1045403900740f515000550b692041d030f40d03c0042c000c0e90011032494100041600c1180c20001c1072100323250141c081c024207207000400d403c0300c186015074541801400d400c1881214500005800040320405e00c5c0000080c540e00c1c5131442500d002d0f08211065140b400003107a0010b068800f260161080703900271450400e6002c0c000c1d200314100070381c036181a5400400030341521416000034029100142002c00c50186e0f0030a5400805003c07282d00d61140901c0e03002424052001072094101d9802c80c0c02c40c5485d44941518001a620080c01007a4494071407 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 985737760 1250 985736510 985736539
    0x18060609130b03060702150726040f0b0717010e010609120c03060617150601020705040c0903020d111509060d090609050625080c0910021207063314 65
    0xd011302440707601281c0c0039100302c5060002400200c540a00400b040040407014540e640c90005000400401c40581040039070740e5501d8521502c8070911002004650b0190074400c681d904014140c203c5240e8070710100c0d80da83c8801c50069045024840c03e0b0014042d49001c0003410420b0307080c544450300a666880740c59072070f51220400d49005900480040d000c0000040642c0c000b0321100d00032103180c0c4101803180c14603000007980c801c4540546441259900e03884031909000c0c220200c0150f9000e0038681c1c1c0c061ba5800c007204030104110381e80340110401108030007051510411105800c0c1d00030001d904013a82ea03078501008041c00d0340110350403540c8020007004100c0070000f1511440c403982c5120301e55200603103400719150400810303030280440c03c400d020340e120ba10000d0300ca0002c4203403411007810350541401c925107101c0007505d00044000080800600c00c031500200741040c0d0b0b101c1110150812018808602900c0341c9041c43c440e040000103002169a8014007045100001c01c40181c40c2d036130 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 985739010 1250 985737760 985737763
    0xd0902150708040e06060306030a03080703150b0a1407030c0f0c0302061206030706020708030301120809150a03140408070b06130f02030108061006080106080a020f071118060609130b03 81
    0x81e1080e103066a000c1020060100b0301c2400541c070803025181d070760031401c100010035515015040001c3c00d00601c480099030030741c825404940200130940000c0b61980c1d5031180e1400302e501106104002864500c01e602110f1a1001142c070019490b03034030b46447c1d2100383c130b600e0000a0062003c80e45c60803c940e0020141e52010040c03c8484601c4403900e2803030130440d081500e041c44544c02602035401190041100c3c89003c019681129a03107019000c05007100e01d416504c0740700d0a0066070b840310a0041d81710617101da82020703040702441610200a8245888202e500c40d440480d4001c00c2d140d0108280b5001a08905240d60001c0003d0450346a11400c000350b00c040d0b501c410711075803c0640c0031004001800b810402035803c03241c009040c1030058100f00004244403414014241030005000102c0d074fd584290703040300c40400300c9901440c1c8556151801c4032903000c0101c4050711903902e04000c0211481602550b42c01030170020545894401c80200b403082c0440340498545d00e06030749010980c201c0c1c03030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 985740260 1250 985739010 985739017
    0xa120b0d021206060103060e1003032d0503010602010e060f01090c09030501020f120a0608030703050309160b0c390303070f0f02010228111201060f17010b03030d090215 74
    0x8040050443d6142c42c0c000102111303c164003914480500c041804100c0c8001c1a4020a81e0381614080750042d212010190102c4018080c0c105804a14202d0b003801d40d030f00601841c140c440d154000d00c882628106070654400007965601c480c04002401040721107001d034040306d0a88020308040258664075259142203802c408401030301c2e0600080e40c09020481e540e10b90b07510030b104c91420000d20741826031403a660b0048410007814001c0004c08030310900c4c000c1200321801c1205000e05642d09485d0038a5014541014041129a100d00d0307280d8150105001030f86004d5050504181d200d040f10402c00410b03000c60f80c0f180e642c00d40400c00181011a8150041400903405480c02908869091000a01c0c10110b58880d01c010800000c5180c0301058680515035000d802502e203d540712108000100e035518180c0500c3d42c190720307002001032181400720211044824034083d24080d100c0ca20801d900b0780b8030750018507505070410001544142c3c3c8030352220b400c3c1c500181508a4820181c001c0112560 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 985741510 1250 985740260 985740289
    0x31706010c0507090c1b0507060c05030708070305090f01031a01031e0e071505030f010509040311190b180604080d0e0a0302031323150f070b1602030a120b0d02 70
    0x340c41703a61001005030090401c0c003003c000030901c2e2080c0d141645030252500c1050003407400b082501c0003481c081c46010000e64a0b80c80e040350304503a54424514010340b080d402080014081d003020b846081e500d6002e88600c1c81e114400c1c0c030700c1c4000c444281004600501000d241c802d00300d50182601303030b5801c443d8880e1460114101c40200b250600b42840d1880c0c0580c24507000c0300700300303040080084601e5100101030440e14242c0d0003402c15100c5240a440398460916120030910440318141c824504150355480c105000d510b200744103484600c03101030300b05002603600165521103c00706000a401e81c0041c09115044880050640d080314800e81c1400d80d400015070050303102240a010b1120906c904100038400078003404900090b116030395560210f8640900d20a10184032026005003941040714094007100640e190b8407910751600080456003652036100071062080400410740c00042101d41e0000c41e0b84460782070410303c00030080901944040140c0224000c0780802c016103c2c0c101d00302030007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 985742760 1250 985741510 985741529
    0x90b180a02160809180709060f05090904110a0602061b03041b06021b0306071e1404080304090e030f0412030c060f0b2404050103150f0e090613031706010c0507 70
    0x1d510f44020005030300503000d2070400017080d1405024000340c0280c43ca9085555900700034404480c0903105641c64040e800307000c0d4021070402e0800c001c20803440c500401c0840221080d0034110b8550b20201c3c0d84810489610400d4110010501c032864500000f8613413051252074980e405058210701c2e084a0503490340000d0150b400742100420814400d0f40d419110002600140203610b0403d00040c103c2d00f4240900d110711180400c1d00c21502d100e03c060761605102801c00ca99180c5e6a01b221355640e61003481000007051912544042c003040203c201d48034030041c2252181002e062006403c00b07110264400c0701402400442040000c1c018042d484a0002d40400021001c194505000c01c032000860340a4800406010f00e188544640c020b0f1416100286000280700001016070103203d18250424031035130b0710b00e540c0000c403103a4500700144107030306460a9a8540e10350340800d249401c18982c0c02008100c0480c04d01ca08100c510b07150313650040051400308040034440e140c0300e082c07100d41c1d000310410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 985744010 1250 985742760 985742767
    0x3191803020f060f060102061b0d05010f05040e031c020f12090d031803020616030b03010f0207061113060f120203041a0c0f030c0d020403120e0a090b180a021608 71
    0x40c1c40c00b486041e0340805031210018045c41c00100003501c0710401415482c13110004080094211811810f47d960b20b40781802c2040156142c0905209080302803155a118504000318a001020301100345d90008841002110101d0102204034002c0e4101c864031400500080c0031080d544030f00e104c02540500001c030040d015003000c5c084c0060030b543c4804070341e00070441c039141d110340040d500042095020f640303003003074444c40360019404801404819075030b554158200240d000074805190b004240c240e1291030104400ea8a815814059015101c0b00c400011011001044041d001c0d50084c4041000d9140001000e800301103580201d801c2603405480100c44680c1501c0c44000300c02180750018012948a0300702413000221002c5c0c0d105c000c0140300182008117081220170802d4050303401548c0d00110f00310161400200041001240407001c81c890b1040000000d07210722345201c0d640c607854028110000e8041c5038645191441d901a010a2119600b00f001101042d07440445a02c80c900c241880e698 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 985745260 1250 985744010 985744033
    0xa2a06030515010509030318030106080a081215060703121103011205120c210723060703060e0103230607030f0f0b09270d05071e080319180302 63
    0x2c50101080d403071810701c0420446a08182d40000c00c2e0b030100c03640030f0500d071000a030941c0400c0c09450301d944014900d10600c40e8100400c00d080001d00080c5500d03c010300c8460307441c2c465450800c1e400440242d08a07000b0085100840c0c4520400b0182804440010403084d01904081005a00984c4448008610030303408404029080c0440b40e40074030300e103480c0741c00c0c19401c61a10341c4a010070701c10107030015091005101a0b50300c3d90142c032041500201c3d0303004903a40c01c0c10f400ca500344d031107a1600e00d180140c0b0b000681042c0039100e02000e94000028050045e800c40c0d0312020310300c007040c480c5098100304c000d0b090308490301000313420700c28429035401003144c8100b0500721040d64500000c4032880b0b8285064070215071180e145040d400741050380000c4101280030f843c0d1228809101c03030300085018100d800c01186400c08001c125040c46440003003855003880706070012180300104024030503c410804500d40c04440050288544002c0400060074855407540c0222003446410440258103e01c80168 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 985746510 1250 985745260 985745281
    0x1e09010623120a02060d020901020c040203100f0602121206040b12010209030106050109120308073501090203160e0103020c1b01030e21030403120903020a230a2a060305 74
    0x84a207205a401880f000070340d6400125076004800310145105d9001c260805260310070400c50f40c11803c0a40210350381c3c10072504201400400340284036003481403c1c000101c00c1d20008400300c200e90040845400c026144211503490038018080701c0c2d0094a4401c80440c40d540c0e81840c4d26100c0c168000140e0381c400c400181400d68002da40a241802503603501080701c0200038100501403a854580581e0603070303440400b40c42d0480003903c022650301484031540c0f046400c941c0440c07803808680f00410242d030f90740c4280b80241d1004590b81d600d80d0307140e45074641c03031a8011031a242d8071640504015007820098a0f4031854005002d08000c24a16402401c030301d9541c0520a6148541c8403801414255040e00319040030f21000c0c0031000c6503414008001014103210300c0c084500da440b010001e00a804a80c20000d40e5030b21540c60a0342c004080101003101040c1c90400c0031001896200600a070400721746400ba4501403006d01400c40030362100d00308040d0002044800041c01c550307180000e03142022030140 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 985747760 1250 985746510 985746529
    0x11030307110717070e090102040b0c07080615030d0804050c040f020910020304030b04080901030b0a06030504050d082e030b0c130503370503040b0a11061e09010623 72
    0x194803c10b0103141c00712070001c10700c2070550b0b21824111403580c03261480d0600901ca0385c0e2003030846850100d0b010040c1c100c081104030442d010f0f00101e80d0552200321012468004c055242a8194801400240f5841c01032291581c82806002030304c1c81031400c1d03c00302c1d00f0341e2484203400701195800118030809161015004003030100c0d0344011814981036559401c64040050006019200082440000d0741c0c030980149505034000340c0b02d450031036580e540103005400140d40031a41c034000c45140c011141d1084241501c0350140b0307140000801009403801c507090340c1c00b8020342c084c801900c0021011407814130030039000b1900b0ba00710320f65034107d8403224411082d454016900c40d401031041c40f80700c0b230456501d0305420089480e07080f04e114108640f1644988064800800502000c02c001a0b04411440505600d46082d1100c13620b0001840140340c441d4021111090301d1710141c2c5100b02e002d0100581940d000000b40c000290300750f01c0d04400d41100d880c02d40134446581d00b042d514a03142c00d140c40003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 985749010 1250 985747760 985747769
    0x121c0c0501180c170a060920041125051c080f01060e15090d2a05100302090a12150f05090c100e090a09020307080a030519110303071107 60
    0x8005a06680d41d901c0030b08480a00c10507032421508103548418a01c02c1c8840804d4903441b003c03c0001542900c1c0240144010003440e5520048241d4020605c0c10030707001d0b8490501112003580d2500c290545040490800e0a151052084d10700e00380c180010010040010108000220240c28485200c002000800b006084442c04441c420040000c203030081501000054210b0350500000d456001c20072443c001c01c048039a100718003040f03410912010b01c1041000c19030401018402d01d8a12090041c408810b2060903004503680d0f1400415034800e81c0a0001790900418220710b03503030740e60114150445002400e581a90250540403c0c030f0101e072013216003d0311148014040303481c107121032a0320780807045001c50240c04048096449548a20074100c29008000d003038400c642000030291004040383e072000ca0007480b4484000c0f8055a00240005110b603050fa00d65280a0703803807619001d901d1400d034041c0140801f901181242640a03c09940b18102959600015007010010503242002a900 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 985750260 1250 985749010 985749041
    0x1061707080c1f0f140315120a052503080a0306090f05070f08061f0903020f06030130021807031a0a050405180a0f032c121c0c0501 58
    0x310500f910080000e5880030705102c2c00c051800102c0403100b030341c940115194484081d2000410130080c80015014000c000005960240c000c03400755030303500e0362046101000b038200c0d4417081e189440b20000394500b044900141c40044d110725038a60b02c08255421003100714002c82d07100c03401408100139078460118000324002d018889400e04d41c602074092440c040c05502000b40b000700140d026251031254200c000c070648400c440041c40114010043c00070b5000491141404540fa45034038505402502d058034a110101001c03c0141c0904000c0e01e2961001c03441040a075050f00005a9580d4000200610500c11504110710703003003200804076405185c8000040220416034509c903100c90800c0416a00b09850020380e94540041d03441d000d2400340c503102498884d8000383c804018600501881440c869218908440c121800c100074010050010414905510354900008e10340100c0049141d0440d40aa0390421504951000c401c00e03c010f224000c40c010025010401c8024411460351115404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 985751510 1250 985750260 985750279
    0xd0e064f121211030c091f030911040606081f080307120837060905011d09030412061107053c0c24070609030305060609030c1201061707080c 62
    0x81500e80f03404050a02040d0300004a06c0981c80d403102d00002402d46801008029180b0f48100010003030300b44800c0031502d00f8915000c10100341041c2c000c0360305031075168890800503a03070754481c852404101c410840e00ca03203000400041c0c6031800e0001701006400b48445104680150700f0141030f114002d0711a10030020189010000d01c5031100319403d07040b070103804002802c040b000300b10020340700a4010b1260f2a25110000880d0301900207c64200400c00f00703046070744e41e2100180760310b0740a24032400070720054070546039000803800e41c400b22910023503003121400c1007500c1e00d40e2441c1a02da840c0000c00054039800d8801c0360296008a03041c00c0d11103044400020818211640d15111140c580310b025000880c4040e0103081031002d890303a8151006681c584500d051b00f40440540740070700080d00482d251101180d03c9007000e4044402140c0050000c06200d007400d82800301050b034410119004d03542e20304021503011550f150b980504000e000c000d0041e913007042c10321400c15401c1440a40308040300f4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 985752760 1250 985751510 985751531
    0x50a110d0206010302041a0310022a120d0f0507031a1009030b2503140105040b100c0602040b0d0b0f040203040f110d080d0e064f1212 59
    0x79095054030303410703100842c3c1c519041200d001f85180c1a200190b040c029840c1001e00c81d80c159000c7c0000001e0002c14032068002078680c02c010500318002c0040c01d8208400d6140c603050300d9402856403144080c07002841001c049040403c5a50564280000070748411003414080d60b00e0107204400141203800031110340051030090000100fa200c0107000681000004850640c40c00840c0010000540c440c0305104005800074010101c4a400403200070a0100200e240d00f458070030000c40c42006010401d038001980740c2500c1040c103509048401e5602003001041903040038000d070418412450020440d030307080c041003154503c1c00300703140380c000d610600410001ca03000880384600030b6003000b42a04420340000c0420500f00484002a0184c5d40c002658440d011160340030244c011401c60a9402030f0310351700584500000c11101c070386c440c3c600c036a40381c0071400114540194500c0403000045005143e1804958003959049000c2e10400741080c4c0f0021403640000c0f00700a0840b142504002801c1780 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 985754010 1250 985752760 985752763
    0x80f011703090f06040801050408120906160e0f0a0620010203090d1b0807080705010b010e1513050a0902040303111612060b090903030615070b01030b0402130c050a110d02 75
    0x510030b08030310458103034410f1460350700c071202228090000c0000a0007d46000c1c10711701c02e80d0f400440c82ca4820400040081d000b88000b1035207600511802c00500e5060008010843d0441c010040180d44403580340f848900595a540104c80105010b845c0c3c8200300385444100c0c0b1800c0d07104100c0c40b1642c2d00400400511000c045050742003482103040524454102410500d42041400c00060046500090020900c0040400307040307010b111b000280443d241d00d400465a0b54a8540e401f5041409011001e01602960000e0721540300d50400700c2da801c682d1035000a0b8520707043e17400501210707400074050080c50f07403040c00d01d00c50705144d900404484008000c9842461400c0c0b0404444480c43d541120400c0080d410144011200800d9007515040c40807109880c0c0c1e200769076051090100441151581c0f41c054280e810894011107a01920382c0b0b151500300603208020412640055011000c149030301a034400d416003400c050741d0b101e03141c00c00400c003e801d190800d1045070103648a1158288030690 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 985755260 1250 985754010 985754017
    0x703110702091305070807080c0a08030711240f070c0e04081204033507020a030c0627080a08180307060f0e1005100509010806070f0c080a080f011703 66
    0x24109203030f001d20001d130070183d0411185402c806094000d04034001040c1c0c100241040741030008030382100301e0302c1d615089140d6a210300c010080c452107000e0301c18081450000c02419086a01100141004141d99003145640e8010701c4036001c60100469010140985540c0d2600604044256071035542043e07115a20320f4011010045074100f80d55000174201442070301031058401032440c550000304c5454480c00b07003040040490400d00300d01700001404c80e900c006056003003c1c1c3c254807018010132041e116007016013080d0f0300310144166429007540d81d5590025540b40e0290080c8102c4dd12586800700c000c0003200003078076a2a4442a6401c902c80402001c01180c0401c0e030300c0000011007a4100e4003a20160010300c1e4144014002c1e498240d44220725504171522981041c21041c594985500821041710001e000d0351000d9402200011001800b610218540d000d00d810801603e011680d00e240da143e01000501000440718018046084003486071207000d4181c008100c40360210a000d042d640b4013 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 985756510 1250 985755260 985755271
    0x5061806071b022e110115091d06010b0d0f02030403050307031a060406110708240c070f0f0308160815010513170d0e100503060112090b070311070209 66
    0x9440c82e0007046589041035a04803401c0348551803a0240f80c003010441c18035a06805030040750998448200000c070610801d003568050b0160000441c0c1440c151500038111107499130407a042e4000180c0d600031040000500a00c0e001b401550303254444074a10040c1c030030b00d4206201060041c400d0100003074001090301c1d80580c16150004450b520030820040044044d6169030304a0340008001c1501a4001c040320701703110096045664482d6104040c90355101e00da070070b40c0c910030050041809400400c07607490f50002d180002a41c100012074458038800882d4281c125400007400f0703180d50805810901c1c0c0350340046146d82c0c07680b82551044001e806848002d01000d4406403800c854400daa0080c02614441000c0e03c601e1454588c07242c0c52604401c0b0b400440c41031b1440f03217041c00718800b03100d80840c0d00c1d01c00d03014004000d1403401040944640d040540360078103001c035000144042007068411940750754051a02c4000b582440c0001800300c900e5100910902d02041006c0c00258440003400794214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 985757760 1250 985756510 985756547
    0xc090608150907270305030304020105070312050705070308010518010b030a270303110a0914041e06091d07031401140106020a050601050108091903030b030a0506180607 74
    0x681e200e01c10803400140040c000d0354004000e20a015801394405002e103442050311412980131683c0031040c004e55000c41c480101268810030020b00154400c001814031144a030038071030850b4071031980c40019a80d0443d082000580d021031500103140d804820180140000d0303942d603400c51004000008840c005005150507a1400000725400070050785c41188004d02110720303424030711000050091060003007002680042d0501110740100c1d030f1100200c980000302504e68140007442c00204820713403d21400030590160395241360841c0070504840450703460401e403500142d5a401c06e180c030700403903101c2c40283c0c3c002e00c003101c64002c08010010301e000c05d0ba5000180b505480806000d1940508840104080000c2c042d500015405400180e0303203824a00c6031040c4d5100e603032100011250707031008844040440d881045001100a034940100031124002c1c5000b041e8000c840001c01d141c1718542c0f02c1150540e015a080000e01d010590790304080b20301c004003606003402c219000410b510f0f1206aa84e405 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 985759010 1250 985757760 985757777
    0x130e01142403040f020604360621031b0b1e0105030c040f2307110a08030112032007090501050a031214091801030210080f18010e0102030a020c100c0906 67
    0x40d599040240c8005082d0304500580403450003800c2d000c102100c0801c03120240300d041c1100380310302160041270241d52a604841b100f601c1800300c1c0c03020508000c0820f4050100c40d101d810449201e18210004c1c550080f038a88605050000040c80c50301008a000718403030403e6801405550340c08620000c0d039104c200d42c00700cad29000c6059504e00902d03161040d00101d481814031311061003000406140329003120b48460701040c0340e420305c4035154600c000300107028102c104010301010214100b4503410074064a0100042c80c03022031040401c1d010780071780b200d2a0f40110020400c1c100c00e0b01519014140c00e0303c21b0801d040c03541c0d80f00c040c0c01c1c0e81c00c4018000d120000d008060002407034000c0d24101c5c207009000084081d20a4114440840203002c00e0f0300038010340e20468003050003500414020741d852401000d0715990421841d03070750007545114604030f540b00e10008030854001d002450003009801001650703400d4501c2c40500d05142001301074403050401200d50040380e001801c0008848080c2009403c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 985760260 1250 985759010 985759013
    0x318011b021507241508030405061621030209040c0212030109181703070f030b180a020d0516180e07050a17150a090b0901030206130e01142403040f 65
    0x10241000d0440c2035015040c81110604d41c841908000e60a40490104e1140941c40b0068036480388070314010503801402c1000031609840400014014060050200d0007035140180b00344c080310324513480200c1c0066008144242285002d1042c104034010a000030000071148042030100e82c00141702d03003003000384e54070f50b0801910070002100c141d96030b0190031800202401c00c07161202d90800e41d960000500424030001c0864003c6c4103a1101000042200c8145c03a001d6418010406004000011007a0244984d0100c3c0380180a9503004004854a01c6e00e040d1500c43c000b80412500c4007045020300b0007580400040c80c2036201075030040100e02d005c9030307122100c5005964150b00c020f0390640240e80d0200300300c0c5038a00c0c8110412205000c171401e981d020380e244a0401600c0f242421103901c9503a440041005240c068000c1c0300c40e2621207040c0c00c14940c2e80c1c20030303008890240d1011070852203a5446a0701c85c82c2c00501480d083e600c80d10443c481003150140d01c1050302005100a1100450b00c2da903e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 985761510 1250 985760260 985760273
    0xa02010e03040b04090c09060507060c0306170109111914011b06150603020910050304140312070206070206220201090b0406090617090a0305030a0e0318011b021507 72
    0x940003698203044070341d2260303104903e403403941c0030348602490146021000041c10344298180c0003251156580c1c10f0521282e0380b00e040082c030a131100203052503a503441c0040c0344104000705400070310041f800000c1d07078581410020004050241c51300d11420826000e448184600c0d800d80f01a142030903420329540083c000180c030b0410b00c035120411005460850030003005040e400100c00d1020074800143c22030740d910780540590041c0603886d41e001c00803030103990b4864402c2c0302441d88a80120382d007a18002c60301c0450b504541c40b00f1500030800c00c450081040b250307010054036800c244a44001d00e80d43c0781c40c0050000c01c500c09085005540c2019801c44156880b50b4a010080c20b003a01d655035803030365241d00181990300c451266a0100b03495030800d0306110041825030348980305041c05000e106c1c116940881e02c5034070081c2260b000c02e40e00d0f022020614800c001403c1e2600e9488842018484580c0024001d01801d038410481c0c204403119020051303c4076101c211080c69546c1409807150380c0f624003030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 985762760 1250 985761510 985761521
    0x926010c020d0207090b06190309050a060209040b010e01050a142709010f030b130212100b0a0e0c032a04080c040b061806030c0408160e161d0105160b0a1503170a0201 73
    0x46c01c01d1150b00102c81c10302001d3b0707004007040003040b035040002c1441c110041d541c00008101c0f043c040345042c40400180b6004010702d81d03907001c0b2003440529001c1802414058031090031080a201113864080110500b401800640500441c102034251a441d5130707102441707903000910001030b9040c129990001c40d1555420403115441210545580d100b0301c2130814010041c0843c1c040c80340d03001160008030114500706060042441103106031450340d4140c8144641120207484a0f0800030303102d402c1d00d00916000c0030f000982429006010300e40140c404000940314500081446403004000d035003c2d4003850401001c41b54800e0714000e07244c1ea101400441070380500c0d4040b0006d4003412441e110b07100340d840c0302c000641e00c0040c1940c8194586e141c441081d240d10325500408aa4494924818a0400c04035506650014074042d440e0680c07409510501c082d00917811290080383d00e06000e90140c0d940075061039007401000da50811450340d02c40302c61b0403c1780605601c40000002e82300c2c0074640b00390800c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 985764010 1250 985762760 985762763
    0x5070213050411041a0102150606090901090e010f020901080a051f030f02090c1e0304021f020c0f10050901080c040f03032a030926010c020d0207090b06190309 70
    0x30006031400d42051030785403072165003d6100d546810500010b0105022103030512040603801494144002d010612010201510180d4441410f10400205a80b001c0400303010301030018002c203a54410700340460a640c03085c9800c80601c0c1c0180620f0640c5d9a00070710301984440c900c0c0380880c0e9078541e10749201815660748502160b24004d8540071061240115015890910030350310107a03642e45040c03514480e03000f92080014804002c442c605c2820381405d01030340d0407500081002c0d5000810500890007103941b400302d100135810840d501401ca10f88241130b007100c00425036408503982040c00008020303205880c861814020550045943d1b007070a40f00b0396001d001804c10040a00e1b80f02d0a01a00c00d80d045410f07481410300c680d001c2441c062568510703028199040d150074561a080094001c2d40c00c0d01480d41d507110000700200d548501a090245a52070b03142da402501a15641140c0241404180c0d0000c0703d143d81000440000b17505c91000f141c8400fa94000a04040d0307030300c04402c6010380f555800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 985765260 1250 985764010 985764049
    0x1713050102040f03030e0636040f14160503060409050a06090b061908030403241d011401051f02150a0f0506040e0607110f1f05060d0f0201050702 64
    0x10041550030710070f0b42840c20b590103a00d0354840405c081040003058440c420400341c5100080800092620610b8003031215a501000890152542c8002050031a00c01d109020f51070360700c0c1c03020301039100f90040000780c2103144261b80003900419500d01030081c0c440a06050301441d900c5140c0b400703002e028801040c2c030f40e030301c000e0520401d0f6050400e07148104050790110300c10904025410081146080c9150031541940c001c1c504191441e142c81540394004013052040a19011034520301c11201e10940d4100410004503541085040c007010342143d5064441c0320178181c2135001442030b0781c2c402030300741607280c06400002289650351000b24242848541800c00085843d02400f4100c811038129244000c9a58010405d503610101003200756000402c000c0340b140c0040020490462081010380340c070700703142000c13541c1c7c070a00d00000da4030341401c01d6130040000450b250081c1041030140502d940110048401800141250702c4200380d401e6002002410301800065000454440300ca24012a502804 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 985766510 1250 985765260 985765267
    0x30405121c270e0907061d0f040603140106030b130201140702030319030509100504080702010c051204080606030f0105010f09051f0602010c030c050a12050a060302210f060105011713050102 83
    0x503481c0c0c2e00d04402e80d1305100f1401020004103903148541e0103801d0b002011020180d90035000c8083c000340006d40000c0c04c2d0015203400010012540f20480c0c0070803138482d4000010072030300e941071202410388080c3ca04116100c040300e5140c0942c0c0e00981e811079a0410030805584c0e2105407000901e1841a03c3c152888800f400440c00006a0141d0255201d074081e0390030b0b900e8ac41c10f841210000c64100f01d030700400300f02b01484584059481082442c2065100d6401c588111000a00664140d000b59001012a500800411038030742424040521103811080080c012541408401042010b86001e00240d5581d00c1c070006a00b0142c0459610301854003e460300d0b1340300d0f140c4a000780139020034000000424144402d035100703103216a04840511341c031541c1381800d10b194a802100a401e015001070025910380750040056a00c0040f2024540c01c1b00c0c8244407074401c894101810310280600f590700c1500700e24010041c50341c00c412140b80b80c4a41a111000641d10302001300300036880600054030035031010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 985767760 1250 985766510 985766519
    0x6060702090a090f0c0e0a02071a100e010807050a080328020115062d0801060c020d0614010f0801021206010806030a05121e04140909100905030405121c27 68
    0x100e80c5c0c1914030305e0446450980c3c1e810140416031041c458002c2c082001c600c0c0342040620074041c00d58200e120710742c1103004c1e030b5902c801081c4904400e8001c94095008081c00704998503011040000405804c0301450625800c80d070307800d000b40c4c410b86825100340010f044454000307100390301003000e000708608500241e54450f0300040c0810045101d140d030721904400c06108092105071540740d100d1155036021156800e1980c01c42d14503c1340f88049030001e003110108400650341e4059031344282c002c1c1c00c000704c80350314048c01c45199100b1507012040f5a4410010b085030102c115501c0d541c0144d01b0b081021550302d91030040307031900c01d43e40405042c0c2d0050660041074000300304010b00204000480c2d021000719820b40c01e9a0303500c501d00c12104640c44c0803541502d141009c100e120345c00303c17040c41074840d00701408826106803102c00d44102c515400000d0305001601d4a40c140501082a1000400790718180d600c03040d05031501c282c042020b00c00100e0b081503640f090103840c0750713100c0900d05600b960a60388 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 985769010 1250 985767760 985767773
    0x1e0304150c050a0804030b181b040212010e150a060903110a09020c150106090608061905100306030521031b0904090311070e060a03122a03030b060306060702090a090f 73
    0x68042103804400d848042454030749a5800020b10035001230140146860320390310019100c0a01034403e401c83e40034880341540300d950740b12403030090080060000040c070305200c50441c0e031400a80740e2480303444d51010601081e030740030300580c0a41e68880c03c40c20141c001040041d00e212142e600c541100f50001aa20119410108402d9510300081c1c503501648e0362501010345400c1c0d410f000e2400020149000181c203490003010300802c224540c0c0b12006100d84030808900c003104000260008030740c0b105810000c110301009840640141004101822038080c0d00c155543d03c070141c603404000c40720000302825880c90000711400660001c01c1005001c00514000c1c0447d2254a107584e864040e0316000603001a42d4010140300d0000100904802030544ea18183c00041102d83c03070003000404801c08019103000842c603100c003c40c003500c072040800a450020300361415552240c0c01002d050044c0a070649425083e00c0f581541180e19600c1583daa01d02c510041810700005000002d400e20343c9002d00c00c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 985770260 1250 985769010 985769017
    0x30602030717011712090402070605040b09060108151321090801060f050607030f14130816050604150c1520031014061606050105031e0304150c050a08 66
    0x1c680c5070b002e40c03603a84c1d06a0f10030301054190181c041604210307011690f103400380006100e0510300070001410854180ca40d1030850760111801c5a4101c4200300303110808004200080c010000c071401044007180344500107442a8014010924030b10450205004202c0c00002a42074007075107190589030f995003940c009056588a03c2140015480e05901140e981a2813203441c054600203070a03a132802c0c099030b5084032420041b400090400001046260301040004018031545c180c19081c034a01c1e030704041c29035061245c1210f09625040f0a0b90040041e0340740d0406507070846108120121040001c070000b6541d60010320350050150203102c06443c1c4d030004544c8054010b0091403030810789400704c10444043d500c000d0750b890070810040d5500b0410488000804490040c1c0509140e051907a0005403400c00c200c00942182d8982d00c1d00300502050404002481c00c2948924a40b89124a20202c0e1600c81c802e81c002d25200e110322407108a8442d00500c0744580c1194031008842010441d41000c105580 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 985771510 1250 985770260 985770287
    0x10c030f030914010b150c07140a080a0605060418020a15051b030a17040c03170d05040303200403030c14190f06050105061206310506030610031203020d060306020307 73
    0x400104e01c120040b07481b10903943d5807038900f0020b2900c541020800071400320101c0c100c1d40d22440211010610900c28400c000740c15226200100351403e00000b044165800130205800707a41e03840b1403000240e40c818582c2c4044074815414582c102105035000c030b45500c901130328080c405407810085000a00000000c10022400e6a80c2d0354070300e1000d800380c0e80d5144007510003a000c4040104180301051403800751242c0a83c02c4000c96160103105009802034800c211010303000f00e43d684050003c0303a0200002d6221517803092004c01d26244c03c4d550040c0c2061041600600b0004454a0004203100100140300001f0740c0912403281c010007610340021035500000d0100d8000e810300e0000992030400c0c905a816007200c0380b807101115680e03a405e0014601c15040b400d050319038142074419002e0b201d4400b001100300b0f4850041006e1500f24149843c050020f0048104014401400c1020030070300680c14008106524000d44d0710050030020030003a08031900068840f503c00010311481e2a0000301c210802c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 985772760 1250 985771510 985771519
    0x91b080606040f060b27180a050603210310051f030c020601050604060509150c10110313290705030610450305150a0209010c030f030914010b 62
    0x8424600014084d074800b48541c1d00c0c08a420302070000c05884404400c2c81c091034140c80880030a000500051642ea6000855403e8020910600c504848180129680480b0540042201d0003202c1422410200b00103030905100380040086108034000f030351204010000101a24901c1c450010130b440301003204868003000c07070310b0910f0520303856001203030480c12100c0060840e814245400710543d0190300201e5040c1e4806a900880b01810f4010009001d40340b41400081c64984245d5220204841e0380ca001c02c414120240104030b410b071441c00d40e04801540c0105a8244050080121003100096480b42d04420700407604001156500c20003440c07003604d04845071100745641235002c2d40c550002400120300c1c01922214841104032001c4403820145510108422040e82c060015901541681040b1103a0700003c80e02c06403a0000490360f0340010402500b1840c00c0a281c0c00688495072201000b42402401e4104502c4c0c14000d40c8030444040e049401c07000307259144120240280740d942c59885c0324 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 985774010 1250 985772760 985772771
    0x7020d08070908030f07050316050115090209130e0f152d04030302031b040902040801060b030c0307120b0409050c0a0b0a141303170a1719091b08060604 67
    0x40c144070b6440801140c190700055443d010207080b2000c2d41d40d0200384251014441040f0780c040c401d40400f04404040e008030700000322014090511401d4000039484500c030503005001284056580c00c8140c002d101001c01d0020f03481c1d201944203404d100d40e0590514050085410b07849004485401043c401c00d0a11180000e410b03d454a0b40d240c1e0240700c03031760800c04d404500000d0001740070340e006540010b0602001d024032071103038580300d440e039105030480c0d4400c540100e41040760325024025540507065492400b030941c640110900807070f00004080d40c04020f003165940a80070304030707032041040c0c407130240c8140700007001410001e075500c0340e80c0911401000c0c0c0f0100021440160030a43e40400050f542d030112100d20112200c0741500007080041d50462001070000009164241d45103100c0350700c280c3c13035481c1c101d04a0058401c8448450030116000000c0030800d55000e04034519250700d198110001c1c4140007030a0608040240c0051107001c180e0002000c41c3c0450001020341c800c51080300c080c0302 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 985775260 1250 985774010 985774021
    0x20c07050a061e032304020406050d03020109050601051c0f0c031e0213020a051204050309030303010305060106080c040f060f0e1309050c041a12120a0302070227180a0b07020d08 78
    0x102d80198201e0717025414000d81745c808074801c803414035402c1400200003142043d2940002041913007810812000741c0e6441c2d484208010042c040280140401c0701e03c80c00150082c880400d046407004401000443e54200c5031041020505041e406543c12071100310105903090903034080004502400d074481d400c1c0300000b049105040c000c84940c0b203000e03a1218244041d022891603c207202038007c031600e00050280003c2603c0401c095030007140140b00611440d45050400f42001401070040d407900074040200f4096081c481203284200c40300c52404c4c65034001c0d121411500f0040160340f03264000503d4040c006881896000f0b04141805175054604108070f900030042181c1d84520f0081d0380300a00700000f0384038900860802c2400ca00317136080d2031840d00f21200f050002e611620f8103001080d40424a20103605041c480c1000c19007d80c4d11500c10081e0107000c00711001c10041090510000d40400c4a1503c8001d01141035000d40c010303151606400c1100e4003940f81d040380c402120000d0a10f800090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 985776510 1250 985775260 985775267
    0x36440d0e0601030c1203032301051e06041a0d0908090a05041a010f2a0b07180b0f22030618030507150e0604050a0b0703020c030904020c07050a061e 65
    0x20b0499512001200d607542c41e08001008088a108041c0e080c59950420802c813100520170b001001515a002e00559604050130842d5400c203012140c00c1415182016103403513103500c8102d03019901c0013130b00702000c440b017074610f0a21407140c1e110291000381000c4500e820407d10030050900c9130b00803034082e29059141c0041c803049841c114912440c4000c07486c403528455010780701e030f1594070002d458040d0400030b4001c0740c207c61440490382c64654451809601051006404030300342c108945203040425480e00d640d01410888a50040c541c180900141d040441c240b00b80883c1c0c0000c003172940c80d40d020a00396415824200c4ac41c1300c25503000382000e41c084019200b9145c2e540766542e1540b2294200091500c61041c55500b105440c00306550b40e003d88841c0440c20001d40c1d11542c402c43c014281c0d06010b10b03015060001c0a40714006160040c440351941d0702c008000d42e00c0c19107007502c0061711000d8000e02c0603d4001e0980c0520742140c0c64140104409a100350714603802c8070034070b03c024000c100c2d092044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 985777760 1250 985776510 985776523
    0x23100e03070305071e21020613111e0d032003040608040b0c3a0b030a0803100902121506070b0a0506031036440d0e 51
    0x180042c0e004c0000000190003000c0c2501035141e1110100d085031026951900586050010100816a641030100800358108540f0f5881900d0044420010311180c1e1000b10b4541110080d03032160341401e1400d0010039945030140010309008140e0310100c1407904028104808042402c1d04203450b00031400c8032102c00000301e070100ca00d680d0b02c820f0150f6641c0c1361410340000140551410050130403026025051409030b500912100785180700401403618081403801c140c3c6130301e0140960501c0d900001654001c1030001a00d41c11540310355403942c1d2020a016809519040410424401300b80e0540030070311000314921801d010b00661010741003100400c03485018030f02c1e008100c02c3c6003900007080041d10742c000c0303038001c100a03040b18842d211460480e0309a5415000d444041e0002e80102c2030000c4200a1a115613041900b0380c1e0040340a54460f8019802640d80c140708540000c2c100b40d003424601c94012080c142800c1d05802501c100c1d15840c10030b0f6220b600007010a5052100c4031240d0800402d04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 985779010 1250 985777760 985777763
    0x207020d12020f1213080c280801021c0c170a0e0307021c0c0b0f0d02162018010506070b04031206080304030b361014060306010f2123100e0307 63
    0x10288801d1030000011742d01d2000c0c9030704404110748c403440051244800d001034009000079072481402403e9002d074142c11516140412010814031040c5844051200045181c00000050340856000e251b40c610f1840c521403104002e4000c20000301c50700c8540c44400140d01d21a1094218065060380c072030746000c2070b010704481c4004c100d60820500c111103075203034010000e001c07610751700210340041901d5240070070745040886060740030514901400c0d85000c803810020014005030780e124550510010800078000c2030310040044d02c00300007103410305028091481820035901030034048103465181c1a92250458031003110b9451146000c510303060900e10340018000c5000340c443c07008c2c0418602c9150301a02c5c0000c920028003480c0c905c200403401901804540030080541e2a9160034190141454920140c0c411031180c0d4941100340301c0c110312801d5821144005002220802c50103041c240944001c0c030722071842d20307140c1c0c0841c112510404a00034611400e5031104101806c003040301c05840b486004070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 985780260 1250 985779010 985779019
    0xc1b030f02010b0d1406330f060304261201050609060f0706061508071e050409060605071a0606070f0215120708060f01050d0e0c0405070518040207020d12020f1213080c 74
    0x80401203e01c10366103040c810403004000607240c5000d0b00104103542d00540c2c06440720305414400b030117140350004419011145462615140003000310502c00c0703020b03060054fe8810640010900a156205000d80f0840111041c0301c6ea9502400d14014005201c64480c0b40c102c9407845a006010758001e02100c0e01c03c441c1c50f1600c05445007101c0503c0c4c42c1342e03007030701c0781c03c051010034000428141c1c56842a00040c25881d2a0241e83d54072034101140142d11606140c440695150200500c5032178050a99500a500400c034480300c49462001074654211540651248040419080d500c1c00c0304000c0917002e01c0954941c148651640300c20b000c106441c0c40ca14a012070320400215402c000550310440c801d8000c04140c40e90500e016001400752042035541c040040d02c0070030700712410781a010940d8004141210118542210385d4049605000180e00c098801c030480c01504210074000d000307040141d5410b01c16604034a1100e00011440d401496141c80944042000400c034000c00069048a9070340c01003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 985781510 1250 985780260 985780321
    0xe060a1a0f04020702040906060f080c062811010f0b12010b0a0611010902090906010e010f080c15130b0418060305100c09150302030a0c1b030f02010b0d1406 69
    0x42c00701940c48110201c0c0c00540c3c690140003c20750304d104490240c10342107103260400e4585043c45150144c07460300203108040c20046450307064110000300c0542c80201003c2e541e01e04138004142c2e004109440303140b0039942400d081d010359403119403110000c40400c03140100e0080a01c4241400c032100d001c0d4181d081030214006124541c00768150160200180c0c0002c142c4011a42c08220078034000e807500b113129441000140903040c2812100f85c050041445400d91300c52410141e295200004181c85006281d8402d1078030701e00300d030b4004075030510203004003488005981b00d052005a5115200b605280c081c0013115070b690030740034021041200d401400510703000f594485904010312110039044c040c05181080000c1901da07800d030481e400402c82d1030040c1c60b8034007124441d00380d03124114007104000c4c200011000741c800d03400d912021150507140a00d00001048021390051403d04c0b090f40e408200950518204000c0302c0d40040c040c00c0b00015281a81c444406107a07043c802001320001074003206 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 985782760 1250 985781510 985781539
    0xd0c0806010602161d190207020d380112060908130f060201020f04090b0303070c06030c0f170a0e010b0406141504060c0b310c0b03091509030d0e060a1a 67
    0x84414006e8031a510000629042c16940015540340c0803000407036806c26542108000b141401d20050b0660075800841c0c2a40800300c40030424901050040c49400c0d20044040c00074440319074801a011b940c0003458966400c82e50311180d803c0c11107845440c2c03001c84100d03404a045441802512038081c0d40c00c008034245414180c40304080c154002800390144030600a0358045100084814028110398400007400c1c03821090040004003620252014400c0c000400c95030810700c1000710703620404601c4005804201c1e0802103003d481c113406015402400d103000403481035401010303c12844001c8030360f9500c10444441c0c0400500a03841014080b54080d80c00002088000140a500c4070001c03640d00e095006440000442449104048020750300002c0107008203d2804256009420550061415031900b5116155120f5103440383d40f095041d45404207685020400030350721142c403000d0050000c2d01c5208080342d030b1a1401c403200741c0702e04e0070041c038030300b0380384482801d40c0c1c0910026126006180c0039 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 985784010 1250 985782760 985782781
    0x50703152301110f1c110102030c0703050711100203090102060f01080303010b1b03030a0504050f010b100c060b031c0207141005210a0506010e0f0a050d0c0806010602161d 75
    0x8080002d0840c02075840610180c0c0041c4014007a044401c1c5d4151503204600e40000c000395840703412030744242e104005000b2024401403d4034076040d45490840d55820642c80c050724820300e00c501c10750b08450070041c1408290780102c00741ca884070702a403c40781980da410307404001d414000c0c840e40d091600100014040c000d14140240720121a03c002183d8010f0f401150600c1c4d0350086a13082101c80d562811b1008000080c00100111800c0314028410340c0c902c80002400d0b209040c00d00e905014488030058100241070f00141c03044a030040544013078005003040303246407200b0619580c00500602c8070100e403100b400810700d01c8000c00585107091103404c02000b03480660003170056001400d84004c0311543c209040b42c56a12524038140c010800d410b02c00005459810390401c0c5501c0350751700078400d10113500d17210318040c01c640d011200704142c901c09041034034900b05e468001010a0040b10b002223240341e0009403980c02e41c9800ca859071401e503694880707101c03c18004041c290501c1c03a00000708107403910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 985785260 1250 985784010 985784027
    0x17070f02030c03130302040e03090907052d070203010b150a0503070915090e06060708030c03041e1101080c04120605090115140f010305042f04050703152301 69
    0x600303004036403030101806030385407030340e04a0f401d504100a042d100c18403c600b0240926410305032404002c50511960740300062005800034031000030480003140009000c03120340034806085030001c8224a4082507201120705907800400180e0007503003020380d082c0303072810444500f0300d040c0410000242000124031048601f580f0181440c007c00ca1a1003010801d02010f2100101024a6880300100c0e2464006004052680200b481b8401c1c2e0040c043c1e040450140c5c012070303501c01117106030207a50ba5254645065130480d240c510745886039018558100f0800000101d04803140241c96015955a0350741039100e4038031890044c0008042c0c241d802000044842d00701c3c64004c3c09050010605819000014488404e1b96000c0c2d403880303182120380c542c0c3d418018004c4640100070700c0e0a004515160312001c0306140c0d030240c0340a21850f5003d0801601c0800460742c09066002441072020b4102140e000b00078040d10225400e0158016100040c460311010241a04042c0c0407016103240e0140c800640c0c400d0b6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 985786510 1250 985785260 985785287
    0x2090103140c0a060c030207080c24120f01080705040912030b030a14030703080108070f06180b18040b03010509100b060d05040c0810020721050c010509010501060f1707 74
    0x1080b0301202e075090703407a54114006400c280d43e48541101540c10020300e4420b50b588000c43c1130300488002c524035103034414840b5104e800b02c00f4400607000070001841070f5203d503100034068890080107100c002000c0c1d000140c12502000300f155985600c1da41003000700d41c140c10b001020030b4030b64a1a04e840500075041443c090f440141070351580741c002e0300d4501c0c00340c00d00e150300c10803a000003c82c9010035802c6203c0502514842d0f00174500907003015150741c262041d5002d50703014000130401c114418a10710f49804054121003040c2902c40c2d01c3d1554020250001c080c4a910403030400210f0012814144107080c0314290b8034000301041d100c910a8400185140072040b50006020003d10100d00f10900513503000381d00c034a14000320325160503d80307402e00f00003101c2c034000b290040180d0310109002e01140145003609a842c840c800b00034134001c1e03426108140b20304145508006c100651500c0661015040319000e40f1904c00070047e0361012a010107000c00c019200002590116008510580101100c413 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 985787760 1250 985786510 985786513
    0x14030103020d14010e060a0c0e060304082a0312090a170a0905120a0b0105180c18031c180815040f1b03051006031e020f120109060b030a0209010314 65
    0x1c19003031050030300f564480c04805c60361343d1001041c001c04451a00c241c43d030010580c130b800320301c0820350000a817031444050400703800c60a000ca42c164100c01c10620400f08460352503803924140c1072098109440750081c40d02c0c03541040c1a01d0000d0a90391011860f0180a0b030700100c0349658900354000b4651507009003a03160200940540042020b4548006441d1201f910b40010121b10202e850440590301050300458051502410314645e0002c10407011034000f9440d10209880c0c04004140307800f542c6c0d01c8100c8030360510030715400007480e035146000c0c0c401200b216a907071008200d00b00000c4510002510607009203901041400b07074881c49601000740c1091207081c2c2140041002e44900c100314074040ca02035220501c0410030410000304100b00c0b030701c0c1c800441d001c0c0316440c81c680f01d80c408043ea0040e035415038000703001610211750b20301070032901d401c2d00108102c45d5800b107030181c00d000313040c4000c0444140e490090882141d00e00015000750042d40100786070010f0382959502280a0140440728500b0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 985789010 1250 985787760 985787783
    0xf1a01080d0f0207120c0503121e0a0201200307020f010501050609130f0e0f07060c030c0b09100f0b0f04060e1311040c0c05010f06060f2712050d14030103020d 70
    0x9100c00d1080d17105041c0224203042c0310906100030103042070354070700b00808510801c103c0d8148000210600b50001d40c0c50b6548661681e0421000ba4050400c04106204140c000710851054600400155000b103903c0e600f2a0108030541803410300300e131400c4c00780580c070900500c08554149852145c00b10044c5001102148228a1481079800d503202d5007180401c80e0020400d145003010108508002065145401040301e2303500d40f4060000e502c20391001d482c051650740026104c00b020403400380e40a146210412812004441d21001440c6619400344610160f030000611440c1078003445043d513028084220385510b400310350f5071082441046c2203510001c140e49404c401d07a035a20445c49094425100c6036102d07681c51604908407685004508e0b8164130b000d030f0074814542d0028080600740a20b0070068a511f0241074030501c540e8010307100c40301d589080b21000c1007039907a0500022a0314402c80071554138a18544090300e0014152000b2048000148010800740c0342c64807117000418090b05a6000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 985790260 1250 985789010 985789019
    0x230c13060902040f051003050f0c0c1c030213061e18090e1f020c070b0901030207020637080f060d0f031805030a0804090207020105160f1a01080d0f0207 67
    0x59030080c0c4d0084140700c400280030006802d101d05040e06084442c40d0410162801c1181c480300c00c08050500c0e81503c101203418500c2e880204504441c0c005e8407100c01d043c050140304000c01940c030030a201100070b41c0e60240051038900690081890303070030001c000c00c5d48030341d0740d04102d881030b030b403410840fa02c11100e090018107a8254031905c0400205900500504142041c464400c150170981ca00785251040000b881071420205001c2c090301ea8503220b040d0784a0394803004130b0180c003840d40003a40c0980006440c81100304001c000010402c040002d0706812080c116903d012514018071950101300c002c03000454000010300780c9540710303500400c501a440016101e1020507140b0782e00c200c0202d900c0c11011000c00b039181040000800f402c40041c4508075060351461084e0240d07114800b401c40c0c0101c0c0e04011603000c0c2003a80c060300b8188007408024010f074100030308950128802541c81c01d50b000a00907204040b1040b0300d0507154500001c14910b0710301c0504503103580030b40d440141107000f04180482c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 985791366 1106 985790260 985790279
    0x90b0901030908130801140109021204060b010233090706020d0507020d0816030e03010504020d11010309060c0905010e0d0201211404030c230c1306 65
    0x9100041c9141151041c00f030307044080c40c110801d13880480d54010540c0111803070084511010500d990340c80c0700c11704074814000003c8181c0820130000f00480d00580000785512010b10407900c0d001d51f0082d000c100c88880200380b00107508201c07481d00004041441c0c0641001c0b240c0d0280001a10b8244040d564015000c20081407000124084096560b451900c802650700003869070340d40c03900b441c400140e240001d181100070581c002d544032914181441000d200e1030307019101c16105080b985a40c8944121592514101622a149080003481c14002c00350106001d032552450380d4240780c000341020818100c03050180390b110a240380540e038012040621030030450349510800d4101600d1001500d01d03100d020203410040400d0000305640b041180001134019030018500b129a02c2d411581030302c1401d1090425401600103489a1404414000c0142090400064415610460b11 = true := by decide +kernel

theorem cover : BRFrame.Cov 985611510 985791366 := by
  have h0 := BRFrame.cov_init 985611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 985611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 985611510 ≤ n) (h2 : n < 985791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
