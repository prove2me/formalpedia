-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1002
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:46:01.888685+00:00
-- url     : https://prove2.me/submissions/7995830e-67a6-4b52-8a62-d679a8c0750f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 180035971 ≤ n < 180215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 180037221 1250 180035971 180035981
    0x3020616060e0606210c0316060806010e0a060f0905130507110316080702030307050601180c05030903040909050709050702010c080106080f0103080a050f031f0e010605030606030a0f0e01 82
    0x20084204105014400d10070b203032903103400c442c00d6922210540f08040548825012405a03400c41000c0382c01103101440820700d48000324449120302c20040200700b00d0307180d00c01580c951184081c40c010243c25812401b049500d0404d0241c0d00c14001b0a0b10f464040b40c0c4a10a11801050001c20400d0034010300c7c0442c400805003580c2c8100003034001140c624401c4000012a03910451800160048829076190300c41250040002282c0c1804100241400f04200300316580c0070300509000d61a8581e62082c1000c00c80f81e84a016000380b1806000304881c3c1000403065400302c42000307202241c802d0291030007604213140e540150b4106c070700d440148007404e40c1c15801005842c40e2a141c509440e43c131381c1e105aa00030303c11240e80401d804590014000501a0005440140010700f48181000904e6840d626540c2007110740745074030700441e001140c1200799519840020100100c035a401c950420600074a03d00c401040240910000404a000308c0b2940e07010b02100312001c0400c2101a60f000c0b0318034080c01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 180038471 1250 180037221 180037223
    0xf040f1a04032d020d1a090703031706060705030c010903030b06092d0a14040507030b0d03050a0e0405011d0105120309011107030b0702030d0f050c0901080402030703020616 76
    0x1040110218040a0035088900340c03604a0310b031403180c807040e04030a44038451070740300b40c081064090340c0c1c6401610b84c10410308615204501d090004101880f800302074030750003014141030f0390210b1001c10200344c021812059084102c030000081e55540408a0b0740751140060080003444000307100103894038103504c042460b601c01d50b01408400d03804410000180030305020720754808505c49545030303403040503010125080c0d000e0240e40442100d0f4400500820b4071584203020404104001d9290b502c3e00c0d1181581c4038250f41010045115024040303020f29070b04410003401e101c4005442c008040c0141d0904d211004014810f015540e10760010206000401c0442440c0780368400000c9031600d4425842e11108010781f00075400d0115020045540714152490303408a03014090010000c5030743d201c0300078810310706a002540d40e000502044421031f4460712055020500d81006c2c4604408540b045640d04c44013481d00785055101c03400040e05001440e40002d500c00c40000740e1544420135100540015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 180039721 1250 180038471 180038489
    0xa05070f06080606040312030518370308010302060a17070e0102011a1c06060504020f0909100807050402030a021b07180902130e070305100b04110a090303030e01020f040f 75
    0x583c07203031002d00200e406540030040007c400c07100c2e0146c5440c03180e40140e0b80324040c01d0340c660303c038085810040e04041221141508441c10400342c4100d040d201e19810100f0480040042206c140984000304119010b0200a1051030b00148402d03c0610072585c80612031007964440b4a6130500500c051b241d241c100202901550030050921041d0150188010760100d010740358956412901444014a85143c08112001e682c6d800007c5000d4465101600c40d180075908010780d1000400100050464014000035070840002c0f41809940e00114002048501c10f450140c1c4030307201c092a4501a002e00b900c048282417003541004c410803000a4628201d43d10002410500c50074001c00701d090300d404220294010040711140c07200786585610800050641c0d43c1134409003500d90b0f031410b04010061034060b0f84682c446540d0042c03881d2a110708900000c5e04e443d181e1070403001c800d001d003a46120307210140070301d43c0e80c1d0500100c00f0008c1d0100e0b1118132496421a6503951150044585c41c81e50703000784100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 180040971 1250 180039721 180039737
    0xe01030308180c010809280b10230609100f0906110a08090d020d0606050f0603190902010315120b010504050129090402040b030601030b09190e0a05070f06 68
    0x180a500810b911008403016000d0680320300741e80010340302040050500c21032842109041c030302950800540d4002075510024181c081c09190810011416018000e403c0303030312184004020708050b250041c1030802ca6511818103000c100c81c0011854014118116005100304840d2000d90b5809603003100030041580394043c5107a1121011160365030038211050f2203600005008021a1032103014203215000109140c48101140e0f011941c500d81600045603102d0f00c90005000c1d80c500008092074406080c0e500a04510b005810b80703005040100020f021140d440c9c00b05410359110f5084810209020704075044400d40d6551008a40800d074002941c3c80408500081aa403609015050481342d00341441360700002d000401c5d5003645c10b01405501084c200300f1108a65031a180050002402404039071510703450400e0000d002e40303c0040c0c25910815803031081190350440b080c42d542c002e0580c1000040c000401c0c0d0100c03450401d80391400b0b0160310604100150a20702d80c1040c0c1c060711940e6540e020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 180042221 1250 180040971 180040981
    0xf0207120c0515072001020f0c030a1205040305031801060f140909010b0607081c051503010c0807080c0f0d0203040c0609080d0503070806030c12030d0b060c030901051e03010e01030308 81
    0x260303c080c195002c00000340613400040c6400b20120311418080c400c400014a0040b1804008440f07030700005460069410108940e5030194020748107a00c25400785c0000d10540c42d00341c0e40104030f8800140012100f15001c0c1c01101304940961003180134190314160301101c0760719070001441c1a0412001a4860707542d00700000c9040f88113005010703401001500490030040a55140a11078111032a0005c0060a4010340d183c140018040c00c0e001d05041003880b640206000149802e4800320101c0c4410301c0406001d0003406948005401e510020a1094940380e20540c8002c901920402400e40d04c003600100500041c891802615000c640d51500c48440b425a1313110350f151100228900307030010a80500000f50741178002d1501ca940800000c00b910214410000046c5182040740800c0900e584007148600340350f00ea92203111030b485401c58151341003111101c0c0740b03a40c900c6800300480c10801d001c981069100b40201c1d0305082e68003140d007100c0d100d42e16200c400c201d00c80d00344001c0d000280a400421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 180043471 1250 180042221 180042253
    0xf0601090515120607030b031903051e0901080703020d0b030709060504060e071b1103100501080607050403260702090117010b010c030e190b0703110f0c10030f0207120c05 75
    0x10a140340f90001500c22980c49000c1940204207240100d60540600b03503103094140d5030a0b000d0f130b0820784207458a039100c40d103042c0c841802900c02118458800c81c00c202e19240d5030303000141c0c5030b0b00c1050782c035000d662000b1120305a0b01500344034016640501c02c0d52404200c01e103031354212109842c030503901040002c0d95812090100b1000741c64030004652203540c4c4440c1224506007041395540501860b0300100c1416000c249072156110003c4048d80d0764200510034a881480900d81040c042d140580c01c1c181107886145000b68807030041c1070442d45c006512600b40e0300304c6054403d1150001c0c4440c50660f55010115022854441c04070403a519010341ea0b500c641c041c1c0a6000308903016a901140540d014041c07159141c0050340951540a500340c0000b41981b2100050008602c280d0302d2216040180c03140314949540042c0c0c51407150854124032010b0344480d601344200c1c03021481d02003002c41c06040c0c2c000080c0700d1942c0207040703540c07001e25011525421545802d4054801ea04442d102d0714101c1806e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 180044721 1250 180043471 180043489
    0x110d0e0a0f080d09021c03090503061e09070801090f1514061306091a090f012d12120806010804050d050901030e06040b070f08011a03090f0601090515 66
    0x3403a1100c00881c40340801d030b061001d450b8000d012a0300040c8461250005070b200e805445010710640c9100190200b0907912442c55001001c0c03c0e0002d0203070381440328606164540d0041e81d2105070a0a00c00540041010824000100b0611000704190512424070010b82c0c0341c0c007003040e210605c1c500410008c0b009648548001207003030341e0480b105a25400200a00854010000c072a86a114407020070300b00c80a02c42c8140d0f0400c08900441c0d010f120b0300c14846203c00003000c001d8118809001004042e02d404401a0207428404007030110100014102c0a007085a402070605240c8450a940401c40e0200310f40c0e42420641e00c6005890303458400450710240100d900034040e800a02c41c2200c401d000b5001ba05100300141004583c5400500640b45009403c07035081c0e4000d816001480011a01b2424407208065030b13150000f029810321524025001404034801610400000021280c807004c0c010003416070122000d94440c0e5070b40e00c1c440000b600050360558103a200101c0500b1a43c43c0c51600 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 180045971 1250 180044721 180044723
    0xd091406030a020a02010902130b0a090b0d0b040302250f090e0a03080702120304050d030b0312070209070e040e060105040b0402070c0e070908030316020d09050d0f0312110d0e0a 78
    0x85510310b03a03a40310910301a4000304000020340d07403560904001680c5415902c14292620341c0700141ca840b041042080d0009142c0c40320742c240703140c0030507000140c80c0c2550441000b50400b2001710035031140d1078106d20f00b4528000c010302008002d081008075030304010341c44c012a1000410482d000b40c07100301001c01c80d400311420b159140c0c07012402d86d000a02900070700364090694011f40d40c901c1080850803c00da442142c0854050300003403006090340780c140c0305854507268142d008100b0240d035110015800e1045c1340020344290342c01030004003010300c2103910f10520707a0042d0003809002460141d040d039600083c025240311b07604088042111341403520035240d0881e005100f00b101c0900e403400040309528050314060030070070100c8000ca2100c82c00c00c0154000c034240d01841c0d10040b41160000d04200007540c3c8a010040c01d80c6040200f580c840300e44150664200b042e084030f007480c9103001c0c0c13015848407154504050504103420301c92862500908401d12403a0400c0c004a0b0a084425444e0140114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 180047221 1250 180045971 180045979
    0x30f070314063106060b070602040e0705070c090f0209040905010b040e0d091403010f0e030c01060f0f090b0d141b04020c071205030d0f0207140f0705010f0c0b04050d0914 75
    0x41881c3c501c0101100c42405010740f6000400c60307183c00f90542140d2185400791074494001904202e1440d40380340c0c9903408141d6150050502d24142c1c0c2e00071030303030341c040c841c515a49455100030214583c0c00e0341100c3c614603000740100f140d034690345080d5000e420b114059a105914109074490362a5010500d240d440805540c0e03e0102401c2c1801d99420310100c0e24400d806650344d0001d030300035400601c1104480c02a5a00460711000c0700e2480a0070342d151034004048110800c0c204004264802d20701c0030036545101c101003400802d44000ca294581e08000140c00c11003d040018010680415001052008207171510001b80c000401d000503407044940b100d0030342d8442c00040040c0b10001c040001a80d1060050303e141144101d04442500c420080200480350b002841008000003108015900f8041c1009071030654580200c168440b210b5106072030500000f001d60103411403240620214450b8015030071040380c03c090515555811420082c540442d41c203c60120303a6006c051031040c50500024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 180048471 1250 180047221 180047281
    0x40b0103111e0103020c070b070506190216020105070f061b0e0904020a17240106090602160302041505060304080a2703030c02121005090c150414030f07031406 70
    0x42c0110001d600030390341c010b6a4000d0a02c045000440c0c0c4004020b042c1c0103000500341c038102000c00400003080100719401052040180146c43c0c0c14100843c0011074090038000c0e02d1707078554200108420b0400318000c0006103041c0c02403101d5030000203101c0e403c202a65031541d51198034024406250340075940a50b0003182042c1c1042001c4040082606032105c2c0402d683c0741908c1c04100c2100c0c01c075010a2031001e03000040c014001135910411a600070304851008140101084180c01c5000300f0743d0101a015540f0f6840d41a42c4420008029004080c0504070543d24030709810491500d41020b030400300080c941404110814506400a1b40f03001c01120390b0f9081c20b0b141d0764090318a0082d20404903000909180c1d200000d5505010400011030003100124481c9082c603181803c00d03184241007403150a1182c90b0a10784200e54058405680c0ba0000421611826000003803030070040c06d111450302d00c1149804010420044070b0080101c91701d0045440d2500d40c40c18552402415062400c9411104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 180049721 1250 180048471 180048529
    0x10c0b010b0a030207080c1513202101020c01050c13060806010210020d05090d02120a0509192304090b13020409171e0c070501110c0603040b010311 65
    0x210000b050118180c1c00d00501c0d081d02a0b54090b0581c00c0f4000a480a800154094000001c2d50714103a47c405000f00071310382000b50340e960300761a055203155241340301c100c5402815241d0700c48141c9452071240604020307410354014080c06010790f2103a07109188550a00e400706c0c50105050301a2040c000001e001e0410290600744115040e40c00100700d6811841402c50540c503c000501c02401c0a07060904041003518050038a0f82c500315900c400340c411035000c030b20102d10307105100064814000607403900a1b55180050300003000b514100300c244205140e041c00004400244020803440740c5000d80704203d40e541d56004006c21184a207201230480161800000c420602c3c80ca01e40e815144000e000180c424034640714000c0350100d00960440c05240022045010000c81c0040d002844c1d0301100c4a14111000310103a8487c00d16104043c14031116010440c1282418000c01c140c00401400f0151a40f600d41000080c5d540c003031000391111180d0211404843c188044004031100009100c1c034010444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 180050971 1250 180049721 180049739
    0x180c03021002030412060504060b22091a160f0e011d130510080f0313031e12030218060c0c09090c09010e0703050906150d1109040311060105010c0b01 66
    0x2041c08008114001040082503440c07600c070603e035085000c2c510028803071515182440c212222000703901d100c1c220850070144004018a40240c140e800034202103604950b81c070f003018074030400101c4411003080207410040005000c100210944440340c1e034002c84a01c04010a40b80c5002c061030003800035026080414414907801d01d0b050b404030000d0303c2b040100010384102002c0f61010703107250050740c2c0e03a01c1d810842c280342003000645d0800240e014500d00024241c0d01e45038261507110003810000b11000080f02c4c1c41014080000d00c3e82c00c5140c0491248170007100078000d50005031030110119a52081c0c00c0103003004003d132051303295000e0041030070140150404c4042d0200901500c410300c180ea19080c52030b200c401c41e01d40201100c2001d01143c1c1000344000d001d0700c1c0010f1038841c459110300100020303000e400101d94060034040c1c43c103446440b807604000e20100c011490040d0080c4d01003090008056200011140550904017903419a0340c80d02c0c011280301d101c90b0405020842d030305006200000c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 180052221 1250 180050971 180050989
    0x120b0702071e21061b0801140d0605040201030b0303340302060604090c051008011406030903040614040314060a050a18080d270c06081b0a0c050f0a0501180c0302 71
    0x50381103c2003929a0265980c10240c07183c00c40114500d5010340409488140c203d001940900f10302c03500408512062404204401d000d01009494641c0703400204044d039010344c1c85219480b20141c20399985001c8101f50481014441d0709203c01400051040c020488201607032100e0030f603056001c0c04c0d4a499050401000d0305001505032040300c00c0800005040d500c00c00d0400c0c1c10342e1580c0380c0c44819850b01007209140802105450b0040d90204204a4958800310880c0c081d103081e4148054800100c9280256901498000500603d103c0384441100640019480c1c800c04111400b4882c5540303010114040c0d400004080c0403041c050105140081d40d010098204082c030007100146c0c0e08142c1a08510403001002100c0381c80b03510600e9003060010003c001c2002d44118140800700d800c020804420385000c42d103001d810a1808114818158481c4c02c24400c2150040c0071a0100a40700ca0225260102c0c43c0d011a0f41e0343c40c0088104d0003240c0b41051044540e0410010401e1a245030280700b80f0703079 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 180053471 1250 180052221 180052259
    0xc020603150a1520030406020309091b0d0e1902011d0d060614150304110108270d0f08010f0510020f0d1d06090d02060a0306120b0702071e 61
    0x42c0481802180340e40101d29100d5078191107039524420240c0c42c5102514808110841d4101034104100c14012a600041200c40c19401919100410340d220300008145100380080d4210b800400180c80e0340e4840560040c0b0409101c8009995840e40515114202154284802404254116001e0380c188440b880e65400c00200609102d014960a9469078200c6907541c200c0220721071903207104480d506000e128511680c0607000145c0c510b081c10b8488446c503880d5261018100719442001400345642055175003080308140019040168840719001d4030358024404881c00240f146204501e50342c45008501d040703407024100ba8894500b40030034003080300c11008078030b07042d841000303241005032404020340024481c00d03550760340d0104a000800740c1c1001d140d0308001e01c07440d02400850100e6072400242d5200c075504030761a035600c01100c00c2c03c0c1d0207441d1660000304500b183d000c2070001d1082d1031403500e124a916500303944c031558485411030031800c0f0302242002000c20091090201b50b0a42d00145904 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 180054721 1250 180053471 180053479
    0x601051c02030a0e07090c09150509060d0f0212040215090d06090606050a1404150e15030f0106030303090c0b0316050a030914010219051c090206041a07120c02060315 73
    0x318900981d601d408400d5021b003484640d61803910040c15404096500a05101d004d600c1c0103002c409030040c814090062070520030540000d400d0500b0066500c401041500c0c040300b5502e82400f6800c040c0a45000c03a4180d00030306012845282c2ca40150080300c260602c010140007004105440f400001c00c05001c0c11602140c0e1180081080c2c0c2d00c0c190141c0081805c0c4100720841c0580e0420702041e50303482013030250a01c40000c801d0110003e0325403616030009014408188404007100002d00d842440d1007051107035481c0000120902d0b83c1a0040c00310940568681201070b85d440c0321040c024481151041d02c0c007640307100314000361441800104448070745480e002c20031840f540c80b10011002e400030300c00840d03940002e1403c64040c516098140000c081c0c1400d07070805460710f9003501ca41001d064400300b019510b071b202504650f162400c2e1409090031801d007030038001c0c0c0d483c83c07140c0e2a817000700c01b56090345c206080764001d81d03c501544025140d001d0412801c41e1030f940304d01521640e440c0b00080d80 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 180055971 1250 180054721 180054731
    0xb030406021b0f150709051c080f0a03140129090405010b030403030e010e030d02130806101701021305040b0f1302031f0302031c0212210601051c02030a 67
    0x1603000340b0306030210810340e0b000203400c3d0000d000090901d005580041400800116004c0080c1c064002038600c007110000e4810030350300d102e40c5101752000500d01100400100020404d581c40300c0300480640307609840e6031020054407000e0106101c0310f036000d21544808003545061500d00d40d121140f500391504090708002c2c1010f018000040c250f80007608600e4408074088100024103a16001e0f601d0f050011200811446180d504100e1b00d901c100c500600e5569000900b00080696904111008201803000e075112414404108102000984a0042418605200c0015022061003141d51700c849229041e40783c94070f00070070321001e82081c100740c81c2c2c0b0a40c020248001516603603544844000000d00040c0e0f01d1a0074502c0015940038101004219503240c4c00600068800180e5104908040713000002102d103103d004031300e810205c1e881440c218501089003a003083c1d4840500b143c14524501d80c0000f561003900445550182e0020020485c1e0715901b1012002e0403039000315003103407107840080344e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 180057221 1250 180055971 180055987
    0x302100c020309040516120225120f11030702040b0402070609030801030507060207060e09090c180a06090b0d0b060a170c04110a0c110109240807050a05040b03040602 73
    0xc9491a211a10168000248109240c9450301c0344035032103060b00007402460103020600800351003403805070001442e80042c5440500c940042c1c00700c1c91170508030b0105080c44143c80c3c0040d0a145414040d00880d400c031005003070013030280500c0c050f02080703000103504000c1c1e13980800016240c060b0f407090304150b080000c000458124084c8c41212400b90b1138107510340d451854030901e000314230740c4410111f4100d002d040c0a00c0346c0c0070005a02d180000c42d03004620340c03102088107081050f0500340940c01590354051322450490315042030b1090301840c20030480e071303075407480070a06480f10551101d03400b12402503500c001900c00e038001034000c080a0100c4940b0741d21440a1b2030303061000700003419681d0001d4500400307807070302d4054144400941313140e0600f0101803900c05084401000c900501240da40400c4081f10707403095520300001c08041106499044070044e0300034080303038108081000507441d0000030700024081c408035118404d03266155441d040c9003c1501c11b0741e41000d0b01c110f030a40e40030400d580b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 180058471 1250 180057221 180057253
    0x20405092e081b03070b1812030403030f02010b04051012140607120b06090d021e03030d020301091a030601090e0a05030a09061206051005030702030d0c0806030708030c060c070302 79
    0x40a80b00550003000000e811010403404141d0458415100e540701c013500b844001e2004040e1800f0f50149881c03d145480c90700e00240c403401841001421a20011400105050340f142000318490001d4008108901c814030503c802c1c1c4008680c1c82101d42010300c030810102c501504008039440c01091540100d4a4007803030207083c072000341d50080c001440000c4089062140744100c01242c0c0085444038601001c1d000031070181d40c11180b01a01c200c002e6851180190b12019a448070044000d054a54940c4c117084c0d040002d420038020085298500403144100c02c0d00d10040c1d1130071040c000c00801e90381e881d10080f21b0140020384044112400750b000180f00040e0208081c10800005885000145080200040101074603902c0060540c0c00d00c1010089034441c88642e01e002c614903d000d65407507903850816841d44c4149200c2d140940d2400080107007195001c1c2c2d00e01d004070b0003101038441d440d56401e203a41c0d8034014001d094081e034001202148101c3d0303803007000b400d031709100e40140c40590540d40201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 180059721 1250 180058471 180058561
    0x30c02041524030608071202060f04031b0e06090a0c11031204030e0607030c030f05070b04150501061107051c0506010f0602010501060908031c0b031207020f0402040509 74
    0xc0c400316002d24400d02c45045041c0754440440e01e182c1009071904d03050800c0c1d59110386100301000c514600c14400305548400c4215040c440d10801c07443e580b00c0d90307490001d21500240c01d1123200e82201143c08103041150030071090050b4070040013220580c885603000e100034a0a09400c9003409468a00e24450340801c0c000b401c565221061464510300e410304001c1c0809100d500658458441000741500181d049584820001d07098500760100030094107083c0d8072882040b9020b41003a1881042201700903001969440d0070400100601099a03202c905a031140180500080a60070400f030a215505203e888690302ca40c04010120401d041604e4040c141038080c1c001c0101c06405038010f201d000c1c3c0902a59005182c24904424030702d1400000311346a004460300201c00e50549024000203610a81141c015250001c040d1001c61800c41d05c3c000c0740e0340c00207000b2030140041c903101340400d2030a8400e5800b201c2d0040c04e80821980c0302080440c0280d00000c1c0000c0c4130390031800000c14a07205000c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 180060971 1250 180059721 180059729
    0x4060909030c02090601030903050301030b0c13080f0d0f05040b0c070b0c07060201061406070809040e01020a030b031006081509100207141908040b0708040512060105010908030304050a030c020415 86
    0x281c0140742e01c150050003020300004041074141400d0500440001e40e20504582c11a600005280b80c15110b503255441c0364403c03105440c01d800d07040a4040391511003c901826150a06011240503040c0e0590a450340c1c1107100151012560604c400c10107020705000800600800c43d064409003a10341810a0b142e030404e080b08003ca5001410a002c510740920828020703103044a580b885000400740003805600c6208401410b28501043c50000b0751900e81000c5e03002c0701c0c0381d0025500c0b03030f0303074010002c006240c1d41500b10322038898404604007e42c0f19114040a86502c20090035600360924600840304e00302900e04c90003031282115420200790a480a464124401d0500c2c015590041c0c050300d240c110800310000e0304050903048040003800141c111000c03a44070040581e183d884508020343c0ca0302a5a00c081e8001246800c1c07040c0050010442d18103a441c241c84104038141c584108642e01c0c00300311070090450307100030784050100740030711010240c180c4002c001103030341c1036220504941031000d0341c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 180062221 1250 180060971 180060977
    0x4020f0702030609010905100c030e2505090603030a031107080d05010302040b030606090f060d02040f0501051c05100213090c020f1903140c01091704051813020f0406090903 76
    0x640c14045250500410341c01048400083c0511450398480d43e1b00c44401030359407442c5640c1c5000700d0088500a822440c02c0e20280c3c4140c42c00307210450010f413500c80980c0c0002d1f01c01916170f40b0105a52620540b01401030744083e009605000e199803080d401082c40207000b8001031030511001000460040050011000c6580041160351451040c003044d5104007140d1403081c0c1068040000640f00da106460b8080106200901551070340b60200304404500ca2002c0d400909200d05030b030301d052080c0c210364100c13030302910000c3e501120001c19280202156400505030b80004503400400320844e00038115070048207a800d2589582c40104100301c0740500303c1c0c00b0150704020700c10441c000c03091100c0704440c2c00316804620055901d03980100b003120762204101e808031020910f86020442540300303090307155005161a640d8002c3c0d440070081c0e030f0071501c581e9201c2c0240348080c0301d900d110b580745503014050702c14541030341106550800c0a820300c1c240555800c04d65425000903212980c0c0260a211030207a2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 180063471 1250 180062221 180062227
    0x5090d06020c0105010b0315220911030c010203070302062e03030f12110f0d0906050108150603030a140307021f1a0603010506040b0a02010e071511010c050301090e0304030204020f 79
    0x40d100e0075031300c2c140d018002c404001e20802074002c4034802c030002c07640000c940d900c04039100068a484001d0f000b51030f80c8040d61412020408106403002e15051401c1c0c04c6003110a001c505100490380c03481049801001600580040380c841840228040703007010b402103003040000350744190f0314148100d59200346c000602c0c01d941c5c0c0c0780a580100001c4d0510081d44000e1107480f001e64042d10083c840d8035090b40e2084000a089913941d485648100c0d0051350056007804103582d5420f80560340c02c8040103682c0c044558a0100e00d05140000841b550184240c88200c54141e04a072517015076080100f5a90541c0134440003214152401120200c5500b40e44600080c0700f080c0d140d40003408881c03440514040c6a0820042c070060740c0781400da400f2251420301c0603070b40d0031020710101e000d40780c02000703640b827441460b00100301c0c0b01b40026078100c01c81c0e4a0395188139081c00d80c0303200d500342c4030080030500100301c003000107010044c4180c01001c1620441821030b403500381e599020030104d900031454211021004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 180064721 1250 180063471 180063487
    0xc11190603150302150f0d0e070f0905070206070f0e030105040b0118060e01090221010803030f0601030207020a030b06010201060b1206030705030706090b0313050d0309020a1203020303011505090d0602 88
    0x10700c0395000d52450542d40c1c041d03103070540d8042042c8030100c040e5072400202c04102e61021508000803034641e031002401c140b00380c0284280c2140d8642c040c1c09140c04400381c0e030001060514080c41014031400b200e6008002d01d803229081943c403c0c01c80c0c80150f04100307000140c018651424000c00340168072820400e502c3d0742c0b40482565000282155103103c40b400d00300d04010030042001e0081c15500c08180059035200210f420880c1c801a1000302c02003d50310000003e8444004000b451003403111803101c4107076a0b00e4000460882c41650701c008d500180120042c000b054032840065400403040c000081c0d01da440d2032184180e42c02207004009000740c001c0c10004903050901503000200015001030000b2828500e02500000351400780080b444030200000f44044011521804960303003002c152103048805a00040140c0312460059000303d006800c0014182c09900ca102d44d8240c041e805036003180d017806450b070011800c2880000070410240b01e0500d079a550541c41d10360061068400507603a9120b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 180065971 1250 180064721 180064727
    0x50f01030308090a2109081c0201060b03040f03030504060b030f01150e16081506030f04020111060903090616050d05130e011214011e061a0306010f0c111906 69
    0x10b00081e80ca40002c541d0f640040c085c08125042c0469410a0040f6a0580003003141d450038a07a1002c0200d00c205403014403a031804503545c43c801e400503030084c02131030707101c44580c450341c4002d407001041c03441752070b030b258010a20035032200380c01500c109000f00f181784601000a10b013569003072010210765035a0404520852540c05154011725506a459a10b0b240085000c1d00700d202da1618007050200e2100000d840703c0910b000390203038140c0240f0041e02c904196900c24a007480480e412804107010011840d11204005242e40c801c000c1d0000641c900741a1805026076038100b2010340031001c021b05900c000154091244080441d40c0342d0342d0945035103000e0340400340f4500540c04030f07504510703140050010504d41080700782c101c0d80001d510144000d9503405940104511003a98202258a08005012035042d401c82000c9900268200c08030104100540b003184c8800c0d1766081c049500f80038044607441c02280342c3d4141c41d01030042c0c08080c260460114014070303907100c000c8a424150b03c0d014031440c2c3d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 180067221 1250 180065971 180065987
    0xe0c040203310b01031b0302030307080a02010f14150f09091c0302070b161107090e1b100309080705060906060a06030b0d1b0f03050307020f0108150f060904050f010303 74
    0x82ca5410884400d0301e07440d10031070080180800b40c811810403800d00c95018100b1002d000640c0e0180403207940c0d045905203100a03030012103444006501780184080c4940503070060700004040c1c8004141c60751124a24105a4181c42c2002d5800c1400c4460700d104e070755a20202c2e141320700324000203480c030a42c00c64444503502007807400d42401d043c41440442d02040340348800c154028042103c0707610203c0204000c1d103011202c45807104551180180118101c801c07900300d001c807503119a00301c490b241c055009250780a00440550381e0030084d90503104581911940003042014000c00c2090310300400ea0301c606092000480355085207900c07890903c6800c0c144803c80c5002070030103150030451201000b0001d0624205400060410003610001d00f1030415003540000082050f501d43c074046550344d1401c0c944980020b0700c20783c81440b9404025a643d405032015603c51194040581541d1040318100300c040d4143d0030f0768642003130b0240040c00903903c031880744a0052501d000440b40640c076515000305840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 180068471 1250 180067221 180067291
    0x3080301080114251106040c08060c040b0904020306190803030f0f01061205090304150905150301050901061206090204090f0e01020903100b18070809060105030c0d060e0c040203 78
    0x940d8501c1009011946125031211a5094040584135400c5011080b103014503480c0d030700b800500400b0148402c0084030381c80c003022180c588040d60010303074038080042800d0142e44a03004001c58200a51800c9103804d50055510903802421901200e81c1c0100700c17032442c01d1a4100c484590b0002007400341440b1101c4100787e0000090080b1111581044001019081c88030440e402180d2608085071000074140180e4010340f81e4554005000030000c0c2c0010010100781c0320351801002d614241540f82e80e4a4000c49041e039401030000003103a4a0200210b0301c0d80042448642010b54410002c41c984916000520050100020101d81034010070345070400c40f403281c3c048a030940c0c410849440d05480104210081c48108900040c0e2014840e0104150140e44a8114002c100e45801c10188980010801b80101c0c2c800b000c8510a03a201e4007450754074007000c032915600103095240b80b0001400c540000204880180941d502000d5200200741a03803c150303401c1c9014501080d6a007004100392211000388 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 180069721 1250 180068471 180068501
    0x60f0a06050f060403020d060b1c1104050405061308120a020702120f0d0c05030d0203011e080f0304090c020c090103060b010f021b04090507080a0f0606080a0203070e100f030803010801 81
    0x180b0314020000d0200d02c103612000380100a00034441043c49001da1111490f81c00103452500710102c08052400003805829088a0500d00b01010341800d051920485110f50781c007034010035694640180421030a1244081125003040030802e03108801c1c62501064003e0380250809601c580051042100c0050b1801c1940302903803003040e84040f443c800050004d41102c0078102000f43c01500e0510700e0451080c8040302c0b15150000000045d50bd8541604540c4450182c040c072144a032035600c142c2e00e0312070b00246040a503109010a21007054198050b1025502e00c3c0102c0300010251400b140b55203800740d1058621030794034140e942095070065451803c0d90442d101519030180d000b80304500e01035400b0700c89405950f030b600d140410000c080003604003402450040b180b08014500c1c040700030940303c8604507051414a42c00041072040050008241d40d030007801b41c0811400c020b01800e04401c02400200050b021400c00103a03c1150f8508801035405036803401e96039070425180c2030075166041525045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 180070971 1250 180069721 180069739
    0x9040603060e010f023a02040f061e0f030e0c0301020c0304050918100506060909041103060c0430020603010306020c16030b04110a050d03020106090b060a02150a02070206190908012714060f0a0605 86
    0x143d551101ccd0b61202c800203800c00056806001d00d000e441c0400044107140c1540c80000c2d841c0203403500201410840d0000c0f20001c520342e0f2001c42051840190301c401c1e0105a20405039141c10010030340089a00440103000e403802c0c80d643c600000c1c03400c4802c3e10152000d482d542001c1d9a43e00b014481691f02c0903041c401545094a025001412004803266a00510400407094040300914a83c914591500200895103d5840f07060800003580721064050803132140100307a44039200d05005403001c407a000b580043d115075079a250700d400034518181c51035000d400c0d040cac00300d503699031100720000540c0241e00000b252802c004440f001c81d1251550548900014405000f1803940064100703200007030180d0b0010705490380c41c8007402901421100960020000c51240724001c00a542005180020341d0303140d02980d902c44040e802c8030400c0020040304540e200f24072040010030071107442d5082c4a403510b0f110712001405460305116003a40c56824140c1588280091010240580401b0300320440c4e124072 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 180072221 1250 180070971 180071027
    0x1c0f06050f040b0f070e010c060e0303090f07080703020906090a0e0d0e0301060f0509040f03030b0a03063309020a11060405010b0909070501050d0e0309040603060e010f023a02040f06 80
    0x200801140c6c060402c070703079102c0900070000545c211070000d40342982201d03240e003030004031562101101040000c0c10321805a000610a1340050500e00300ca801038100c8007140c40312014400340c244000c00c0d42550319100e000e003120700303e010020b59800302c8269851050300305a001c10142580c00d19030113609501000d030390031f10190b603030218840e030840d40c89100050440400e04d000c2e0b000e8645200b51310350100000e10004280526a0440a0910060004001200450700484403200c50b40e000e42a10480d80801c10300091b44503a00a20880103641040f218404507000414a011130844080b52542d441305254540c50520310844c50b00b01c090007000c0c284d41800c0100080440c040c0019541d645038541214010703540c0b00b40100c0759104c0005e0000c1c040070b038403030920001500003503180d00c003198070340782041d41188004d20907036400c1c00382503a0090f4643c0d0303061f090150284040b0000b0031121080c0b69000b48540c070a2004000400a01e030745070092501d4060060000902e05200f01103034402412030700 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 180073471 1250 180072221 180072227
    0x7060228050c0105130e040507030303060602061b09010c1b21050c0910030807060504150b0d0215220f1a070605101706060a06030b1c0f06050f040b0f07 67
    0x4040e2102803a1040d00c40140b5006085005d0503544090f0101e241c80040c001882404140142981d010f44c4041c0001952031004076a9003404680c0d5a51010101210701d562001c0d0200816201d4014035125004000540300c00c5035008013242c03030341601203581000704500703940c08110411328855502940100c1c881c40d11501d03250501110b0040c0306540f0500001c140c0d5031000f25000207180c01080094840b5068038040c8010103043e10203485026441034040c11051690207180c41140024203180400c210513801c0c0040c0c41c070b0020320801140418400c0c01c481c3d201613000c0744103420300c0b00340081e11035140c840d201001017856040b9004861040891154042e40c5104032402d00b54004c1000495030394442000407800390f16080503000b401c0c40501c42d001d800c00050034901840703045030344400b129500c80d802d404071000c8040d1140c110b28000501c94883c028284070001c2540120407002241d01180d840c1030071240110b529031440105070b07080c2b00502404104856100424211100341410201c00c06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 180074721 1250 180073471 180073483
    0xe010e0303010b030901090b0a09020a0801110702090406021e0424050909040f05120d060f03050a120201180305120612101d0a0308091207110103050411030706022805 73
    0xf0010080000000c0740054609500c410205a000001e9001c1403d040c0c41c444040c1280704800e038440c1505030804100c0000600c1076032400d08803032a0603031400c0482c0c0d080c03201d01c0c0340c000c1040d90803560034018501421403600b030141c03a043e94022800e5131941001c20b80b04403151481c01c0d1480c40119002141c40f015042011158000800c440780340c1c80c1d41d0356107021840c0c1004000c0041807400307601241090b09140201501c809039403400c051040944070484110b1003203252002501a0344420002c40205101c0b20704120180514400800c03003d00c2106040e07400030803075038203d0005030b0006e034200064112220a58000c40d04861000443c01454802c59489142119160215503101d0a4401400d07088140c1403800100c2400d071200c0c28a18200509880c8080380d0a00c03070343c004ea0071504a00c3c10f582084801003580103c0809850a14000440c0203000007401140c0d95408000c90080a0307504002e090003e2840e0340c02411401160300c0c003e5411299505500c0340000d450075113500040001c501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 180075971 1250 180074721 180074729
    0xf04030f0f08040f0212010f050615030402031c0215010e070305061c06050c090a14010206011a0a030b0609061813180602030402010513060503041b030b04240617010e010e030301 78
    0x104d01442e1150001031140d040c0340280c4500d030341c44d0852000700209941c02c094031030301c011605c44264000510320b0005503c41124001c5d80342d082080f40c204115042802c4804012030b520407220364800c5032404c0702194200b17800011411a080742040406c42d814059542d010400351004110700c0c614112900c0ba900c8058070003001540c941c800106000d0303041c0103451350000c2c01070052104c0755442490382c649110300d80310140180034120001c60000d09030020061030f0040890f0301d40c03a1000b1184110020000042d080354050400c004c0740740c90380d40300b0740502081030723001c2c40a50602c076005041103030300c0c80034140c00441d01d0b04107041c910391101a0214410107d821240240c0e8030780e00d901c0100c4061141e418412583e508490000c070300c03103a2201c051845240315101d0700940103484003501404858912000b0448003105001500080c440101c4000001c00f0000c3c01942d4045417180350240c0d820740c0c200881c00c141043d40350101c06030034010480900c035284d000308411b0750030100840e103d08c01401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 180077221 1250 180075971 180075983
    0x6081306021e07020406050906150306010c0807060c18050d0602090d1209030b01060504050603070c0f02030d030c1808030a0f0c021302040e0609090318010c0b0f04030f0f0804 77
    0x64002032112903011101d0600d050041c18800b18612000580c1030b8120704000c1e03001c0c42c0f030a00041514206080003d0190303c000304a20620207030340c001c42800d40e200412160402c00e80c0403c880005060301b0180080602c42c1c240480e44811b803010040c4400c0320000c4000e01d800f141e130002c014540321181d410343e407190440800360ba1070348070790089601800300540c020815081106440c1110b94024110800c5d64441c81d045201c076640c81c00204d9403070299004090f0720034005c0012903030050180421102c86071085d0404000a210364000900f400c01c0d00d0316020201340c60f070540313000c0d403684080c0182c10304109100c1402e80c1c40c1082c40007503481c064014864180b01c4808145150140259860340059078014030114101c0c02800500340030750018403c881c0d00c2c1e181c07a00840e4952800f400484c0c4940310a0004500707001800d00000a80120760b03202c503050241c0080c00c080442c0885c030020344543c1c60710b180404103040c43d2400501103202104032004210345400444082c1e90310032071640e041a0001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 180078471 1250 180077221 180077251
    0x70603020904181101121103040305040305070605040302012120041701050c0315060c100b040b042a050403020d0501020c12070c18060e09010f06050a050303030c0f0702120604020a09060608 83
    0x120441b00400005003c0d10558402004002c1019403100050046d0f91060042e44c91140c1d640d82c040e04c450041e404002d0100700c00c0c102c21074141401c07280644080140042c04500c042c10803410361420788000740d21100da000300103402c1c0140d94002528050420640000b040641f070704641d83c0c025804080c2019185a00440c0d80380c00c556609025900b510b401002528008041161506c0c007d0001154840c0540e00b041004052031a191048a001c04607908040c0c0d08182200340f205a585503040142092200c14080403000d41c9943c0d1701429210301c201c00041e41c0c0d1000b13141c02071400700084824510140200700d10000142031486440c2120507031220013400d2055103410502800c680c2d0425039030301c0c004d5030802000c40d905401c00103404024030010444181c88606101142a560040d250142c0c410000704038800100390051540040c40800c00d420480c3c1640062005040c1000a44641d8010001e00c4250b240544c40304e4000c00740000704110140c0f034400e015020040041c41544055201 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 180079721 1250 180078471 180078497
    0xd092102010203040e18190b0a0c090b0a080916121113051e0c0c1b0f0312030708090a0f0204151a0c0f0f030f0a020a05070603020904181101 62
    0x1c0098070041c141d0b004101c40d0318546000a1303844442d00d17001e01d112610444011071003610300c0e0301d0300340d11186c5c03c5070510f1010742d5201802005080094a2481040212f4800150101980001e000003003076035078030101c842c00c0692240d490b0803400e40224605c1850404104090101440c261300041c0d0700071421644c0164071000070b1414195031102c60700540c2400100f00c80140030307010084070076546132801c0c50903440e0b00c100c24a0764090504624084d0348041c002e46551400c0710010103103d80018072400009141501190a0421a8101401220003c41400320702500040781980c070406080042110007140d40308e10301c8c04032000a000c0d00407503941510410110041e10440043c100c1c2c1d1000e13020107840034020341d410364081c001c120b00f203004260f143c04448501190049001130303000d0045050440c14000e410341581f0070020701080d0320803031820f000000d1081c4a48002001c8503280141c613403c11509103c240c90700c500c101d50850341e04052144c0050230100288441d06402c0c82c01025103928 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 180080971 1250 180079721 180079723
    0x13150c0b15120a02010503060d0c09060f08120901080c0f160c091a3105090102040f06030c0804030e030102040b0316030c0801120b0a060b19020d0921020102 69
    0x94840600360101903001c00006582420820003100d400740d684408580121112980324040c01400a0002e0404c10126800d0f1401c0d012030304909008004445401e075a940c1640d0840c0d03e242d100c900e510700182c0040040600610180d1041601d00c42d20518260310710000030035811004206080000000c68669036400e00001503031034800001c4032860a03041d0605000c1c03518445840307019041030800740b05803a4108024840741508501034071004d00540e41820103a40d03440c0d4400d040848100039405d0060444190180b90300802c150000140d07103d0500d8050090b0005a8009400381401c01c22103400c00c0354440c0081740d00c16054074050100c2d520b000d001902a1050744c0c8141c0b803900000c02885211400011040045d42c030588040000c90f00c40b20040d03501d440240b04501500c0b031103510b2000403501c40310f40baa6101300d05110001c0d1140d02c4001e0220940c20842c0f10229400c100d203000b0718102d030100f0414502580d1820a41c4a1f280380c4280e644001d904000151240e8401c0e0000300c0441e40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 180082221 1250 180080971 180080987
    0x70909051306151a091c05010b090a050411060a0509100203130816050a0e0c0f120117010c0e1507051005180d1b0f0f05120d05060301021315 62
    0x251240c8207100b11030f41c444494825812500800d0300c1610681e020034030700c1508104951310001d014004110f4038000e00d0401c404902d032242e080e2915503e48640c4001651082d00040c85103c1d48180003c40d03040501785062b4641042800c24040c120402c2a5820704c0e0308030342510070401048800001060742044201d0a50141c059107030640d00e0f5901300402c41410100ba0030f43d030044045c0b0041c1340980d482c810131250f0059403042c404c0d00c0305c114010440001c403a1005084040030f070702070541fa100503100d14009600702640081600803803018600700380d01007800f400748941190f181c000507090350b040000d108020940700e50580c0c204002990001c0080a000c2d00c01d03d090000010002440c051483d03004210080c1a0800c4034003c4010210740c0174080c000d08811142c080c40550702501140c0d43e0840420151031090b2800062006c07004001101000401009941940748944900442001c01d0580c0c038003405451007640140500d2500f8030074099003070704070351080c6006408504160070584242c5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 180083471 1250 180082221 180082223
    0x902030a021009090b040219050d020c0706030506010f08060306070c171917040f03030504060e070b13060903020f27090a020108060301090201080c030901060902071103060105090709090513 83
    0x40802c080161007260000751001c112180d00c41e00340034003ea450304002c00ca10075814041d05041d1218083d0340c4080c030440240040400b85800185030448603600c041c5400540e40c022030001c0d031203008100e003650381310900c3d010b02403040c03c214240d07040500020f0748410303008001c2420407401e0780302c03541400f145201c010b0300c04902d03841069035110f1000300f4180d0014540251004240b20710345070030f400249900d80b54400c80e0000d03980304000d5020f5800724080d1030064016120b6980340e101e025480c0307000380107003401408882d0a842c0d032017841e0180c000c4105000d0f801b4009111000e5810000358864102200e1100000c407003402c00c44003e00414401c490394402002e4282c040c250801c0950480020541c0c5041c0c001d8a4180b0b042e81c070201014240d038000040240002c280c1000b140c00e82d42da650103590040a8040003040f110b84503d0902c007281c10042c02560340103078090014a85040c248526070240505644584c1a8900040c0280034060603202d2240a60ba4500c0041c0c058603c4a02e5035480f1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 180084721 1250 180083471 180083479
    0x31302060304050618060f0a05070302070b0702061801020f03061c1e20010e040c02010f02070b01090f060303050708180a0e0f01050307050a051201140f010f080c0d060902030a02 78
    0x1c0c1c2040d00f0070030f81e15001140c0541680c110808622103a55000880d64418095540c0310281c40ea1541c2c0c60001030a0082c1031542410340a0004400241d00301440c0d5215800c1940181281e14060404055070111a01c0c0303404541d104021080038050f9900440341d00400542e4804049a8000703040b510341001d0101c0070b0040101146c00b2409050807400c0705280c03034028907589201e10503c1a00c008401442000b02c1d0104406141060450403e50041d070382d400c0b241e000005080701010f2480c0e059901410044890005c043e0050010084501c181580702c0c2d00c00704108111819550040c00601c200c031000f8162040110740d0010312000350060303c41065014184c00300066442c9841e1400207801d0b071b4040194802c540c00420941000070706a0122040204420007583c90310060040740500c592042026541b0b91410000301b201c0c04a1040c0501289080a90a07601d030021481c5403a000703800015558000b030740d0083d255651405881600d41e00b040b000107140c41c140c4002450501581002904 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 180085971 1250 180084721 180084727
    0x81306020a0c03030b0301060e01171e031c0e0d0507080906191e02060612120a0e0a09200f090405070504090c050c0307170715290d0803130206 63
    0x100540c002c19005400740700b600d05200d01c200039400c0600307a403042c0c0940c0e29500010740041240d010368030b2400203010601019148200c0d20179240c01c0b1407a040240a050f5030344001410391208100b031103109441d00301020100800e4a0101c46d980d1541006c0ca014810024049440401e10090741c0845109420003080f442d078071840c0f03401c1050704100d10b0510001182280c000d280b1035144000c000003140100d1782c0036101da87c0d14a01044001004600c14500350710612041224006020300141201d403000d84415600c60341c404100198044280c000714000c604002d010201c3c1c0481d550102214a00c12500540720301c07004240c03004501031104101ea006080c9418818055000340042040d280003403000c0c0080388808209035404c1c8103100e04516a42c0c4100030340404103201044087c83d00c507905113201d01d012040d44460105110a00c248003040b5030300d81504004084c07d00c500fa50400751102100c500e2201ea800080c65a060300901601d800780000c001151620b011851143c8194014143d9031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 180087221 1250 180085971 180085987
    0x20f030304030f0305010e09250504180606060f0203070602070204240504061520010b0a06050a030f050c0901080402010912110901050306042003150103080a090515090108130602 78
    0x80304a1581d00f200011074075240011aa01e40c5640a05118100c0c440c0240301d02c403002045420301421a184202c000e1894440c0825191b403140508008100c80070000303072120109040182c01c0b501c0560044c02405446a030001100d80c010040e5183d0a42010740182c0b110604d0000c500a0140030800d00d1901c00311044114918201c000c074041501ca042c0e1301001056252100700c8641c020080410300070841c50845884152551f40c1d00c0717002450b1520001c0b0313002501c50040f400c0c45526811000c04200e010454840441e031500c206000440b044500f4012402c1ca982e04100910400d41e8480c104166680000c0543e4010082c41d8000c01885058a0000c58241003a048030511080c90510036550310000042c2032400052041c0034580021580d40004110044800c0360f51141c1c0d9055054058075407401c442d41803110b880da00079402200d0300707a03407210980b400614810107138001038440e1101c901060160500101a80c00c0d01c0700a0912400c541c880c0390054007400602c0d040100041d0001980324 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 180088471 1250 180087221 180087227
    0x203070305160302030705040302091909150b0405011a0706110310080708030406080c1e0a08090609062503020d090606050109120b04060c050d050106031a1e10020f03030403 76
    0x68420010303159040180342c081c100c11003c1e880b081d1100300010303800344002c1c4054502944255040700303000d900140d80340c40003800f20003510300c00c280c251131489983e5084000340382d16010b051b16480084804000c550706000d401800340c00e0034000b00e400c4c00030114030141000070315840041480c010784900c40c0c481c0f0741007841c042100194010b2041c5030042250010f000c1c0400000d60b4140d4800d0b45859441e03941c2e082c0e02c01c0320b039001400010005901d15000010b04a56080200b48c01c400c1551807400601d130000d103261070150050001d01065100c40100944488212064000b1910001080b40351108042080380680141c00940c000103180c00c0007603081080700e034081c00440c0c8080e200d10410b16550102c41102c200c540e2409040d400c9904001000500290300c081c00010b82410300b10b003000b0344440300004580c000d80003035000c26aa60f103021461048004d1649000700e044034100705e610225100002c1c40500785156a00441400c1010404035000384011034491440504480e00da1505060007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 180089721 1250 180088471 180088481
    0xb0312030a15050603010b07080409020a031406181f0509010e01031205070c0501121d0c0f030a0812070504181a01031103040b060a08010e0105040501110703021203040302070902030703 81
    0x101d544185003600301c0c540c00403800007580840300e005054a065a2a04241031015800b040c0c08071500c400402003c20403100a102400214069036000100710341420b084810b08540684054400e0102210916890704401001a400003044640c4d49210803c107002c0c2341500f5041c0c1050303034400c609000118030361880083c0319040700d0080007011281e5070118019645031180c002d000c2c0842e070345e040c1c05100c103501030140c841151034156000200341007006403c20141d49040301071044d50300031714903c2e01d440c50202c88203147c203141140a0b2500d001c00d03a40b804030a00c81e0441503070000d001c200001e010304e401070042c1d900529000300800c11008040d800170b0001d0080340f00c1c1c0c035502e41c1d00001301e1229520921908880010000140345143c40710740728500401c030300400321030b840071400d40c0c041640e050070f0150b0440e1b15150000030030503050a240107400e650322003548030049a01440400c01299001821a40032a0301c0304c42e00382c0e0380d107032414200c0c1070080312e17004200c10f1800003041c002813907415404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 180090971 1250 180089721 180089731
    0x90204090e0709050105060706050709180902040b030c060405040b03010921081e22051b01140f0403030c060e0304030f05100e0c0f01020118030206011e080a080d0b031203 75
    0x1902c0c8850385035041881258002c2c000c0540200007030046c0320004055905c070540103c0e0038203104840310f80e0340059034a451080700700c0c011260703198008402141014000c0d40b0704c03d1400c40107008003540302008511140168401c8600c00d07502c0c0d00c070b194110b0f1400c0d40b0061416400040c404529544900c90351001c402040c0101c001900b020009080d40d0344004030704d20241c0d03c16036507105603201d182e100004c1c4212441c020b545003208081d01400210100010754a8020400600f064007448400160150311020319050b13100c6c030100244990711007520200d40c02d50303a040c103000e40d10380854180800100818401511540310024011062040707010701400c00c07501c070b4000c0b500e80b80540383c90101540c2809914038000d51000240a0b01c034a80100b241030705a01c1031000041640341c128144169103a440b000380c0243c0c0143c401803218114007013600040750720202050303048915200e802c940c1c50b502500d000d009008082040e4030b41000c1d076045041050002000c445000c180b950284120384e10980b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 180092221 1250 180090971 180090973
    0x2090106030908030c0d2c1504051e07030f060b090a09020102072105010501030b06040c020703030906080c070b070e091003020f0d17030a05041e0803041b090204090e 73
    0x50100d01c240500d012480d80006000e00b59210041300c0d020b00c1c0c114102e6004403503103d40c2000307440c84419100e1111815000c0b00c00e0780c0441d031410b4503401d0150100d0003105c2c40b0a0b40c007c0002086000581b03034200480805214860141b00c43c0380c1c3c0c140541034100405d4000c200c12220184002a000700b840301404440313030092512000040d070704035001800004d015810441d41004500540c41104401c0305800d98120000c07582a5195400c44000f60411640300d485030081c488982401c2c4196860f000d803c1c0000c00003e4196100038096828074464030301040291000180340480910a40d400720b03500084451940c100b004002d010301e1303161003840d400340d82c541c130004000d403189600c0c080882c3e40103403440c02c030001520140800c002c6440c400b0b440343e803a5244581016448040150300c5020245400140c80c1003d241c03031f070f0386104c00310a6640c4104074102203101168500c0101c81d00181d018403080480101000f1000785410164448046288042800038071003503507400c03031418806514 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 180093471 1250 180092221 180092239
    0x81c020102270a0f0e0f06030309120304030b010b030c030414070b0d09060f051b21090d0210050708070309020d0b091506061612030e01060b0703021005010509060d0309080a03050702 80
    0x141d002c02c040045101d003000d045c1c0c16130041500124004411034010304041c0a0340e03c5c108c201008188042e441c410130b01d4159000007000c00510809601980c00b4082803001a0714500300314600d80d03c00e020240015100c0e044c00344800085610420000c4004d01000011070b0300c82c5041907003c0c00400d0b00e10000d0b0345090030800b00304002d0602d1b11a29102d8100d031502500900c81d8803100700714075004010b001050b0300074950440b18141c60420000d218964000091071000c1410b24000d0401090344c1520903090308080c140710003590007001c400e9004a00c1d140c00a600b0301c035800000c0441c01c0e8a04040c184040341d0041c411443c40200710000340c1c004544041c0c00300d071511403c1c01000d204103c030001c0106118030303042d8009281d141022159641914011a60303145c0c19185c030307003143c941c0e80c0718192a500c001003180805805003d004001c00fa801400c00041d071406021882410300180f82074031500c80c1e00036500425025400900240c0040783c11161403008a140181071740d800050140d201e00081 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 180094721 1250 180093471 180093479
    0x301091a01050a050c0a060f0c0f03090f0609111806030706050408060604020304020a030b010914090f210f03010806012d05010c060603020907031a010306081c020102270a 75
    0x398000065065040c2d484510300321032084111003030340126030042c0d070344d00908090602151081c003a40c2420311030b8180014006620100103050402d407400074005050034000da05008ca20f00c000c3d009809500702c1d1000c02d92104d1480c1810060001c2601580d00c1050301c00c4030031426280008192140c1025803c880440f51202c1302540c40f400b5620450131550f105000043c8181031940103160068400f5090344449502c0b40c0c0e5038486080e00760081d095156982c05224021102c0510307080c0c202c080880900340b0116514009500c034080011200f09100311114002021100c00c4c003100c0c420168541c03000e0b12035031207121464a546084c41511150402c1290001098101c0110911a5200d01031400c030068075102c010342e090401c1d07880564103103a60749000030150b156480c00b00e101d00040d80d4001070000d9034038036208001c0d120210b80b134105032808400b070003100800204c1c0443c070302c00032a0103003403d03162a604030b0282c40b03411111241110051810b008400d980c030846204a00103e6400e080f10b526 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 180095971 1250 180094721 180094751
    0xa0c0501090b1819032109030b0a0924050117010203010803040e060f060a02030702010908030412111f0f270b180a0b0702040609020a0f0f0c1502030109 67
    0xc0d02a070750400004200201418031002d025800002000d0480100b05000406495001e0351a51042d6100b01c0c6e0130f00d10401c024103001440b84c03c8011814203c0c911030a50f111a040c13504014151001c560f0790714021400d00034448800340d2100040f0b10796141143c3c0240c0c40d4000392a0078440c4035402d4006000032801d584040c000c0c3c0303043c0c0b40c00d00c00860401e46440b07910207441c0c0000c0d16080d081100b000203c41c260311807800400c030a01454008564500311840010241e200680c071022940c1c2051000703106c09070301000300c10012904400c01020030242c1e0400030b464580728418203140c080604e00494a01c6030456521503504001ea1590340011056000c003650b02e060405000b6020500c08405104540b119805040c050840d4400c40c801151b0140c003003240e803042a00113003142c50000c81c1d01011840c0501895020713045802c001d600740341001001500c58079112a540c821321a4007139101c410b0a1040c9040803400f6081000840c16032070300300c55280250710038002c00d10303510b08000340c01143c40f40d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 180097221 1250 180095971 180095987
    0xc010f060f090e0607020d0815040515030d0e100f0509040501120218101206021c061703070f0303020705160b0307120c02070621020706020405030601050a1a030a020408010903020a0c0501 82
    0x29940103829000c07c4044122071300040100844c002030f4440c5d12078007103911588200752207081e200f1a000d81181307500e4201440c007240244c03c0c41c204451508030940503207682d1007084801c80341381030984489880030019035890044451294026281c6800040d50219000c9021203050003541c0f06841c80c3e01440f103180d101103003201c4081d010703202c011042080802400c0c43c2003119019640c018240882c1c20381d07000c80c0c055080e203605019511040240f0000c1d802440c1628884010350082d45030518075904c92800781440b20015061581c0481e102c03061000078040080320000e421702d03000da0503071181c0070a54260010317034441001882440340401e0301144c500c0740741040c0d410345d0010b050803032411104460400d405030006001005000000f4454160340c000391048034406c00300562120304060501d85809070591100f841140031600401c42008420b041c6050004400c1c282a540d545141c00b0201900c51644100310961804801405040c6d01091403150b0b035200340721420900da0b0b203100469100c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 180098471 1250 180097221 180097231
    0x3040b060a03110108040f0206030f010302152d0913020d14010302090604050c09120304090c080f040f0305040b030a09120305011526180105011211060c010f060f090e06 74
    0x1c25410360043c3c0c03942c061007185500911440d03a901e00f541040d030106045030800d890b18885288a24014001c43c0707403500d403445007080b000d200300381042c480044140030600002600442c074004000e000c4010100388080342d11422002e0854002c900301c0301038020080d03206200c0100740d06d25080c141411a01080300041c101c80c3c004040c21020340f980e004010041c44c0c05050307179450711000c000d0340e809030300c070210b60b070501c004050040c1d910360785007800e81016940e00c10400020003110008000c641d40c3c200c00ca680d00241c200102200098a516003528148120380001d44c014401000304201c0c04450f4218441d0903204100c000791001d00d04a0941c10307618203010b201d02c180405414440301a10030000c00315540408081d43c4013401d00c040c282002101d003076800040708290060700c0c0d02d80800034020980103081407008403800d0b14040d00c60502c01201c80d401a0304c1074600040302940b1407025040009102c2d0510010040c1d03075501c0c4040301e4000c43c240300c1d410b0041c0c2840303006d004c1c064021801620607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 180099721 1250 180098471 180098483
    0x140106020d02071203030b12010c0528090605030705040305070b03040203010b040c12091110031407020606010918140c091503011805040309080327030d02150c09031203040b060a03 79
    0x4408a0345d01540a00200d00c080c035001120805954001c1400b401904140d500c1d80d00c4581c2d4411040b1805161100d0340d003c12200301d030307810303004000042d8418aa202160a03d02d00329032262150f94040300d0ba0f11940e84080c2c882e05c0f40600202d84107070880e000350300591088008201040c00300041c803040d200c1d21071001002c54003042031041409159086240180c1c4135080c07010000034036000180880700f840009400080d07a81280b002c4030700403106c903e90070502030b0004002c2c51a204000a02c14645405580e05a02d018400440c1c034440740d412000302c0c01000c0e00300c4480c1e403800180d0501142c00c0000f100d40704595100410301c101c101042145d058600710307051601505103030816034014100203881141001081d01c400185c18600303001070304481c43d1400010340610060165002c50b6460008030510070b411540c4030710300e002d80000317080130364003080c03120a01035944000c009461070148a0315541c15000d4140010098600f0000440c406c0f03100c3c90701c1012545444050040341d0485000003080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 180100971 1250 180099721 180099749
    0x9050c060904020c031903111303060207141c020106170606060f0f030403050304020a051c1103012301030c0902040303092709110111010e190c0504140106020d0207 72
    0x25810540300501002402600c054600003800302c102e4603682c0a58105c080c03030b1140503e04031459605000302c0300705140001c0c1c02c60811070301c54480c081400700e0384002072549a000805404002e20307080c036903440590b10f030140c403e240022601040f01d1940b8080f15030055180c040701143d40d160b41c40a40050010010041403103980f1030b41030060650009208500c600d5081c4100d0111311810307001144a227101e43c1c3d5030790300d9051078410b0000000c413541041d8807995034411001c001c0004010b001c540190004600b030030b0f4111400101e80180030284195103180c400300050000380102c0b02c042412244621130396480c079580e0340c440c40c5c104c1c0100d01000303000514428003040b101d00c13480010544420307440c401010007054008660100e07000410125032480344072182100560704284121801000c0700c000b07100b04003190054a484540005103000c03600f9030790480c902403101200c500800784c030010340208501c460a1700160079100091164400500c51235400048007440800c0030002c5901d00b41000d04 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 180102221 1250 180100971 180100993
    0x40905090d11070e09010204080f03191403061e09010902120603060403051c0b060a03060312090f210b07020303010e07020c1f18030303020405270408160f0302010b130905 75
    0x15241300c0171302105590740d000c0c030000c00c07000402e01080f0360114425005560728200c90001045029100d094642801899801c80300000c90b9681160740c803190844501c0320074129650712801008140030041d8102080e040003081001c03150380105042c40d5075811481103a0f80c0c0408055485104803030040c0040d0b800d104002d118181c81e510303100c20205040c008107450130004081503141c4c1081403441c0c002603c07004100184100e4842d101d0740d60346586400548903040000d1080d014400b8451600c0c600003140a506074480c00d000c295660070360015406420b420a020000d580c1d800130b0107a6001c005203840400d605500005004040e140c02414005030066030722595101002c0034102035052041e60441c038a080c074195101c0d0300155100303442c0103071914189024810f00302d8000881c040c2420500780c0d04a21100c0e0030306043d61040d4802d80c0c0c146d54260841c0704414500c503119004004c2c1030107001002c20541c0641000c00c003081e09407080d960021081c1da0800540d03500400107000e5400000d9500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 180103471 1250 180102221 180102239
    0x1c0902030a08070f0609080703111605060f04080703140601120506070c02040b030a0302010608010f091a06040b06030c040513020906030f0711100e011104051c1106040905090d1107 79
    0x14000d018000030340804139161a03120941e0b8180104982039800001c24404154101c260034180004004c001e00202031000c0301176041ca84503020f090301c240c031301007244502007560701d04440152481c101030307800c85644e074a03200a00c1103211110348a2030040c1c00000c80d1031200050700c5541c00ea040002000a80c9900d00e0640b42c1c409188000da0b00a500ca540790800e40e1004c00a1020b030601c030b5800061039615001450b800c540416104110072030074602c481000c101e103d191042241c1003006040e17030603190b2100080c02007508a4041da0050380100070003004000c000041c000312141690600004160181444100c0c843ca0071030070380c032100500116074103d100f640c030a5400151810300d04807403401c1050b0b00745810094001e0513107440c1c494412801c4a8800c0c0a00708001c180c0359111424503040400064000110542085085180c2d0300c460f018010220007090181c6400741c5140d544540301c0c0070180241c0811180b19080b40b00b402c4026520603c916124282070200300301401d10340382044402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 180104721 1250 180103471 180103477
    0x102010e100207021813050c1c1407080a0c06090609060c11040f020c0d091d01060807020a1a010302181012050c060a030c08130519050f0a03051c0902030a08 69
    0x70303038001c144000c85268400e040301925002d115108102406c0d024907107000d616010020520074041c1d0385c0940c548880010281488180503400019030300b820382e007548002e150007807135400b86489104070400712080c8071202000e5015610301c0d81d50340b84403940b10701040e200c13070106c1d10038100012000d100010100746040e81701d1100350001032010814160400c0224140d800c903044204140c0c21400807621000d800020150050280301c0010100349081100c44180401c148110b10921850b00f00007081c0700c6c8203018100041758071845001c0c7c03440e49809517440c641000d001c100d015010309a000c4d404810382c80c500034819400d844951440c6414001300b102c14445c0698129a6072003610b005c900f0942e104006400801440c0c0e85c00250a890707100010301901000d460705041100d81c141980c0803401c0410501108021611415203c2d00c0314542289440003807000c4955038021912071004140d4807000600700881c14050000700f00f5072046141003103545458009606602981041c00000c0c0b018010b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 180105971 1250 180104721 180104723
    0x4050627040603060f06091e090515071d03010b0d0201180f150801050d030509010e06040312081008010204060503040b0604020f0c030c0d05090d020f041b0e0f0102010e100207 77
    0x440c0e00c50352855004241550042d07042141c103d62100a03485400ba0b40d0301c26400208082c400900c0008109102548000d951140b010325003500c030345030002406010130480303515490241a0041e1458103050041c0038800d0201e620140e0515480d9035441c03480c0502031841c2a141c0202a810040e00950040d60041b85100c0705144184141d030002503d8034840015030024450b00032145400030b14000c0042c21140140c120030f01c290400700810000c20350040c00d0710701d5000207003025061440c40388006140b6008a1340000d040d40300102d0000301c406d5011014034080e4040403801c1810540350b241040c00c2c1e000318010035001440910000b80443c1040708800e4100d4005080149011034031850340d40c4c941e024040e40b150b80d40c80068410a10741d000c1020514580c114540705080c2080b100c005103180e000110060300c5691950b100001c1652550720161041c100034003640071052007200c000d030429202c91003051080d0645c011042095006000c1c0956990491016024444605403c44000c0d002010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 180107221 1250 180105971 180106027
    0x703030f110901210e07180c120203040807060c020a02191208090a0306020c1f09120f020c040c020f070e0103030e01080a020f130512010c0e0121050717010b040506 72
    0xb0054400c3e490501c900050070903520050281340d410004204129100c200e48884440d15000000300d0162780008406c0c1d04440c40c1502594944860a1013516070240c00c82c0a4000e27031411040e8042c5070380002e00140440e00c2030722182025610f401140c2070002a40c400e100c2e803d080100e0100024540d030006000c0201c0041580d440b1075100d4031000300326044903c6215a81d4400109e07041145036240f0b004021814083d800e1006640d2591241000d82d4090611418001211040c2c94000e000380620008601c2c094410041000080402036444030440b24100e00c40c041c068022440c0d0300c092200324140c075095280c078050b807910720004540701035004005040c61907080c400350508001e1640200b200c405c50b4500000080c1c1820100210071980c00700c0c4144a0f813415000043c0039400400941c128802400c100010700c04203000e10040440100030542d00328035210030441c2036030f00f1080807050700a41d03071807101040c0c0e210114404284910b01440f5480031091042c20309951079441521042c0504c10b03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 180108471 1250 180107221 180107267
    0x60f070c140a0f140d0203070809010c1a06130209031b010c0605010b090103060503160306020901090b0d02030f0702160b090105121018060303050304171c020703030f110901 76
    0x72603290305024034080d08803041a5402d80340004d003c02e003014024069a0750018003280810031070045d5592140d00c900908403040480e81c42d0160380501c000e11506900545505802c40300b0b4800c56804490444a1510800c4070f0b65060f00b010545109036171305454007a005144900d5000105035222b1554448503040100c20380040c40055640d00a1342d0090034681035984d25205003500240a0710050b8016901a60112000f0100ba070700d040040c208a94100d100141d031501c0c1040101c401444a400c00072600d10009141074040a055004501c103074502c050141103078030380100490315042801d0440844401101080c0309001c482c2e00200b03850001418007500d0202c0140c1d41058880086500403000e40c1d032448100580700a04180c8000071000400030030046007566400b8005005c080c0015000120035461321192a21000813030340d480804180d01d4100e10003110a42001c0d40c0f0190b41180020704164414080d458540035000124540b54046820018401c00460324034055401052444d1000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 180109721 1250 180108471 180108503
    0x1104030f0b040c0308070506060a05180a0b1201020a110c010306053a0b07020f0303090d12060f030506240a0302010e03070e010609064505131b02060f070c 68
    0x17000801040d0322540c0507050300c3c075007002007218400c1943d03c03141c051404007601315403903041003500c079030b00920021002800803032200228031084a0a903200c803030766100155411030711360001c410101e2f02000d0001c441400c2001001141954403910405800800c002c2da1600e0303e004074400d44c0c0c0c00c5100e422405000c100f41c4c9070030350448444d42c0001e0710010000002c1c07210155050180c0d01c00c400920000b1480c600745060350a030384003510400d0354108550b120f078208800c0e219400540c000c04007800686003880d1241416503c903a81902c1c0d03913011807100c3c0d80e581d03100310380c190642200000061229215038550340066804000518040703034540030300c0c0004251450b0905966010308904d40d5582e8080d810148040c064104500070540320040e818900e401801c5180204000c40302100540102c1d030041c810821006045d43e0030451f405020a400ea80100040d580401d00c5040510f43e07051f03d44100c20b02c16030315103100f9a41030601034000000160064007030080300e1155486540500c049001c6 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 180110971 1250 180109721 180109733
    0x160e0c0904110c0d0f09050f03030c0f060708091b0915090103030e01120b090402060913020f03060f0f010e1513081006061706040f0209090412031104030f0b040c03 72
    0x30002c000200e24030100d006041c800040100b4035074208079040035072500700c0118010780080d00b580720319842102944541d80058905000791030030010b85004885405c4100000503844a81c2101d405000554420000d0500680041c2c046803074260030300741007820408801400706601004103442d00c03500351103e1900260301d9584a0741d000314040c3c1e03580d8494012040c0010310b010903003441c0041017420070f489c1102c145d03280301030107402c107174112074065450003004c0108004072105410f80300131920200d10079000c0b20300a80214403070702044401100070345c0381f1420070245d420b00082a40c0000c4001040e1003090400503942e2032480007100846040040510000a003d01a50009942500001074800c1c3e984040e01402014086600f0316081440c2400140b640181d00185150320a540301e401c84054800c480d81204c03000d08015003100e15030724180c01c0044ca5691841c54100c002442e00141c010802c1064043c0c0e4283c9034403103900340100005445079070322007001903c15a440d01ca501400400690 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 180112221 1250 180110971 180110981
    0x30e060f180103061502010c0206060f03030f0a0201091407030506010603050106080f0603030c0304061713030c031209020a060f020601090608030d150803070b0406060f03031b17030a0204030b09160e0c0904 90
    0x31686d0300204500044100090909801404482c0568502d078184400365501006550300c20444083c40d07a124010450100d002d040c1c0200041c00001c3d40319165802550041201130607a4081c030200d17100d0b40d0743c401040781110303400d1090400040d040c2c0c001c504014000b0858540000b0024101c90400d84a15009425680645d0111010030009403000310000c0034041d80ca984100110100c03480c941c61610040e2000096950040c09c0140d6648109455011980040ac246c0e4014100b0303030b050340d16101c01030000c100c0040d0140240c40344da0000aa83c0c6824056101501c2d4480051410b00445000704000f800650000b100da0000000007c00c01807800c20190a225004240d5115681014100701080f0303031654201030301c15103001e0401d0000c6500100995291441054100d81160340c0b420114255100019401c140340c0f0008103110404c10550044e2055900134030400c4181d407a101e0300c0301c0e41c1705c0c00010480115038406104010318002ca00300343c4d078045200f51905180410000000302120 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 180113471 1250 180112221 180112259
    0x10c060c05040f0f03031e0c0c03060207060516020c150c0d051309021e0c031225020a0506041b09050408071a0f011a09041503030e060f18010306 64
    0x1c1c0049070030000002d019401c1070040c0964038140b0f1400e0700f035440040020000201c890401c0d1001c414840380329125045844840c4c3c1c10540400c005034a9151800180d03005480503501c0781c2c10710f000300e414044900014601c026240d002003210103920010b101e103201141e0b80c1603c460700144a41080d9070b03400e003c079040b4502a9034a072540c07880c42c0b01c40c0e00c0e40d04074a0b4101395042c6105002000e030340094034034100c00251481800544441a55005500d184141704001494a00f078600b4015011120120b010060340046150501e07228100030480e41c03422207043c0900345e64000408100071400030f400704881c0049100c143c000c504e8030341e080c40c0152141a682200c0c04134000079003d080c030240d040c4c110b0f04681d0380130b801a01803c1c9014807550310312040c000d000385112190340c1280555010742c115004090060002d002c2100c0811440c1c4e020381c401d10040e4041003200c00800000e00d0120301f120b10a00402ca40d16040036658042041c00f45407038040341d8141950b8002c0480e240c3c80780e0219020003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 180114721 1250 180113471 180113477
    0x309020604080a021203070c09020706062d120305070f0224190f050d0b040b04060f080c030c030a1104140c0318060702030a0c11060408031806091e010c060c 69
    0x1a0880c4d00c140071150001c0190015203400502800000803010548042150f14072540541c17602c01c1401c06d90700a14990740711140140000b503514042402c220403035103640204d031400c107116503591991110064100c06001300051020850400090b03202d507002c40d82a4005002d18020007100d06030209001020900070f4a0200301060819041040001164038009140342560300010702e040c010345240240000341d00700300e40b16840400d06484030342c041d04c0703103071002001405240d43e206074090b811080c0d4001c0310404e0086004c3c40e001d44c100021003c01169019000b03104004040d1a0828013210b40c2c00819801521103c04140300801511100d0103502c450301890b98908084013011032000c1d07511845002c0381c100004200d034244c0c0110603128070402c00e0030316003840000d501d4100a000c80b0100ca082c0e001c1400706000c11a180c001015040b2900c128014075001d102641c100581e500410258640c000819050f05100d40b08141c050114840103041c400c1070152a0341d100010365651040307000c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 180115971 1250 180114721 180114733
    0xe01110711040b0d02090703110a11011d120f2b050a060f06110c0310140112170c01020910111203100e0c041505030f010605120a0c030902060408 64
    0x2400903820384080ea010040b034003080440d040c1404103032050580400a84141d00410014001500a0300495000e809902d1829554840f101c00548401d0f100d80c8042c245618085220040c00ca4201050521540381d400401d0081d400c1d10181800d98010791418440d000180321a4584180c400f458018107496100c0c901c144c1050114540101c1d900100744040701410020100302c901c4c0180325003425610b061900c8680312a03154100341c0b81400381d00f08284c06116015580c1da07512080d80c0070004486142032544241d90b41e8482300000c2e07440450020b4408a0308081610611200e0001400148034840003d400c05000800061013060709190a401040c40351310040d12906082c400383e0507030003003881100c6c01c2d418159442c461200ca2401140030702c2e1510404506403543c85000c1c0c0b0000c10614107955803140c4004001042501b007581c0b9103042c840326100108150340a07906640140350791545801056849400d4130002c4d01c0c4c9500c8410525030b0750541d00c001b586492008001a01040300102a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 180117221 1250 180115971 180115973
    0xa0602040803030f06060a09060f03091a0f100b040501050d090221010b030106080c04090f02031606092412060504060e0103050d030507080703051e0a140105120a0204020d0e011107 79
    0x5081c4002020103216031000c0020b0160140c00070520416141540b810030442020b099098009190746d95003c1c084c05010131a1254004886c19603612444aa00703400c5181d03103131015003074030604fd24007a0009070802403109002c954410350107010f8410300c00030003241610550b00411011140081d2990700400c0039442001c80b0b0100740503442c0e40b440154020004a4580a201a1206030000700302c0d20594490117071a09000c0c0c03004608a00d50740082c1940c030b070b08070342056090601c43c452044402144001c5400503c3c594126403d0240500800f1007140c08a00c49000711941190551a05005a5128404169522944200b001402d81c2e0040f148007035045040851501410003504401c26043ca81044400c503030014a03e03411608038100825603403a005a010384483e080401c0b003000200400801c0490f408a4001e0003410000c02c00d200d040d82d8960042c0600400c015140b502d031a84404400340050620758010f080c910721210780000c551104210b60b901b99450f0480032596200d01282c080 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 180118471 1250 180117221 180117241
    0xb030408040e07030c02120301140909011b050309070806040c0504050a0e010213030302010e0303010b0405120c04090f02120c060a1202071703040b01090b0a030b06030f010f0e0f07180209030a060204080303 90
    0x1100b100b035600c03c038508540c5094080c440ac142c0301c6185a019030000004610200025000040845a140b41c1910b01280b01a4010a950001c8071410618410020300180005000c250703603004940000500422500380814400a0500603200811300750f60b070703803c66109110a101820480700c41e001c079455031078076504000f400d60380d60700e0343c0000700d0b0001c100400901c113a00048600311f800550349440322b40c643c0d03803007103042400e00210507401c00d040c00c1006080240715110303560701d140300700c84650b082c03a0841c40321662102005015034000a04121241e002402540d9501c21814242009890512181d80e040e902d00c49103c015001000d01005120801103514251805084004400c200b00105100082c004403440d06c400340103146014007050158a09008010114204000074440803400640c504003d00000142c805a401521000fa01d0340341c010410308111041c00070040f249005180c01c440007984500500d903458881c4413240c07400a94203001400040006038042d58880c038041c1229 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 180119721 1250 180118471 180118483
    0x50c03070b03060a1e0512120a09170606030a0b060a12080307230904020904020d15090f0e072c040302070e0c07080a0810080307150b0d05070b030408040e07030c02 72
    0x2000e201a510300f0244441117000c070560100e4034111000200e03264410b600c682040741b1060b10101c0071600107402c50307006802c25511011a2062021f4001014981d00c005848810540e800355154102004e110040740b4003101240d080400241070000003555111284090890400111200c140210400542e5504021414850800707403c240540560086a10714188941c4160610850b40401c0048242d207413581a18601038020004002c9501140350141c0f4103d0b092040020184c10314490320418400c0340078003095000d2200003000340c01d040144c031a44408855005000d00341100950307401441208144d1401240650058100c107820082c0204200030014060748807181c00700b040100003071841085680000c01f5243c290005c1d10f4091184035030320503650240d4510320020070344031b00340a004041444c4400c00c0c060b04218002daa441440094040c0100c0540b042d04503103c00c0081140c01001503a1061240907503e14140e15126090386942c400d80b45440000d0790751500003c165010008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 180120971 1250 180119721 180119729
    0x30804021807090b0315090a0b101b02091509040c080d0c03080c030603010b03011e0b09060604030f0f020607060b1908071832180303060d050c03070b03060a 69
    0x2581d94520b40580003034a4040341d0310030001d200b040040014112035000000c009030b680002d0070300740703142041b480c1c0101420340c214486108003140d60100507a9405005009210745d20302d6150a03503c0095001c000c0c0145004202280c00314110600c07100741e55a0040700c03846a072180400c042500c0c00d01201c6880e000c81e0003014410301c4020030160f404247c00c11901c81d80495070b5201d1640e29036820000c02d01403d0b40c1c10341c507034140d801e01c1e2001c101c48000c030b8102c8a0051070341c2e80810a008507802007184215040c0e51003504041c0800007800400c89050b0684c600c41d020301940c413072640b155404118958041d2000759103807a902c1c4259102450500340d02c500c5103000e82c213008411824604219202c0c80e9610800b2106600b40c1042807415a43c1e4001294000c120012480304212180400e210300803d424800041c850210010b074100301c000001b105884901c0c4015400c0d50303600f400317004800310f0440003a9800c0c46800c1040d2001c2d503003000140c018101281d01c0c241c07281844c01c06d102081c3da81d83c00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 180122221 1250 180120971 180121009
    0x30a2301090201140730021216110105070c12030305010b12010509070e0d05030406110703081909081f0c0c02091506071b0513020a0f0e03030c03040303080402 70
    0x3440740541c0e0300c9130600440c80400000c1c00c2c0e80e450f403854000000442c10010100241d41d91a11002803004080e052240003050f17000d40c0d032242c0070000010224425094041c980c00c0a000c0040d02060103004030301061141810414500b007680c0c0c0742c0c0600e540d0030303138404041c080300e1040402c1010b525028460041000e03110036414095283c007030240143c814011280102600000680b8041c03144009981c400805810f0701c00e5120903062403501ca80c024001c01000c20b0160400d50410040020325408607034021b2a018200301c0304000c080300a110381050b04c0304104071103002286042d000d0058104075010380d212064540c0d21060480151201100301030207101c00030611074050317204d800c3d0079035200c1c4080c4110050a80040c0c005181402822000707464a901081c00518645004803680700345c1e50100c0e4100400034040701400c0c16031282900320301c00618118403000003980240012640da0800505690520032100c900e60710755042a80f0950000d150f040a0105505150b440c907003099111135 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 180123471 1250 180122221 180122231
    0x305091906023307120e0102030406200a0e0613060f020d08090304030213020d090c030309080109120309031709030901140a081803090d030c03110d0f0c0809030a2301 73
    0x3940f040b0309203070058900340d800c044007000511110301c2240c1c00e42d400700c0c151a00300038181140305528000e420464081303680614050440041946d812001d01003040c211541518007000d00c4400c85840e4044501c40c1c3d08001c003849250913a03115504640081c10055903200888801000000d1401c4c02c0b02c1800428401810240a50243c0200859041c0e0390184c540c2c1e20a1444913031144d00910032001c941c0b400fa8a4079010004000503941d00404490195499050268440119a08858090b28014143e00410300844a401d009070000c1003158003d090001145d2080c514801c5000d00803103105055804c002400c541c2980c2000d80d01031010301150f0b4150800380e484a0203403124002401e800c40c000e1100e290744020200c00c02c11502c9a8101a10700742c481211860b02501000d059001100801d29104001110040001d00905a42202d640e071080e8400084401c2d6502041c0000c1591f104001f003240c10402d8030108401d11249101d9841c5041c40b058440d451002420503075861035903a4144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 180124721 1250 180123471 180123523
    0x8030f0a183504030b040c081902010f0203070f0302061f181805010f1b0e030601060e011202041202030708120403110607050109060f0b2b030509190602 67
    0x200001124103407505041c0d400100344242e481c81c4055000d8001c40740d0030010b0080100880000058090303442901000311107525011610b484400610030000d10144030044840950f20030000100244618010340b460702c07445481d05e014101040070b0a402507407080061124152041901d034820a440c0b584032502c02d0f0a0407000a1480680d10041d220030b038868800403260034218281502a50b440030080000052500b00200030b0074080044062030501c00318584007440c028041c031105c686000740517100c03a0382409416a000c00790024003c0c104113040440c180c0f42910707803000b003014007628201e03241141d1340340c4101483d040c655041400d0603080070301c0020b5128007110680e01540e600c40141115030002102144050181600c060301d207600b04961903040c8038695104043c1142da000c8244803c0f42c8400500c407090b101c4401302140410b9280013144008200c400d501101c44c800e1910318a002204400680505464543c0207203c000e00d51701004a02d404220415901890400889606642c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 180125971 1250 180124721 180124733
    0x702030f07140c030d03061806032301111303050c1206070f030906050c12010e070f05070f06060f0602010e1908090a030b010b1c050112080c01060308030f0a18 70
    0x1d0880010000901002400c10040c03051000c1022078402808030b85118502c40f800a010780418441c0d40e11140c4100340170042d505640c022801601c0c2c00c01940b00400e0160301500358090b8610000c880d03076561b0340c002845201c2124000340b52418407554000001070440c1001c0342803d200051042c815118080744034242800843d460f940f042a40c1850b00f000603901d0001c2c0c3c0542180840100002d141c94100403a240c800c01c040d107400002590380403030684e22a0300d10752000d801983c02e44042502c41a141d100d8611072001032515030710494a8031440c03903042d6561400c1c1e8459401c40c2d845192040380030300080c0e80c248105984100102c00503c0304450300c042101c1c04401c4d030790300a007c0810005210246444d1001c1202c021984403000d42c01075079546e8607038040c40c0c00244884221510300100c0c5400109035024850680d5150007070a08000b24941d91006240c2c00b041400303c1035500d038200000482c00c0320001d5842030010801451030fa2824100800c12502d808180c0d0041440d410300030030200d01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 180127221 1250 180125971 180125977
    0x20705010c110a150e01031a0f0109050d23030a080103020d062c0c0604140409150c020607080106080f0601030e010b060c0a120801060c080706060513140702030f 71
    0x28200301c0504615800c1401485104008564000d014400c0010308050400148a040c0e15550380e0840c100540c2c5004509994000203225144504041800c06a1502c94510020b4010505000e00c0280d5240c0c04100d003c02048000c1d40d0501c10115078001c0b541c140c00303018110044102c0a545400315419010f084240f045c000030b4007605a26000381c0c01c1000c1030f444a184141015041c034895801c0c0510000c240b00084038030720741ca0145211101403800c00f001510256029891804126903022060100415180e00140c2d4030804800410403449101d110b00b00503100d1660103410035151220300500b5080040e8402020001c5043c02c12001c20072402036a500048240380c081040c5100c2c540b054050400419002e03803140001903814030b0030b10001500e0314003d21803500303500407420050080d203031003009108450100f05660000340015418a00030140c131403040200181254583c400b141d407503e05000002c080b15507402540d112079100115042d44811140b0040d840c104000c400d900c8640 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 180128471 1250 180127221 180127229
    0x3030c0a0f17194b050a090519030b04060b0916020613150e160b040e01030f020d1205030a050c090d080c0132070302041d0712021303030e03060402010207 68
    0xf00748070000d403c80c41c4100c1082c2005640511042191100a04542c041c40d03440005200d103d11500c4d00300c0461300480c2668040c4016407104080c3e24907020078402070b0200341070414480300040901000151882c0c1002d8080c902a200006200117200f00740071060502610008903d240340c46124003080c1d0005400780e0116402211b01240000c520300140c925860300d0130826503e0504000c14070407800060040c6a04500101901000e5520008840c2520460041510b40c0c15200014004100f0600809502d2032002e40380340500342194640607100180c8990102c0062000010302002c0401130058540080188003454504440b10000500b045005140280540004140ca6034801029880300380c003500010504403e1400b50038400d02c0b8046518403e000c800001404540380360300c0784c405e880640303001c0c0c00004035050b080c201d000302c2c05100a02c4041080340850514246c0d84541c0003510302d600103080b8000310f590640ca0301400c080c288241140c041e80c0030508000241c0c0c4d00007401021a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 180129721 1250 180128471 180128477
    0x101112040f14030a11010b060c060115020f070e0403020c0906060901180e0a0504030f08070e09090309040c0207050f041e0b0d1b050f01020607080703050603030c0a0f1719 75
    0x450314241000c1000b10300070000d6030101184009065801c68072030203c040c0d0690082100c51040d0741040002c0c0107600c0c69000c264000c1c0c005201601c01500c104900000314011122004640c6070305c0c6140420a40081141c60154014001015010450881c4c0c03040225130142d071302d00c0d105000c20304a02940c00d2590410244691000741100246a0000074102d0490071400342d203000c0310000045c2030700352002c50001e41440e030b4901d1420f106082c1d85000c2c1c509580c503510f45110003410030204010151540406000030050440142d88070702c40d040491170b00f0307009041058070b4402000200e101031900c03680901c1c1481d09048081a4150070908942c00780708000500d81c2849021500d4083c961100400f07484404031071074024031010000000b2142e0403200c1281100d5108012600da020a6880320040fa03850400324640b140207070069035210002030116402d09080b44821440c040078448152403208400d100c9106002025842c5070300c6403402c40c00383c0e150000c0301d0070541d2091064400c180030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 180130971 1250 180129721 180129743
    0x12010c1215030510020304020109150e04020a110613060c050405060912032502040c090b0723070603090b0105100f0311120405010b100e0a0303080402030a120210111204 74
    0xd1034504010403002c0c6810900315140c0d03588481c07140c0025070080d141640070518071180040da030760620b171018010000560340c504402d021141408040d4110300313900c805000501c1c0c00680c146130100701c142c0c4221005040e139000c03a45036050100441c1e40c803100400420200300414480380d1168011a0804c1c00242e920308150950398248500754000d501c2041d404488443c03281d06028100400006c01c01d00844080018207490790054035405203d103e102080e03503013486401c012030369500c844002d140c5888503c500c01c2404407802d900b00380058001c0c070301180d0354401d10070600c821000384c1c80c09000d064441e0301c0000d16100c0068509268158100201516083c2400a1104090035644240800d15035000c45080a1070058060a601e06031140604000e80c0d80000d0980300d940d0a01d54882c001c2c1c0f100020905540f0115015100244166054826800c3c0400022164601d18860809942c054040c850603503100c0f0b002d0b5016012240c1e11100d041c0310700b40c0c1003001c060027140c226600c240203c1c0307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 180132221 1250 180130971 180130991
    0x9011403070e091905070203030406110301030b0402130f0501060c0302010e010b03030301030224070309060806180a0209060c060f01030c06050702090c0921010f060f031709210c12010c12 82
    0xe84c00114444403030b00307505000c10f1090f4182c0010140d40124813510f828410308200c43c211503041e010074480503007800c3c2c458000c1000340c240308441d5402246456404202214084203003000c2d074500f03034804400100603140da18241942031003000b88020006000b441803081001c00a5981d01041c08060b205a4081c99601140e4100420b811181e80000c00b01c0364560440d8180070705403440030301c10030021607101e60010f40e8034030f003105401920604200401145484028150380250001200c0b1a0044c03c104203a14410a080000c0d03481507105c0e170700d442845e40c19440c01000c103040c507600460a1210606ca144010783d504000b031603000700705040d07080e2200f25820004000380184107000c5400403108003503002c24401074009002100c51b5400a01c4059901c2c1c2d81400281c1481c40007401031001c2c0c51550a214060724024a000700c401403035084e0101038651091002d03800713103074034050f207500c281046061400c2050321102d07410100c00080201c2e0814180c003603d010b0481d41c2182503144e45045c011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 180133471 1250 180132221 180132241
    0x2030301051503090606121624030b010f180b130512060f070e010e060d1b0905030312060102071e1401050c0607030c021903020312150d08070312090809011403070e09 73
    0x142031400d4411210001566849119427650840d40c00c084803480c0c600034050324902074000c61908640c1a5035000e0b01e400c0540c4215402c1c0c3c148607009580340c0e601c14000980d01d0440024094200d98500210b00750361902e420402c0700510150007075442e811120402c00402074460195910003158240419125840001219080e011100c0d5a902080c041080d1501030090f0b4018002c64860038a1000700321124102038440c01840d1050302c0d4181d00400251010480040c091a00107406004542d480d0307480720704407000d204404412450440c0e00c0740c0d04100c0d0b01a03410a020b007114082c00d000c0d00e003400c0e0760314040d10740c4801040340c0141500c52100c1e140d10391003045892004030040c121040f090600c3d150094680d440300781c0243c541400742004c20981c140e10b41542c190410014004101d000306540e40b0781a03500560015014080ba0602e14103101d600ca009031003481e4030510503141c0e5080340c04c0001d4401d81601c540107442e000300b4410401d0090f0070000b03642d0088000c50300c4c004255680582c039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 180134721 1250 180133471 180133483
    0x705030a0b040e03030403020d02070f05040222080a0c050402030f01050418060e0d020c09010e0711071208120a060506041a0c070f030309080105070504051c0209070203030105150309060612 83
    0x100741c0151030f1a0080035540c0000c40510300551095080d5602510480c904070798640c050b008100d94403014070f02c00c02551420740e0003840d5100c6101c0e20310003410798262007448442202c1d4401c0746560031281c201c0040007800da9000d0040c113404c807011415030502c0c170f424815070081401010300440c1e0f04c0d2299030603008210407021070302e80e0101051001c0c0c10420b900c0c0d502d80170712404041c058403078081d4014032440c0c1426118140d84400c11103009071780c0c8640048440c095800c01354003690007088800b01c0e008a16080c0300c1d804074041c0e500a42d0301c501c01020001500f000230540ca40d054502603040c07105a8462089078100c0c1d0340702181850107002c96003400703010b100d8000c004515106030000068401c800c98550b41c02c0b28080d840781e041d02503a8000440c01d90350216040400900c007040140101e14101c1080c1c0704504400110720510740003680810343d0024140d03002000341c0e001100401091902943c0b141c0402200c00c029403c500b4041d079084c0c2d40b00b4025001c039214461020844008200421135 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 180135971 1250 180134721 180134741
    0x3021203070c2304020f0702040504031e1d040213050609060d061502010605120d14040305011409100c1b030e03060103060203090d08150f061e1306090501080705030a 73
    0x190414240c0e036441d0400f0082c8801c0d09aa40015601100c2c0303a29240500c00d40d01101d8801b41c0c80e0386010f0880c0d0030000240b000400880600049800d5084d990700c481d40c0805503c1c00c1500c2d0320710f000385c561400c1410f40f160381070010b208138010802031200101c080e05800850b103050fa61191280c488000042580c0500d40f143c00c94103117000c40c002520020b5140300c400710202d03500200940354945d0107006090100c0209507030594066915006542e20a000038042c800340301c0d07481030920703859540c0c113803c2d90307200550201400080014080040400d20645419003040c5404010000318148044d204600307072040019558650040507082c0750003416006480c0c40c000303043e24215a12440c00f000250015034100c2c25034440c0d1007000003014040c1081c64015180c4e10410304048900320100302d0903948003d2841c2d00100180a40702c0044910841d02540c80d181c0ca101640351240d22148640c00e1800c0d0f4060002c02c808510104060390f0082102c0d030300010180382042e078170f0350340a042c0b0b400341040b040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 180137221 1250 180135971 180135983
    0x10b06071a0708040b010b1303060908091f0903060f0905030c0a060b060304081213061b020c031b010503040c080a0c060e030d0e0f030c090403020609071505040302120307 75
    0x1800c103040141ea03500e03945150125081d0200d09460301c800c200d81448044800419004406006000d50001c1202504100940c102520501d40e101d64a07241900e40c060022648403102013121501c7d8a407551404015202d03072120100c0c100e81c038400040060ba40d81c80054445982c0f0561100300c03404640162201300e4108046a984030301c40141d29a4401195409844561401c654122180f1701103080382e0140340c2190400f0300300783e41ea0030641c0c2000005009041d550000800080003e2143d009c1c01c1c18200b003140d00c9070000c0c0c107284006801c002c11303600050710941012000840440412103c148141406c1c0b824a03102d9945140c640c1c080300c03164024041c00e00c114200c16080155401c90700341038a41507910342031082c010500380b50746d0340800706888000c04c0e0640d080c8481810181e00d40c0078440f000404a690020559000c00c0c500d01040d035003580140c0100040124100d0204086401410a01180801e40c103061030020403a00550000901c88c911880050010150800503100c2058000c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 180138471 1250 180137221 180137227
    0xe0609060d1508151003111c060e010b0f030307081602060d0203010b0409060501050a0210053c0709060f080406020c0f0c010315030804050f041e05090106050904020d06050702010b06 80
    0x42156a640368541e8130190200d00e03220000f08440f4400440008880d4000d16007068081400b00300045040c01f0354034056107540c0c190000b00841c3c141e0183c4268903190704000501c2a5168080c000110b40d40c0071140e020b80c0c010482c0c500003034016812906507810155612a070003c1610008820780701e54a0720454890002c800130030400c0d0700d00000c10880e100c0b69030070400301d980d840064131580501000f010250300410b8035500000200e800141e0701026500c8071903002c070480410b400e0300030123080a030500765004852580110605288464014000b410006001e40c60b1160040c04500110400c008100601c40403608200054050703800800300802525480f8082c3c00280c2d42e2010440c9515000904001d1004154100910b9841c282c0c3c0c0c1044000e45000e0405003030004089084c05c034190403a0f0b0342c240d404201d00ba400d0806501c142201c10101d09810000c80e240c6c2902d06d03982129229001c00c10a0100603941e840210038820b40c44000450b0300d54441c1c0c81a40100f40ca41c0b051600301c1000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 180139721 1250 180138471 180138479
    0xa0e06031803070506070e0f0112050703061a07020a060503010b0301030f0201171608100b09040e0c041107060609024807290301050613030606030606050405070e0609060d15 76
    0x450501c0c07040f00ca9640e07170340c00075000f5010040b669108c0e612a50200c0c0201200c060007a1980d04102e51080c098240801c0035940c4851000807c0603034424481c6890340070654008500d0140780810050104c1d19242c1d040d0350501c100001544410f100007043c40810322200c40c00c40e4002e15800855160f1145528060f141801d040803002541850180004400c140010030b0301ca80108404190356400d0b540b2410040f0160030b10004001c21310a00c200741c820100003c850741e039280203241031005d1014905860b014586030000503102150405c0548600500c9181c0c1d5054907864113100041c09140c041e00020342c92522001d40c40840007410740c0c3c84000c840c146820340c200040042c2150280402503a01c1d140c1c5400c4a9080f4031040e2a04800d0001000104a145040c50160011140021000110700d540c1c2d510305080342c405600840700d882e102c3c04104214981031040607031080180c14820403c42e80b240004001d8818401c480e4482d45000c02e054bc0894030720751018101041c8101da54000c3c6460b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 180140971 1250 180139721 180139723
    0x140c07030b0a02030411010c0c171203090106050306180d0503041e0c080c010e0d03050f040b0a0201060311010201050907030204020c0c061602040b150d02030a240305010c050a0e060318030705 84
    0x80f04e050380d0104403c06c0650007548243c48184000740c1041c200410035040c030002a207002d8095000000310303c00c0d220005000350b03040000350300801a42d170000440c0d910b03090500d4140754000348101e0700803540110901076a4004240c025169103e442c00325074070f655914203e40302021060340308182c100740d11103030420007160390303178070700c1070300e02c202c0445007414a42001141c0c0d009414490035000b0002e038500c8400203015402401810381c030300140c5400c0903252000840c450308103108180c010303034448038108148880604100c82141080c030082c4414a8a070340803a540c1c005c02d1000034010303a4000389504030b8500034001280c1101008010f5580c038504640c001c04004100078082c0d110364906403a8015034a841b03010145c1c083c0d00d1030310325400c00c0104c0603010000e402c028111802c95445007111072042035600051032004013030000b22210f035800d6091003401c6075584511b8206200041049841464101302c0306580400c080311b00b640e4a039542c0c1c1d240303c020b0994821403a007512021600e0001c0041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 180142221 1250 180140971 180140977
    0xd08060306060a0f1202040e030c07050a061706101b030509040501051206160302070c180f060f1e08011401030b160509010c0201090f0807031a0106140c07030b0a02 72
    0x508030200c1d03901e5110300042101020451043c80d078003402040b0208005415417407003140d01400100f00050450b100c04c01d5606551100e006480d5a42000009210618208003600e001e000f151418170204444083c1d02034020b50060b0400c0d10505000354070800340b902c50b00710405a03609020b541c804030b0f01d66280140045d000101d019120341d0904001013140e092803550100742c2c2c4441001444030391620307980403403113085801d00310f030070141c08124000c00709170b4945107100100301c07141c1090484840c20b03028030101c82502e0b032030705801801c00f5010006614000303428401c0e51034120b8001c80001144800d6046182164010343d0203508004210600c3d648900955040364010110030400741d41d0740ed032140b800c00910900001040050080007010351107030381c150b0103491060400021300d50321400054081c18030b80c0c0c08651a81d201d08000d10401014540b00250010000080c80040d41014809000a0b0b9050110001041c0c00314000040c0401000f1840045400040c507862604101d000680a54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 180143471 1250 180142221 180142231
    0x1f151503020a020f0307020d080304080c030304150e01050114130204090c02061b0705070b0f07021816030b030606060310170709111e030c0d140f01080a0312050a0e0d08 74
    0x2c0114003d0121302800031088132112540105245030040c0166100b240d281c0024000707a1b40d004c0140311140480e007041004500a902514411078861251610b140603144030800c81140da034182030041040e0342000c111203482031001c440a4043c90881080e2400070301070b40e4404001c060034400542d41a940104005010b009448121112003811041810381407054000040241d4828401006141040c0000e444d4040780121b0f000e1030503101e600000c816842010f0780d0382d040b400e00c03010701403400c4e00142d075450310a80b541010f100414824000a8940314018104c0d801550000009850a504201e2a030068040780140c0035904000c1a122aa2120306002d81042c4515111007845541d03003180503518805d81c00b2260641d005851848441d6503007024022000100051008280380c0446000f401340004100d0051000c40c40d00b01e10b01211020103a22400c850b81202d502a00402d0340324000d45c0da40012030b4800701d01d540301d109410000b048203580b00d201500819008400f00d42d880806603010f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 180144721 1250 180143471 180143473
    0xc090c0c012f07030504060e130c09090e0a11040510120506061305130f0201091a09031509100c020a0b01061206050105090a090e16030c08060106021f151503020a02 72
    0xb40101c084420242c0c0300f81d403806000300d50140410441c0700d105200c0b4201905016000c071070008410914074040d150708030792607008940030040611048081d44101c10180ba040c9008260102154032a05029a040700243d130050f610361000403603440342e10f20341130020f000248000050380040d0524a171501c409a4031a446082c003d041c40c084460b07917004480c001d802c545a80010343c146603a5480342c581507600200e0500030071000000f030900760ba020510340341c051808079a68485c0303840101410701042c8410074070a41c41074400d00c03c01724000900b46140012910001680300c44242040e45002807184001300700e81001d00000c05d803e0b80c8540f0000c2400030f400d4042c402d054850b0019103a80c003882002a40017005200100403804d255009040d1003218041a100040052401017064030880e0300280c1b10380c0c00c100d2040040080404c10700c5c1c0100100c1c8041c0070480d0610086e000c62500b18007900c0007154841e2a040a00714402c072005c0c00601d030f910100c1401414508001e4086e4100740484005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 180145971 1250 180144721 180144791
    0x70b0403050a12090b06091308030a090c0905090d050c0309030a06020901123308070b070b07020712151d0c030d1701060f11011e060501050702030c090c0c01 69
    0x40f078409801051a403030703400540b50080d551004180001103900409260112039034001842c041090345009501603900f01101050a4000e4104580f0402c9181d012400c041d140c18100102000e01140804800c03445281c1540d44000209030319185002d07074008540d0500640000c002000003036801020401800c0c0c030344410b10001e00c1c039100c04a0341c2c580881002d204041ca0340803e80c100c000381f4814030540c3c2d060b10010040e110580c552800005421018550800040315400c1c0440c6607902c0b54008085c0c40144559030030480302001c1040395a44c01060500c0408107a40e0328840c0d50009c03000e2500040170403140da1980224141d5400640c0203041c024018111040d00703051042016402188100030f552a540c0d28000080741c00300340103946882088083c8003060407100c8280a2000180034004100c114425901c24440407a10300354089410300000b00190b0005880109520000640071200d07020190f855102c4104135201c0d08240103180c0d46003142121661509140d105080501c16080c801e0b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 180147221 1250 180145971 180145997
    0x9060801090c090222080d03050c181e0907030501090f06030b1801090219030c12050c1026040b07030c092907080a140a0c17070b0403050a 61
    0x8201d5841e200c0191820007000000d03c441c94072900103080b0000700103001038140f07100380c030350301680003940d002040c080e0000481c0c0398200382e050040c0394114030318138111803802d1464401c8108400c0c14010603809250f6040e001d00041c0c0c528940201064405840303001503140004e40100104003d005000700c003845c003084031081041601c106415641d000d800300c1110340b50503621040c0d01202a0550304150340f03070348000700180c660300d0314055030b901d8406910f060b07181949064511500d85400408180e9401807510000c5400010030410700101901c1d28a14841d035044107e900c07000e4916580190120458140045c5082d2800c40307110307130300962049160b40c0761441c00710151040071482400103045404140310a00b41181003c500300d042d003030b1071070600481d0042000280c205940980c3d40850200d90200900e4004219111a0f416002e0141c504410310501500c1c8003c102c0c00030f03050303102c2101d614160195003c202c4000503080b0582007028074151400502650018903000d00044041003002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 180148471 1250 180147221 180147223
    0x60f02280908030a030b030a020307030f03090602010b0907031e020a11060c030411100921020f030703021f1803050319030b130b010507210e090912070302150f01090608 74
    0x90a49103020b01651605150382400c0300074008014549601d4003911030040c00680d010449000110320401d45e01044000a090250504120342e00041c15a41000300302043d40d558180c0540d030080071070400007000000e040ca51000048507240d035288a03480064418005e60b088900000c0072017400048921a0303071515070202070b900054070010070340e041d011442c001c02d03e0608118452810686000c0c8403060759a0581441c03010a440092542004400c0232800d40c00c00c114050ba800c10b05800501d40e152860780880e0107010b4540411304a50b2640300fa80d4aa00e00c99400b0013806008041000c01a40c2c407824841e4a0364082c680d6401c41030380701500040d0044c0640152400a6001080f0891400020300d20b0005001e6800040381080001c0140c00c00140e920f0000007501440c030510848450b502c0b4001806032114035000324440e000150401082c080009a000c1c0e0a130718044800c1c3d115030300740c074050b440d114041c0c0c4800364840c01c7c5401c100d280c3e5400c2400c94101c480c0e4135414000d566488a1311703 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 180149721 1250 180148471 180148487
    0x501030c05040f021603050f0c07030b0f1302030a060507030605060f0315120c010806010504090207150f020f03041b030b190c0f02150c1b100b09060a060c060f0228 72
    0x1c8029008110317803404280a00e01a01c80d103207000107c140340800e0950001d041c20195001150b00843c5c90050020140c01c140c2816130020641d10406552241c0d0b4001a5860b505103000802154980c4000743e8002c0c401d80001005020140400392034080040302568550011107640d0a0680400c454000500d040c2c0c50000404d0041e5001e04541e1540c40b0046030400c40c0109524117000c0108400166190284001c0c081c0b58001c90311010210030306110001a603200c10411821240144030214843c070100c005c80390015445145813000c0c40c000c0b0b20401d0018800c3d400900720700070107410054122002d55a6004070791101104000b00d00c0c1141e0140c0d95800710103070354401039001110b201c01505d00d001059400c1041421500d050890200c0300d211000d4a0859551003600020250080241c1500403202072480072141801d50303141000c04921500114840c41c0100001e40b00d2400038880141d00240d03d14a040b4020f547d0b40c1c0d404d004506074481540c544080085801c11700700c0c1c425100b1021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 180150971 1250 180149721 180149737
    0xf06060307080a06150309020406151403100e1303020106080a030906110c1c05010b09041101080a020d02040608010e0601030e0c0f030f060703140c04060c061e0501030c05040f02 78
    0x94150744035807008503090b5800030601c0b41541d40d22107010070313025410380c41c04224901e59500455000118810b010030380c4c0d81d47c0c0c1b00706186246443d211200035000700e1402c204400c0d0000e1152aa41c803105c2001c0344500ca5482903a91440384c0d018040441e9210006141850194000340a0079507140321590b0784d14101a000750005200c24000d0025a10942c02d492011052800701c803580808000000c1011200907125185103e0314020201048000e015020030090301310348030015860951a90705c60120303125002c2d4104504200015a201c500b03905694040d0241d510843d200d88e1948005000c1000a0050801c500e031000d0004242d98843e01034040d0707882c0d020003d03080c003608990a001c050744107503031016030500855808400310481080b115128040581d00440c15070b120341c803070760441ca002500031a54000104800d000700b80d04005009190782d0700410020b40802d200010392208210003400040303190070301300000b09000d0940c102c0c3c0c00781d5404460801020000c08450004c130b12400c61 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 180152221 1250 180150971 180150979
    0x90809030717030307051b0610080c0d021809071e0905090607020c190302030f060708010f15080703060302090a060302010219230a0503040801060602011a06180a1d09060f06 76
    0x381a01c0c0c420000381c061080742c2d45610001050300400c590078098202c681020301b01006c601040ad0400401c5466240002598582002c1c43c2940102c0d1080300701c406048001c0c00311101140c254001045801c0c0180b80468050340d8031550403043c0d151080d540d1003641030680c140404240114004204bd81c082c40ba5a0002d2140300703040400e08ca070010f1503102c9a0503040350344100201507101807092160300c201d130902414041c0703022540948401c4068202041c0340134040818480762101c45496250014281006034503691010401c03005030246400080d000031410040c000714134801c3d041041903d100341c00340c1d508800101c296202007180044060000b01c0c02d0241c100c084414140c541e070350b01030417400359040b4400688071a49194030075480340d86035039944c01081000c07607828491082c6521850204d6090074216000003200b82c061350300c0c0a085070700000c3d0103500c169654040301c4001c1280e80c642d82c3d0450701d005250410807004a41074540b07809402d00060700c902081c154248a81c400030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 180153471 1250 180152221 180152227
    0x11090d0204320402030d0903030f03050606070c060201091109090a020d081b0f10020406050913060f080d03050c1e0706091a091c12021c09080903071703 67
    0x140801001d088602440065502d440c101d1403a01c5403001d14850211105501241460620b44181031400340c518100c00100b0106030410701c0001c1d0300441d01c01200b0f80501c1c021685407200000103403d4030982000404201041c40c0c00078106c0d4040d040b0881007801012400380c9180e01401740440c9070000c80341441190007248002005142074100c04000e607008034400c0b4244400d50100425440000000301481c4d441b41c411404000c504111801082c01c840400703604092a2120241c080e00860000c54450340588100548a811690080c401070030007008820350340c1e82d40c00607252644550071040e00040c0c00e001c0050310403401c94003112104511041c030740c40309180040035035500780c004160444106441d070f1000404281c10b0704040c0100030041c6450103090034441c01462400c8142c00c1c400310900d07820744a4044d01c641081b00b1906601032801d0150395081000d1402d00644038184071802e20620703007507440c014040d4510281c801c00d00d050b02100c00183e00d46542c1c0d4105000f0740c44082c01a4010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 180154721 1250 180153471 180153473
    0x1050108031b070302120105090d2d020c0d121b020a0b0901050409050f160206070801210602031305010b06031306092301050604150b1b0309090405010b0411090d 71
    0x222200d0b095842100e0305a035400354aa90008462042c2013001e814540e45600900c1a07807903091107014000c4406040244280c0400707501d8550303141c000c0c0c03503288240b9207180034551300b81d00900c031041c418100288404041b4100c2d00e0714a010056032034042001440180507803000181003c0d031420309940040000e1980c518150107402c550348a850340c1410840c0605c80000c0407003481c0a0603029103000c980d1000b2900d000c134880c0d40145d800c100c5a00465002000348554150842455419640c0c2c0e00d200c08041e840700e0580c50303807406d11014010209807001081101101804071450300c00c078450402071105040007400c00c54070f0700007960b40400c207420f420072040010350994441c2000f64450500f003075082c0205480f524684001d030507400c0b00d59440b401041400c0c0740070301c26220103141034100a26803500700300e09120140144a03405402d0503603485c0e026124482002541d0f01d001004000690382d00e03051800d6030207401404510382c000e9040072495440c11500c903040da141504050013011001e0701c9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 180155971 1250 180154721 180154747
    0xf14090a030618170403050d050708030a1a03070815090604170706090c0e0a0b0a08030a0302070809030d090f0b031306090201030608011503050714150304110d0f0b090105010803 78
    0x300c8054010303c045040c5000000d405003101210702c0301608095911207146080c900d04000c520000c5a0070000d003041044006070500c030a0300d800c00302c0035000203403140d007602101c0900c104080d0042c0d8184504400020300143c0051803410504003030b103c5551985800042c15a83c680035038000341811440003d00c500c000100f030191100b61301510010411030241e8551400b80e41040d0000c6091100f45010800c43e90954000c2d202e121704107451002410303160450303598a9000ba24107a07001c0680005501c0e05100c0800300f0703149100340041c1511340404211101410080d40b6200c0ca2002280c00c1e44002500682d030020f03244951582490640420943d40c6d40800070542580c0480c18155500800704051500b4410040c9410149413442d4190b811810103c4c070b8640d803540092903a40001c120001c0ca070302c030910b01d000210b14811119499403500d1415a0402080c4019150801018100c810901081c00c16801c44580540ca1550b990b1302d52040d00c07400d0329024000c160300d42d40100084400108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 180157221 1250 180155971 180155981
    0x4090e010e0a0b0420180105010e01090303090513060302060a05120702010b1020060a1a09090a020910080a05010203160c0b1611010e0309010306081b220207030f14090a0306 76
    0x859107a0030185c5610520004100c0300758035540d1400c0f80145001070045503000301080303403141800d0a102c0051841c50703600500500d82d5009007805005090f84600c0201ca40d030700400d0280d41c0c002c00b80c940356859590000c0040d00104130100400008001141000b4018032a404440c50090404010310844480035a2603480740342200805003400c0184a13003100040c040c03240500d94940d00400c080e40303645800c2c4403140a80150031700c24110788043c000e0b40b85c00020702c090746580c191824011a690725200100d1107105610012860154007225010041c06600a500c40c0d44070081d034140c00044d030710049401e04402e03070000f8a031910320801318042c20020486904190368a10b429503030004685d000c1d60a4a41c2003070100813903400803075005461b42e098000c00e000b420485000b0661204140070001300462044540ca01810304268050300907501034450080217002c200301595209000c0c5401081c0740f20030402540011045410409010701440440fa01764a005040c402c0141c1940c541c400282 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 180158471 1250 180157221 180157253
    0x6060705120307050c0a031e030c27050a03290402030618010e0d05190f02030d0e190317070203031e09160e040b090106030c06050a021204090e010e0a0b04 68
    0x4502480455407481e001c006ea03a00d554882c0d03490101d454522040d15103400f900e0311005c404d01d41012059400190b0020f07030f01104118803800761800d000b91921070b50f100c403815040706400031318514010040c0010079245000a100003d00040785039101c1300740300b48012090760029856003146000c51000b2090209246103034180c5000021107156441d121480e00d02d001030728001048010480384030032441e00b0626060320006003426030807003001c0d8000079224070403560120b0b50139981e02c000c2d010400300bc0024050101c0820310401c0c041140341005003814a201502e98015025440010b19051000c410f90f40a001c0c2c0035598210201c4030030300c2c01034040004040810f50b11624410782000c100128440c00209840d0b403542c95541040d003440b0042d01c0004000e001c4607070500030104000350140d51a0800c940c03003490301c1500c40c0d00d0000100c1c2000000d488030400000007180200d104002175000c0e40c4c0c514400c1d0003c021203061407a020707840b40c032003000c0901460340d002c0c0000e000c038003510341c6100c0303039 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 180159721 1250 180158471 180158477
    0x304020a080106080c130c1e1101020d0b0f0a060906140c150f012102060708090406090b0a050301140a0b1f0305040308090303060a03110a0302030f01020d0506060705120307 76
    0xe1034585900d076085540e2135214129960144042000c6800c0621840c03080040c600d0081c002c0f14545400909802c2c01400300f008481903045441c0c890030321a480f07812040710114005d6684000c800394800181c0074560825118000b024560b010303910f482e0f450501118021f86500c94054508107060382c0000d400004841d001100b0401148001000c3c08540030b003811825100d6070314284549240c2441805810003140480c1c5e500224044601d000021605160b04848080c2e503030400d4600410b0a003d104401500300d41402004681100941c008030440202a00c4507511242d5038010103090302c81d85104440501c00410100e000381007140c04c00184014060000764600c2011a000c02100000420003070000e690b0780b05010401d40e00c0360f100350300f1006010041d402c0d401c1520005030154103c0c800140440d0035a404041c0c15111100b4060055400134140c030001051040924041d40c00305500042040c9030500203510303032500400755059182c00c0402465581c0e4001410b00140d40041c0c941000c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 180160971 1250 180159721 180159739
    0x170109060207060f060f03080d0c051b15100b0f090303070b07050d0615050a12111215010809070909020f09190b09061c02060c030f0307021b010e06030402 68
    0x2242041c0001c0c208a8820000000d003107540107084011104590048030088a60701c02c10008070303c445d41501da1002007040005540d646c041c3c026203142c4035100100c64031007042010f00ca01500d02148402c40b840d9590844491543c0f1482c801f10042c0d40c03070264101c0084e06100703002c090000b000c003800d00c03800003404032864141c45407102040000d04503026070014000048041255519010b501f00030002032584210a60382d400c0003130214001e030004003040140448013100d0380e50035608400c0031a860904200e540b83c1101590070746500c3c0c203c844a4210380d005420f010194420309400d0701c140d811402904442d420705610ba00071b030044003810ba920407002400c01d286513440189080c020291072607036824a426110380074082d2a8a140c180e88160f00000410080c1d07200d440c0d980c0c1212128134910702d082c1100e0304c0011181d006607180400c0328800030a110302d500044100944c041c0c52107800301e400c0541c1000001c0003120a400c20540000d8074a0703000101d60030010080c540161009002e01d40d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 180162221 1250 180160971 180160973
    0x6100311040f1104080f030301030209060405090c0405090d02060f011508070e06130303031b080c0c030f0a050909010b040308120601030b040f0209010306060c21050f0d050f0603011401170109 84
    0x825521900306071001d050001608001c170890401040d4a83c280c6400070750709541c50740e000501c007840d0042115018644030703800660310032010b103c1040f003800001c0007001581800c90130503030f0b10607929008001620844011a16105115001d10b04841d0040c400c6801740c0104a402c40340b02601405550501c403400107201c00c140da40c0409019007400030021607003103510314180101130340da500b51150031064100c83d403150f10b207900508141d0b0122146c0392a990342c00c0245a040d01e10711640c24018001003010407612242d80c0d004004101900c0125007a240ca662915000d02a43c40783d480010296441001031008a102e450480c0e503000905040018090b003801c0089001d5502c018424105a50700085401c0f8035a05481500d003d00a1860446002c000540d12034101560340312a00c60384012012006c0308151082084440c11000c81c02c0382c54a0fa0000604030740030b844140c2d03040b88048080b50000b0901d040c144100201400f812064402c540d1820303204010b40840800d5070201d40d5241d054440c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 180163471 1250 180162221 180162251
    0xa06030902030a170a1e362d0b0304020f2e020706030c0203040b03040618150606050304080d0b0102030906070b010513020705060714041502060411030610031104 71
    0x5100c810354500456038440640750300038201841004c49103606110f000c56906420390114000041e07e403080d0035001110794941103044005c14020605c03056502205021800c40f100e040e0b01d42c6d242140c0c000d41204c00c000c1008034209500c10780101c0340c80300401d1002402501c0c203107500c84a4000003034403103280601c400705140f11055507004400c4048010b5440019501d504020302e2000344007610342045a100064802900c0b807242e44105c5a00c940040081303014040a0351040c221041c044160309103d214901d841c0c0c21402c0800740c0c00403114075100700050b039207019101316442280d110508500d8040d85080b02c1c4020100248418110302c0180580b48c0305461300310003090281d0003015249807940c50718080040c0e02d0381d100b011400b030ba401484642c0009a00041c03480d084803460510110030309410580d4445070107580c0c0400100e0b40104408070f09290045955130266000300c2002c0c0c0000e1545003071607902c1c0025038088449030500c1500300007280b50491081c407200030003400451241c1842d0030103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 180164721 1250 180163471 180163493
    0xc1b03120a23090607051f0506010f05070501060b04030f05010606090315020304030e090c040801201c09080d05010603050703060506090112090803010f080706020a05070e04030c0f08031509060a06030902030a 91
    0x40320700c3d03880b100d425510402d0705c18401f140c407a803140c0b0600803490100c00080501d00c95079014014040c003c5101c0702080001c5d00a1000750414404440e200d580d2402c1c50800c04501c060140d485529190700030540d248185460410f494100da101000c200c11280c400c0c000350b100800940800c2030200d2040340507507030307101454010702020381c46036110350800b04820700310784041c90a1281c407035240b2800d02e181c165080a40d04602001d5481212082503140000d02800c0b100030010216000010a008000c03080d900082c16150690350070410b90740c030003609030210381d524001c050b072150f0103120010b001d610940c88071000e101d03011000300344040c00b5516450250000e07048038810308404d080500242c10700b007003c0e40003000300d4401418110384607141c0039120380e200c3c01518114140c04000a042c94080c00303800001560040d05441d00000e80d04080b0225001503d0040c03203615001c615060614040e8261030051400a0010504510b0b01c0000c3d8000c0c188401c040f03815000c1d1510000c003240025003c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 180165971 1250 180164721 180164723
    0x60306041425080c040b092710061a07050a02040f060302060706060524030109051003050d02070e06030c1c061103070f030b0a14010c0501020c1b03120a23090607 71
    0x500075883c10400058140194030140782d02462a110700c1c4c076003076500e20039141d800003c03140c40e2100c0c5e6402509015400b000d5900c00103582d100305000d0712206625540200b0407a60300190700300001c1261a0154224455800c0180542d40003c038440c000d07180079031003030a11150140707000465076540e5000ca80c9a0b040010103949039a0707541010002401e103107003810078120445000c041d8075908012075400c2030106024404407295684000b84400110801040155812000706e6441910f03a80000b0340c0c0c3c030306900403104e18a110402080d101d0030005003840032801e0050414400c00e68502d0180c20b0041580010784042da10350340484114030220004500985055803803e20100f1303008009416255070081c1c29008001032a41005041800c10000b90848000d190003100840d850400b40c1c0a030240d00001a03142c0142d01c0320341c040c4050a5966545040c00b03800f510381d185854001020784c0c0c083c121490001c642c6251302da10303520081d024408030003d00c13421514101144c075404030b07a66400c9070710 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 180167221 1250 180165971 180166033
    0x8010b04051005010504120203070e1f060e0d08130302061b160b040b0a0309020406092f0307180e040317060901031205090607050105100302010906080603060414 71
    0x40002182841d01400b540b105980211503815858100000c1162049106494040c2c814440c540c00319034046c40360000603c00750300d22642c83d003031031001080303071959840c078901100940036030004425014681d054081c0300010726089000403030381c650088540c040303007511540914030700000c001a690000684541245070100c01c0c3d6a1007401d644c1751a0014414894a1000c100b000812070505c100f0221800d4540300500d1944545d0340c6a0300368090301034094000d600a0a160000c5282103407581b11151152450915a804501401800c4255425080909100c00c400c20000d0120390280007040840c082456400d51065590804104090411354044000400703032510404144640e60101f9000740d0116030001031549150f071803103c031800f000407400c14460040b450b22100c0d5202c90130750b46100e4001c0024841403812904403491030015000c120301180346c4a5011480301c0c0b08100b140d10400014009000380c0e2a0754072100c0704842414148038151051080783c0781010503d503c41c07608462010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 180168471 1250 180167221 180167231
    0x1120b0307080f0f0f0c01121d0309010905040513110d0f0303151502061b070b100302090903030f010b09040f1b030606170c280e1906050304140708070801 68
    0x200d901e0501070130204550965204401000c0c03621004030303e01e4100c2000b428034040900d0100f0a060181a00c0c2c080c003c02d0068504684084900100052401e904240d84541c2d40e5a03c640c1040200c5c1c0d4261000f4640440882403000021000f160b802c0c7d082600400900d40c1207095070b01c0050700c03900086c0480000381c481c0d150f107200d0414000c80001030308140c20340d04075859541d600207650300c0000305140304c0c0d50520031000d003014070000102c0d0503c40d00080d02080ca40f4088c88981c404803200d1004a000352072550008000d040c0120a40380112252649051564600441d08802c0d400c18500b80b075209581e655000c1d15606248200c0f0711260554840925886140c2005000c4a441e0342c000d00c14003865031140b00c010f1841e1101c140d40204500f901d2915840c0c0440043c41000304c00c90a0482c651320b1b044030b0200c4c3d80e00314080e5990501d04645078001d0104240028503201e08920a280115005001150002d5070540c00c00100400700700440303540594a04107245801142d03401a0f0480e50b4139 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 180169721 1250 180168471 180168493
    0x2220207020a0f05091603020f040801020c10112704140f010807270f060609090506032d010e24090f0a03050a020102190314061e01120b030708 63
    0x15510b00e0b40100f142d40900d41500345401c02080340c0b000014020b0300b1503107403912041c207100e0080c0e05403045800d9940d1103c2c5c42e1903c449950703000b0340c00481000c03458401c0d4081d001c0c40410714010154070003484a001418a103041466040100c103001044201c49085516a41d00e9192032050719401c0524040da074040d414802003180310b44c5010f8126403004d070040d00051100743c8041078001740d02c000218900699203900051400280004181040b440341030000000302943e010700440103070344541d5000c0007141c4580c420150b6410b5a60320301615209014522640701c001106204005413101d400462340086c501092410009421104290030700c6010713910303201c4804d01c2c00c442c0d8003022020080c07004032010307240940d86034070b0000000c080000008000c40da00d07200f9010795440030400c901010103200520005809849581c101418030b41e9080c0010380c10386426103d120341880422810000512801c00449801f640c400950000c0c0b51140e828910703648041103550010108003014020382491 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 180170971 1250 180169721 180169729
    0x1b1a04030203030927240301050c0a1412090c130c0e0d020f03060103051c05071703040f0506010b0712031406040f11030108030a0e011103030a05250c0b0709061205040222020702 78
    0x2481c0c0c6c040d40079a14060070480c25800803401c80f114040d103414007120140303032004442827501c04c0804e11000440b40340c05204c1c1030900000d00410040c4215071123042902000e258404582c4580c00e09400a20940300503102c6050040350100c2550020f031070034540c580001d02191904200382c0c02110280e0240410b8280550b0440c0d06038240c24203468290700d805415108d040c580c4100d014410b0341032500002103070411a0f201d94a0312440d80c0170054070318540c1d6035503003082c031a00148401c0d01d180601c010404250f920070310452607040244190604035484140601c401045005d1015054a075520808002d980151001d0b50080caa884003c5a80342584400100804c50040c0c07894184101c1c2e8620142441012090302c0d40094175510000306031f5a01c00d800b03400c111240c400182d15103980c003d400c0056034081c01307010b10302d4000c00ca002d8090f1070308041121140034a2050b040000c402c542044002c1041c3c2e00300e1501300380020400800044440740c01121b2280304202d10340d4080e80001d4500460030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 180172221 1250 180170971 180171031
    0x150703060b040b09040c02190b010303021c08070c0224090f19031101020c0d03080f0f070e01030e0309180f0703020a080a05090a1b1a04030203030927 66
    0x5006614030307040903d070201d42d2001d4010140f40c43e115a484a41c508610b078420480f030000d045d00c0401d50340c0121001e04025400c00c01c2070005030010b002e41881c07010a0140b5142100c21880d2907a01c81955a95024086070301802c0804202d0380544200818030244814440040349210340624642c1d80700c40340c01c100070490442154280c02801c40343e5114100380b61702d0710a00100d0b034002260030303507034a00030004038200010105041d078810001c200100626a0140481c1d218091384d02008041d40c0715030f5a00d03500110101d900a00144094103400259407013500f011136a00318070300c110390030090020b0000d81085862043d440322132a80d50104641c0d62950014030381c20000a0a0031481c00580711801030580c2801400d00d00102d44920100c0c400c107008200310000541c101d1400410903120609810010041d8410f00005c91a503020703036030900c09040201d400312a030040c011454410780d5401e0002c1c003200c20b070f41131940b60340911882030901c0d0342d001e25501c2804440b64080c14064141c4101032100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 180173471 1250 180172221 180172229
    0x5041b112b0e031207080d020903160302010f0309051c1211130e0411090c09040c020309040c031b0305180d030f0c021504080306030f030c01050115051306030c090815070306 76
    0x80d1140100c81c1300d010b0004100d81c032180c1c101d01d160780e860082c1e01c178000c0607208152010b0b40520803480d9944030525041c610500340c80c802d0380c07413140342043e50b070048081d13901045000e0500d4020800c0092200e400004484801c803c5041420700c040c1c142d61200111604181c0000c40b0710350000310311001c104034900c100060104c0c2a076404c801c2c20a500c0305d6008a0789218454000c0000002140c0c011041000f0340300d4014000b00148400c10f51050b000391250003068000340140d0502c10325820482c064000d9568031030040710800d843c02d15a013005c034054800680401d0004420040e0780b18080720502203400743d01c0307490320702148841c041c4581004440c142c500345030447d000070b80b821450603d4680115003254020740c5444c3c59031103c00000e4103000a40071603107910701c0b001902c4140b241041d08054121703440c01122190980c5c0680302a41d56104a140f5004804441a01400000e009a008002d003451501e401c1c0c0c10070761911003043c6891180711880380407810800810010702d40c18018038000e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 180174721 1250 180173471 180173473
    0x61c1a0105030613050d140418090c0801060b03060d031107120c0e0601051806040f030b0108150c0a2604200303090a0e041a040b010f05041b112b0e03 66
    0x4182d060310703000c6d01c54268406440411800c484000800005003064a0103007002041d10381c00c4032295441c000080039501000c07240c820360404009042ea4041c4954001c03191402d0883d859903132a0400c00c205110803001c204c0130b001c01e5201440100d0000c000303101c060480580015004411401d014100c844070b40d000c06504502c94003040b003180d9000060307a8214030654800c20306200c007140000c44600454001d035040c28080d4100205102c1c200003068121040e0609440501c1e00321040c41c0d4150308200c4003500025020400220428800c07181d14040e8140c400310b44010f13440c0552030041c5480c00352000e550001c08403c40a030b881c0101e00d40d020060000710b00a61802070352401107607100040d442442d6114185100080902c00e04d031982c12042c1c0c5810f440ca07103487c50b2500e441c0003030107020700803076a0700132a4600c04240c41c202881568815900344070400d411085d25842200d4016000e002c802c3c4078003500032160f44031603c1000300c40900c001c9450003010714056440003410714001003202446 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 180175971 1250 180174721 180174751
    0x306041103090a03022a0910080613150902010504030f05010b04060e09010c02060114040e0f10020a14090105040306020304030c12050a0e1f03151205010504030f050909061c1a01050306 81
    0x4000d04006880649050682c0c0411f03141e582c04030040719006140c0d12454042c0109030401081c100b003d144142001d00c07845400000c1c1000341075810440b041440005d01242040006001282d5691140d01d613030780c402c40011a40254003404a402d80d05168130801d101e0080d5818004000000e01880c116440707684000d0406d0340c504811407440341e01c40300ca49401036035a45981100b44806100c8601d08110780d10440c3c1c101c070724411035900254002000180000d00091410510740da043d0202c4840720b005039500e500300b40c21611003200a600c003810072814001e40800c400002040c0c3c00c00e1042c140801d44030152107000440c4007800068200d68981d00c6005034400c1014030514814049003104074230310700010414401003076444000420b81001000040e000d440c4400c0100541100340704511940d2041004100c001c0251f070f1600030303210362680c8540c00000007281420a10440452001005c008602813085a10b6034642c003030303085207440300b203202c50001448141000c000c100e400a004d4140107803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 180177221 1250 180175971 180176023
    0xd0e0607020606040e07050a0b04050102010c02030a0f050d02070b10030c0801020403031e03090803010e07030f02040506070f0c1701050f0f0c121e010603021306140d020306041103090a0302 83
    0x1442d10b80c01081c6610a650300d81091802c12804c00001c000b911000d4250441c4503181c04005146804c24841c050041d801d1649401c482d030f20120941c0e043d0f44407601c5a0b84409207014095a00390004d029240c0c2c0386a0031311900010891004145000d44040390305100f90f1821030030080901e220302c5d04005c3c0ea81c0e004000400000c1c5e4040c08420f14840360b49800d20034861a04001c40252443c040090041c820100000c00d80c00b40051025014034040c0e2000c120b510400c40f110400d90040d885415400101800350902040011082e18400c500c1800e81d10301480e192425840b160f0b07480440751006039910000c014515500c0404250044100a5038040343e1070000705680251040e042900404c24913040810550314400d0040c20360002c490041b04803968441e5802002034001038020b2003540441c2c2000901c0a008081c0c400110a0300c00d040780c0382514a0700111702035400036103140e400c00d5075150010004844070000e0350141700300b41c01800c01c1d14203606001380b62681c81e1201405040ca00c104000c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 180178471 1250 180177221 180177223
    0x20c010306051c0c030c0e10140603010302060d11180a05031209060706060b0f0705011b02031e07021201140708090705010807020f060702011b02060f0109021b0d03020d0e060702 78
    0x4864400071030060a03401c0e00c2e107450800f1121342c0d03100800c0050005070114100d1820b40340c4a10910341003007504001680c955900b42801180c0d403106411078010001400941424001010440c90070500810074480324200c0b4885030340080110610070180131304500b0070340303031081011004110840080103020144441c080d8070740b0032845900d01c03c80d000a00305040120030382003030300106486400552074107609894203c4603031241c00b00b03c0d00c951030f28030329070105940420034540f02680c6a000f1030a008591340c1201555195002c15040d019060009100682e2118010800b801700b210004c0741d03141200c814480000ca018003480d0522600340c040152041c0e000980004030342d400d00e08100607442d01141a070420580800d0407280d405503500300b05c2c986405410032000692209140c4c4d684220134102243c650b14103507a00d100d0140d4800c0100610f100903005000c0268101c0c001c5075803c55110b50040c80d001107802c50801103070300422800729400c000e00c65490304403501d0010300f0252038100802 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 180179721 1250 180178471 180178489
    0x22205040c0509061812160f0b0313060b0f03070914010f1208070213020d050423060412020c030a03030c0201050105040209010f2010050a11071703060102031c0c020c01030605 77
    0x50366a40701e945c0c40100e103640c4200007a0510000d02c1c056402194204003d41d800d07400b41d028a04c1c1d01c404042000909108500460b8440d501c92040401e03040c5d503564403040604840d05c48213500095084243c904c643d814440b6a0041c800f807540024041c140c0e0109140d031590503440b0320001c0341c0c0c030403080200310342c40744c0405501a442000340707903141d00703034400910000090101440400d2001c07c3c60051044641c0c00703a40a1401081440145022190780d03a4000c2541e880500c01504418085000a00d12100e80380b01000140191103a4840740004281740c030b0010441900002e4036164042a030640a1241c18050001a14158548411180060895046a1000020441d00300004a204820340c40107940310410b400903107244549a03444080584000e580c100c07161441c09502c214191079800c1182c0c4115404200030b0074043c982c101c0d101c0d80b03410051110f810350108100c0103842005a6140c02e00c1c420b4000300000c6d0205003220000d10301115428002d06140c64002c080c40903a03101c0045c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 180180971 1250 180179721 180179737
    0x512060c030a11040801021803011523061239090d0510020d06050a080715030902100807020d020d0e0d0c05030a0f03140304020a0e04030201022205040c050906 70
    0xc026900e440c1c0e55001d0b0000d101c040b1604241c0407012030040740002d07042d00101483e0900c2c0301c1410306580301c88100f40c00c03541560004070a104001c0f80800469600600c0010f860079040c0c80941c2000307545011450381d41c000400401244169420040280030303844101103003644010a09240e408007107000d48009482074021204010b011411042660ba00c008120380c0075803100c2a11714081c403c210500181d080b01c0c520080103802d00b100820903013031640b8102c0803521b4060040407640d01e04182c2880455103003e1017030030035864640c0103000d41c481d07401c00d00070030740740d030b42c6004c1c032480e2a0000906141038413688400b10b41104016074505039009a00e0030441178221610200c40150f0700e003450032000f2607030005070140141c41c050313410b01002c0c40340498054080e40769110003140103c800541407008480003075101404072802c1c001484040c100719400b500c240001460030121240b04d0a4059003d4070040000203094010701aa0605001d0b4814a8005091590401403c00000341c028003507135003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 180182221 1250 180180971 180180991
    0xe0a0c27090c320304020d0f1208071709070501030b0a0f0305070608070201021314030a0f08040e0907030b01030b07031404050601050f0409110906010201020f0a020c1f021506150f13051206 83
    0x342c22402c0c803509240310b400641d4445c0c50070030046000d49c00a03144140440b1054049240b000000f21407000b0355110501c82c251070805050000e061800540c010440d00c0e00b215081420315402244030100400384c08040e5001d02c00030300040c1c3c94440020b2408800404110441e40140040420160004640001c1d01d00886d011640b0290240120345040040b000103400002812810710a00042000800070b03902031f10345d80d10240e030796001501d507030350681d102c000d090458a0004102244181481e541c00010b503107004a050010a83d001d2004c4600b0744e41034485400040c0108624900303800303c1c0d00700c4441500c040c805c961270360702e03101c0c0780074440c84109014150010020350268400c4d41210940516078050302d4a800c0420b030000d594603a0280414065000e075241d6900c0a85001181c48000b074a070390050035226100320102280c2840030b040150880021100303800203a0001c2d0251681400c4001e00980341c07003109504640710380083d0701007400340402e50300790301451001080040d40510700c10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 180183471 1250 180182221 180182239
    0x6050904111c03030b0405061504090c0513060e03071707090b060c070f0f0503010510060c060b030304080a03090b04030b16050d0501030b010e0a0c27090c32030402 72
    0x10021070648082d4011102c410044980321204154060303010100c004415242044503a844009000c91009040310500c01030754240410040c503c41c80e00702031604400c40c40d186041607410258440b4204441e000301001c600000440d074110300307003040160b00508410b5420b9003c64507034080310fa00c41d0340da801480b114a0301d800141ca4191642800c560201001030f04451805d9a0303402030614040c40b0340141c412480905100259500e0305010391400f9800d6510b404484601e8030805035000c1d1007812040f80c0003504d0309920800f550b002c2c00900010080000507282002492800401c0245503411007079441205110500110710b602e0007455100441c2e518a18280c0c0302d40354183c66900450b41c20410140c00c140c004410098801811412100d980901c005680c450350b01070713030175500500700000024041c001c40d40324105280ea00f00343e08500844441042c251220b40f8502a1420880c04501180c0c415078002c4d4101d8a100a0560203201101310000540d140c03500071009110191010303205000030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 180184721 1250 180183471 180183503
    0x10614130908030f060108090c03151911031503070f09090f06020f091512060f0a0305060c0301051503151909020c0d08010501030b0306061915051c06050904 69
    0x1d40c0558085a00302030816180d160005000e2034140b0200c80305e42c0002e81d00f4000c00c00d001d40004040d004e03003400602034001c296001c00d031240006401850341c01001c240001803450f250607481244051048031813000d54070314000e01d91407003501942c903019002e0b502203441001480d42040e00344054400811011071041401c1c10480840328450034098200380c40000c1012a1040c03050040c10700d140305440312800119061045d00083c01200310710000510139100003034891800d2202c1c4042080f000b440c03020350540301e46a0600d0700b402140c0c00c1000520000040c07059151200c62544621030f508052071440c90202880f018124484081500680012f12440030300704a080429001c2c1c410500115181d041d400c40e603070390310025000340b20081040d040020131075511a000700b401c13008000d001414145c0f114818020b181500190351300e0100f021040c04542074000d5200300c1e16541c0c8c1e0b542c07038a480d06800040a17170b19054444840d490140f41c603c041100c0c1c0c40382c032161607000350000c0d0304031211685 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 180185971 1250 180184721 180184759
    0x1140d02060a020c01030f090b0604050403020316060614060715150312030b2e080c0409060803040303120513060e01090b07030603110411070f030c05060711010509010614 75
    0x84044000c0d804a00414402d105950001d0144281102640c0034018400b1200d640380c11038010400c06000d14440000203001c41c1066048150031900c2481124901003c03e02040b13494030728007000305d5080343c0340c01c070400c403512008a1141000c1000c4501c2458440c0c01c0d80e4200d411301c5910080007145849140c100c40e074291102d1040c00030341d0458070807491034549400041c003c0c406c9040b200d01c00c01044020b65038916018014000000f040d40111402d020b1841003992807040083c40e03034010b01410000480e07015190702400b8000c16142c0d0003181c866003503150103003510f101110640b005c2e905d094100b01c0003c0f092400c0c6100c080d00a0800a410220980d90300e024012520019041c1209141804400d540c10740c0000100c1e401001d040c40f003410144100000c0c0e802540d80504032034814020705020412008104150602c241403015240b0f0580c0d0300d49041c0300c2c046800501290b08103c555612901c280030340369014043d0b8008003c01c5040c000010031105a0074140342c0543d0410706038207a0415 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 180187221 1250 180185971 180185989
    0x1e07060c170706020c0f07081002070602040f0308040305060c0a0807050a1808060a200318030c1002090108091c080c04091a0102070509010e010902340b010503150114 73
    0x9055910070340d45440c9410304002070b40c011034100c0254400c1c13100c0034000c1d11010900c1d10941c0c1c4504003602d1203041c0898038802035001220305030381c1e40d03034200400107c2e20010700449008603c1110003988031032860401307504107400108aa4104102000a4030503564410343c5a64440d450341420b40e119050b01030101c4081e1704803d21800c06404e0300c1c2c00842c2d03500d00001d0427880313030011100c180114080407030560248922b050101203041014030100300c1a202d5004942c080f10111000c072814200c50b50621454400f124084511301a8002003800865a01031842036001e0703011001080707070051000d400a06401240010720070020108041240048050211b5005104101080c8600f005542030103600e1001100c2860140c89000000103540c100003008e076040790801407815803181c0c40c01e41300c0400384d4400d41e403040e92285105029044000740202c0100b104024407070481b0903582d20b01e070880701c040c0182c1003141700ea8880c241d048405548001d0aa0541c0c0250003030749890070008010805d818 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 180188471 1250 180187221 180187253
    0x3150b03010f0e0f0f0c0907020f03030a05060103141302040504030909091b0608010b0301090207080f03130203010608011a060c070b0415030b040c201204090e1e07060c 74
    0x250800c0000d8580c03200703540000f20142c0d0088180c3d07564180c050710791075641d0010404550160045259032002c1d1416400300d9038884814010f0703c0c0c0001d50703042d00714107680c41140c40d0340c1d0b803030758035018441c1c1940e16209200018160b12980216820f1401081c0656422008020b100320b84420005007014460107828000b0030a11101307000c040341d64601030028940784081d4036007072900c640c2c000644900c80c122030390481c1d403042c283c40e02d0769013041e9101d0081c1d07020650540d8400c40400005031801c10104c0114460111101c0e8900240c005104143c01e442e030951024403642c1c1801c400d8850158154031180c45160221502c41d0b03a094035038080c43c101049940000800d6002080c0040ea00c0f074603c0c00300b50381603140d5508208175030b40c2e41c00b0803040340c41104400d0000b605003d0107030805140d4503a102d42e040102012a0744c0104d5407106001c441d442500f1a02d026034585a4030003140400304000c2802c002d00c25218810003946407a0240d907028103110303c00c10002c48410090a1025203078401e0415 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 180189721 1250 180188471 180188473
    0xc0105060f0a0302090a11031501030f0b210f030a051809010b0a051602030d03020901020d1b061a0405040302010f0c02010204030b060910031403030f1f0e0c092211030f0103150b03 79
    0x640789c50028144808000d6030807074046402c00c281d0109800c1c040c480d9001c0700304001c10001d40c009040d640d915400405002000c03251050072416403070408108050000c215060340d503da038480401181141c0c080e000701102d8000c3c9070100045c4030542480c000d580d510101840e100d5161005208001c0c140c0024032400703034050084452160011798590004d0a60171420707021920102c04402c4202c0e131258a00d04100340c181490482880021555000003040001c1c02200b00170144030000010201c03035098600f200580c1d07440000c400d07203810502607100610b405000841c100703482d41d00c84410250340182920711034078070701d000510902c100c2031004001d142c0211058000c1070084084a60f1b0303601c1071724503030f80e03a00e101c500068513040c5140b5280b402c0c520540410380750600e0040ca00302c02031000707450300216240910003070141d900c400841030015214282d078042405441d00e550811912110419181d0354010001c000b03980074001c0c0c2c02030440e03a11102e950386581c0940011070080c6504001c15501d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 180190971 1250 180189721 180189727
    0x60f0409060902030a0501050d0b0406090602070b0f060102010c0e0a031202070806011d06060c0312220318060315061202090d0809010f08370c050c0105060f0a0302090a11 75
    0xd82c031007035030245100e00450601084181d80f5001007024417007060344c2c01015107104200040020340c290b00024005407007580094145403081e40e588081c014103c611100440e00d1101300095980d090040e080b1200c5141410812199513901081100403540005007101b10595003200305070b44200603980042c034582c0d041e40d01d9561103064011101012280c009904c14900000c58540c1c0307440412070b4201e0041b80300035450030310000750303100304100d00601680103859007503d1510040c1c100008140c075284640c4d01c0c4480b5054502001141c43c0c01600b15104040c40c0a5030300000100d00074421042d01d545040042640645e0044007019104003990541c1183c1c1c000040c1c402c01001c10f0140c81d2036603090700e4041050300749080c1143c4211045990788141d02049900c0310f111030700c1201c500103524161b100c9002da002258101000c1d22803806210300080d00c0016083e80c440c00038400c07280c02060031900000d281035040c00150401000d408064800d40b08040481d04030100b41c1c1c4902424004000e140340c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 180192221 1250 180190971 180190979
    0x60d080301060206190c1d03100c020c0910050102030307080406060b0a120f0b0f15041706070212122410110d090503060403030c02030c030705280b06060f040906 71
    0x1d22030740140c8103080c8aa2000c101070080340305c41d0013101700100f410b540d000f0840300c101e00c2a480188144500c1501409000c4807080801200d004113610440d8035001000402001c01c140041890002d10001030607014940900081c1e901108485d0454294946001c075500d03039080c0704000300b40c03641c00000365440c0060301c80c2e02d0b0b43d000307031000d1910f6860290802a1807034200962042c0c1f0aa0000aa030002001401040924011858061060340f01d078020342402e1f1902000c5040d841e206000d0300142c1c0c8074000700041c180d070401071007100c2c0c00d051201c40d0500710780c2441040c00c2a0f020b00007800040c000340031100c01d00c201c280b4004a812000301445480303008500040e0607098402821201e0340a05140340316130a018041000071541c0150081000380c0c0c540e10200e006105446c2c180e01140007c100c091001002000038004490042c030142c290100300c41084a104a20207068095480c503007080d110201d035008010a600500c00d80f4602ea59070809203074031340c0794400e58012583e100c1c83c00034042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 180193471 1250 180192221 180192223
    0x3020c1606091502031615090215040e090703030f0c062c0c01020f0a0803090a17040e070305093408010f0e03070b0a1107060c020321060307030b060d0803010602 71
    0x20110f62800c000e48848508465007240c0b05c0c403440320940c4a42003080045000905076140342c01180f0045030000036000c1c0340b0b900242c0a40f002030544123907010040303014402c00890301401c1d9082a81c0074010810145150707006403e1499104207001801219940c05003440150b42042c0700083c2c4060901e60103002c1e403800301d00700300500001054036228240c903484495000044600c2c10080d03010042c007024515580b82560784e84010584181801a0048080001c81400800803042c51100c0032585450500e01b105440070b000504031400c25050405200c0300c8000860104400c402014848007087e0780b0b8041081d00c0120940141c440d620004400038500c0c9040d400340461429442c4d00344080d080700300406540380203649020389150542400b040c8044e0142d0b200c003800c0048101c1540c140085612410704490a884011025070000560081e0558058999030020a9142d46014843c05c0401c003003943c80505020041040e00d031100494650341d600071502c8042d42d48810382595940c1c44480007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 180194721 1250 180193471 180193487
    0x31906150305070201200d06171f06060e090411030d020f0708061e070201060902041202240a03090203012909090609030d0b130908040f08010902030d03020c1606 71
    0x9000024503001c0401c03e003a106001e107002c0050241c144041c2107021000840880c0e110103825a2882d0781c60000290004840c0c03a007500038811000904607510144191290514014166034189403620a090018582180c10864204015558201e55941e0703464400e0840d05103104603130340740c480c101c81c46180660010360700c00060f50320300a652015503900c0526a95410030f40d034101d9108816204c0524400c10f0a0140d580b00c1402d00c00812920755520342101280d00a8202d82841d81295241c081903040910940240b03999001c81c942c14a2112241d072241c1e40603e9100c2c80c05c042d15200c0600a56400f504800c9803d01d04070054001a403ca05044662130b840c2043d060044501c4800286c034540c0c0400c2d1240706183d0980035524001d20090303a40001c00845c60301d50b070721800c2c0c1d8407039640035141c9118010185110300b0356150350794108403040422418641c8a44107980c1010031309001038801003544925011b160401680310010f401c6254101202074002425440b2400300001d140f6a01c1410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 180195971 1250 180194721 180194759
    0xe06180705010804170702210303040b0708040215090d060608061b030f1609090c031a030c060f130803070605070e09090c280602060405100b0d08031906 67
    0x12541001c1c0e81d000190341c0c4902c221400707000350903160845800c8001280003401850300c0240f00c403488410000c0c22604070403030341d5400400b0343d00100c208410460191034442d0072041908049550303180903400030300c00b43c80c01d6045030421800810724841a480e9409401d04581d40b18105200640e1903801d2541d81c0c8404030780b04240090011545000d41c0d0f41c4804507401849040318030002c0b5581c0c5504400040000eaa9034402c1044140f40060300100c548110900c0041d01e65010410384a1b4000300d0f1896001080701c58440e80140040c050310b0742c0c604007211107500d98030100a4940c5c0943c4a0442e8120860388540392034080041c49400f0001070f90b00c4103100340a2604d40050701e425000a102c03a816048a4080f01e0f0b50080c10001054074140e800624a245040390300c041240b4034246481410342e2070780c404405a07108506000810405104050001090328008c00400c0d40e01c40008a080e04c007140040c0c00e21030000081801026901d0000381c01c00341400c02840180e56852410102111f4816 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 180197221 1250 180195971 180195973
    0x9030d03021909120b0601020705121b060a02070303080c07020d0804080714060f09191203020c0d030504120302030409050106050409050609090d1416050f0d030c020a060f0e0618 78
    0x14046020b80d0284034030f03200752445a062020210300741e0b0340c3c94a0490b800b6003ca415440780c19070004251fa03845600914502d09400a041720004842030292000c14460b1224424142840041c088130341c00a1208226505451310403c9601c0e000004012807151900103074112680f82840c5040c000104001c00844840c0d004940f1019903e00d41c403000c2501046903980d001d24104180c01004c0d68800250414000c010840c05400044d00c0d02e40650001961101a1b25202c2a03540800d141e018400c01079005030680300e400c205810b80d074000748144030307a0180c0c520041a203c404000d261080003500c1c042c0010180030072195854210240441d000351046016a50900000036080c0c201088100d002d014100002e191032410080c00342c84502c0e069501a4203034106004954280c01490300701405140500d018203102201614803c0c1400142005c02040c14248082449060340c0042d50030000d5030405000206580300580f004040d1a95500700700c9903200f60414428a090700301591844244280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 180198471 1250 180197221 180197257
    0x160506011d16020c0103050c0d0905061503120a0c0309030c0b040e0112020109060305061201020d0903030b031603031b060507031e060815090102130e0402040606081501030e0309030d0302 82
    0x7815400082d100e0909140058003c010309104e60750003a081a0303000300302e1450301810103000440e400c1c2119070a2900740c40e20362007901031246100342c08000b420a4075042c1d01510b040005030584a989200b421358400800070543c4404081c14400c044000145500c04c01040c03507280d84a001007526005401020200503800b000010b4481016580c1001254181c40701643c0b14500700c8150300400f00244041e0308551700d02c4104000d12030a10051501a555500004940242e030034000c040381c00711780c0090702907440034005d03c00c0c81c0142e9184104807585440e11103601058501c441402c0d03084100300810450502d01404000741e010f070003508060b0650103004441818210391041036880c02e1103009003940112015214185000445a50003540c1400140c64100600b00e40902565a079000442d20031600c8184802c40c81c02d4001d03e070003482c16140c5641c0c0c9040c402420160780c01d0014246045c9560b031204188402d00610603560003450003000d0b11170301c501440015000e54008201d84003002c0c41a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 180199721 1250 180198471 180198481
    0x21f0503040302010c0504030b1522020c16030b0a09052d1203011d061c081b0d050a05070201021e0c030f01050f01050616060507120f05070f05160506011d 68
    0x40055a0452744c0140d140328a944602030309951610070300c070aa54200b83d03003480700b14801100050a00e1384d041e60401c0140d41d0020402581d0503c1101481e82069000c2d05d5810008112002c2e0b8098005060701c10000d071809961810500c2e142c600701d441120054241ca81e00d205091170100c0382928a528001d076003060703030756500401d01c0344070901941d116611740034000500d8640000205501c800c1c00f50001651484481d90348500c008112000c940e104000a918240703240c050442245508003c801002028030000300075041e07000311207404041000104400040d0ba10030050b40080e0011907005508802003409400c0c3c8500c81001e41038020b10a00403148a08d0205200d60b511480011080d00c80b107900300303800c0103c90b501c88078a43d01800046a10000820a548a940d000d20075640310804144a8401c00d0f1050780c41586240210034900300030492a2070700000515203116035841e00558410f0901d070090025200503401030400d102c4e48002196840322511006ca4100c840494900950b1b19 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 180200971 1250 180199721 180199727
    0x402030618060115050403080f13060c050703080307050d0501080c0114070b0402060c0f0706020703060605030604030f1103071406041a010f090515030a1109070c020d0807021f0503040302010c 84
    0x10061020801c1d034003010040040710882e4411030a454154909180307400da59440b00e0708a90426118010040c03c00944003091a240306c249000800260030f11082440554980c1912070a481c0300140602c200040014402c41c0b040302228040d40218400300700702d5860b40d104669610703185403807502184208000d55281800c50301641d4080703a0140c0580300701e607a65800d124450300648403040061041640ca00302c0c400701804600041c0943e50700504104d841c5007031840036110a6800540070750065000d020120798000c02c03081c7ca075404c60420038115041c40c24010b01d0352086060190135440342140341440c41d01c010401c1e6000d00c0c0108010600d1848204d245161a0b50a100d03032131800d0b0907098100580801e41d0050396010640d910b00031020201c4002017428812046000c894080c00341c025900c081c5080c0408680100c00d80c6004200307482d20707602051017031041000142550002040100440d52603c4802c01440e240504550340c1e4480000e002c0d0007500b069400320055401c0c0f11601e42c0d2584 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 180202221 1250 180200971 180201001
    0x90111090a17010e0a030e09010e040503162f0a0e010b0d0e0c0a0e0a15060207050d0501060510081503030909040210031d0709060806250302070b0f04020306 69
    0x1030040c000200d4502d803501c1c051110340304031401d071925501c0e82c440d039125001c14003d0300c03840c5009445651203056038004004405030140c201405d06502c0b030080c03002042000080e1101032100500c3c0a40110040c14240e0841c02d22603143ca2000701481038240182c032032041c00c079004900c00d0795845965a15161642240102409104143c580900100040c4002500103000e400c440c2419950340644100200d424000950000315608101c40b080c018030051a04c149003030014080340c0704141c3e40c1846002511031217030f44503562003107400c40b031081c040c01000e510000050200070411907006645000207007050404607142580e00d01c0017007048a043c01d011049401d600002004141555039680c00c0040340c6085c10112410159114950040c540407034500e0042c080d01c80d8010700b60940707400e107a581070703d019030000d031800e03080340040c04441d850340102c2c92400c0c02c200f40a00c501d04070f0104100c0c000e0140c8a0044d15440e40c1c8002c0c400200800040346010724003c0e016101d507a5120108410140c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 180203471 1250 180202221 180202237
    0x318020d021c08190e0d12052802060601200a150e060a02030a06050f03030405060304080c060c040509090a020d021219080307110d05040902030601200105090111 71
    0x50500d00c00d0061419141c110100390348414108145105a10f403025a908021001c01c404155004c0c40b8032095000808103c11880417502c5c2411000c1940c1e820521708402c0701c200c01448000b1903640055090030030410103528204c1c09409180c0d9010500070341c1c4440541d034403404101d442c02c062a5540341c240804105402d040020507595032556110060050a540c044201d9503803400404010301c42400200d004018101c809a282e08001e44008100c0d001e80c0e0084d40301d42c4500b5004840c9803000704c151411500103d03409a2241d4803800d05900340c0c814085030741018040e51041124a207910009402911426203204941d503480c0c0001551b40c6204110181d40301000c1304041005203040c1d21010b120b6030b06001a607031014240c2100034402c00030f40c08102c031106008400c204086070f10841015070300b21050000d020380c0e401400b010308244100d0059500c144d800000265491340540c0c44011441100944000c1140c0100140d42c02400151101c02c120f5080048618000c0718038803d83d0114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 180204721 1250 180203471 180203479
    0x161e080312070c1b0501080a021201140a120b040b1006021c02030904020703030b1008011a0a1e0f030f05160503090a0804080607030b04050c0910021c0302040501031802 74
    0x403001c00305024002801040d0400704002c028040f000218a00814056998510007401a650815002425a0b68010240001244180040041504902d585904491003003d6810342e40066034040360751982c40d600004c2c0000d00070f00501c4100001c10100c2c9200314015000c0d4281c03901c0e8024140c4034200c082c850400180e02400c0303034560b2482c00034000c00c24580c5c103004503071600c04020040340c180d802c0140150f021980c1e0b003459001e9824a00c000300d800300348500d0814819810304131120a101f1801240403449180451041c02e068000d0340d94420b00c070220074200b59410441c0c68014803866845440320300103800d0000c5062385607043e025050080d81d5100d05403078040d000030300840312038000820740d506900c190005c03240414160b90003003015121100c083c101c6483d0444029041c0c9e09840b03911401503207441e0400c9400d22103141650004a021540c58401ca050004101d180c024888031364a01802c100f6600c05810360103034020011180d0030303201400802170840c0c20f1610f110f031501001e504 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 180205971 1250 180204721 180204727
    0x1b1c08010b0d0608010c050715090201090608090a0609110118030210031505090103050a141203010b0f0d0e0f010c090b0d05090703170d1103091506030f161e0803 71
    0x3600c0312000140103402c4a103200060115641c0c0010343c2510114100b0f4404200c0001e03a11050005408906104143c245410701c2808000c1d40000c1a89949118010400611402040398800148203010500781c2000007032000e00100e080070100c00120011050100d6800b00166001d4080ca41010080b00c2c0c00419400c2118280e09082d800781024072407110041081c01004100d41c1e59040f1410f003e140550000c11416501d40b031301e900c180070301106e114050307481004a040c490054000716415a403480f01c0464640f91800c42c021300703501801040d412140d0400600c62615280040c000042c11100c600a0010104400065071009075602076880750a0b4104a0319040c0c2881d500036a82055400b42121101ca61360307160300030384075083c40c3c00c01085c03640020000075008480c002c0e500610080384080c0c3c0f86080080e2129580c00071442c4034a41d4080070f80005216560501850b000408540160742c6422034231000d924407425103014503201d5025100e0011400031035050684140c9804400445c6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 180207221 1250 180205971 180205979
    0x40303020f04030204060806010303080c1c0b04110318060106110c061b0a0602030103050601060e031e010f1e05010b09010503070e03070315020c0609010209010c0206090a03081b1c0801 81
    0x40a54007031050318008210411001006803134900c0b03184001c1403d003001d030031254114030b001041000003400400c0061014040000d240010700b200012403221041e00188180e00780010902a044c00065052491004401c000d0802e0212003150486040b131002e80c1d925a890300d006039009294100004519484501144d0301818444001c114810901c0348500d81c000c60762404510b0801e420302c048440e550040010404c01a0820825025200d01d0500c041580580f001181d41d0300c219200011002d8000d0819561109080d4004c2d9220100c00100b40062a02850740100f03403520700a11101ca50300e0000001004402007055a00800c0f05075602880d50b01d49500864000508540c0f596140c010514004000780b00443d510708011018080903840d1545040001e0400f5001011004940d0040060031a2a84c0c032608404e042c590444041c0d0704d489510020660300d40168200600460740041c03076500400600b180c0010b0044007200300c1e20041000a000020400c8004018010940140042c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 180208471 1250 180207221 180207227
    0x14040e0603070305010504050a030e0102070b0a03020307140307030b0111010506010e09071b03080601081003081e160c05031b0a150513091a0301021201060f0c1b051f02060403 77
    0x160016001070840700203079240c0d240e280c21920305035000c64007075010261400805821514424110100340003a19030f19280c110303000801c1c03041c101584201603000000a41c41d902421404000b015003012413900ca10700560f000d00101101c000560100d0000301d125000820140900392040806964446441c0c101e40c0501912800140002c82480301102d140d600042101594120381e40c000e5a4180302400c29800141545074060314086440e01103001c10700c04102c0e02021940c0c0c03040d03007000074403c0001c3c4408040c040d01801c0000039414482e0041c1100340a01c030703951202617410032015074186840122060a900e0f50005942da08880300850400158407004030070f1076481e1785030400b18942083d071280e09044100c190000100f079955100058061150140e40344059003080c0c0c02103251220f800c80c103800050381441100700f00b00140c0d8070403200c0c03441200d462078121360100200c80103a400d4035a0b0380c3c200c0e440d8045c0703030700403122240742420510300441c100300e039003540787c01500803603c1d1070300c0403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 180209721 1250 180208471 180208499
    0x4060816030f150c0e09060f090613140405100e06040507050d0c0308030f0403030b120309091506040b030a0b0d081603140f0301210201170a14071e1404 67
    0xa890f070946041100002928034044c5000480456883c00f81040c00310040000010001c4d0510f400307a08503c034030813819103403148165040803048462609103105080f28002034060071400396420750420051000f00480082c001e10f0f03103005100f06100d10001201c06907910141282c000d00250b0091504000343c0c00c100e6604404140500c4103402c04a40b07030380f07800714181e00580300726250072a10002c10041c15418415906801c0301120701c0c0b580444851912076403070082c1c01c0070700d10400c032030008902060039001e030003468480702608903502d80d9a00e0440445a4008441648031503041c00400401c2d460074002d1134040f954041c01d014205030a216401c254044403600031020302010a502c060fa00c08000064904003000305110b554030760509018402404a07040c4950000d00c20440c0400182e0304a1030100000087e240703050655503820350840045c180087ca42600406613800344036007141c0c44240300300350486408111100840301034048403081c50b20684800148000c1c0710500410b50b040041c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 180210971 1250 180209721 180209723
    0x708010504173609092a0a08010c08070206131a0613020d1a15031801020d05250c0305040501050c0a080c0102030103021302030c0d0b1903050c04060816030f 69
    0x10b4001c554858600d0480d61280407010126420f09541c01e5481902c1d20580003980316103824080d1800c0008032a41c808a0600c08811071540c8001180e150282c0e04d0b40b00300c020040a64000900c0400b91700580582000c90a440c020014060800040d4450001d1180031a0313013035010201c0100c418030701960030315002001c0c148561044c0b480c1d001c055481c01500160001e100c401c003000803a18142c148045503100190305440c001c140101d1500300292600040d0380c1e102140c0310520300c102c540c0440050080c410250380080c0a45082d050202c3c1000b412a40c1081d0303454004019041088844140c8034003910b658000c000560420040c440340d48030f200541007445001046034489402607480d00c120750030108502030107a42c0800100250f241480100d08120644d510845c030f981881300c0c0c048110f202c1d24215a44080c0c5070035100701c0f1629603a51000c2220410b51a095507542c42e4078101307480e0150015120f201d5030800e0700108804070003241c0791000709118615280185c0c03543d40c8100c032004401c54 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 180212221 1250 180210971 180210997
    0x1011010e060a0203012d03020103050402010210150603050609060a1a040b1902010b120c09040c0b0d05060432060102030c030d20030403020d030b19080105040203070801050417 77
    0x2280003120380d081015034082c60141d50096229030401403c0310381c984440b8803c21a840005080300a4207000300201800d8030340a10740401c0503592800142d240500280f0b2035080a0b183ca003046e4404100c0d070300340f030050365102d68050000b40c0340c0c002080324082c0c041d00d005a0184030440f00300501481c94680155009034040000e00341a50750740d029451742c104490944c42c06040c902200340c944d50a03c00c0000c071600c02c07034031034666841d1501015542c10a9044c0140601030390380c081010b0010b58400346004006020b2501d0ba2414640c0156020380004d45000c2c1c004c60500c02a59a42c06c510803084144101004e071851800c0100030100c0c041d42030250100e0305500003000400e43c07040b0144018404100b80103004203e034222018014116101a051040d801800f4024400001c0e8080b0b410b4011000a1070003080c85001000081c181110b1002504541c010601c00010640019040284203a00840c01e88035201c2d5155030303c038243d50303049400401c44100c00281800960507030010b0184812110 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 180213471 1250 180212221 180212231
    0x9040905190602040801060b1e13050402040605130906050d06021c020301060815030d0f08090f06010f0906120503070210020a06090b06091b0a0e01020a060513120c02101101 76
    0x800c1ca4491040c85803025144150000703402e101c0310109008041c010401060a145491790718403c00d00307000c020407208107039a94002400348601c600c1448c0c44000c0c10300180210760b0f441d03444c88003a02540c0481c1520000340b5041c00c00284c007250b0ba1182004075180600301252071b003c3c2d903942400079800f00084000c4200c1403042d56081c64120310146000e069940c45002650804252080b0041900f4030b15a10070b40c445203076080c40039071040400c581c2c0203450411f50400d03110302409a080c120141c220009601c50740000140031103a400c80c60003241c10210040021546070032119001d060700c514054680e6204201c240d0060510003105000340e40d03284152030000c46103076a1602034031800c0d0010740781e58842030103000b42807900d081343c0c540000e0b20101c2180602017030010b280c098002c2d0880c00d030900442c030b4144511a40244500c2e60716a43c0000f08202600c0e00c004032645c0c455820f00c00740c076696103031461400501c1c00350401809554006200c3c04007486400000c8230a800c41e2880f03101d00d55215 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 180214721 1250 180213471 180213493
    0x1f050f06120109090218070e040914010905010209330306060408010501091d0a02090f100f0906030309080f031c0905030307030b120705012f1b0907050f09040905 71
    0x10907081c50207000c6120020803940480d00401c200341000346c1d80308000600640910440c01d8004025103043e450903100483c0c280558203040380b0200d01c0310401407440d403c2001f40020440e047d8010210904210380d40f000c0409142440402c840c400300507468200d11a128400100a145003c1e642c0641d00a2205107015113501445003952402c0c0c2c040d403074940d160400c4403029280348040d00503032109880180355403032a0f03400156601b180900b21364540b0007840c010421070382c0e20130004400b62a038048403212450b5186180c0008101c288410750000c0c90000d4003117081d21001c130b4900c041c0d800d440003d5003080d031000d080549100081e40381503501c554442040001801c1440914400c59503610b000413000c0b6290103120f46880054100c0c100e5170420507090281c0c1ea0441d4407c1ea440202ca080c401c0304040e40307a500c800005a1b800307014a14410401ca0459041502a40500e081419140301d501e1340c64801080c5c90358021080d40701c141070030070f00038415241040c1d070003290380750b0092044420641c24 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 180215827 1106 180214721 180214747
    0xe0a020f07020f040f24080f0304150302090406031209050303090a0b03090c090412020f010c1d0d020a060903060635070e070503040b1f050f06 63
    0x41108003c201341c8540e8008061990f24140402542000d2132142141c0000d452441a2003250301c2c0b008124400c0101e440c140c0f8000000c02542880c1c00d040c04001640f03252000c801c1056400e0003c5842c41d601ca00612004501529048a2802a082008000c030b003040e04903d010351300800c45803825490b032000c0142180e44c40248552a5180c00c400213080540c0205580d80c003441c1c5400344001c0c01035030100c41c00e901e505034080314810300d081214942030302d928140f440085408106132500c56074185940d00401200144105005281c5500291450301c0580215000921001e020700800c01e0034403d41c0060000061803000c00e070760454000304100c068a11102039150000503660110381c0812404000d040510704107005031900010060807034104540035294a440d40010507007094850720301c880e4603807107901d40e420000c0c20042441488888161500d401c000200b056880c1c00c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 180035971 180215827 := by
  have h0 := BRFrame.cov_init 180035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 180035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 180035971 ≤ n) (h2 : n < 180215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
