-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5342
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:33:10.082884+00:00
-- url     : https://prove2.me/submissions/f64fe63f-dcd6-45fd-a4c8-3c23a9398fe9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 960611510 ≤ n < 960791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 960612760 1250 960611510 960611527
    0xa02030a0806180702060405011d10020c030702151312080a030b0319080c07051005070b060f15031902090d08070503120f090106060c11190305032a06010614 69
    0x210404200b900c0f1415100d26508107084002e41d40c4004440469642d0b28003240b00e010710aa540400001e1000c0800078040c02e8103140342c00d0b003e03404c2910f050300c0314030041c852240183e55405024041e00142401c0588520035910f0405040180343c2c00703000b0382c2401460010104400e901150007042c558100132074040076141c0401d192000c044050b43c0c1905070302320b41e00b00b0000c0d031400400e0700d10130110481d000543c50ba0100030010b8444504100400ca007000a00005a102c1072030307542c4410000c210311421607941010403121160001c200c0d2601070001300704403481e00400883c0c2400344a18104600381040c51380401d800700145003001d00010008a101400c10100b00116084108106100d40d45410561811401000203840074062542800400f01d801842820100060380e042105001a500343ea03061001c01d5100e06c81000707a0100b802004004a6010801441120590442c410f422840c5502d403419100c1c0b1001c1c0a0401e42216004015990340700c00c140d04000c0c031500c00155160b851 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 960614010 1250 960612760 960612769
    0x2b05010509131112070509010e090304180e071215090506070311070f03031409060408040612020c070f0906080a050d030209010219080409060b1611030106080a140c060a02030a0806 79
    0x49443c3e40d4050b04210303aa200d40e0a011078000304132101513803812126600e400c140200860200c401c2c902e40d9109010400c25030310030b000d040101003800000000d1118100c1662030428404d41c1040c140e20b884d140810042280ba505031443c1d038110138600b0400d5501c00d6540c1034442030003510010030507494105c2208110103e07012100340a5210840c41c171316101e14074005d00540000c440021a01f45030304c00095003120007140b03480c8600d90150342c1501c0c180c14100c0540303200d00c41441e020000c2d0f40c2840413550b0b0f07841c200084c84c043c116004040c00d46034a0b1559200c1559126044102c080d0807100f560700010700001400341e0341204c0c0741009602d0314020701c0105e24080800002503002541003490780d0500101d00c00503c2620b20804c01800000d440d02c4541c00b06100c0c1004c11690303d200e203a00d02c00811b00114500c5011480140082100c0b556400324620b41101e650044d950400d448001c29101d580801a01351410019074580b400e09003103a5000e510f9002e0b9078580c9080c0201103001810039a507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 960615260 1250 960614010 960614033
    0xf0f1b0a200a0c08030a02060105150f0c060a0f020c06130f1217150f0f13021201050a080c0a090b0d14060925090f0b062b0501050913 59
    0x100c40d600100740d0060440181e0362000721910544000d48a40b1011402800200071103041c130180e5001041140d10f40000d1155010020301e440c0f01981080c0b00c541001c507030381c00040000c91007100c010016800d100f00802c0441e08402c0c00c4100c058170410110f0840c3d000850b0155109000c401340c510340300300d603003090344109560b100c2c020a58846121040d40241e040300d1031a000598040c1c01b030602c1e0307803001ca02c0c120070190446420b5000c007504007206a10700c0d1101240444c8140600310704074007014203401c4000d91700302d8481d5a2421081c080148600c0c10554405c4c4020f103811001800440c80c00341c04980440241d00410b00c1e50380c0c4441d5000140c0e101d6100c60000c042c0c3c40b070f548100c0d40c140d20400340d85440c01079a10303c02c00d0095100c9081403c61a0995003100040c0e94104621185003440c1000185040800e01a850b41c079100e410350030342c0e202c1c009800f600b541208542c041421412941200d05c607540000e040e110700c1d0030300600031a1a0384441c1035000c45c5104021500c540c0c0b0b401c00398109013 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 960616510 1250 960615260 960615287
    0x190f0603050d02150f040b04021e0307081b0402040b030105010c110916030b0a06091403010e010c09080d030c021b0303070203071701290d0c0803030f0f0f1b0a 70
    0x450710101d420702c540d002400c10142c2c001c045112095071181d00040245201c1906c010b070a80440340c022401520345800c148035400001000140012090404641007842951003040940c0240d182c6140100180021019041c0708880862806040c05201b08050006000341d07810080c0c00c0c0e20801c2003206400c42012800e000a04102079480c240381c1446441d101c401c000d02c0000d0034060202d5440c1450013940e02614900d40750784002d6800c040412407050314880c080c1e03a06649401c0110101002031144a42c100c2c2d5980e075188119007000074681c40c0c103001038080c10800d4500450f440b07110707501044c00380b030780f044400e41925200380e0307440000d146000360440650b140c02410030020b0758205c510f0501004005800007445180340c44e43d102148078812030341210f14580f101603022014902030480f40d0100d071140710032407035450722a2543c1d40765400840d0080e441c3c10801061190400356058210382c407070000700064945142c59520706640c0a03000307050f22840103000ca00c43c1e50040c0512005943c11 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 960617760 1250 960616510 960616513
    0x130e13050609030d0e0f070b0f04030803040f050c0922060e060a090c0501020111030408090a0e010e0708010509151e131506260604090807050d0201050f190f060305 72
    0xc0c1014070700342da02c80d407000c3d001c1c0036500e00d01090450314440114203020741940030301c090b2213082e24040b48040c4a41c0000c01d10702608608000c0440002c1d03040e0055070180b40100c6803409070324083d01d455850413140c9911580b00385001410082e0364900000105141e00544040090750140d500d4158050810481061958010081000b1000070143e014088030703402440e410ba0714555a80c01039080350803c48100702614420000600072403510801400045030140101c2c0419550340e01d0155468002e1300040b031000008807c4c481c2070380d4805a03075400f402c811a0b400c0d00074203181200c4e030b03c081c0c0149911b40c0602c890044482c019060340c1c0b0400b10410002e4140102c0400580740342d801480403d0303d8a1414030828000706545104407034402000340081601c1007201c000b00003c44600308020107280c2d209840c0c84103400000d075180081c2290521410040000380da0501e03000e03094840c01081d07040304030010010004a101c1403150240c040002e174030002411741c07000c41118003600294201511a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 960619010 1250 960617760 960617773
    0x31309050f0c1e0304020f060a080a0e063106060b090109080c0609280b0d0506010c1502162a080601182f0d060506130e1305 55
    0x12406503040a4851820038092001d1940c404040c8000c0380070740140d070a414040e0260555140750380344001d5402c140011304040381e030b092040010f40d042d4007100c1103800260340d0005001c00070301140607841503952044090b0401e0f2900c400c2c0603004020710b00520707211305035900b44295202010311490b81d049411040921400785c4400710300720035030b00850449000905078000024105004244500070900082c80c6c0740c6002c0c01c241c1007100f024441e0034590080c000c1c0c01406c01c0110503030340f894002402a10700c040d88403000300003500301319480146207505110400c0741e00d600081c4645120407440c0ca01010040c0c584818540d02c0e81d0901031800c008168001e40038480c40a82d4510350200e142a0011021080660301c900c1010707150f0302c00317118000c0354170b07034910b20500c441940c0d800c441441810003c030b07400b4141041c87d40c1e4040d070f08803440441c040700000961030b848030071601074000a40f400b5a406032421095000c00320780405641f14000201c1603410125100c0a8484101c403e0310390008101e410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 960620260 1250 960619010 960619019
    0xe0a0c11010c030c0e0319021011030c0c0112090b061207120b04020306090a030c06050a240503010b0a060801031511071209270e0705030f031c0605090a0209030313 72
    0x4c1c040b18907048007140340d40c9281c2016290004d180002c81a001c1d0250350041d00660901051210b214410000d000783d9046441c6001010006403203003500b41801061b9034414500050031200080d01510805400c0c0072060000c40c0c182040c941e0000e0060301c11100c15243d50000070b003400c1954001940c00f035500340221023406000400d490040d80220240d8503a40c0700d01c0700d1241c0d281d55600004000c203c441c0598008600d50b54401680003c91201c0460111101c004004050001300d0a0507a0740309410404c2c030885c1402d22600000a405840b020340060510002411300072051100030403101184c0142c801204607900311504065046014a0700e503040303031a244002d030800071b015000040c00030130002520005d8500c0d002c5d1618404021a0344440b181e40c4070000790001c0d4071410020300c02c2c6000011141c90802c0a001c5005c4103401540d2104440e07444c48080c18143e6214030040c50a0020600403035581903020b603048480390a0040e2389607007030380c042400c5014030f25400440181e00c100004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 960621510 1250 960620260 960620267
    0x9010f11030f071716060902061b03030403030c1103090409020f0616060e0102030c07080c0c100c061b140a0207051f0f020f0c0d0c09060314060108070e0a0c11010c 72
    0x7002d920501007a14152500107082e0518050100481c2c5c443c010f0882c074130041001e42e071041c002140094180f503d0100d85402d01590300381d0f00c51440c0059840002000103041e0b1500c01c00c03441c142c00c1e00d00201da41c80d42810441e541d000b044012480745a03104203003011556204980c0b508004041d01c20743d12200200d0000c0160400008140c51080c01e10008100701c40042c0300b02d034030135054411450b042c0803080e00c50520642001c00841c0c0305210300e520f19030040d90741d50f202c520500c001741c0d036440c819406494400c055910b40f01c0311000703244001011041403a005440512288198910319458080e0010102e1501840f540300a800042d000c402904242c00d10350b030741d5801c0b606901d40d040f00300c82c20b00c02241d640f05413050400c02c075004030f03061000a180190081030302d01e00074007003120307099151905902100c000e940112000700016004240010050100500400c00c0602611481d407070b2034000070400d080107080505440c3c0c0c60003000c42c0e06003d41b01a00d035089a10f002046040d03a12040036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 960622760 1250 960621510 960621517
    0x5430903020a06050a0801060e030c030a0b0702190c0b1c0905030901080105010810051908060c13060c05060712111b070f03020303090d020411070605010f090e0309010f11030f 77
    0x2030340101c402d0300000ca8041e0182e0211400f00c1e54945c0c96107800c0c1e10344202140c201c440a0003940d13250090072040c1e480c40c0d40030400400c1440c0107554a94090900c80380103407400a0315140100c5103c2c030002c40d00301194854211400f140c50142d4540d030303111069504003c0c200d0310f400d1140d8660349400a100c09101001010b010804000c2c3c0341e5448590300d8000540d44505c0464101703000301034800042c0310508200503e8602601004103400c01aa00c0e44061810000200c400b0008c0840105c0e0b0341200002030050000144036a050035606100c1a8480d1501d680e030060020007413203403211700c2c2145000e141d44a075506802143d0b4480d00c45400c680d244811103003034140342c0c02910460a0210304505921340d10303000c6950080c000c61400c0d480300148121500b04078000e03030340607507103c0d140784a404095005120b1a40304820000301d66040108101880c0709503001040010301d029402a100c007400000c4407014042403c0c0340080081401c0f040310882d440e1440e101c11408041803401c0d210840002030f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 960624010 1250 960622760 960622763
    0xb0c15040b0a0c052a160303120f020915030702160806090111030709030314130e2517060307050604060302040504050a0207030c02060d18030c020306060405430903 72
    0x9110400e030088048583d0f00440c8490f1942ca05090740e42c14004d5142c00c1e2120000340780d4020740307141281b04d20f20310901ca0441d9009501240c1d4800306da1107840c000d44548035900710071140450a01440101041c20b9207404001102840d00010110328405d0080007400343c00c420441000059640b5001c03980c1c0c5804090350010260342c2440719001c2d01c0d800000c1524410a415036491285601c0e5440c01c40c0d500c5491702c0040c0e10554100240426845540c8403500904100c410381002400c022802c6921414545c0780c009031402a9507000d170145500c04500040301006403059038050b107803000060b00b4110355a000650115002400240c07058040e000381c401c0707030300c100d03801c00c000d54400100c00301b07a2040c0c0d000100050b50607908080107141c460f000d172211301c2c94054001040550030444421030ac0a484084d404138200d0030403102145020810503600900944060000b4100001c000c803040c020580c0d000c52146007610301c801a242024050818090341c0c051211781d00d0403942014103a000170713020 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 960625260 1250 960624010 960624031
    0x1403121504150501020c011413061106010806012306090d03120b01020c150309030409020a1e030e0a03032301091b050f03060607020a0902072f0102070b0c15040b 71
    0xe10318014642da60b00e00c0885006801901c1d01e038940500446401000c0c0a080c83c25410902141d6081074400c11114094609920b40348520078040800c10320f803070700580c080c10b42503010304014003824201c680d0040c0e1032a644296451030011000000e1490b000b07000026410100151030041807660114500110300c02e000800c000183d409001261141c0303881c000180c0021300b4841c20742c0009001e0000b941d21400b0380302540e04164031101d044090ba40641c0d020310002b00741030340c1c01140f0705100c20000c5001c172213400d0821207850040103461711000911000f8090545d542d1015a020402c50400702d04046504961400e03503843c2d20341300c401004804803c04d503409020800080f141e00031012980b5100c0c1c81c10301c050a43e0b440318200041076110107012a0410402a00002c40003001e0024114035403003100d134400301c145c0340c81013000c0315003851024600001c4070003d404d2160f6000700c0c244095880076408140e440020100d010b240c0050040c041c0e021610324001c020611581020642c0202c2002a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 960626510 1250 960625260 960625271
    0x20c03121504060608130507052805010c23122a03270f0d050c13111204020d05030406020307031d210106030c270e0a1403121504 57
    0xc1c00d0104584032030051101007075070300021a00028807411000c960705c1c8544125104e2940f100e01041c0d0510180410305011956085601030b481c2d034046000c0c010b00380a02e489001c003101e03600d03110700108450840c1300c00c030444842c000b0441c03001441060301070781c940c414030384d503880b40c20100c801d04080f0781320f1845510a03800c43c10328000e44003008880e0b113055140071a00c4403801c0e10340140a070701c81741d021150b407010400c402d090341c1d034807510024040b050203a006800840380100c02c0c001e614041000d00c8440711f20301a07030018440c20321016140010002841411140d4880c804130314001e9489401500c18440840c2c00168968008010041c842c442e595080216650003890729880410300d00c165840360084001d442000c00b4055088810061980041000c564980f50340d03160142a82280e0613690400c0360a10485210090850180310001e00800212130300b461203588801400c00020700103040700015051009007001501c21402c1c90000e030303c45905010708100200384810850038000c60826 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 960627760 1250 960626510 960626551
    0x11060115120b010507140f24100509070e061309020301030312140114010e2d0916031d011a130207030903020112150b0403060e12090103020904020c0312 67
    0xe00403040410b42c184c42e418140f941541d1441c81b403500c2e050601200d480b80c0001843e81b000f0402a12051000404801c0c105448001c00340c000110000d20007072904503042001c00c4691a0f00c03152a610410710b240ca1101726801e4400240705108211001c01840842080410040365590046049900c40c1d2581c094045548540000391090076a080703400c0740c0c807071004100380043c900700716980602c14034211554540704000150310b41d003070751119048103124a0b1241c074540c85404200c1c100400494040d440c1c0d00d80104490211503054003d0310801d6120044140c0081c40c002031102c08a00c048024000b064000c03039510b2002040803080c5102c2e0f044030b804010b100c1d040d48211110f150b0940d81d82001a404d580043d11140c10f0352076400c40091ba6500c0c580100709004012002070440c4406044e5110318504103c015a443d402160005801c0799900d650b0003810001218418a4207080141c0c544400d50005002802100c40c03421142c040081c501c080e000300c0940040c822107400c03861011f081c61070b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 960629010 1250 960627760 960627797
    0x14010804030215070e1c020405090c13111903140601051204060903050910091401110703030c020402040b03190c051606151203020a0303060510050702090711060115 72
    0x162405000b40c0c000c882d003c01d502e4a42e561240d404a014145500f040d01014045210703034800c011405020400c0501a07003c618180c01b540c2d0300060f400005102c09080100003501c180c4020000000c590307540e4a101c03241c02c007014190f03000002e1100401090790b4100e140600680311000408000f0070b00700e00001c070998042c20641c1d2881c01c10044c034950507075640c1e0ba9580102410381c000d0303052200611040f51243d640012058000010f81d41e5603100524040000100580d601c2c00b081c144486680c04549a9030b0020b038040c02c41e40c15162180d40040c480c000701d002486207400104000c0800020043c064030b011390016122440c219003040391072203441e8201c0b040d0141d080c6441c0c04905c40750040000c00d480c1c2d00020150407030360051042150b0707a03501c108140440100e044000d0b8004a507840e0a148c5c244c401e5100912080c1c42500b100e0407143c030010014811960000e2040124001181d641071180b0902c46800303000004981712543c6804100040560207840303000064100502c10015400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 960630260 1250 960629010 960629027
    0x1b05102018041b08070225030b09120a05040503281707060203010f08060a0e0601180b06030a0c17160507030309020d0b0a0e0118170c06310314031e101401 68
    0x151000c7c0d46908a080d59200c000c025005008044148244010103034825141c1b4010f001110003503c03801e555910300f106160610005001540a10b0741130001613a9024040685d210429807001401034102c0d500c4d806009a4081c00101030b11152011001007001c031000d00005e004d0300e018004841050741c03110700020944501e104107400a800c0000100208041d155500c400e01d451a1030100e000d072004000b14240e504122201d00500f501e92410b641155086400301503181c00290304d61400d0b103006140c8101d002040c000100070080c0018041c0140340c4030340d000070206a0b004104d60452902802c0550310748209940007841a85044801c1c000490144580c040c0c1040d0440c40c1421440d09885240b6400341cac0300d4504204540801c429000d401040c480c05d4410059011280110540141c02051038030032500d01000701140100c480c00842e4005c50000300003030000d410a9501c0da64000c9083d03400e801c800310b1203150840b66060004140010680500355244010390f00744034801c04004440c01c48 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 960631510 1250 960630260 960630313
    0x1080a0203090d08100801090605061903120f0905040c02070503010b03150c0706020f131404231017010b0405160c03030c1b05102018041b080702 64
    0x28001c03d82c0c891000d000300c452581c8040c1c0707140044441c83d943c580c007509550740007908a520b0340d80e5600300f100c1e070f26280032a030f00d824506000350881182560703180030702c1c03c203800103040500c1445c0920f150007911801681014000140052080e044002c2010b9a038500501645101c0c1d400c140031160f43d810002803141d0b995980441d81c1402d5121050140e200d90711000080d224a5020003505150b0500c10005100b40d1001026a20405140641c0150040d0122080ba440795060050240c82032260844c00090340e100d2103e40e0300c0a4440c8548045114290343c860b562840b0400f164240c0500c066100c0c00403100180c500f4402c82c0d80300c440040e1010003007074803940031905100840f00405e1184c0d1120045003060b040c603100034800ea400c4640b80f0b1007841821502580700201d06011019140210552401251034041c00440300d144001c1050048207010241d07200e10003084409a40c882e0001d44201205000c0400d081400c24001400e0f100e0441b0000090322031030955440c4880c140d9040c4640303c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 960632760 1250 960631510 960631513
    0x9011d03120901020c2d0604030e0609180a06030b090313120302160f0303022a011b301d090402010c0c0f060314091b011b1101080a020309 61
    0x28680c1c021000e80140081c00981040d0750a0040d64070301d03202000030a00c000e44500c05402191882e0286401d00c080705002840a82c01020900000030340001d4101800001100c6503501c1d044503401190902c581c41d0f0622106c8440c0b0307410701c04840b0440d40010140d038059064000c45031340300c14290759039101d6141079100d00000c0f01b070200058042c13200100c0034248071744180c07810645a965180861403494004101e2003442316003c20405404100d200f01d2500390690200c0002d041040307005480980e56555418030000c20000f10358814442c0c10104071542c48082400124507030310403040e9007100502c880c60000510071801d11428000e5502d513000d0403000e211804440c00010500c03220040103003080741071080c40036a40d80040c005290f2000a44444a001860170780340c18001800d80355045481e01c45a80264140008502c010803900380180400c120400e00c0b003012401228060014040b603200c400000c541002040582c0b580000e518200366901c11035520782e035107000200c5c80280e8400c2100e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 960634010 1250 960632760 960632767
    0x203071407051506060d110415020a0203151e0c040f06020712080f0909040f051009080316210e01150501050304141002070302010209030d02030c0604081c06090509011d03 75
    0x21160752800460340f013800640580c0c100001070700400140c4019501028184070f000c5000c3c01f629201180d0201e400355944000c0640c0c070f0380c0d03401003511042021000c07800d02c00300300001100903002c6401c0d850710a203a61500c00349841c040f44454060b070454086c82601165554000030740c188000342c500c0664082014600c0c099050b50380c3e0302070301d502040520720300100601015103184d80c1d10b40390a00c500d009140035070036140d803860601c1c201075010101205591900742d4000105a01702c06699001e013903011340c154007007a00c24041c3e445180d10328a241c800d44202072403040200850f0842962207980c5002480b217007145600d048200011400f40d1800101c042c8006000b00f0000790182d070000d21840c050720030010807104543c003aa0f04c0400142d01503034001070080e00c2400c00b04010b090003641ca1001d14200070b00c110350b031500e07850068000b03000312a010a403080ba03d407070594982210b1011007010401d09130303a00c501c0005000c0403240042d03c0e5281c1159aa03d4120221034100348903c1075028518 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 960635260 1250 960634010 960634033
    0x100501051e1c11120106060f11070b1606050115020c06090a05030a0c03060f1a010302090a08101409070e04021e0913031209020f010c050709140f13080a0305090c1003020307140705 79
    0xf040581c0d0110b02409e440307071304000509034411320000c224040c0d090705504034480030f5040240644506a101d4031000e80344229191005502080300401e8540c02c41b5056611025640000c0941d002500500e61501801c0c0e511401c010883d03a0311400c491282c8020301c01ea0403c490408204c4080600c8108416001600c0b0f40d04c561195008100703042c4010036921009850700c0f1801d1502511401034a4910b5542c18902d85250391031b86410b602c2031049004040e007a080c0181803e000402810090050b400111200501100810b11441d29000608094402d01d08103460680c03801c001d05098010800c5100d030440c80c0a054003403219050740280c240200661088011110f07860394040680b164002d159000c2842e181501410501c1c2c2d8420640f000b450420b203400c0040c0002c090b007149403c0300301019040006071640c003683d04c0380146003070000301583e030b02c22000e0030a0704403004940e005407241d011098070354069002d140100500da0300e03a8803003108050b94460505c9280409030169000011202 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 960636510 1250 960635260 960635267
    0x90f0f04090c08030309190203070608100b180f030c03062809050d0e19032402030f0714042306070210020708100501051e1c11120106060f 61
    0x148600005000001d045000341c5410444403166040043d02d0707013000081c072840e40c0040006a600c1c6c0080125140c40e0b0740146d0010740d8071031051290000b408800310000380305080f5010010028002c0c111841d50b2840e100821112000d90b4003c43d6125240344c0d40d03000c2c0a4180001d0903c950b0402038024103040d211030340184000a001c107940449032101d12039604102d00300703001c0c0c415454030441c0201410411420007801482c003641c03d050003104070f074a400c4d140340b20b005080d908890301f05456100d6107481001d02c003030079400744043e03040c0d40b4000828098008941c03251180b281c0d04642d2401e5414928042040751132281740b09240b0850350114100c90010700c1403403680810440201042c0c0707064619404a00c0d044048030801c0c015070860501003014000078460b00c1c891000c40c03141000658103100004a1175845560002c01e50703488072000c3c0405403528241004d260401155000c4000030a10340042d8131004103c0c514012001c0e0341a040c50204140125000c0d54200e88030078000701030709030044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 960637760 1250 960636510 960636529
    0x1b0a020d0311040e18100e060105040f0e0703141c0809070501020c0d021908072409120b06010207050406080703021314040b0705090a030605060934090504141803090f 73
    0x80c0106c0c001e01590181c0c0a1140c0320361a030000d488405482d01d9031418040004513100720f08606091400d00d0200644480007150a20949910200841e10300580980041c50038601560022054410790403074040d071034100c0c0500744521404421608460740b9100126240c00b413103081c2030382001c40b248503040149480c56004e006107200700803c408007a03440364803c0c40c242c81d0f41d2104481c1c00d13803800c894071540c1100e00500c2150515051441e00286400c00c02d0144203210034000d0b1104e5802e8010a000703a06c24000c030002401c0051040c020151100c0030152948403911040340710300c034048462582e10a42c1d014030210910420f40b4496181c0e1551a03903d16104010240c0b810801c00b040041d20341d03500d00308120003075401450001164a13000040c0101000040c0440840641e0b1041009060020100028502d1a00788105e810b001013440c0580701440c158002680c003905110b00012800c00c1e41d40464402c0c1544a8508000024070342000d0300e902c1800c103031980241841150645500346110071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 960639010 1250 960637760 960637801
    0xa09050310201c18030225062a050c04061e120c09020f03040b010b07050d03110d290603010f05010305060d0209070305040201080a060f05091b0a020d0311040e 70
    0x2c0300100b016903542c501100c4006001045103144c00160109043e0b0410010b4180d40143e103440326440f59080307260303a0300c1c003181c8108810811000500c071003080b8541000c0c0140c0302c014817046200315030ba217032403074407072411004850003030740b41c410300223411500c500a648a141c81400e40b01c07890703070500c0030400030240070100a544480381400006206c124920007412070801c43c1c0c0c045030322806e05141450201006900000741c2d0042070224402144002c42c498503040360500340000e10030110051850303103004000e520644523240c090044002e601c40c07440c10101903080381c4034410340d60016040001c00d0000f03000e80307211240c1002c4140110350080e4002031700300b4802403020418440503400941c02c1e010440f00c0100013511181804215604034070b44903040840b074001070000038182a40070f072001e1602d00c51184286c0000e008500c0598048030500b0780c0342142c0c00c9442d80c1d4114124041d6070307426080c032560006850300d56103910f201800025102901c5400c0c9044429845000b502903c41c1c0c0105003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 960640260 1250 960639010 960639037
    0x12030412170103080d0b0411031303030e0a0c0305010605040501080316030203131d060f130b0a0b040b1324030c0e1c0b0603070303080f07020a080a0905031020 70
    0x12a0600507803444509000390310440b00300d542e510b5606009025149a00e03c094041d6060042210b143d006840503264003c2d030f003e0020891030b0309410f084002d002c0c5c0b0020800540a0100c020040c0810a41d030101034a006d07070001d22519079100184821a8024807840c0a66081400350444030540e481d47d01001501034030440f0300b0b092101d074841c0c81444043d40014006050619800b4402c00081e00503035105a080b540298002c10030307804107908110411002d172080d07a6500400354555100103424001d001d40c0801c0c503440d00c0e124140f241071980214005800c0708004040050740c08552204007900501c441c1c81c40c030700240c19002c284c1c040d0a1900c0f04106002c18444c0d14000d5032185519184110759941a00a03c058503082c117404080000e49003d0081c1c10121061022a421548464012402d01d192001c140d8840c03004a04195150000030240040090182d4113264008400b07419100200d05031802c030360b514a100d100310b42a146840013010341c1a2145800f1000b213401074070380900c1c0d409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 960641510 1250 960640260 960640277
    0xf01170f0d0903060f270804090c0e09100501020339060a1107080306010e0102030f0c07050f04051005060d1401030b0a051e0f0601030603060507080108060912030412 73
    0x6011824a807000e2038040000381072601c20401e00180d80039440c10107155401c2000f803c0d10b114500718a111808841412403441d903400f11081042903400c980040006603000c001c200c4120310010046007010303040307601c6404110080f50350704c1d401c4656074040b150160011032509600380742803000c01b0721101c5e010b0b400142d611400805042d40c025084081401307000038000c0761610554a40c222180592075540e060001d00c9640c00103110071041b250010ba090030300b1a03000003440c0040b451441881d02010340040041184425080b002403180142d805c2102c001030341c2c000c0007040c0000c4400490307522014000301e007820811820090000d000705954014081142c4188458403e0301c80c20a0b8801c9801c0c15203203080002140f050700c2000c2d0841107280404100e0038a031800040b840a015003000c0030642c12201003103d81e0b0180d4000c100455000d0401e100d58a0144e0001e003100e802403040d4070380c81c01181300080c40100c011581000820441500c24259111174541140344103650110006020010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 960642760 1250 960641510 960641533
    0x1080f0c010e0f0d03110d03111806040302150403020103050a0b090714091806040501090c050d0f09150b09060604060c0b060a0806010f090c09050d0308130c06020a060608060f0117 79
    0x500e410034528040e07111686100286d990307072031a2501c5150351400305442c0035070740541030321110b04584201c40148400c801c91145900091024030031540002e50040b000c8100810041620002d0f00c2164000d8904000e00c0d59054500419900d252840e02d07404450540081c440c6400b40c410f5080f034014910095062614001c0030030307034404580d4000d145a10701c071810881c030b510345406514050728101006000960310b0380000b401c540242112142c0c642e0320303a8000140708140d580290841134004941c0f801d00608010800014041c184d0420301441c3c64400203a60340c240300080701c003120703000e580e0429108e606848080900c8030140801c0d52124074408006807000c410400140648001d000100ca1103251080b10340480380441c03220700a004100b8010446a658584610205905810070850940e41e00d00d00c03903c050031095005003140502800071550310350015000b8621071080e60100311036529203490640d5860100c903c0d0108080c214018054021070f203101010202c0314204895245401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 960644010 1250 960642760 960642769
    0xc021b10050d151710061a0403030503090a0501020703081905060913020607020d0c1d010311040203090c03060f0601030f05010b0f0c030d0608030306210d050a0210050a05010e01080f0c010e0f 84
    0x40c03801340d01c0303901c920219002c0f40103601c250002020400b400101122908041c1e05c40d80c00b4510029040c0070020000500c5010144083c040f85070b800700003103564800d54a0060000b40c010303940d640650410802d540407054191040d80c1c080d41c1c0041c01c02c0300b0340c2e5650110414000c8244012a0018070601030000180c40d170086003600e25124541d05401c05052000c1f0b50f4160000e2040e0300850380f408001000802c4210081205060060700c000d0382e6682c60b01400c510703154054891a070144280020020000303000f00506018501c26a001c0c0515901c90102c141966403c0c0502a202c2804101d040c10001c010700040003000c44410943c1c6c144200000b400e0200c92080e448241190000410407689103001a4038401900c21a00e41c00c03407888910454a0740c0d0007004070740506100c000207498500790300802c851800401c1220040c00b280c60300c42c1e007840c0681801c1c8180000300c401c600001ca0041300208401c20b0b41040240144403c030221001154600070062031250080c0e20390095141176203c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 960645260 1250 960644010 960644039
    0x2030d02040b370c0314120f060109030b15271501050a0f110102190c140a02030a03050d110a2c060a03110d0c021b10050d15 55
    0x1d050041944494100200078032043c03800302c11055400500500140c00d00903030000440e090b03401c2c54150300710a42d602c0d003920745400301541c81c0c17003220001c1401180683c808800c0d5110310002080900240c582a00544030004270313000c02071081d07845100050b0507036044400c5401903540145480c5c5518005450369420300d94416000c12003080f440304002240030801d8a18060b101c5c04e20345649068210a8010f00c00c17184100d000040081c81181d0000c058802d406031026140003010009070741c040d072480070700500c2c03808104450504040c90541e84004011400e101620b801034003400c905441550120b070190711042824110564400c03000030300e1012a4058803d0752199104c401c0180090708804000c03901c1c04e03008814400e282220a126a143d000940307500040c40e08022410900d1070541c00c0b000c1c01101c400a03102032400c7c1242d0b000315800504803c20001c03200003c28074001590a105000f895080c3d65008030790100102030f16040654007a41d98006141f50141c04981c4036880000101e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 960646510 1250 960645260 960645269
    0x20c030409020c1c0c08040e13140a14210a09091121061c06022502010801080303131e0f0b06041104080a060c140403200d020d02090702030d0204 64
    0x9100c2800b03044c00c02c5407802c0c07851032010070b07090051145c0751655036aa164400d600076040c140301c1000210301d040d03068440115a031a030080107801e0314003510700b01301d541303c52194050b2160302c81920682800c000c082400e9503031a01191140100196890701c020b450703800980341d070040006000700005c10302294400d8450807018180015a40d80f003034800301d402004641c0243c00d484100000b484140d03542d10b0a102c55801820600050704041c5050400080c001d26121710b12806424100340e40b0711808010080000303100741c80e10f8183d40d0700c81c25641c0c0e990008440c210120305a440d4603c01181c010140400c0d0300d00407c00c107500c4060280c0d540d5400c44a1a00c00f1114036180c0800c1c885589041d024500d080c00301c1d4400d01d41005c1ca003446482c0d92740c040610181c410b944da4804000e06512800c44c0d085260b07010101f40d0782d50b82d900e00d452034000c1412410610300405912450400c1e243c0b0000d07080c50160024110140c160182e0208900600085c1601d01980310401c44c421800341d01d400504000c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 960647760 1250 960646510 960646513
    0x106080318120c1e0a0b370c170d0b01020c040b012f03030108031309050f1801060f0b0c12070b0c07080706050c09012010020c030409020c 61
    0x694111400c2a42801c40c48181d078402c90110104440c070302d400103004002d80c001160300c40d6585446600e031585903941c00145581107900d00c1404549401030200916000003200c50719045100c2c201c1002c2e600006040f0030401c0c85104590000b0b060348504108042107010f00b82c122203110941064404642c050041d514143e0f462300b825034520368044c0903076544041c0585080c803c000035038000814818045580c0b05800c1410310112a054624200801040e241d01044a80d01c2d40c6980c0701c1941c1c0d821080010724034140c0d402c0e000c1064180e07070003035900861a032000014542ca40824001c01c100311071004291a40d030f034000000d0300d000140c0001d4001c040507520950fa440154660380c0c107100341d0003450701014800300200000161010b01c540ea2140c481c90200d51124202e2410f0401032058050103803640b0706240c01d02011011300d80c01070443c2242600c494801a000c0d04103441d0700d445462492001c0d40003900740140314543c03500103282074914078050b24070341900c44030703444100d800c404415003030b5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 960649010 1250 960647760 960647767
    0x8090a080a03110316080906070f051e0307081803040b070201390302011103090307020d0c05130212070801030206030c071704030323090d3e0f0d0c0501030c05070501060803 76
    0x25500100240c0e005107d2401414451800303810103082005142c4503e000c100000601c40d080c2c0050420a000002443c000b00b40c2c0e9041103500285a0302041d503039405580b1030010311080c3c0790000021a412500010200c508211881c1c0054031100b003036661100ea4442039a6070401d00680110809c0311491010035450081001d43c03c0c001c2c2190000075001a09001c10024000035000000544019542c115000c500d560107620700101480160f500640d0094085d0320700c41148022500034000307a103486840610103540d040c80448002800b03210280d08400100003203111042e4910041c6002743c004c03481d04100d98010501c1e102141c0c0950f00540000b064040c004000040c8070f160414000d00f10480c1c10304104070f010016410a00c0800000c100c00d0801d07204194030154008224111655010a80802e003a6480d80c04240d0030403100d1180300d8800341c10b2401661400341081048141c2020100810b242460015002080049424000d006007880b003d0001002405580081d0503004081c688 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 960650260 1250 960649010 960649051
    0x90c0d09061a0103181101113304150b03030913021207021528020705070311060a1b0614071d09090d0807031b08100608090a080a031103 60
    0x5034882e4800240c10907041680f09021a01705005000c81117400c244500b000e20310400040c0c8000c81340c10a80d10290181c81302c98140941810048140c038000511801c010b650400d0b0000c0c10100d04560040601c41104260106000f295002510b000c00c00f034112854000b406001a0444504003008140ba03034000649142d040c950046641d0440d400340001c09c0b2082f40704200c40c2c0c80420060059400c021031441480380021080711000307901c0542c040441d0784070014104103407551540d0000b83d80e0181003d4001140382400021118100415034420344103040c00120f07000c0c074014043d803d441d100e03155064041c442e10140d4505006400d03d407280f452240401c104040110390080000f03102d0503444007005121400031941700204541c901e0254400e41c2c41103000e800030a622580a4401e4442d0800c000c42641c01451b21401180310700c0820040642d101c001f121a2442100c1c01203164002e5803140001400070400ba00003c00d05c0c0c00d01186030030540c1468246904225060000707141d10300e90020 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 960651510 1250 960650260 960650291
    0x120304030c0f0e0906150102160b071205030108030a0302070f05060f1f0506030c09120f0f07080102130e0403050906030a0b01110d0917030c03030c0c0d0f0e090c0d0906 74
    0x2483c1601c0408018600607401c0c40d15518000d00810b0300703010a002295180c0e1080c00110340321880c0840c40580141c60b0320a0720301c1c58201385001c49510400340b4480c05641e000c1c0055134122402034005520702101594214003039000070a040384c0540700c1201d4440058000c4c80110b06c81e00c0d40c240001030070318044028141a08429168245c5084600ca090003070b526840c0459070300c40c502c02603095541e03000f4008504110911b0294085601968a10180031200841d00c143d102001c04101c60806407207131521804c0b445502000f004082400d03400f04034201030480040d41c01030007818a20304100e00c03c800b04525910844501c40748030781d545c1000c206580c0001c2408a40441c240062600820943c005011200113000d4910802954120080c00d503078104116803001846600b40c0e40c90382841c031081c22403900700400d01d10b80d5001b043c018a070281d1082e040800f030303041155510f042c840c00b403206100b0380d11030203030404038081c1080059495948090049800d510f01c0307604000b91707508031558042c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 960652760 1250 960651510 960651539
    0x12090606060809120a0f08150a080d0e0f24131d0c03070c06050a02041205030912160603320411010504030c17011d0c01090b0a02060f06120304030c 65
    0x2004c000381801350620607170384151011101101350030012156104d1200f41041555000606640011511400b01c0c2e45c20002c601c1216021098607401800b280001c1040780420300302e80d800381c0061095403100c0410f04140d0044950784142c840340d500d04448611300240b481c000c0c2d04900700c40c00d00031a841c14400040016140c1c4003030307250500341c214141070800604800d030820005d8039040d2160b021801000303c5a044030010702e6a205c903000031b40c5007458100d84075045a00241e101b1104041100c50500020030030148001d0701003041c180c0b41d414200700794010000e0421a80c2d211108640309559054540807000d91140b681c01c07070185515103403800b03021210724040d00c81d040000510041002691140c030301c409541c07000303907410b2000e900050900c0c01007140c0781030b040266900101c2c040d883e2038040380c0145409030a0ba101d0342e20315140e2503003a201e8410409030800507800040003904040d50040035580200740181070300f08015213828400d1850f04030341c2050f13560f071040f0303e001c0024202c5401d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 960654010 1250 960652760 960652783
    0x2030607091202010c02030f0304180f0c1e210f050105040e100e0a1a010303080a11180a05032d0c01051e220602011404110112090606060809 62
    0x201d50182040410a0100c02e103071070003414042c20300c90800842d613040c1700c0c80c122441c1020489890350b555a0124401403070f07024800154526218401c2407010780b46c064003a68008545072a1241541a07120002d011011380c1404c0406c0741c0c800144440502130210340380f62040c104400300b0310192038603400003103e03c1a40700d50b00c81da00d00968045000404190408050015403000901c0459000c12030304001d5140780c0208030050317440d940080d0014160480d4180d034000c2d642d2410b1580d6885400080b12003c0c0b000082481c2c051012640c500d004110800d00c1c040c020340000f0310036980d90013103480c10418480d1000c2c0c1840e0281040301c030381080c1005007801d072100001007224a0f402070000e0040d100b042059000310300c40848915149003000d04a5891001204030070962221090070214001c54500680d0010750800b41c0c039500656066030440d00031900001c1d9000500c03a000d0046d1034012811090b80e552544840500001c00c5561084200800164031243c40500c0e08850071030808191403038 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 960655260 1250 960654010 960654017
    0xd0b01230f0c0105010f0e010f060503060609120d0509240316141306030c0e0307151b0f02090105030f0c090c1603120b04060b030f1e010602070302030607 68
    0x2540d40e804150003508284040c16510740c0d0760028210640a446000c0b41000740d5130a10000142c0260689040f9080700c155034039215190b62200707800c001d15001845030720000390092020940390b02c0d0090080688000c0200204e07500d215842c00c1c11b040c01c5042d80b0400105601060001c00360508032114010300b0a2419140f081c0c582d110f80781c2c0e000e4080a42480013403483c420170740910f140030b002c5290701181e054121a44038084200d004010408d035003c4d03040082cbc00c16030000c5500740503070030558200304018050683c0d5401c10380941c40d00d0100c95817210402c0340550f90340f14040d1403c201491203a000b920030081c2003e8a00610084544c1a40100e00951201c1c882c8000e110303010400303201c1700704216104101da03140d41440d00c065003c0d903101800800041d03080030f420950020401c010700d03044040c1c14444042800204410ac0b9644d104141c2040f10400c00245c0e0013441c04841e6500c00380e6400340100c0d10380c503102c000042c060243c002e0005648084401d105500e010412294040140d18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 960656510 1250 960655260 960655277
    0x31e0f0f0312060103090b040804140105041202041505040905030301091a0901030b040f14013303030305041712090f061012050a05010c0f110f0a08071b0303050d0b01 73
    0x1180c0c80e501d02c42c40c08010511882c0c03401141140c0e21a81200c0341003900556000d90f107091030705000c00c0c9a1310902c100141000f100285040c5035001c1c0d402c0d03800300c605400c05145c02512503002c0c000540914001594194071a440201c2c65564a2081600e4180a000119100d604041040085a42690044207200b80d045540303040d80d030b6401502419031341e12060025007038445150070803c03003001ca40000e011b00b038103030080f801945056125030555240c081c08105c14602407403842d610b40c1841a40d4035a400581482400400d0194000700d8019100d09104d500080172104040420b800810300101d085c07040405100d44040c0c10014250f050407034038060101414440191403040c0441e110f600110b00b17420514109002085c80a1516150004024040c0000c081c0300107049940740100b4401080d40c28041003418400050407400c00c0321910000d010b09a0980c03100e0600b074001880480c0c05c041c1510030851880741070007000c0c00a511030b48640d0348411002c41000180c1d008102c0c094100501038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 960657760 1250 960656510 960656533
    0xe0c2209150b2526071b050102031b210a09091b030e0f060702060106090609080d1b06150302040e0303040b060906010c020a1e0f0b07080a050702031e0f 67
    0x142921900c0b1807044900c01c01d2081e900c4c000a81442c50802400c1181100001c882298081001418014800e82080c2c544800710031607140b109006004481c0181c2c81071102c031190702030311501116080188012241c91140c40d19030310040c444d00a104140f07440c00411240c07066a005822000505854202480441c105400c038402043c46020440c081686072000c036001c003a000d01c02c245041c00e81c01c0546100d454080c0c4040d5695a080c40380000041d001e50000616034803450550090b01c061602801030f01001d1034045824a05260300c0105c500c0b01c884440000440500c511036190650360600400341c0e140d40100300c1190203018820140390020001c01001443c4e00c01072592085003110001d000781c0b24500120303000201004029040411003101080d0054420381ca0030314418691003401c0c2e070036101c0f02d010507407002c1c61007988100681400307030700e0009800002401c0341d91081d00d8030909011054001034649580204100070000705058010510301d02030248980e44415a001012141010b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 960659010 1250 960657760 960657787
    0x905060306090a15062105120a02070905060a0e0403020607080a061215020f07060204030213060e15061c1b02010203010b0412020a0329100e0c2209150b 67
    0x200300003401ca40d4080b00010b140c8540340e00c07041c041c001e880c40711000040c1c12000d610740707580c2030074017651f0b184501c044440b10302500f81c0c2100d01100266000d0501c842c9071040341009880d01070700c2503500240755a80841c1e130f60b841c807500c01d115074082d50050030b40741890b1002509410015200722441424810207000600020b0950b100d01075100180348910080031511600038001c080003035000c00070019080c402e110003600500b040c0d274001c80e1441542400703216000e04a4800c3c0c4104142a05028009558500301550b0034180c804054485031512818042d0000c00701100403101c55540d6841124184c0b1205a8880d40075141c0c2600003189594141440c7d02564000c40c464180c804282c1d6000c0b034110f4680300f8a0310000e40c0d020003861100d00d0682c2039807001d51009128401609004000205005191500102140e83c400300000b01a200d10003c41001e510011051031841303403440c000c1e6000e40e50406100e00500800f000007410300c10010304492802c45c55400740520703401c10300010300034414 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 960660260 1250 960659010 960659023
    0xe15010c030e010e120a110f210f0313030b1006020c0d08040f03030818030a140309010207050a0507051e130b030a0c0f0e060303030f041e0f0606090506030609 70
    0x801d0300b8a0209801d03404012a1100e0702c814145030410300300d43e0780b2a0118000a036800d401886920740310311400d02c0c1ba003400010448000d100360710144081062050f40b80180e804020600280180c4101484800a280c69907000000390b1084185001c0c0400900c05002001a000782c000a05205405d2400000a513113940c0c40c5446849441000600d82c100f00f0b615003100c1c014003107210b01c5210302d9641c1c280540310042c00c4401803400c64035401001410b03000030040720a2114103448004081801602165441e0002002c0c80c0d1a50b5080210b240403c2007000103484a901c07840003440e5141c00c000034460304a15007844141800d008960007903070341d0340d440102070b50000d01c07120010b14184100300282c50141e41140141c07881141440100e03641d101400014180c6110b6980c018898890005040c0d80740f0046441d4005404200041000184030341e02c510184509254404426000c0c0d4880300c42c0b08644040440300c159039042c0c01c0000591601507990b0040c8120041c103510b1400d81c0c01d4584410 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 960661510 1250 960660260 960660263
    0x90106110a0b07090315020c011d070b03070c202b0f08070b010e04060b0a030302250b0406210603050312250e011403060f090405010603050a08040e15010c 68
    0x80b40c1100084105202d00305090085400444010f200c000180d4808029405416038501650909030303411624200d000100c07407200d030407034003c000652a0003140320003500042c0c401401c11800e6200200820401c0b00394074502c3d4500300d0681910340c00081040040c0075180051a18081108000020b01c1068900082a69001a510205810b0300d1410421600c100b01008100e014400004034800e280d10382500c0c0304078440c141c00c100c0c0c6000350081054800e801d20000700103910200c6802140c2074022443c0b400400f0801d09491010340300e03071142c0804d03040f039005030000070003c085a5180305d0080d00402e0304141000000c000c00e6095848080c0c6a2142d40c0c2c00c8144008a98003240226050b44c603030120051407100140b40f103100c1d0440080c003004a10400c140010b40070b130341a400508100342140d0182500a0240384c00041220500080035402403094449543c0ca80700080450801c0c8010b030308441c85a0953355449040506944055501802c028200441441000031990b00042d5045226 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 960662760 1250 960661510 960661523
    0x105180c04020f070221060c12060f0a05122a060910090f0b070302100c05031b0c03030a2004061209051c09171c0e13020414090106110a 60
    0xe80400720f005038148140f4500035000141d07117030450040950002c0c10b511071100c12041d42d1580e207030182285000d0107807070954101703008800017180f030b1403800c02d01e0022100b0b0007070060440c86545100060013a00118912442030b04002e003010005e0b03d42026181c0110a2040082e0740410b9503000302d0f14074029021218040c0980c5000030380c04a01420a0340e00400b140400e03048416205d415076000c6401642084000d48200558070f15103201502954035900810340d101811341d034519400316803000c608001410f12181c200f046a2000700240015445014000c030080707009041d00c206030072008000c50307011100c3d040c2404140b00d8a540310000d4180c0241076400030a01003407a0070030a040030010203621600001d0400d034201900d403c03070712020842d6519013000316182c02d4081026111516070007109008030b8a60040b03c816405440307400010180946184030144072030f41000120b90203900030101040c081d100200d220b161000c0c60328090262807a21400e89042d6220483c1c3e980403a00000307081 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 960664010 1250 960662760 960662767
    0x402160b072c01030c03020a08190e07080a1727040e0d030b030c0d0201120504050f03040b090405060a053a0b011a040303050f0f0d020d020c0105180c0402 68
    0x24180704000414402902c0a252140300c00c0c203003420200310380d640b46620f001c00d050000d02501c00340a03109651419850740c48240c00c0342d036181ca04594a501e000d05450f401e50ba92103044481b18020071000c0c02800842004100a03482404e0100c01401a4041c007541f01600300300070b0682900c081900482c104c1f42d503880c28200e99601002030090f141c4043c662a0703038483c00711060701c4264540c0221174040780550030389072541c5411081c450840301c0500041d0226032054030310f0503000270a51046501c58080c406072055449480d00150039030b41700307038000302000c64049145140c070700d0244511600205e08840c0e0f030819900d0007001c140000410240780c0e01050b44640482d0009001d00b2450311060800e0440014418841c68146104a42070084101c54500400c0c4d4591105002003203c040d01c3d09030711041d04104241c050403030345501c1410030544131041071003000d00c0304140740050201010041c0000d40c031510100416801c6610080900c1e000031140091415500404a4810081c0c0740550740542c2c3c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 960665260 1250 960664010 960664021
    0x105161101060302090c031e1e0402060405100206160518010c060f060f09050a200310030f0f06140c09060705071d161706040504020d0f080c07050402160b 68
    0x10b000c00c0d8806508605260200403000e4003210080d03124901c00c168103041c41c10303804030940070414125201043c209039000d051100040701108160b0151008102c6c40c0b82a0310382002c03414801c0c05510610241e8060001e02c9181d801c0080e001003079460504d0b189040503095444405003d800b81400760512144010440a000c070729000031390541680c10060044580d0340951b101da0b07000c0b0388a403c0300c0038540307408180b0710304850064014800c0f0b14210000c02e80c001c1d0400301025840645182c0040d10014000000a0f805c5c0300c1d5913500c0c83c01503103107501038045410000c0580d80d0900f540342c045a20a420000300039010740545000c00c9060b100f254440443d80340161400130030707400c01242603401280f1680710300300c7e11000621071318070020b81c1349010060120959000d84480f4018082400100015000b810554801540140024652402c0904036100c0301c41402507d031065407900e50001e940d0011141c2000088001d0030140c0f021803400141104d280d000340725108000382034034800f401055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 960666510 1250 960665260 960665263
    0x130b0f1003020c070803030604060611120c0717010912031e020c2a03071211040213180c0e01020a081c1e020d0b04060510120216060506090901051611 66
    0x354100c55410841c1d02c0075445c1c1401982d290000c641d410310550400c800401e545115030001c6108000f1840181410060b08ad00843c26420143c0c5a80e0907220b01200000d418240044030080d491002000290001b81410b1940d10403908100d0034040c5400c00c036044803003200303001a0356110594a07a0040c0c071042110342c910709100b03040e041c2072420070340440740c41c00240c03041c64003a150f10703000c50495151139960710205404c0300b403000e0301401602c045003800465042a40041c46005c00e5809440000c540368500b0b0440c5c690301044040c1c5080d613032014034a02c0c0307400c407502140700e0000340020141b036131003075442140a00c00c58405d80c203005009808915141c0796a042030b080484480c0459841c0446006140e00a4002a01c2004414148400c2e483c003410107209240542e00050301d50803007807011000507a01c22030000702c00b1900d40e9080049040c621f440070743d0700e4402c504c201008602c41c101002000400d01c4050039102499240105002d01d00b4040c0550190648081c100080e03905008035919 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 960667760 1250 960666510 960666517
    0x12050d0f050f040b093318031e2a060c04080d230304030c060c0527130513060b030f030a1103040504090c0e131101030b0f060f03010302130b0f100302 66
    0x420445005446a142444188006d60810070054260b041c5641d4403031900111701c00c84422540c0d55003040250305851018004000384d9544d5400b400392905990b045507a0131035543d294100b242c14103900c0d4a9121010a000b00c0390480d02c0e00381c00c0f41c00c160800340307415101d40f4003009100500c420050386190310141d01c01d9140040d298185c0c260707140d141506016020540d21201201d9181c909602525200e000e40d081e038124140a010450581461102c0d0070388100d000d180555101d81e0b003821840400351240150b0f4403841d200800400c103405c3d02c0c54a5010b440714001410b10a0700032909202c120000001a125202c041d480d121501c5c00304110746604600c00c0340c206540041c20800e40105000f02103041e00c040f1116010360b2022690303207038035190350240803400080c02c40200082c509141d41c03081d0061102880d0040800d14004000e00c00551190701402c0c8403901003501000400c198900003a100c1d07214014420203220035100c10f4001280b5440542c00c841c8500c030b00d0036200718802d00c658140d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 960669010 1250 960667760 960667783
    0x1206030605090c01021510170f0106081006091a0418060903030501031205030603121c0204080607140c0a0303020d0e060406060f0f0e060609030a12050d0f050f040b09 73
    0x401107070419080c1a0340b10f00f1a80c4180b8058810781d21005c003074010000702c240c85100b02c0b52003101454100100b0b2041c0712600b50035020036118252130581c80a00030312807080140306038002010440d1481d40004169080b1b94042c92010746004142004120318251445031114202d80000c5c03501d582c17012202c414080040b011b030995140034082c404044d05a4007a5050300c0c06103034003021144580c2c8003150503100480e0b40a41640000409008075000c1c1c0002c5d0140c000080300442062040031118402c903082580030801c6584681c041c040481c2e006610403800348048080e42c0d240030322500810f5540d040507480141090350000d840d00726004c81d54405c150900c140c5050319201d007020f00f04a00544624050f07009052221803001070800410201d010484450074040700217941d03018204911030700262141030705130103080d103a24000381004e140da6082e91440e0f1501030b01c492900c403d00084410040340004420700d0f010511145070402c2011590017940142c604505940d01181c40c2c1c1850940d400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 960670260 1250 960669010 960669023
    0x81c0512010909051c05070308070e1206040b0705040b1e090909030c010506040c09050913080403080a09050a030308040b0a2a3c0c120806032a01120603 67
    0x3160b100019000450094041c004841251103481d130078200e6030300109036080c04140104400320000e230203070f95807540c400c040b0705080702c5107401100401c00c3c0d110101088205034002408000c200201008a603410006600d040741c20700341411224a01c5210382c031441c43c05030710030500403c1c0203c80c1c0d408607002c1c041c01030440c0140d403c0c00c15000d0368130340210805e41515420f0000041460034180b00d59950300b802c90b0340d650301c100d00d40401e221806001400446c1001e8207019003002144601740240000c40c4900c042903034600c07140d040140070a1254100601c94020460308002280d441403070180c1050300521042e01a4441da5682d038000c140148c0c41c2540300802000d207103070003000d051031003010400320b445404800304014802e0190040301c41c24140f0504000034800045aa82950034007005903d04000f40184019100c01d545044022440f00010f49014100710541c1024030a15614100d14040c00882600c001c0ca480400c1c81c0130000d0504210140f0600c2c00191317404d80004005581144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 960671510 1250 960670260 960670297
    0x60e1816060f0f0e010e1003020d090b16021f0507020c0429120304090c170a2007030801060f0c0b0a0203040c0e0c0a0507080c1c0810081c05 62
    0x120040c000900025440b004990300195440f15140910306542c1800016501c01290f04101003c109610728142112420598207204000306040c0d40c1c4110304031280103403446c00d11450006110402440111001130841d0046000000400810403d00141102c6000d01180d03d66072860201c1c548003041c0d409a42c041e0400c010100703188a60066000351001a10402600c0d903014810b02c17144200401c513030012607100f000200310451680c1d03c00380f80641c084c40c1c4080d142d0031001c0801d04d4081d042c1c0d05050415076509802c1c0201c012200606440140c0300c3d15035040240581703001d80414070512909061005465402c400d071880713403441d01724803940210300514a0901c101c1080094008640803600a110f801d00410b10880e2008450300c185c2c0c56503040c618109a80004407442c4d00840b90461b04040c040c4803c180d40d0400340f181e64604035102c681c840e00c0c0c2600c00002843c0c680c020f072841084840380c00c0c0521548001141302d81d1102a405400b0105a40e00300040784c00d403203803810081c800b03001c28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 960672760 1250 960671510 960671519
    0x11e0f08032d03190609181403130305070e16020307110f0301020f0c0c030712080d02040506070302100b0a060905010c050f030c0304090c05040e180a0b090d12060e1816 74
    0x6038001145020104e004000103030f251006101120361301305145854450b170640010000300e00210455015650000303a03070070050401c0690482d00f020340c0049645800444045c40015003c0a40720fa010b010407400b000107035810300010307450f482050700250030322510896040854407000101380d04004054000c56889541000b80c207448e4111854440c81030183c546c3c1035401e8a00080c600058035a00c2c804100720590340d0b510142c541c2c0c020405458802d80038000015107555400107811803d0081d005089501c0e2942c0020044034207040900344103003c0c1070400d2009a500a042101340c0d1400c0c24802d80c280e40750b05255103050401455801c1320706c40024601c05030032001c000b91040303401190080c40b08590851080e62540628001c0c0f1410000705030000d904444ac2203940f0b0302500c00c40d82503a12001964032407000b5644112640c2c40c8540c801031900809a0707008150381490301c10342c00d040080c6410100c0d0010405d0000e400c202c1152362001203281030800c1400b102401d140201e0305100304c907546 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 960674010 1250 960672760 960672781
    0x2010b010e3001090602071a100e01050f011b05160905011d0c071b180207020a0b03040206250b01060e03120a0c0b011e0f08032d03 58
    0x1998101030005000035052406070800b0142103020201c1c81e24151100e20142940800030359010041c0451503407905942000b081d0a880100f40350703070040081300020303182041441032a2001038200c40300c1d074021036420005400b0345103000c0d05460080315891568110140102c0b500c8860300d20050145c031451000d0341c100040043e0f040b40c0c00003c0c440c01000c40f580c90805004807a82445040c176840a5404503030f11040c2d2101030245e000510301821802c2550303e07103c441341803000244e80c240c6e0042060003840481c410f4210100441c45c4170005524000c3c643d80410b00c081c007540b00316025200003102240440d69004140c5002c00107420380c0c240d2101400b080c4140d40562583e00381d510580417400403c00500c10100c60b000c1d000702400071700f908426641a0566a03000c02048010010048094400220a010305600810070785840300602c8112550b141a001c4081e4041100220021401c00ca446404019911510403051500c5e654403881d16044c42410320314a001720b4030a00010070001d80d03094 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 960675260 1250 960674010 960674021
    0xa021302030f1b0d090212010e1605030706021c050f0307090303030b01050309060402010c02060408120d0f3305060316020705040c091e05040518100c12020c01060b0a0201 75
    0x80b21201c40155100e10344800030804804030300701c4514200b0080003291180c65040300200c45c1c0f0250451984039204050182140c218520451082c1c101c250000c00f001008012407000c0d060480c06404080d1400102035956441c04e0107084c540b5805e1001d0342c2000d4052020b4804806101600c15035030f141044d8002d0800b100b03400120f001c01d152411000640d4414003c1c1c0784547c00000080c0b9182c3c5070b980045d11505412a001c90340a0005c02c40421462801e001d0f01e4129140801c2483e216507a50156a0950303901205950480307160403580c07841c2d518820141512801c81d05d1591a08141c2080441100030490b00070030740180002040c407811100b441d0704280d0410b00ea60a80c1c3c0310a868904220640d5480124000000c5080300c0c2805200c1e030102c0030801252400c0410604e00b0395a4020405440003150310140300c55030361586c05031030001402280c0b8403140e0f81008014164080e070014004038200d001d4031120b82c1d408901c01c0c01d000c42c2503101c800601418200b254882c094040c0007400303000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 960676510 1250 960675260 960675271
    0x4030b010e0703050c070303051f080106031e0308011e0306061511010e12090301060e07050915090a031104150b03010503010b09060f0427050607080906070c030503090a02130203 78
    0x2101d100011501c078407920405016007000302c06130385450348944040b00540350207010002c84403c1060800c48c85201c000c03044000341740310030000c65560300d50b007040003841c1000200d018981c01104074480000e6400300030b0a041d04c040e2441502c1250840c6141c800c0440c26804c000c0410340780c20b80100b40003042080b01e24008046989101c44590082405420390300480d020300841d60100030750380344040c220070140c041d00801400000c0d0301580c0300114420f512003600d5007804108001002a06801d10701c411441c6d11081c0b003030752450001d011020034104001d40c440941408170340d24445416540350b800c54281d17160b81c0c1c1811001c080d1140c4c103005456000f842650710031341c45d203680c0301c045081c01d03e0b0540c440c0c0e10050490305030341001c00a0002824500301d1142c00084541e03041c41134501301c03201003081c00b03000714002c1003140b038200f8024040c000054890f6a05500240c01c1001c11a4001c5002c1d248691500e001a1a0346410590350701d85104510000c2d400604402c610001c106a81d0241d407152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 960677760 1250 960676510 960676529
    0x30b0a0f06060c02131d03040b0301061407050a020630010f05032802041d1f1b0c05070f090e060a0203040c030803062b0203010c0f05070311030f04030b01 68
    0x465072000142d40991031620020340010500a000c1c0071150310754440046c0115650203c0317039103961030504900b103a0058003c00d65030310303000c401071000c00d42c00504400030030824130b17520b45002a6a10782e035a0711030006100a2003500c1c002014242c880c021812884074500090309440b411944607001d81040909000e100c000442c0b13030000003041d16000074080e14103030001844503402012a84107400312201004241d030019203c03454034039a8800c96103181c04111842028120b019060f02501110781d43c26a5554075890826510b001403603114829600300401e81d061a802010701494407604042c1198050901da80e12500005105641a08002c1201005805803522a624494544202e02098134080c0043c840d41c2028000500400010b5402000041c2070391810f010701001d5000c0f111003104090349204c0400d05000460500b40201096030281d4145a00f1410050100070018000d800f005020001d402c0403085200307400740221450341c054141300c16aa00d0326420450110360081c403d0b0600c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 960679010 1250 960677760 960677771
    0x1091a090103121e0e041505061303030809030f03060d02010309060606181d06010f030e030715050709030206090103020901030b130c110c0a06050706140f06010f03090507031b030b0a0f 81
    0x800c4c5a114100c40f0072000764551804403400041408010405045480100f1000c4000440c6d65599278000e4014650713441c2a8042e09801c520307008020b030740081c02c0800141d000f800b03100c0c1e0340e021400c141e03a40984142d0311003114408900040713025207011a07021705510300e003090115015a00000a0a00b401c1d01c44201407010303542d1f0f2069080c84c069416404601220801095456128a50f1b0041d100c403103140c08119900720400716400d5511000e0200c0b0114040058020303035490314001c5641c4000706044c820102d03407640d00480c80c244220b08200341019030028005180c1c0c1e001c0c0d03001c842c6051001d0000c041100f80030164100504582c051b03030010401d4695001121b1800050b21003040360050709012610f813510509940e103802a0108642c2c1c0e586032041c2c074200042c0c3d95500c61040d0104000c0401a041c14000580711a950301003032003c242c00c140d40c0700c01294002403132104480e1301c14034142c5680d1071000003860303865135904000c1c11000072005104a075011a046000900c0616104203c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 960680260 1250 960679010 960679037
    0x180f140c0a05181e090604031706010c0b1e0a050402030c100c03120f0203070207151407120309020d060b031506011d060c071e170601091a09010312 65
    0x1224809803142070b9104000601101d1101a80d42d20f20390071849449581c49040600392100311400e0044400d2161940460304000600d40d001800000500503d241407031a801c00c4000207000601183c0c011704103d49540101c1c080341144240341010030390116482c55a41030027905a80640b406603010303882441b808140c400c0901c1e1441d44400da605e0a51a5103002d400b09a0b016940400041c04038441155203c407400320418a6000443c402c00a41c0e02074180f081c20040414401d007032141d504410020722008030031010038910104e4840b43e410120044800c1040642200030389118907009401c0880524014100907550b08541c446060490503502d8035064001c2c4400e1401c2e04503102c5000410740349a5001c4094075100082000001034041880c028242024a04c0c103030b5554004605112482c003503000c034050360f0043c20081c0c40d035021140070b5000c081d45550750300c02041c040d685160b5510340c81040c038251382c041c00400400018000355090343e507a003072060464401030205804943c0c070642d107e0707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 960681510 1250 960680260 960680269
    0x70b04021509030a0605090c09070c02040e01060b0703030f020f0a09030b060108071b02180702070e01050a03080a050a05040513060801050901112a06090f1c02030a03180f140c 77
    0xc1c541440600100003204d042d4941101410700a88010040e02410440001030780708c82113800d108046075114800d004040f44140421203400c01420112a45421418004d4041280031a041c07150189004140144609002c1000707100d400d645464039680040c2c586030440d0000c90040c2203034013a01810403250703600030056507404822120710000542d03000030351b4a10b00e0f0200302c0700700c0180040c00d2038050384500310200314500d1050b1a064051f900c002410400c0c010384441d400d0141005513807042040d413551381da4075440d0140840c1e1005001c0e011038026101407103881070314002e010080580002e0340e0b0070701103180102100c2c011902c865003440700050b15600140161405019406c1341c0501d06031810350344a00742d505400c0c034404108510102180c184204110582c0a00050070103011690301c1a804e041c60030403180320584011a0360f81900800700c0d008001d4500004043c140400c080441100f60b0b00604440e54004240c0389682345001c00b44050642c02d14441c00e4400e04449000f42aa410803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 960682760 1250 960681510 960681517
    0x14070f1706130902040c08190b0603040b18010222091e0b060d0e0102030a1b0c060f0209041401060212090d1119140a090c02030315010212070b040215 66
    0x1500349854040c04121181402c611407a0b10002803140050f03450764681c00501919401a60400041d00e0f40e024403800c01c0343c480f00000c0e5401110000c10820600c1e0020501601004002178515814140000c9a8004541603128041101402199150030b81146039200800c890036186c05501010310120303882070b0078880e10310f4040e1081c000801e40c0986203005006130401c5114180c00c03080c00d014078105420385024081c050580c070800940c1700e103061103a04080794000000700100040036104943c01a0f08980000700302c940103c4007250201c90a50078201a104400c140c03038101d450314121500041d2005601c9068481d69402c0c2c4407400100f00480b04076002e4001455804603007695a1000030314800392000c8881c3c0060102c50900101d5121940b03281005e80c03101400542e4045101014074054103d5030207004864820060481c1446000f9031b240030003030000300246140b40010025078000c00c481180e0011040e0b45e1075462029151404032008191030032070240c01e001180f801142c12101c141c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 960684010 1250 960682760 960682787
    0xf03031605090918010b06070303051b040302090c0310210c091a041a0d05031c0203040f110d020303040b04061206030b0403050313080a080f13030915090914070f 71
    0x6201180c44e11041c2c40e10180c1e2022940c02d6640d42c030440b0462544410000d89511400381d1000500c80c902444103020040e481034050343c145104100501c01039603001c900c2904007036040010354490341c0b220b0101800102c00c6d04084441252040442007030040d01040c02c08851141c060081404e503510304000a85460120919200c2c8601c02480c08908055100406040d0382e01d03a4138100d076100002007005041503032820b981e25040082d580504036124100807140e0050100114558601500d0380e1400b10098100100b1401c00704460100580d40c064403d084980c00030305581d42ea50b0703503000d010b0040e8041c1c03184c100410241164601482c0c054030440d01141e4000d46001d020b80c0e20b954003114554002400710403206084800c603404248018064590380d0502c3d03ca40420703041130564501d200130000e0515840111070252400040d605c040041c00300c400070310300700c0b05006100101340c03004502d60f0008030425152400300390415040c00c02840c082c12150300d031510048040d0741c2c1200d0ba42c214510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 960685260 1250 960684010 960684019
    0x309210a02010c110d030e0c0a141e0906090c091302030105151315110d170f15040b030f1005180703031b02010c0501020d05011e030b0c0f07050f0303160509 69
    0x10f07507081715401b9810048000d050780056522050404c40054010500c580005d540c40e4500d10100450b400c00388809101e400702510a200726510b60350005600040007002503008252000110b1000584842592681100144001c00a07610102010003c2d0000d2007954070880d809001d0018950fa1070088505070507042001440b00ca00f807000d610300070811031040f44100116088051000c150600c0031140a64076981d89455458074403c02007a4640041c04040c103d074103d400784060502c07225040e0764180e401751000b00d030a0b0445030001e814100d0016209580d8003959483e50040c0e842984418451881e81d081c8100d0306e4400b641040d550000b500004010509820007500da0080e030000c004c4085105240c035085a040f40d0351110300b681c00c8424140042a00c032401071100032000c8a0748200d1000e51842c0d000340614680390901c0d4100090504550500002a58121814004c084403d60368000c41119241c0611080c4961390340e0084502c4601c0028411107480201d1003a0212046ca210080 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 960686510 1250 960685260 960685273
    0x31b01050a0623010e06030109061401050a1731020301060603050402060a031a04140f070201020915070804051005180109050a03241b11031e0309210a02010c11 70
    0x20f140303034401e101e428055043c0004450030013582e075031300f0700114064100604c0c08510a844e00340001e0024400d0712010341400003e02c4034100295000c0c88440ca0505248203d02164548030942c0d0481c01140c0360301c140e03100080202d00c100d60700c00041084800c2c400d4000304882d0b0340d03e0404030f08440041e41c4c020346c040000c106000c2e049129420201203492607013076900245524800240c12a80340c40d44512242641c0020061428540d003801c1c4c2d484a403038002507150403108400161000b0300310300240407900011513081c0c1884460070035a0094800580460381203010003401800c15084034082e00c801c6480092a402a540310781a1202100c0c4040c00c4143c0d014116034540c40c102c0b1001c40c5480c807031070000042941b005600e000c0c08818a8110a42402c81c880401e401400702040020b00c3e4001c0e4410802240c501c0c03903880700c00030b0750310082030856100c0d15214001420880a400c0e40e240c8044203100c20030300301881500420007410715070020422140055015201130100003a4807001c5c1d000349 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 960687760 1250 960686510 960686549
    0xa0201152907151e1a0108010b0f07060e0f070f0e0601030c0302132c040c060f021203070e09011e05040c030e0106030803060907080f0403050d0e031b01050a06 70
    0x1e0000d422814800d460b002d01c1a8910440c00003102c40684205003c000c1100075030502c41c40c0307840740e040b0004109282107500c07110030001802c011410b1080030020b07100005c030201140c0c0c00b14141c4403540d510020500c480c50030464440c1d5541d8030180d540c076441c05180000aa0209881c6510084540008203002c3c180c2d141c0005400400040f52801705054003040283d0903001c44040610141c200c003040d06400c45108542c0729021810010f504180720040800c0c800803a245a80e40d0080380c0d490b18010b01c2d0154100003c81c20013640180350303028802e0210030f02c000b40e6000200c01410b12000d0343c42030303050380e44c92480c1d4014100003400010103020064043c00075050030341200e1074030101400c000c24080c4094500c00e084810952069030f4499001c4144801072070038000103500301840c0c0c039001e43c141c1011800070a501d50050001410321070700250103100c02d0383e55086031641c41d041006803529004441d41c021070160a030107800d4119403a00300010b80801d0684148c07419600e02072070750b450346c0c29403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 960689010 1250 960687760 960687839
    0xa1203030f020906070f05070b0f120c040b072d0222060b041202030d0504050a0e04030210050a0f0e0f07050d0203030904020f071a0c0904020a090b0a020115 69
    0x140c007504164081100c2072403a12038900800307000388151031520b01c108035824020b0030700301030f40c101c0c42c0301038420007022811310741c0241580c044a1584001b0032482d02d0b00003a04503140700315442185c540c0380c0421500309100007911075090001042084040500350b85d0801c0d244070402c0700c0001d500a24010088508524450355a01c10811680002407840d45500092000d0b402c11340c03112412002041c03d0743c086003070600070b204400001d0300340b20341450300382000950b10381101d00540340c11882210025082c107108104c1240302041d141e00403c0903040020031440501120000c40805504080700300800410000b442c11141c00d103903002c1d1030b205007840100300c3d000b81c1480b0140e030700d4070041c0a0421750380d0b2503100030410740c10030849081e80c0388643e1034042c4101118001032960b82c0440e004000c0049812000c4644101c0c0c1200c0059131100240310a0703a0000c0c0755000382034241d0700412050000ca40550083d00060280c1d003609642035a40c00700d2841c00b014140c2019280b0101c1c44e45103106192 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 960690260 1250 960689010 960689021
    0x50f0c07030c08030d060b031b0706090c0608180a051e10020c030a1d03030a1121130819470a050f1602070503030d15050a120303 57
    0x10024152403003156203403284400040346400604403074000040320410213250384601c0c0e004164000030a03044d4548103214047c0c1d443c0701c00c205070080304005012001c00500303a1101d03904e00d50042143c82ca0701d46591009011040440d20a2403c5e524000c0c0d44011040c0014464801a4440e004161000c02126149000691001030145074800c41210101e03424070350014003005052140110703252441c40c1c000602c00a00d0340b40107080e60144070440c0145840200440d00095140d0a100d1134603884092034600d0110b01c0d115400445501040114401d503000d001008054020b025111b505500d82c0c14041c0c96107480001840c04e00b04141c0b00600145103487c802d203250314003000c0c0070955076134451f140e09010130f00031000c1c500007148031299007003200e801071158104c0c04000e410015850005039855500501801c8181c0001c907844021612030300c02c000d80c502070103000c0c0c240d9440b401c92148503005030640c2d0005400100201c100800c0f142000c82880c01120580c40d14a0580c240c81c0d00c00782c00402 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 960691510 1250 960690260 960690277
    0x70c05100504050a3308040f21030504030e030f060f0402270124020c12010609061d070806030706030903030f0e0f06150604051306121209080706050f 66
    0x280070010340c2d81c0d2003140d0340006240c0f08803c002e4407a8000d6060360445005d542a8099000318070380901050340c40052070345d10503030008460b5040c100f1030400400c88e190440403090040075000f4a071514a601d9004a4001d9100b03859512400a2030020076480e004400300c400c80e0b55100c1030002c1c2c1c5a142400704150850700162143c15a0b00d480c00c0303802d0488550025610350a40600010418010040800100c2110f080d0b080c2c42403010800d80291510200c4201c2c2e0b02c2000d08103070700c210b0315100f03502250040c9105481080400c2c0d46141441c00009000041e100e008000400200c07100d00071040c580c820300c001400f80404c0c0d82451015802801c07040d0003178041580c5c4610428000070301c0d1040305480f0081714002e2100080c41d100e01c3d850504018030710895125920400742032602d0710415201030300c0f0100c410078007d041280702c030700062413103a1243d0b05000c1824100c900380404091140010042c1c0da80c0c8074501038480040355980c1c5030301d1068500042c0100040581003d00350064880217 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 960692760 1250 960691510 960691517
    0xc06021b0418020d3909051009020a0e03030409060515040503071a0c060f2e0506070206070c03110307060203032205010b1206090c0109120b2e0501090803070c0510 72
    0x762400c2442c00305c4183d110000b03441442e20380d0860303510250300030246402807003401c20603c43d82c03074120610401a4410312802d55141d401141c5c00308007500400c0407031a40c6102071b0490343c4a0360396490400180c17071903104040c050201551401d00780c4503200201c4040d100003034000d10700d042c40c290259104007008818140e4405050002c2c1001c58402d00c04903000702c111480301d000c5400c2010049610070b45172160b20582c148111015446164014075000450314115442910350b043d9001082541c8030b4450001d00c0704034551804010003005c101c0307040c0f9040060301110245500c0742d00c1aa0303240b00079969108407500c4000410303442144030b00402d5001d0303c0ba1001043c01c0c01c0e528040b40c0680440c0500d1001e9070400010000444801c0080c500c004500f40381101c0038a1800c040c0f8101c1c2c01251a000c0c0084150900154108040c149003d0011080c1051054000c4601c0c0e070a241090190140d580014140d01d000101da40c40081a40c901d2504140450340c07562804041103a6901850b0035001032 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 960694010 1250 960692760 960692783
    0x30305031012050606011202090a050909010f0501080307050d021209090402060f07030c12090f091d06181209132c03090a0602070b031807030c06021b0418020d 70
    0x403a00360155a503181403041001300300d82c0c2440c41c00501010901c101e044c4400b8814003501c042652020403101c105d51b01554403030b110f40c4072502d469002d010f55201c440013107405d000000400500000041c00d80354054000c0d41c49241c1c0c1160101d8641801c203140c2188544144495800da190030440a43c02130700c010800b41c40c00100555190032900030b1101034000c1360b007200c03502060001460303420320003440c94a040341d07101d801c00c40c1c4084281c04500452071100d03a0741900c11098800e109900325440020400c13074810b032030008460040700302c42040d15030084c010702104100510402058a01003c0010303c074840c1d2015403440701c1e0040c0000c0400d0100103c80c1c03036040c00240100d040040b2080034040265070b5a101580502c00b0b4070517075503c018210346c000c1604014081d019819203410400d0391400b40080e040ba01c020528180300da803c041c007407070620200000e42d2900095507009281c00005032402d1454034004120444094031f01c40001c500800c1ca43c80e005160102d65400801d11a000b01d020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 960695260 1250 960694010 960694019
    0x207060504031805151e091206010303110105070c080903070530191509080a0804030824101803050c090901090c1a0d140a110708040303050310 63
    0x40e5002514280e0200c0c900003d106200071940940c0c001400c0161054001c0b07440d505c0c80c5140741d10581150400e89440140c081880201060889080c05402051002420b40b421903081d00c4a00c01c0c0310450225080c0300d00103001000600400748200d40603210301d12421029114620b240e44491211a454020400c000c03607299289001c41100d00d4502400c00c4550301d042d0781210003911488441082c5502071481c44805460070841e0414aa500c403038010000710341003041c2c1c030141283c104000c05030741d40032881d54201c5501c011510311840c041e642e010b007181c982e050a1005540d4601611511014458022626041c40c00f5004c09510300e91808035110020564004c03c03580b005d40040b03c158108028004031468030b13000850f040003c40c00200040c600c5a959000c000c40d0390301c00c03040d0b2407100b074156400da210102c05641c4c1402040c041840b1a2180c0701d65030000000480d100414640341800040ea2424000c099072203048d0722400151a0504580381944d207500018a2182c2c082c000140108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 960696510 1250 960695260 960695273
    0x10c05010e0607020d020a0f06090c030506130605070c1226011806050102070b220302120d08180703110406030c0611010b0409051c050c010c1106010618090c030207 72
    0x98002800c0050b2075142441c06000742007070070b403601d0042154442c000740d2020a40b9020740b621142d5000c0307030001d104030b503920b0020440d41c01540043c00c2c40c000c00041100d560008240443d13138603c00c0d9070400440d5120342043d036507005424405441d001c940344000201c2130103180ba006410072240a08010910240701388103041100340c020f40d4540e03401e800724074000c01c1c1601610001c0c10090015046180c1021912401c0f8090740f054541404500e4080318a0b800da104100005960040c040b0294100200510390350f4172109035106000800703083c00100f03401c02070f03405642a034075820040d00c081c4d4555103406a0040090342d101c0d42c00381d40d07101e001000682040b510f40c010320040e01d0b11100035043c2d003076107800c49501030b540c940902d00380542b013030008030045141064807104609001f4030f00c000303080481d10ba005803a9400265860160103110716508040c40f10400e001d0b01e0101c3d04141c0c0c0328101122403900b00c418070313404498019020f014488143e000140038072201e15005081c00e80b5a00c03940c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 960697760 1250 960696510 960696521
    0x9060a0b030f0c1905091504050d20091510030209010219061b0807080f01140405100308130305010b030a053004030309050f1e010e0409060e060118050103020d11010c0501 75
    0x8000c1a0005680c8150f410103140e2202204808038903181009c0c582000304080c0003141c00010003410741140d090091610103070303a0040f4034402420701c0790f16140c0700c001240f0780c58800580900c0703040d0030045400780c240b06e03008036070382203a045e4040c3c12121004280c181c071416107120100c3d03000da1545003448094407001060080c1100a6403040303030341e04081c40007800003c00503000084010721240180f1214007004e030184800801030300c2c00580b50b610442c010150b5072064000501e103c0d000181a50b1140c402800b1a040d40d004500070009203064204159643e0360030f50000b82190083c003080411082841ca20802c0360511104610b008105004001d40c01da025400860201d001110240003c0c18a0340411211840c140d5200300280800308c2c200b40c05c04000c105c000d04000d484c0c82c142d40310303031074580041502603030000f406d0025a204500a640b2042c4c05d0241d620081d80a40303c0c050803071010300a007412a500a0030500b40750041d516030402c01804020064180320390142c40c0e00015000b44290b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 960699010 1250 960697760 960697807
    0x70b18130209011b0506012601090602040609080334060f050f0903030403090b0c0309030109050c03160b09011b140c010f02010908030c0a03060f030503040509060a0b030f0c 76
    0x6a90b210200c0c000741c0400d040d4060040c01355402c0c10000300207500010500c0c15548105c844014210040c000141032426625a0308a40d50070b1a09106c00c100e10b58001d0b00c1540d415031565450b02d61665801c540c0d074000d020000820b05100306105141905149000703855540030003c503110b12001d41c48800a952035000c0103888160f8403c204000d140713020540d1504035004902540c50350a0544005108001c140952184990001040240410200f080b1205c002010b0000e00914615040650f2901c0100d400240a801400c1201a0350313046140050107840804282c941862441001100c9030800c0441c03181ca02c000882c0c00c0d07000b00d0121a00c12a21585220041c007510304031a000411598403039041c00196814a00038000007080001907984c85801246103944400b00c61100f02c01414096000300190080c0d007c0c04000c0c464084010300c1519415a000c014035120402070003480d442c14419044039030707020300200c0c071042100c08036680c2003030030b20301d00900b041100900a034548508081 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 960700260 1250 960699010 960699049
    0xc0a030c0e01140105180f100201050a0606080907060c06060b0304080306280e0c070f03200721020109081b01030f0c0c020d06021c06140406030203070b18 68
    0x2400c00018003041e01060140850360300b0181903000e208006421401050b08107460500401e004c180c2545801950802405000f410100c1381d101c00d80000e4000e003c2603910400007030911501049482c06842554000e080c034000030422a4a014002c4800291158044414546400000980741192400345000b6070280c61901c0d524202002080001490050200e030b09441c0d100e00c001030244a03003000c2d01201c460f01181c07200d07a40d4004103028a8032401c14000d100030700700340c004010b0650203400405c1c0008200d02150010710032001c419070707820281c895010901c2503400d1085450b81c0d0400040109032060409170203507a2500981410141d040e07107911585180b1900341c80340c540c0d01d80548850b050650b401004410400381c0010000048500003a0055600412038020011164126085c0d1020bca04c88505030400c05070a0001d8503041c45904902c1c60b2600354025140740611561080729401801044c0e02454564a14850381000003441c02c007840013901680035445d13211561070f40855440d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 960701510 1250 960700260 960700283
    0x1a0c130b0415090302010824060f070515060916050c100209010207061b081c020703020d08060405092a0d080915071101051c0905100509030c030306060c0c0a03 70
    0x1148030300c401410b112103900f00071001104102503604000c00a070009551440c40c032480c20040c4a403071248101044083c1c01080004d0030702c80d84450880500304c2d0501c18802e4071480311180d00c403e1060351058420580c02031f0b140000c5102501003c500f040301d14010309285082104a181003170070a82404c00c80e010341030700000c02c070143e981d061021202800c1c49080c04903511550380e00c444206000d04070020312001000a0508030030b044492a40148054484203550f101d0940c5002512140e203d42c0c1c01012840820100310f1034034140c041c03144070354034280007032481c85190106810b03200400101d0105402c5284940242922080d5082c420030b4040c905950b81d5000382d1051011045410401611a401c1071002200007500c031066803584030b0092a20540310000004580d4070710301c80040143c0928540b10b005020040045620100680203850410059803545503880c0caa00c41d146801d84503400400001d407145c40d01202a0820054220031660341c01c0c04240418510300c06500252800340384074 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 960702760 1250 960701510 960701519
    0x30307050d0b0919180f0605041a01090e060f04030c060c05091302250209070503150429010302032a0c06010e04200906010c02041e020d15031a0c130b04 67
    0x1400b17541d550411200c0800070300d08058440c0011b0110340346000303000030303201c001107020300880325290031803144200000b01c0556076400d0340c000200100a003800300c40c021800081ca8403507803900e42c00d202c1d075090303120f21800300096942d200080141c00d1080080c04000e000c1c000c00b076206c40059040b50302100500590b5004481d07425408800100c81050400f811540e500e4016250b5a210641040b440c3c203000e0b440e0b45400e140301140c04a0b5945036a0094a8260041d15515003401e07a800d03422250f441c4400c200300b04500450607880205c0b0300c01461400303d0b510121039901c100104062702003602c2c8040c01c0c0300311284070904210303003a0f002003004881c1605110903c01e54044161078110b802900c0014980d40e10f0101d0181c68006002505000c1959946025902ca9402c10301d0900d04255140f00300250079040303640250008107801c09198a0541c0b08131850100e861950150380e0004640440704c80711115007100711030f0040c1b405008a80510861900c904881a102d001e04515883c0548a9003030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 960704010 1250 960702760 960702811
    0x12030210050c0a090803340206270108240102011407020a050609151501051c02131712070515070c060c05090108013014010b12030307050d0b09 63
    0x5a170040a81604104200c9010600031100214540b0072104c2629103030080d1072039944001240380c0080c0d000040021001038000e60350980c0c0d40c01c150f0704c1e51300365041c803411030045890040c1280da084810501c4039a014a1038110120703e01250710500c00441c011402141d200003110080e5101400350b400b00c0a44001c0010a2281a1744030503094014451110303411290214640060405c40241d46103008080756648144115501c15140021000ca001d480c024654025801800c407400700c03140c0348601041000c50000080a282c01c03200080c11903182022018110394007000045030203114000714154104d021083c913920a94460304d514044c9595030030a1810303a07418990100070010100f04e44090b580e000740031181900c42c00303031562440001c0307824840001d0100002c14002e00403150000c00401084140003200f140b40071000b40003010380741e014008204465000003e0682007800025540c41c4a400600841c029494001c10661019400b08610303035000d03a00941501a0007500d090784000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 960705260 1250 960704010 960704027
    0xc0a030b09010b19090e0f030a0315080d0f080105040b03030d050c07020d030302030406050f010806040323040f090608071203050d18060b03150907290a0207210b0112030210050c0a 79
    0x106d000c0600000301c4e0700300701581c80f845003802410a055581c18184c3c2421040000140500707165411079414619031880588000340722112200050909000451076082c94040c007072006002070020340c100003c0241003000391400030b0111424520034894080584d40d509803036048107000c5e440060342ca00b01410030a0903280c0041650301d00716803190040000e8100010241c0c2c0c4580c05182c800e501201400322140312840100f2801c80a413804500498001e141c2e103154800c40d0082007080105035030700c2d114251145060710880702d07200103601104000c20700600003000901c425800014004240000783c501d8440900d1b0b058683c140c0d5080c2c9010541000c1040c03520704021000381c07603410718040d0203c513a038081c5409500302503082405402000c5203d80300c0e1080c44400d03062513945401050a009640f018a44104028146030000c000c030364010894009640c10b4005000304040da0130310441d0449031000c45421401c602c00c03000061104400d40c0325041c06a000c0c5c0d600141e0303c90082e680181f4541 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 960706510 1250 960705260 960705281
    0x10030b04181a1e2806140a050307060906080a0f0612031d0a050418020d03051e2719061d0604080c09090f070f170c0a030b09010b1909 59
    0x30500c0105100c0f507080c0b2010141d009007132400c0c0c10208010060007006a00244c0d034003080d1a41841000305190711540c0d0780d440000c1081c0e8a503002195a1030406546482901ca25404520001d1040c04000c1c403c000e035507404503003030360081070584050b00f40b841115020342c000c0c80100c41d500d00c000e0406500120b43d0900d23782100340030751241031010000d41a4291031040c1c500c5290785460750701e00882410482c0c40c10640041015041250034107000d00350ba4403082441125155007c54064844403d50a4610302c407590070080c04000c4d030168041c6021900c0a121942c0000c1c2c000d01407045200300303d2481d003e006250344002404904040c48000440700004607441180c043c8001d00080d58001990f00745100304861404080d2030700c503001d40c28110340c03801c42c4406000319480804c0388400b0190007001c0b115801c105882e21b01503004101d845a481044045c0d02c0030440d4420004901c02d1010150810030307080002446160b40f0340001c04000c6624910006910603d404006603a0184079503080c00c1c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 960707760 1250 960706510 960706531
    0x20105240a050118030602070b06030c010801030323040b0d0f0605040c0e040f0908040902031017190305160f050c030606060d1a150c060601050910030b04181a 70
    0x1012404006640068a07020b141d040180101001d9041a15640303c02c00a540200c070855071200b01c2d0a184a040e04112071490082c0f150000141195221348a00c43c1240e80503500d02e4804084811541c10328076132040e124992507002c1c8401b10f1002d000390010020083d60500000d05250400c0311070050780c02541c450b6100c3d603d411105c0354001d4200c0c808441001040b240003070080e400806207002800c404001502c2e2500209001c22507210315402140148098594140d003d50786400c5100c40e00c01c0344c42e05400035041021000c90010385071301c50103034107072090408505000e00f80741440000001e00100b9680030300210160f1050020501c14a0101c0c6c03003e50142c0701d580307004030106000e40300c0c1c407242500080c1e54a1500d0800004205040885140203002520400040702049890740003411501c1c40d42c003614002c12103660080d0204c1d80d135807102604038081031140c5c5030264010040001160741007070322180b00c4560100403510200d40188104003050103605903e000004080c0024210140c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 960709010 1250 960707760 960707821
    0x601090e042a2409140423040807140a110603090a060c0c140111070201050c0309090a0902090a060503190c0510080916050a0513091401020c0d0302160f031e020105 72
    0x45c0003115948841540c400d450110720380d101d001200d4840d208107541a003503038034817038184410000e40100402d0018002c0f42c46100c10f801500703000e5220703034414400a251541440c4182c503d070500401842d40000d298040c0d540480e51038480200740c64401150b000000c40c200c5404081114907031001c107200d0b001200070000381c0700803c858051480781d0300c000790600c50086072002a14404000300c6108503c06000400c0504000c440c81f000781c400807c3c00ca1041089100054420070603203d120110b0b04014020f210810034001d14014a00c03903035000751084003100301b0204107030301c5105054405c400a907a65407100d00d41a2083c42c1030003a00c55101c84a5046176204201a030b95002ca55001e566007240e0402841507002c0d9041c0052007000402030456200d10b00c0105c0d511019030180c00d41e031004c141595195a1404000c4080344103d0608081201c80314081c0408a10210452041c05c3e04c03d0901c001c0e50b121140d103003100140c2e4842e8200051b0b440f03004002e90103440940048a40f0350304240c403402e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 960710260 1250 960709010 960709019
    0xa0b0301111e0c1f0914030702090604050c0c01110a08092e06080d0f0f09050109090b0102010e030706050411270c0f0409020904050601090e042a2409 66
    0x310418a0b500d451080002c00d9404905070180f1800c400411038000200c04404080a0040030301000301d8169030344081c004030000c4c2d01c140030003100c0559a004000001d40c2c0e13940c200f008000d201c0a0012072070000148801c420140c1d0034401c00c80a0115010707030507103c204007032004081110041c0b00d078640d03400102009001240a603005032184850b002d010568900c02c008000042c0100e038002c9005100e09040616000e030000f01d0030410f4050382d640c241111468160075644420140720350fa0004010400030400000581d02075119114144008114034609000003490754120072000d48441d42e8072414081040b500543c1a080180309680743d00322050722000380ea800098006c2c04402241000c00000c010000c568215806a1141c50343c09031115258100d410007900814002406030380b07032102141e02503004007408012112103404800f1030350344681d1110448542102ca4078075402d00040c0466900d4800300b00c0e040a4010b00241243e548d0880200545c411401c2a01a0502400e84014032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 960711510 1250 960710260 960710287
    0x151d0a0305030d0b060d110c0f07050a06050d02070203070b1b010603030f030c0908060a02040306050a0501150f2609010c180501030c05120403020309150c0309090712050a0b030111 79
    0x40c0d0711043d0070780002d03c408640000c40c145124010031441c00030b00e0031201c2805d007410f040160030300444c110103c0d07000310039415101e955200f85005040d400401c415040003264443c00040083e1b103610381c409810015640e001c6450000c00b44c00405000c4004501710721104981c00100583e0540d5900a004241c59a00d0180a6544e0402e0700d6042540b600030106207507005440350802003619070116402864070f1000c3e80000c0d0041e0001300c40c228107081c0481d03441680c50141a05840128043d2020754008003802ea880d00d041c103841400740042c02d01018a00040076100e1080504c0201034810a4603048102c02e007120400c3d5200b209201c0a00304240e0260021190700059520031308000540c400013a03010b98103405220b844600da4070901041100301540400a00101002686c06818445041c03038085030b503005541082e40150700511034000945440c4440c3c1350803c60720304144008524080c03007802600e6040700c0c0f1800003911645104005e0074240300d408507500d051004d8900300540c07442c80c01c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 960712760 1250 960711510 960711517
    0xc0611151e0c091203213c0702070e0a09150b061b07080706020718020a030b1e271303020f03070302012018010f0306151d0a030503 58
    0x189944400d000034107040b48640440340310f048014103a810400c07600c0d6400f81c0d81e5000c4110442c010a12010100e11350000c100064000c17440906003c41340c100c000b0700681c801c0c07810001a54400541c080340403000008001e4140100c0555006e1b118090400c1102a240031029104070328040c9410728410104810075841510f41c1d10902c0c000c0b62501103000020094002c030b2401c0c1d13813102d03400d904100c0141000502407040300c1a0400355050700e030b510441079844260511418a001e0504024504810140e030300030012250a400d00242d0711f0310080215615241c94404e4100001c1100f10299441c5400640d5820120389414882550048600342e103c00c104060070409c03144614003905002c060081c40f500d201d850a4030300704c94842c0c84a05000f4081d200b40c56414403003e0b8100e01140364186681d04540c140e686108085404c00070340d1004640c65144002c5040415035503080104d1481c545010303000b01840f8580d14062030112032043c1f1241d81803d020064410600d2850420000302c012055 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 960714010 1250 960712760 960712801
    0xf05030f06040e0c03010f0905070f0806183f0c031c090602190e040b0f0127090b041a0306040b04031107060c1509200a030c061115 58
    0x1c58007040c0b90a4062070036568114440c1c0c0b46d400c01c000340e22080301d00d134481c94003e0700400485118a5036061801002d80660007101c0450300000005020300c2442c1c0d10041c01018140103c1c5d0000c046203140140d4003071102e8041c643c2d02980300044800780d20507900003150451010400307240c26400021aa560306c0344e08101002030303480e200c80d1a01c01c502c95025100058001c90305540e5400b428958100241305101500c3c04030b02c80310100b4141c0d0a02d8490401d5883c800784c018100e491070100155280d410304030120315440d84114a10400b091000e2403000100304405002c210130030304404010950304600307c8030010405002c825600c80e034000903110740040d044120810951140e08003204c44030040040e003c81403003035013400500590302406200c4038902460740b05c21076190035120302c0c7c250b4225550281c1040e44022801c4640c9030720302101c10715980700910800240e5540d030307510180d0550b00e034051408580642403030035803020280240307410305107070304c200c1541380c5030034600980445211146e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 960715260 1250 960714010 960714019
    0x14060102010c1d121f020721080a02070f0f030801051e03100e0f070b0702010905040509060402090a0b0910060810030503180f04020d0c0e1e0d0c170a02010f05030f06 73
    0x80041c1d00c0d090a0283c2040d8a2145914522054030000703540701a40c80080e080340d0420825003c04d112041d54032194041c04200d0b5951b0403192112b00340c0070040e412aa400ba030b11401e91084580009001c8600c0a6403984a0b45480001d90b01d40400c10141e80600d80230000c0c11103d0b03048411142d68080b90840301d50943c41800a840001440d00b1441c044c0340c80d2120055114241020408144560241030414801d03651004140d44403001e02061b070390b081c0d80c1200075a00c2003000c5401441c0640c1000e5105480940000b02d03501e0039000608000c0c02502c03003110241d40900140440c990100c2150390084440c1807110010b895603031559940e00c6085906800800502c81c50300a5540d0f0b07030b521036540b00c0c000700103544807004d0101da08002c00d05418070b1408550b800f2250b100d1418030251600040c000303031019200c2c004010081c030031003030f0120000b06d4441c10485000b042a00c1c00071111040341d44c01d05c00500340740000e44005040c099000d40810f061040078001c00244224041c02d01d40e200f00f050b45c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 960716510 1250 960715260 960715279
    0x2040b070b100b04030309030512040b0a08070e04141602061006030e070f06030f150b121e0705030f060a1a0a022e0f1802210114060102010c1d 63
    0x308000d5030b1803507a03004181a1200020b0000a2541c8403070082d0a403802017054401c6107008070f00031000c078030461091509004040c020303111028054000302c2d5001c11141011141c81c031844c0002002c8420f81c910550080e2140c40a0080b0b210300c03d802c5407c2400c10740001c24081c1040c42804910791254421142015103520b05945000000e00c680c03401028a41c40a02d0a25140c0b4409800390050301d0f107a9044030b00e0715001640c4280c1070403010b130460751000c078000e2504c0c2c91050076000e0134400504110002040c00c403000101c107081c041c0e1310f116000f5a0345064480c02d206200682c0d0800c0540300d10310800400c041400381d0304501d8000070b030103011040c03500d903140b02e0030000360b0804610450003218240d4200315640c2031003442140c0481c520b44840308104050309000d200c4101c5010503455030022615065410060521400140d04070541c030304246119014114010300f07407600300e40341c400840140d00c18000d0a58090082c000f80c41018145034251200100b9154101003100b00d00611403e0001c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 960717760 1250 960716510 960716521
    0x603040c17070b03070306060305251202090d060c0f03050105030d110f0a200603151c0510021201050d050a110a05090f1e01140618060d061802040b070b 67
    0x10400b81c8014110364422640302c0c900b0040c0500142064800d040c042414000007407801002486910600038010305d61804403003401404854071003801d12116451a42000b614146998607402080a03a1140d000860030800060009150154280221003030504140040c8035035500824101104111440c00c107080c4c90281601504d01004070f0000c0020b80180a003a9092012041c14038031400264040307681004840c40034031441e03100c221007004003600380c480c0011341443c00002e8021500400c401c03e50804900e5100d880c1068030000c06010680c0d4009070203440e0021100d503403401800708032641c6c0319150700c0d91141074485e1030401c40200050301015000e442a980d001d00d050143c54094030340d2070a8075154800d42145001502c1c01981c0244010810300b094030311001e9541030b240141e0001d5a4503020000344041034003c3c803994402051034006441d6180c48010281ca100c0100001c04904585040510f00049940703200e06500a4010003050200040680444003c107034002001c0e402e40e50364 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 960719010 1250 960717760 960717763
    0x70b040305040504091b12030c02120c030f01050907090b030a06200a08010306112109030403170306040b0619080402130603050a11011d040915020a05180603040c17 72
    0x46800240e0f00500d49905c2405009041c20060407509121003c10407180d160401c0c1c44c2d044c80b2003600100013070403180000d0f00500b001031038a907100d5400030489002c042108000f90809840c0e02107a01079a54880422043d80310402c10701e801400c9d49401080194445004a600da00300c100e805003503246c40d2144145020340c149250307580b40c404410920f840305290a0010082d1800384000d980c3c45003040071402c0203180c0102200c6120b02e03d2080b040041d1340d000084400100c0050030140d150100348000400314a8107450010001c1c1e20700710140c0d4038980201000216030085140134003524040c0000c00001c100d4410103020002c250500d003816584901c009018580c460b20710701179050138010000104040051400074841c41680308441c04440c110045407540010301c4d01030340341408110407042070308040e4000b0a020b80a81d001c3d19034003500400c0ca1050340d02442800c000110001029190303c008031031048008a800c4841c41c0c69400d20340c07628007900846000c0e10000045408000320a00c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 960720260 1250 960719010 960719017
    0xa050625030b13020409020d2003061c05150402011710122604030215030f0109020904150b0c070f0b190207031a060f010c05060f06150f0c070e010605070b040305 71
    0x200707070042d561246c8851403100650001ca404210340c5080101004150800c0c5005045074a00302c5541404d542d1203004000400f00c0301d0525001815a00312030001003034050181120800703c4840d100010f0400f4400180b10302a0704660341104001c0070244450301c00100c8102d400c513201d0403a48601400755007031000191442e00303d400c9600910039a000c0700c031410749001e001164002c55103284056a011500b864601c01150b4000080107c2d40040c40f00407131076806403c0d4500068800604a60645400d4120070302e1900702044115000c6982064040f041219801600101c8004480185030040005590080c40300401020f0031010303082c03807098030070005080155004035030107038020080440940711010550302c5500400748800e882c0c9640d409840603006a82d4004010103030b45d5150484180d13200005445c41d54417604400c2d006007040c0420b8050114802c00054550340c070040506c28518040d42070341b02031189800c0c07500401600e80c1104c151200da503080400345549695524003203c10b4803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 960721510 1250 960720260 960720289
    0x5211204032304091a100507060c030204082d0f06040213271505190506040b0a180c030e03030412050915090f011d04020c0c09090a050625030b 63
    0xb2001c03e001940c1a900e8003c4122038681000702c4201401480500c100c44804550140102d41c04100d12400038900344d1000f0610b032418130f0014101034680000d03d0030090046012004040c1034112980c81403480120603e82c860410014902c0e0300d841840207032640401003020b4810910400c041703da076075064001400a07406c0f882c801c0c0c1b000c0f200384203091560b08440340903501c611039805002800c407141c0c441d546c007a564100700904c40c28114002d84011344401041150029194034a564082d01d800d904080a4010003171044040c0000320f080000b181c44220161080500b0010100381d10034020044a412580000040c4240d405280c130685070b610030a9909508550695080710304540020081c100d00c840c1116501d0130001400011503052014036800d013400394544d042c0546a2800c0e50041c0880076100f402c4e5415401002c0015142d102d00f120540541d420031302c071301410004144405680040715254041c20050b44003030b900024124955a00240341d03449510240340d0f520915640c4808 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 960722760 1250 960721510 960721577
    0xd0e060403020610050105030709150e04021911060103120c030306030b0c1218070b0d231e070503072a03021b010309050312100e01030521120403 64
    0xd04003454025501c030710858148201004a0700082201c0d031091045a02540341552002091401e103225050101084031010080c040305170301a000c181c81e0341c0098000032010096589000381122005040218840d007444800d41103603006000082d6010101038007007980e49400490b0701e00c14a4268000d01c010f403c0541582078040404c428011400001c1c84000e5041035075410740c0c0c440c40c440c41442001c084621901e600100c109110b01d440d000050904006442000b02e221030001c0081414422885039070360303100203881c0401142d0554805500945104903800080c1d038500464001c045003c05406030040240c5408500e0007030b01040346410f8070318150840082040c0c1a031602a603100070301400710140a2007030140203410b41c040d12800404a8000300510300d0990406618101060300a02903502c104c81c100f4003103030100703010260901862181008240b0f60560302c1861916080800c000c2c148541d0400c807081c059070710046103d4105a050404800c6021002c0081446549080310721020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 960724010 1250 960722760 960722773
    0xf072603030f04060b1806063009150103030c03030f0905031801230313031112040e240d1e0b0f010506090307030308130f0b270a080d0e 60
    0x80c215000b50314040e40c402d03002042200c4c4014103002e9203001e002c2c0c000d0305407501d00300054802e081c000d004094001789410480010701826091328060500780f0030802d0619006010404044006c108a01c1802c003c00e204045640c5580d1300206400c2c5000e5004040584a0140707007140c40307190f0403030160703194410103503900c1d440501510414000c0c0c6a03003550028001801e011000d41c07212600b051908030a2120710300e5075451145401201034890812820891000c100b10741c11401808a250b15100030400d00e550fa520305185058440406820010111100100d121410304142400d507000441a51801080e40e00b500781100120308130541e038030359086c0e81c040103410010b04010180c42440c01c44c1a4840710307602e0b602400384502450942a4040e0700c02c440502c0880e0185240340c1c0e00c07003840c1c440d400c510144e6580700c06045020f81d03002c5a500c5600c0040c13102d85151030004a03100d8615500340d6080303644002400e070b503490141e4400b42035654006810541c240454000d10078000b8400221800c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 960725260 1250 960724010 960724021
    0xc0509190f150305061e010f09150e0c0a260a09052826091311040909060c080709090c020a020d0b0402010f05270316030615080f07260303 61
    0x1103a102c100c1e107120040c103464078685031b00150f00300e4440c1138030284010b001c0d14600703007605400203020036207aa01e1400e0580c0300004045e200e100c0164402d410741100725480b140040006850224003a107550f02d101a0070101d0000700d4000001c8030f80c0043e00000c04102c0d680641020381c1040c0c60061034101d40d0203044606444002281d030f11000701840f0f40042014031401144400900391400300160641d0341c20010540c0a1401040703980400d8020340c00020185003070500d05a050b40141d11555450303455480704020311a4a01c02d998030640303070342000400b518100000801c0c8404d00d0140c1c004490780e0310000780840d8400c00070010040c1c2d02a160b03401420340b506200c00d03021700848040740021045290700d01e886100e10300b6902002c0400009000c1d00035052011804035100e201d0144d0148501c04440b0500f42803c003428000758060700c00000d1042c080302454103c02410780014000b0b5100f22034000031008009180d1048a003c880d42080100b560b0b0508151110100f115900c2480044203206 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 960726510 1250 960725260 960725263
    0x605070203090316140d05032502100e090a0e0309040e0f070803070b0408091804111906020619090807030906121a01030c050c0a0c030c0509190f150305 67
    0x9030302e1011000c80e0a808220f070405120b0300094041da1411841001e5041040d00b091240403807400e22600581e030600441902ca10300d00700001080241d844451322403407040d4240314041c4198407225150603507902010002141e4250380141c290700000da600e19003801440c0041c4151140d00320010414002c80100494156840703045070741c0043c46014040300011400000412070359295804401d6034103580d19500c90000d02d800107030301250803d50502c0b080c400c1c1107149802e80e119034840d1003010000860f840134800030300d460304010400702e50702130410322200750000760072940401003403841e10800c5d404d002e204000d40126180140540d40c08500380c820181c0144103001550040c1d0346040400300103103188011342e01d44079452207084602480d480380030b5105e078118241110460810358a0603a603403024078502403402100352010310040d1424002c0000740d08000008007001c90313062a10b801c010a40c40c02e0710010b000900101680c58145070039002158221815900c02c4600c00382080c0d42e1303414008d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 960727760 1250 960726510 960726517
    0xe100c021e031b0301110310060509060f030103030503041709010c060216080705030a030b060301060921080d020a020105090a120f090905010b040905130302060c09150301060c021c02030a020105090d0605070203 92
    0x84c400d500b814001c656140044040e64401d2591400c84070000349425825a07150b400209502e0b0050420400010483d44010065000314030a41c2c50070345d43d2500f8204903074548190490000d088008000d003084986e48180504042d036082480160340d10444d00c0c0340f002e808180ca00007002802d003c1066014884080042d0000803800d4409016980140b03040200f184000d024000104007604c401344140b0500f000100800800000e01c0c0b0700031205602c5404c543e40000a444c5061500001c82c105000d9083c003800b42c000c0c4c0c0c03100003020780362403d656500540300356603082400c0007040301d05a04800e2082462030001c0c201c110b020001c80d6150808400035910a0182034006070810700070840303011200034503042e51509540900b45540320000944210703800025025800f400d041d201e0030030612038100541c0200450748640d100f140c124418000e4240e0b8503240b40591145500120002d030302c022600102e007550910303010781d81e00d40d0000062450140e11801420a40c505801c0210994000004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 960729010 1250 960727760 960727813
    0x90d0315030b01080c0a0603050103020112020f09130606120908031315020c160b0a1d150d0905061e04080f160309030507350c030307120e100c021e03 66
    0x680d0780583c0300d1f0016400d0f16001c0c440280051401c003e0310b000500140d000d45588140061654030300009800080c0550701c6250400c266503a807040c04015564104000c4841400061002e00443d4080e44452104d404010f024003e4010301200c0d81e020005180c07011030000340a000c017103455440400d84559a4480d282113040001c0101201084002d242819550610043c0e44c642090390341452243e045001200840c40d0404003610a10f0f40c0050100050956006c0d44100050740f6901400c0c09464920094109811090040b1041030500c0c0b0415404c0d80c4140c000e40740c1070f5140150034070301c101031040b41280c00701c0c0d44a588061003010b50280d8100d04a134000e42c00c1310030640d02c0d80c000014200084020300c01308285050700d80c4102c81e4011000160760385107819188041c0116010130b007140d010030070403900802c0861002c0001c6410032aa4400303001c00341e5596400004100019190858074400030307110b83c0c0e1821058072264840306000d004900007a080c0c8011003056101d8428541c075a040c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 960730260 1250 960729010 960729019
    0x9050a0c0e04021c0b070f02160b070b1b0703030207020d02040f0e0c151602120303010807060f031116020f03100b0f18010e04032309040e06090d0315030b01080c 71
    0x202c5031540031544c00c0c2d001e24135001200518551601c84054070800c0c2d030380075020107500442ca50728401c064081920340080500144590f9640b46070300c0c02c103000345001403800000071192884160003c2816003510f0b203039980340c01c0050b83d448980c000180f04900d82d000080d4068100110804540c850b0382000e420400c1c3e00c0b0468035100240c2d0300b00800001030356013900342d4000520080100e03103078920740341041600240541551802504249056038404d82210040f80d015600c100f041590245002d10354008628080090000074541c4540c5d910840100c00621011143c1c2203065607110350101d03111280c001c0480d20040000017000e07024114a049162141c1c11110920304181007516000009500d18000041c49a080218100c0104d4000d00203800f007201e0f4010703a500703e51941c1000d801714000a8a6551912040e030200015510720380028110f5804ca201440900c20703000841050b0143d4904021803420700091603c00140e0f5250f0014200c6040340000080c40300020510b40d400b00030644 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 960731510 1250 960730260 960730279
    0x61e05040509010b060f070303020c0a03031d06091c0201020904090b0108121e0f0706020c0c1c0b0106110c040908120105060715051005220f0b011209050a0c0e0402 72
    0x1460b4204c40c024401660011402c00c1074880f1504c00070010550381c0e1203400d005007801c0304e64200c1da24061141d0700c101c010a40d14946100d00f506010041d00c8010602d1004020703509d402d1200d56151104421f280200080114029035003500079019211450005801040040c0380ba0910030b00030302080c454081107004004400175041d0498080b00ca0302024121a0044112116100e50482c0d00c151010204450244045800606140020182107400400070400020180200014860500413010406c10700010b0b09000510240c1120304480706410b0000351140b000090382d040c0a03405d081c0d282d002c0d141520b508204015070001c0d00c0b01c080c40b50b200c03441a82c0c894040c002d90303204545016051480085482a80140f0f940000741c1c001e00c04804940d456070f0740c4000c610309544010034212150303140211103190440c00c2c401c81d040200220000d01c04444281c0020705030100c1d600d20528001d4455041c0c0050010401c901e20803154007030110000e00f0b50716100d0518581d804c0d1412846200d844 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 960732760 1250 960731510 960731521
    0x180d080a021c11030f0706150803030603060c0a27171c0507020a0311041b17061c030809250603060605031b03090c04020c15010f0614030a061e050405 66
    0x500301c00c0c0e2804803100056292030800c117201d01e50340d0000101102d015482e124150000040e04d200d010003484840011030701c03800c10304101400c160008100c540391f5001440340f20300c910381c806200760054030741d01d840e4511020101e840c010200110f030000004040d000014290b120781c0051140e9540d00007403050b9580c400d0b0796504440328490100081c0d840044079400b400880c166002c211050b082c0204001140a9130361f402e40e40b000700da800e404020900221070501072240313030031010381e00900884040c40507011001ca86204000e8817440a000c11010100240132030404100c40b100c00240141603629078070032200309071400710711402502c1c0024140311001800c0c50041090324060352108134601421042c031441002283c10007482440e162140d42e0fa070b0f541c540c4491000703200d60718020014082c0284a281c0d044010350042e40f00350542d46108004200c655409000e40e0081040303404003507035076111550700c08040c2c885604080c2c3c402480a410000c40400103d01400700c94003601d00b840340e44d0380c1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 960734010 1250 960732760 960732767
    0x17031810090314070f0605040510030e100e280c120305030a05040201030f09060f0b06030c0a03091a010803120a020c120c01090816110a030305180d080a021c 69
    0x35440100200d1940c840900024901e25008a5074090120495060750f41d21a0341c0c41d100c4030240d0190001c00d40002d424411403c0081c80f54400c0703240340c141401a1024885401d9840e500f03080207024491313a03480c0c103d00c43d00741400034a80e810b9814200c89074a4055098200783c440030303482c08640c03902200c0000038002c1b06c03074007640e03050581503100e060956588182c50780243c000140100d0400d5514618422a403d07039201c2d0350819805448001024040546504111342c42c1c0000c03684100000d00c1044a101c0c41c2c0c0c812a410f0b41d070280b402090910441c5025100d8001d44d00b41002c820442000220745c1c80b0300000a4145040115081401034849114840407846014001105030300040c034038410700b180e144000d0003025611f10001039200c5c115111800701d80c0204d85408031a00c2d10703420380800d010368106c017403049443c1140c0c500046803440e81c01070014030402e080040d0302c2d10aa5a5a0020307507561800c002090b402c0103120f03655a2540d08000d403100c0f140c138911a00940c17189158101d4502c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 960735260 1250 960734010 960734029
    0x10021c230627061c03080108060a090b0a09110612040618050a301d0f011706041503050303060103060f0f0608042307090f021309020304020a170318 65
    0x6100980d89401c06076100e801c4070b45031006104640180440c0144e000860003014041d0443e8000e54460b0304650604008500380030303020b0b1175105164100240840810200b82c0445c0e080741c1840800144025140340180300014007440f4254800004620103508400c8000040c0c401d51003214100041e070b0200c1c40b05942d48686c02006041507004090302000601c0b01600900340c82d12116122600329411949003424815248448001540d0440803c0c0081e00c0724807148001d550864a1a0b1f001c850300c000208041490350281c4401d540030004509a0b0710303150701c68080903152617901001c2039100c1c2019683e9600580c7c440d030000b072820385c2c0041c80d01000c07c1ca104c192110181c0d0030b0070680ca0000300725015000a042034400ca29900c4c203000900111010043c15604598080d0413040d140140c1c42003104c542c1205800c250380100b0104640c06002210f050642e40410801078817078645d800810304954680e080149103110301d140f21340885c1c1002014201e9141c0e4074819540003022102804410721 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 960736510 1250 960735260 960735289
    0x2901180302040f09060e0a021206070e010503150d03081509010b0904110904061202012309012d030e120405090f060117042001030e10021c2306 63
    0x41450080c40145415001249401c600c840b0101c1c025100d52101c4003220b000240c4a1895446800c211045040001d04400154041806000d035890044806006030300700c0c650083c1040300010008440c071001e04804400340c2c0025150703080a40c407074600901040026078035400242e00d244424001d900d40441c50506a8529015040c2425000824400070304091000d040140c0414044901c45840e02d01c250030003400304180c0c2c3c02550805000240003110010002e0b1755191450548001d02e031840d808440d9134400c00e18000b00c581c00310340507904044000350700004420504800a035079241e80b6412041d002010b00c000d45442c0384256040b041e8521561040c140c21807020310005041e07035002ca90050b44804181000e010144500345c0e96603994400b1201160303250a141101400c1698402031f540940300282020041c08000050345982d514041c0e00c0120901c0c0c001031211410180d610318040030416058040c402540025490700080d8928110501d0705151a0005039180c81c1007944201c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 960737760 1250 960736510 960736547
    0xb04030c2f04090c0501030b211b0307080c0d08071203050a0f020a230c0307060c02150c09100207050a0b090306100605030f07032003060406060504270605042901 71
    0x1d00d401c0055024007030348c181c03082d80b0050742c13510a880501985080201c101c0600041c286441d008220401d111a000c0d42c041c2c000c2c1d2094505005500c0000741c041c3c61210201c5844403000d15614051682e44140180280800380d070b08101d0010707036095040340780a40c190900c140310b1720850511803000c0380540e052010004440304c1846140401e560590903220310103010403440e0024148849155030310240c0b0031030350941d8920400002e96414403800008211074052181c242c14080d04045160107108039041c49040b40d4580002041d000f0010310004200c00b4106409040d650ba960300617581161360308501034014100012040404840045c1c10381e0301c0764a401c2d00b562108040e2460140009040300300b807690700d5035111000c0ca040d031007003000d02d940341d10780581c3d91070301205101c00c0e10125404070013440f4081c0400c0c05020441c60404020700c0c41440d4001d0742058a0050101401080e030100c0d80217440c00c408400d85071000250078010012458261000c0102d40c001101d951000500f098400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 960739010 1250 960737760 960737783
    0x60d05040201170915060d050a03020a1703070503040831050a08010e0303012c010f090e0109080a0f17010e0919050c01080a0f2d02070206070b04030c2f0409 69
    0x441182217030700341d000382c0080d01c0c8528409180d41c0e0300c0e20300883c0d014140e001d680302e03660010412403452041a0176000b0342d848a411414a60345c040c2c5540009040208680c41c00b0a0080045202d10000c096611911140c0040b0510101d2548800c2c40503010380d80c0170760400d00000c141c0e04414081c44030901104401180b4580c0782200200e013a060b40b44540c6c8800c00720840c2607030400c5200780324902900c040d041c1440c0a030300d0202103c0840306291422038040e41021a504042245202501c00fa8002c50070b19030020000b032101181c0309002841c61080300b091400000c2541c4122042c5c41d441880041c0841e89503086804181581d0b04129000420303a0f8400019258194400c100064110030a904045010280381256034161040c080c0d800c0e5180c0c4c2c2e40b18080102e180100c00d205100310401c2421482c1200d190041106031080440181804004000ac501094451080022415081000c44e07190104006149024603010030084452100c110880354607840e00348140034581e076001c0401ca22 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 960740260 1250 960739010 960739033
    0x3031e0201090b1501020703060e0105072c190e13030906090e070c0c2301080106091a030408040b1201030309060801080a11060912070e07030e07030b0c09060d050402011709 76
    0x40044c4071107200e504500030034030000005401350050644a800e80f100105952419400050054040d2030842c4d8050304554000c1c905840b104031411038003017081e140100b500c0584c640c40d1171180b116a00811101480104000ca4051480c400c011518400d0703032044bc2c0c01d0307075400c0111552401c1d40074020004500c040415504c80c080c4510b00742d001c0c4115440e046242d42e8072550f0540106180120451340c00104440e182582d010803424098146414105845810000400041038101404014030003001011170180561032081d200102206501d8a42c0c1d01404021f800c940c040030312007100440d040c12801b0400c90301444400c2c0c1600e0a1800400c0c00780500d45036021100012803540d0f811420170814029207460b4075100b00401a00e40d0010403000b0724000b800030681e040280300c801050300d0400061406d03400410f46004898000e0f194070f580340c0b100004041d00348100700d080d03503204400141e0300b0028a1290002803040d4000d80f1103141e10175821484201104c030031508038195070028500100c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 960741510 1250 960740260 960740281
    0x80105070f0e010c0c0303121401060c140a1b14041803050304170c010213090b0f010f020102300906040320070302090705130f0302031002030a1503031e0201090b 71
    0x42c8038052402e00f1211445845140460b41a130f0000d0b00061121005230710405124015106d0100c200c0e0212035196141000c001c0c04040348120040c040c0402c00c01d0704182c40820408243c405400c40c3c0c1d10000303915480300140b1912280c0c0709802e00724400f00c00d080d01501c0d25104445d10502841c3c03024202d07070380a9600f1101c03584000e004860031045810341740da042c001040034100302d0140e000010794560310b41902c40109a21a440b941d9068100001b140c0c0d44e450302c40c403801c001102820440c3d403100e0711250a81c00390182d514000c914140c010420000302c00702d520740d1455501030001520054403098030301629500308480180c0854040300ca5440742c0c50340b042410204078609019103d040f03850794002040b400054810034009440800d0201080e034030402290003e10380300400c1d0001703034a11f501186c0c5903c03190200c90b00039603012000580001c1260440b188a041141b001e404050f107034a0090320030395805070b107000c000703040c0f4401d41c08460052144081c040d070411450a090b944191044 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 960742760 1250 960741510 960741527
    0x31701030b06010e21030c01200904091e12090e07090b03070509210f1c080601030e0d0305040b13110402071a1618030308070c1b0b090406080105070f 66
    0x3517084400148a41c0c0e074030569268000107000000069030359229074040f102d0950309411440301c0f800b0032042036a221803240408580c0c85405c185d4010a1b0080f04e0b040a161980700786001402840d560010041080301000d40002845d01c00d0312a5620b240c1c4540041c141001d08683c4000070901d150801d1000b194450051944609985403180c81e00c50f4880205104031000d07407581012041003524041c1c00f07001480784410b02c00b120070080c1458001c04024802050b40e68903001c090220003404199070740d01c80c3c0c008600c0002d051b01190600408582c0c000c0060808031029102e584448012955601081d65425220741c1c201c6c20a40c01c03183c224082100a6125440885001c2d014000c41280c8549001c80d4901c5024107003a12108001030740c40192000c01d0b892003a40eaa006600c4081c80004c0d000b581323041e004802c03031034500010761283c50004420005101c052010803008200080e8400540c001410b9081c800c1d5001c0c014160b0350103c50742a50019508900400d07244000c1340c070120720401c405d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 960744010 1250 960742760 960742787
    0xb070905060d0e1923010c0c0b07020106030b090f07090e030d022a0f0111031e090a080408030a02120405010c17090a030b0a05101a0702030313060507031701030b0601 73
    0x255100d1561500200c503c40d060120203c90401705518544c0b62000101d82848051001c03000078082d1302d83d600742c024544900901c1c01400106d0007401300c2d0469101750308c21405103502562a2800b400c028030300507964046000c07400d41c94031130004041180d40e0680074a1072942500c4004506041d81c4222401c0a90486000c2000344c40c0e40600e0820981c4036030f000c0d040002d5031440a085940d0303c9100740d07429108403001c02c050104080062002a884150f055400301c032110200b0700c0c0c10340301c4144150030f1130540f040c00b5104000c045400710300000c01000030040300030140c08560700303c11114181640350140b84a03141c0130406031880003001c9400c0490704190b10303001c0650549000c2c00200040c003082c110340c00994904120004004011420b403240303d410900451183c1c440e6450114560b00700c041c0c008100d80b001d540820101c085450403c26102c40311146010f04000759114400140309401c5900281c0009201070486101285401503441c16243c01c074400440690b00c3d00c0064030140c480c8c451 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 960745260 1250 960744010 960744013
    0xa03021207050403050609070e010302090c1912141303050c031620121b03030d0608010902091303020c06090d0506040b04150e070e040203070e010e040b070905060d0e 73
    0x5035041040c0504201407003048a6280d480d00d543c02c0d03040403850a0303c001e0001040d44e1201d40c06003d2032820003c00c1c4d0440ba412070700b07071590342da403d8182040c0c0d0003010b015402404403440e28424076a0000035052003191507801c03c0094403000c0c2d501c1c68800d141554042c0204820b070440c03001291041e4000c2040407801402c036840c1168000042050101110060728400d922111324000d1501410110541c1c036000c68a00c03809200d9648201e0700d403025000b8003420030400c01360a030312070f85040c000c1e00d030050b5440c81e00b0043d02d80c0d5103402c240641803c0c9800c80c410035141000400e41c00300b445000000d103415070700400303c40c0081e0b800d00685030f01080441c4d03841718121500d140064810080705106078800c150b03e4034075090a18100c810a9441000a41c4141c18884020b090700d4000032681c046504151010f803141d2194000f09051040c950004070484503601e001041125400350241c1c0940c2c403802c4200069034524504596080a50013210350001d01001131484240d11900518004143c000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 960746510 1250 960745260 960745267
    0x30e19050922121809020c0d050a0e12011805030d0c030207050616180602030a121b081003020a0f060e030c090f0603070b040f0302040e01050114120f0a110f1909020a0302 75
    0x50b40071136a820103038040590590001112140d2910600c400701072200310342080ba041010040c005020000804c0206001d0100302010040702002508000d2194a000400c920072488a04005803a58018181e4914290511a01401c0148a4805c40b528650000d01a0010352121a03490b0b0140070144c80380001c206855460508101c440d500d404005d0555400a550311101c0c0000039246c9282045c10800713003072800a0341d83c59481c800c840303100e07200850318050500f81d80f0100303040001001c075000603401903403111010510f807420144240030354100d611100c1d0203000c01d20406da6a025005a6542c00c442e41c0030201d100c040360050700503003144004090303e034000e85505504107250469405110300420760002081581040c1c421800110b0000000340265070601c0c403203036202101991024050340000c43d464000c1c945c24031681050f103880d201901c0004031141042c010400b5030100003403042103a504065040d1401d04a0114181000d0b03200d2410b4601d0409141c0c0203400101d01c4a084c542c082 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 960747760 1250 960746510 960746537
    0xc050a05180403090e07080103061a032e110406181d09100f1a0405240619030218040b09160e030a0f0309170a0f030e1905092212 57
    0x171203c040c85100e00744d54481a0390314504109040d5050810b0505100310010b01904040d00c0104460134400110800d0a41d4007242c2c0300c0354005407840345a20004d0307500d04940e40c00074164607c0140200d90442da601d07040100b510380310030b41440c2a84a045004207120340d0030082c08039401c400320f41c131081031415240742c2900d1203102c0b0255491000320b00901ca036180303000700c03040003408140300c2019416903041142c0c1c036243c2421840b03440501809000c03203000358980d000d07a558150842d030355106c140d00710011003114650040d0103500b020044028443c04410402128103040c45001e0042d00b000301100e001e07468114050254513122a558000c00c030050042d8a682e0710b04010b010342d218070481041c084021241001407141030184c00202408050703050600c105440051034100c842d0308a284440c420405180a689409802422a4012002d00707002c0e2900b5246c02004400c641069401070300950b600380c1c03041e20700b0513004152142680c0412010340441d510346c040ca9010002401d050203841d050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 960749010 1250 960747760 960747779
    0x140702010f0909180210020a051b06070f030e01030b1516020a050301060b030a0b09090a03140d0f0914070b0d0b06123309010b0c15010603090c050a0518040309 70
    0x552203843c0d040340e41c4801c001c0440c2064104c0a00004c21b0307102601c2d200f8100d541c1d280d20303031105a46040d0b900044400316020b03540c8100440784060380c0880d86c03800a41d007900d800707046c0c071481d681d0311070103e4a0500c42400500f03200c06d40181c1c1c80d038040710076458404c0141e0f41c01c51001c1107100c141d0b04013034204404590b5071024410580601094040076849241850b0b220741941c01d6090710600900c0d00c101400020740c0e0009045d202e0551500305807000e903450450208150140c1c0c000304030403509009850518a20580c04151111701510400c40d1960228155640c1c412151081035038903c400c001b42c3c03032202403651080c2034414bc02420305103003038101020310840721001d6558002c09101c0109c4510060855a11588842c40c10600080001800d100145021030140300c4d808071507400007a0041c183c0810f0207107490440e00303100c020b01d45507104c2c080180103040703444040301e18461002002c210303880d28017500d4003201c80c001c011101e0b406412104c0310720548050b00c00c6041c85110140030900e1004d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 960750260 1250 960749010 960749021
    0xe0a02180702100618060b0408030f0f090315070f0309230c091005120712030e04150f0504110f04060c0f050d18051806010516080d0204060807140702010f0909 70
    0xc1040117444024007282070b0007112044d610409804800b08000c002586002c070542c2c80409000c120140c40381d81d00d14039a0054420f800c4103691502848041100d4090440c1045001d4001d55a602c0340b1951800d0341541210494040034042410520702182819540d050558103050200169403960390300d24045000f01c0001e0321000d50b115608201407001d0708080c0204510000d203038004081c00c40c80c004240648000340c19020b020820004022113054032540c200c50700c9a010903c1452015035030750b01c5100c04d85a280109849035013850840b654541d040d030292069000c0d205910303481c042c42c120050b58030f8102408101d400c0c0c1c07410f040e180c0208a0a0001d030440c00c40a40350640b00c15400720b03107041c4045d029005103104a50701440e44514022030201c0d5588043d003030030881e5480b02000c0c20a0111104a0380040c011580040d420048006680240044074041e403148030a50300c031030720240d914145210a0284411041c040e41e405036104405040503c0c000d410100b00039901d0b090204141e44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 960751510 1250 960750260 960750269
    0xc0909050601480305120601050f0a0201050f13030e091b0d0b130207052509020f0702130c12110d05090a11040506061608190c060e0a021807021006 65
    0x5004010403c0070b1100700d0764840c2d074111106148a620380d4000e00b2500031044841d0201355408000f5240340d00420032109980364802603d504c410742c0c00742c001c1c041c080480c4e007088004c0105011650001c1180641d540180d499160b155008030641c00340000c0110041580d401841e2850807071106103080c03801001d15454440300412411101b8040c030480c074040f1401500c0d80d9204009504c00300d80040344503900c001c040300018440034445101d40d0724070529500301642e09440022410104901e100040c0415803003a582680c0d214640b05210302203858400d05040420002504144006400d500c0a802c0c90300c0c4201c254101841041d0031401c442d070031640e102007503105860b4001403210402016200c50780c00c03501070045140c1000886c55034014103010104051410648400700010601503c82040345409125960410442d00900a44032808255101841e16915070010540400d51206035a00a082044140c1a02643c103481b903100400480c218000c080e820001c00406028180090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 960752760 1250 960751510 960751577
    0x6120403020c0910060c03030e0f03071703060109030b0a0f050103030f1e120e010b040213030c06051e0c0a0b012d1a09130203040b07030c030c0909050601 68
    0x28541440c0180c500340c055280316108014030420800107a6240c102c1c0700c01d84040d0701d007051035000c9915041e0090310b86030901401d0750159000c9032023909d0300040505041d41c02400e00440004105411811511085c2c46441c00030b81d00700d00500c04558600402e0340c004c840410000b0f00e0b00400e80fa41001c54500307800490004000202090205034420603403c84460200c0384175110900c10300002d8581000140d00c201da040d1075582c09a20403100390302a442180700900f040d9981c0007030b03049000399241e180c002150116214140845c3d03407440791066400c100c070075040700a000d40824900308455000056200202d102d007040410015080e07070a00d6000b403800c2808074402c3c0d50040c0c440d40c0c1c0340704064815141d04441d0b402c1000b241c5201000d500c1e2000b007044503559990300c0364000c2030030181d030300b504039407003a0000041c4000c0020441c0342e0b0b84590303001e6a0130420545003000413802d48040801e9580081c2c0c26801c18807038411298400e9030040414100103510800c45c1114580450f500c40c11107038078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 960754010 1250 960752760 960752797
    0xb100f11010501033f0e0310051611031813020712170105030d1b1112070501080c121803090333010b042312011a0405150d050c06 57
    0x76140500201c0074000b80c541c02d140000c11003908507016050845c2665041000c02c814602c02c42d1028000000e02c0f03050a44e007030000303280013244864041c2040000000060942e9201c0c05182e42c08015600c0b41c04c3c88900400003810711034108003031329030000091070200d0f40c02c1040720000745464034814698184d0b80c8503501c84606c11317427032036201d00c00581c41540070b6004011160102d84d8420b400d0001500490410701e100b000905012840d001641801608448207410651007a900010b550044070026a1481c13429900c2c040e0404042c01150294540541500089000c0e008804440000c4513954011282000010300000307241140003d40800990702641031602c3d01d40007800c542502c45841100a02554944144255035215501c0388400a180350310160200c05400c011403c441030004100c41120448402c2250080c004143d09400e059520000f440c1c81e030425001d154072400fa401ca41c000c018a20b0414002002c042d50703011241401004c2114a1650702e01e0b01038a403001280c0c0d001d800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 960755260 1250 960754010 960754043
    0x51017010e0c13080c0901090c020a0326010605031014130b1324090b100f03060503120a11060705090607020a0302130b03150c0711120f030901030c030b100f1101050103 74
    0x300700ea041c0c008c141a2410310705aa40066000540d84042e160300d80303403246405c0c3c80d048510380885521105108454000800000e03026401400355000310300303401ca24001b06541d035060f1505124410409070b002041d003c103220024200d03600c0f0314000382000e405078122800c0030400c5012901e4401307401c80c0081340f40c1c01102008840000f02c130040c1803003e500b081000340d1400000c0c02d040665000c0070400034298285040c0a220b90028001083d000d001c40755900032081c403665a0381c100c0318010000502d81d007001703585800000303411805a4400d03210145003043c044140035040d4404513087c5c0c1c0240c0783c0c420000050306c42044044404020003000110415640105400c2c0503040200f2030041c01d1010074801403140c1c0c282111007040e070019009041c41c440c040455410100d00c1d40b401c2c00c90203203c80c01c600e2044040001d00c0c000c070099904124a10303130250203800703c4000e0940c26420510002080c0c1c10b01e07001c1c0c1d844125019160400500840e0044602400c1d130b8801d07001100c12024407a02c0c0071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 960756510 1250 960755260 960755269
    0x204270e0a0320060117010c180329191425090509010f030308070c0b0f0a1803030606091d0c0c0a150609060b030f0406050408130609051017010e0c13080c 68
    0x42011450709e402c0980700b440200350030641c02c5500010304a98a06600410190000e500c8034000e00c0420340c880705a4541402901c0c00004600e030329100f0715060401080519600c81c1c03540f4440d105120300328902070381c84100b1607542250303142881d0900c20110070101b00356880441d094003c13340b4015072003688e41581b41c020040d05000c0c1000041c0500074491341c0014420a403207662200e0030100c002c54507a55406084040c0ca99900c0007040360211078003070b106240c0d042d084603040d1440c41e220304022681d80c103035118045003070034043d40f4403850001c0400c140c00100300081100d0215882124211181a12444c02300c0e0500c3d045160869559402000307a41d06500848000b07140c91443c2030300350701d00070040104082c0010402800c09035603200050801692809880e500503407400c11880050321440090501d070520b0140512401180700c04401044c46040d04442500390081c0040544e40b801e10010031044004c0c0203444101e03410b104040c550804803920348001d01c020402070905851102c01d21 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 960757760 1250 960756510 960756521
    0x3c0304050d0809070b0d02040b0715050708060d0609060905061015020616030c021509010f1a06040303080415020d05150a32040204270e0a032006011701 67
    0x3081c4500b4808012100c0004503051044032840241d9503915100401024000e1080d030304034a172044801702d2420280030707000b00003101d601c28161003080325071100b05003515008011100c450340440c4c2e44008800003003054006021991003000d0214020b03056541e040c2c10300104607141d49026990748810011458000d080e0303412029540041c041c10300b8261101b00740702920480c040113150300d5401c40c52900b4400c0110003800c143c00080481241004c0c500c880c060803129086184160909141c280c0d441803c81d95095606c200070b0040c0e24061942d41d0590f81d41e040100181c600d074401500c02d80d0740200328001010101e00c0d0150008052178105d5000c096541c5000c0182d0107910f51910601012081d40c4110700700a4161885c0108006c010007250b105d440c00d001034982080c00883c002420310300803d4010240c140148100e44070f130785200048021210069950703011a03000142c69000709015558192000e03040303041001c2c218900744c42c520302d001803c1e0b205000f14203000d50390104e604d00078400e0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 960759010 1250 960757760 960757783
    0x50610030605061209160b09030f0c0a03062d05010509130203070b09040207080f0c010c050f0304060b0d1a01050909030f04050f0a0509010308030f100302063c030405 73
    0x4000507428080415a00d0061385001003102d0700c3e42000c96082c000030880e0303a082e10700682a18407055100c8140c0d8a05030094000c042c028030824440e40212180410b10200003107000e0041e1100510310303210341c0c0181c80070b0649000c0b14090011001501340300c902c161603801c1820742c004125940f41c070041c400da10800030074400c0c10a4246040da001039401248030012221000d00c0701d40c6450400e00010001d20401100809210000a8040e00004400b000e81401114940200120711503518166180d1013480511303080c6810030000900091035642c0325800b038410250034070f46584030982d0303000010806090b038801c1c40328a110041126141c040300141c0d111160001031400c1c8000c40d440200e43d8042c50049601c10810440400c0c075503203030440c42000400c0001c0400c132030b07542d40e07040020b010ba10940311050b019110758009125551641051800c480e406880c1a151008502c020301c07040b03410640700100001810500138601220602c0240940c0241006039a03c3c03e1900d017007803524190100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 960760260 1250 960759010 960759017
    0x241e170a05090631050a170c030f0c010f110304060614030304091a03061e1303120906141608061e1c080d0605010e04090b01140a0e0a050610 62
    0x801002e20b60105945030803088901000c2c0c441c1d000c140036007140d034400324030b01102104043c0b05142030001c00107200885c1401502c00d4052407a50500700010751160090a4019510402442c00e031000b1000082255007904000003c000c054180720205407011800580680070001c010700c4180400c038410000280007443c0720302141c044070b40100341c49025500c035441d485035603200340c9000801d805a28403c1c00c50000d00740d07803103480c22041031070b80e0032800f9100300f5840300d800e00041e00428618155440c0c0c1900344e11901e4000d00003942c80e20190505000c01c8034071649070025000c06204001c0858015181d6447e0030740d14514a07603005052002c01052680b0890042034192107400071240304203003128058814003243c414942010841040155008001d20400518604240100e03400541510f00036078404e00c0c1c1c081e4650412017980c03032054000c2d16000200e00101700c22518201017247e81803000e00b0007907604d1f50359a00e0003462402214a2000aa102c5080003150310388460f003011000800c0c00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 960761510 1250 960760260 960760271
    0xe0102010c0806040b010e0411070c0f0303140c0316031e080f0c0c0307080d050f0a09050c0f0109050604081e03070f0209040204060e0727241e170a 65
    0x3000a04402003c0c0910340100c1c2e64410030503540c2d11030b142c00760f004040580705200c40100d85580302220b600c401030035541c00d0000c0c07134041201e07405403202d6411130b07405681c0d0036002481e82c10018440d0f032200c1500359162200300520000610030788941c10090b8007a4641c4000d1411956000f5201900391040e081000743d410108040354120042143d0442c070610b03440e0b038441d01c51a0b0403d00d90321601601425441012401c1101c0700281d030446403250329001d865201980320744405030241d8200034002443c6422601d4141c41c68100381807103100a21051401c80c088503031b51070102d14654040d401185240d04040c1510300044110128541840c454000551401d41213480b000203025400c0300084c801c1d0700110204081d9503440c0c000101503c00c4100329206801c1c4158042d1000820724410170707111100c0c07819400e480180d8006802214a05c218400c0700000b40c1e10070b91551490154007800340041242c07001450030764410f103001c4141903030303c912228060f03030401460040340051420b1003103400c18 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 960762760 1250 960761510 960761531
    0x1202060a091e1e08070203011a09040b0c0f0a050316050403021003112109060a1b11010905190c0f0501050d0207051e0d09080111040e04052b0e010201 66
    0x160201e8002c10048011210400e03551800c04494aa00004107006000d412020b000f803268450040011501c224001c01c0062603004901142c62a4100c41e10b42c4943d8080005000c5215810304075841010700d0b2545252840c42c84604c94a5009641720000054010080180c95090b100b00c2d10050500e900f001801c1900d5035001a9540903d640e900040685440310704221241e550103a54440300d04068003111a15071501d0982c802d001200c20391003500c21000443c40d000402c0c401d07a20301c009100220f421201118a00b55030840f5a501d01080c6907503654400001310314248014055541c100988080042142c106003640c0d400c0e5400009001204000c108a960303003002c1207d0040d081c404025855017650f0030041d083c0a54000007805000c40e9204005844001285000fa00d03141a10b806400d25100e9050a08903210191b200e44901420002845094018440258010b00c5171088803800b40802c080300c081c10119110f0302400310240907403070072101e4000d002da610b0620288001c20107082c61 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 960764010 1250 960762760 960762773
    0x801151a041212020304030507120218061516050303130201080705030c180111010c091d0910020c1e0705120c010e01200723060f0f091c1202060a09 65
    0x1e10040c42d0707083d00810344070280d000b07000755001190040c1c180c54402d540c0f43c0004403580387c004001c034403402d1b541c1d20448a00c007080203558016180503084224010460404000c05d5004002c0c514801c0100c42ca20000144100000c6120f20404210402094014400501480e801400c20300500c1018030410a01c084e005040c0c8901d44032035a1a54004420900184c03140500851403040a50800f01d15090072a00059414111203120106e5840c7c11541501c5017080c640c03daa08400c42e0b0001e0344010480b02054003cac0100180f854180c400440101191640702c2404100c1702d94a174005071020400351410300719440134006100c0180685440050000303140000078802c4c1ca050216117410a0f41501e1100d120203556803400048600c0f90707032290400b859058440e23041d40a01290b464404517141444420b8401d031252041e903103400c25107641c2207a00103030020500c080d003160211050058034130030051111100d50043d4050503031000c40c0d0600a00704100104900310f07603800d100c1070700c000070308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 960765260 1250 960764010 960764039
    0x803070503221502010b1002030705060f1f0e04120314061020030304020301060b120403110307020616060b030d12021806190810030b01050909070801151a04 69
    0x4940c448001c20b40c0300c0040962500c202e8103c03503a529281e4140d040c000c0d03015400707500c41600843c1d8004501402c0d0740100d0b564403552400801355000301c2c0c00318024841904200e41c02185102000d000d03410082d0518145980541c440c0b0081102c010501c01400b101a01114122800749024012a1480d0201c440403a001810460081001e150b03000c0d040780c07203410b0b0b4050801d840c0603104460454012014bc2e84d4106640c00e910a510300038002950a0310501111003c2540c4c0c3c40c0d461b001e58444c1c41c1510016000203428249000810005005a03030309002460098040051020610b180313007452001c559403451f03c98000e40c020102c05900c0d039040400360703001070381c040000740c0e031215030803481403051021940040e001540800d840030881c140e80b4060b034411110342e07103001c015650b105036801040400c0c48003800c8280b03c2c60051055042000b65594001850701c101d815059917180c1040c2154030b902032124081882c2602485100264204100310f8201042264109030400d03c181d0190207 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 960766510 1250 960765260 960765277
    0x1b0d08090d1104020d0c020f0d0f0507080706090c0608130201080a0b040f0c080601080a02040e04030e041b080108160e0c031806010305030d0c050a1d06120a02130803070503 76
    0x29a0581401000110b10318082800c01c081e00564075000b00102103409442110042c901500800202c1260b030940001c404240c0c0050b941e8550000a40c41401e5030340e81d0005800b03840104003003028071f0110700140aa07c116a105000300d42d442e5107480c030300038000b95020b40714644e000102d01c54600541e1703000005d1038104050200c0050b01e072202038009402003031240e6808003418104130908081d1508218070a01c00c800030f0300c070000141e98001054003248111b0081c1100640203c010801182c4140c44442d1211805031002846070410000104440d400d06100c03000242d0150052010305803d0103c08143d0810040c0c00440da400c04400003139980b002444c00e142c802002c00003400203403104071100040007100c001c1d6980c558490070015225030000608030343d2603041010503003c05101d03c003244c540d000f482c2d0f18140c000c2040358903e0001030142508a41c0302800340000406601c0605007980190020340b0016a1071030040201702541e00d0690004125400500801000c1403000c02184d500c00b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 960767760 1250 960766510 960766519
    0xc01030c05041d010f15122706050718030b0c0702131e060f08100f110a080702070509090604140f03180307050301060f1202011209030c1110210f0e1b0d0809 69
    0xd600e401c144088d9001d050021311035500b403c080300001d000c01e030b40c0306500640540e61107018900c010400882c0c0f0f0042840010a070094000014007072000c04405841c48a1005201c81400e4100103103000a0351087c540c60641c0c410f104c40440d00d4480103111340c100600041030a4030909282070241c0b41c0300c051191185d40c1441d2244020742a1340b1160f4005000c4041c1138a046440b916100e80003040c50744101c954030050300c9200d101240320319004550f50b1049811100411050341d9507540c9460041c08515110751911079100850401941880038182008a1180c10070014400004161600000390b010600031b91511005210310140200c4c130b00c0682c1c05200341d946a603403007440120342c400300649030102041e1800403250101903004030540d850718028058004e941c0725078000c10080942050910000c9004110300060742c0401000e000516454003d00041807440301300d60100f640c8038030501d60a43d400545002250010645c00c840003160203407400c1e0010000c40d13842c11170764421302003a00d214 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 960769010 1250 960767760 960767771
    0xf101506050c0c150a030e060c09120c0a1206150e040f1403180f01080705191b0c0806090c010c03030b0303070c082109030c01030c05041d010f1512 65
    0x42004024107010f0410240101202c004080b41c81c4d00d4541081d80d41c40000f0b41000640d6041c11400039400d8090f188003501c071850715981001300403801d20242c411402c68001d09000b2600780c0c1d148048113000380304400c0c8003910401c2915051080707171030b035514075030f030700c403506401441035048001216900590180200f1030710407160400f01200c2c00d0003003d01c0914800012914003a1040c280d00e010300380010f03104002626a54401036680c04d404603034400008a040c80795010410407849180d52125081c02d100742c803040340300d4100c601d03a071416006580d90171450500308600d0f442004030b00c1d4485054001380081c07455850000307010705c1500317801408140d01e03000700e14155a824000c44200a074040740d840500d9a94424141d15009507800140f90b89812a032519212400301040b40c200e4580140600981c0f000c40c401540204039140c000002c01ca0305000124020b04805040003150410390300c0a8500e61604492070302c44d01b00e5812074000c8442c10451007140039008007202c612012f102c40003146c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 960770260 1250 960769010 960769027
    0x3020906121f110a1d1c0602030402030d0807080619050d060c08150d02041125022106071101110406051206010305040c1206021204050f10150605 64
    0x111031109164200460003140e409007007503a01928103036540b100c22002449030411040c444a6079000e41c64800011030210038030f4a520981c04002c0300c0c1c0840000703204060a0300e00322000720300c2901c0311604139181030780001804251700e020850a050703064a03203018201490261401803071460083c00701401000000800c950144030981d025000d00006001c1c0d03803c0c200070b814084054082001902d01241100300401e003800003180424160510292a0b811300540369800e1200070103448442c40c038403100c180302402a8801c0700e461038019081d0030344c107035450000b40d0040090f402d4481c2044a8100541c401000c100e480100c1e1a651040d1541842496140000c3d001800340249140401001400140208203030f80c00401500110000034800304155449400640850700d090340c0c0035210f4990040d0800c400c1c41c0c0c0e5001072050510400d00542040c0000307038410920030003030b90b044996402141544600c03400030081c507412481d4040b01480303c40810070049034450018000c0108200c0c0010b40e154 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 960771510 1250 960770260 960770269
    0x10305100b041d0313090b0d150908070b0f0105040203060f1e060a0302041403070b04030b1f090603030e091005011404050a060f2010050a0e06040c0510090e0103020906 74
    0x886100704440505800f4440304159840f64001030360a00300c00384c0d0585c0441c0c40011845003010701a03015240c261500c400d0b0321241c0a14001780307800e04a95441c2e417540000543d4000250038a10301c80c2403545a5400c03c00d00c2c2d004040d80507004903000b41d106008200a50b615180400740040c0309954403040520a2013900048169000ba0303103401c0000016042c100b04d6255000b4003c40b16100c6800c258407641341d0400d40c480e000782c4650f000401041c4024404500403911070794106240c00036510003200038102c0c54107420507690107480a6640c4207410824182c104003075a00d46141214070200c01c0c42e00d40789040002603c0e00a4504001e100451003400c0080c10301242c02504006000c07407000b0743c0c1c6140013440c0f080341c01e11a10002c5c0413180d0b2101040249014940520b100c103010b0041c00c1844000e01005100040503041540d845000c0d2000c1c030103041c4100c0d030041d070091501041c03507030520046c0f000c03241101c031084041000d02172080206028a07030b0b50505407a81114028903039181c900024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 960772760 1250 960771510 960771521
    0x190e040212060910181202030d06060306082e0f0f06120c03260d0c02010b0105160b150409120207171906020c33070f11010e01110d050a05010305100b04 67
    0x40480c404400d1106d0b040e0b0300000a002c1c2c1d044480d80a1001580b56a800c40c1039807460f10078080c20340d104885114070310341d0502841c4001103001c010210300c805882291003d640d15a007001041641da0500380b020120b090158001500341c80065908030821b6a940044007001407102070f000c42c2d803181403103456191000158200d203009203e240d132641a414000d600602507401c040700550b20b031040d17558241d400360094800103a08031031440c61a10083d01d440e219504002c09068101101a4214009179102d20804520901038a402e0048296134074000c0d141000355048103100c428800742d140700c1041c00064050748900e0121031071081284514100c80a4040c0314408400c1d0701550490501d800f50011000c1d2500d400910502440b0210304a4512641402ea41c03210018540502c10b141060140030300511121020380001030701681c421081d42183c0300181100d4000c0c0e80003401203141945801404d03007040c8441c0003086154555510956a011030209500d0000c1c1ca0300c9410415a84580c0704 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 960774010 1250 960772760 960772763
    0x60f0f0e0a05130b0a0501090e040f02030109020a0b07050f030306060a05130302040216030f0f0e010324141201150302011805210607020a021509190e04021206091018 73
    0x103c03000402c00c444041e000d04035401c1e0050146002240c00a01580724540d03280456207500083c404d00d40743c035150413003410f41001d410307a0503640310085034006807201084c150081404082280d1202e4540c682a4185481490740c0d0703405500c14400d11000c1d0b60703034000300c0388140f0050400700c0e9208003000620081810300d80c4080e40c8944003151040704540e10b043d116205078070a540d0098046554142514008405406580041c086003201031255001e40c3c00640c01222402004403800907800c200c01c8104880c1c0c020300480311440c1c1d18800141030080b0541e003444900341c024800b108417500c0780b6120840b2840007904000507408904944c4140c080701c0d401400019002e00c0503102c100c030302900480340214503408039104100000c0c1c100c51000c200e40540a40c020500e1a8135022208150040d800c0402c6090f403003000c00c14071400e40302e09449407000415001c444000c0916150042001500b01c0702180141a081a0100000d5103004550041300195031040010324500c1b840b580e0102c101103880 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 960775260 1250 960774010 960774019
    0xf09130510060306140903071e0807170a030b0d0b070f0507142404020f0f01050f0304110901060f0f0503181009060f021c050601020c0901030b010302010801060f0f0e0a05 75
    0x80140300307580d005611045d0641070002c2042d10b441c403038540c1d80d2081d203001820350120001c43c0b5520004410001110318001c1c056a410807560b500d0310b1150071901c596a03100d04000080034814640c01d4000c14080d45000c8801c2d000d051195100c0c0046520024060700c100503a0b0422010454012030a81d03841e15000300001d5083c6851402c0590740c1e0688001d80d00c521003024602e050701d00c110250f00343c070565015010602403a101ea0030300c5103031900741c10920b0500c2001c0c0070300854213141402542c4110b001703d03441c101c40603c5600344003000c1c1c01038002c0070404c0aa1111915010b800041c0300100182500d000399403a51200c0c0d25a0314081840301c10380007401424800c0c1008000c0e40c105000d0301e40902010005082d059110304121b1003000910003000042100c0c2c1c4009980d2640712035400340040c01911900903035000091803119098004880a035445030050040d96403008802d4003500b010b08201c1d9540071a40c002801038443c01d0440810064a410b180905440b001c1807000100f00241 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 960776510 1250 960775260 960775271
    0x1090f030501021c05010b09040507021002120a050609040803040b0c07080d0c0206010602030c0c09040212070e1519050609150c0c040f0629040e01030f020f0f09130510 74
    0x34256010b58403103070756840302489139414040c49070700d507110300d9040316941100720b0b2a010070703407041c4000780400510040c294091004000407078000d80c00140840050380c42041414a0140b000310120740004c0c2c1494050b05001c0100f1000503452400c80360403d410481400b616900c1580001c0c461144810040ca041008103070121002c61541000d9068190780d000d0300c2d0a41c0e00d03240c0c00c0f0307a41d01a24100000640c0011501800c2d42018684240c019002401c0720f2014001c00c29614034104143e030002503080c1c040404c01000181031030300300d102035104803002450034100d0f80444203200c0c520302910b07220301c800055202260f41c4005400207010070186055459248041440d51251011080c060245d4201000e01040003214415202034465180c180326601030700400c1d90003402c00d60b0030b5203a4072140401c00403d00c51703a00c0318001d000f144039070520a11306c0803e1052245140d4420070650040c101c041d18000c250f0340350385002c1d5100f00449241c02c000e4482e410000d290480d4007016030105030cd4007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 960777760 1250 960776510 960776513
    0x90221130807080a110607091e121412090f0913152007080301150c080c030d06080a111005040e010b040e10120615230918030f0901090f03 61
    0x260052500c05d4444143e18000b414203684c86a004850210000c1c00c03003542802000483c142c042044c507000b0340900f10361510759440101e0780044403400c0c1c5850408101c140c0b0680e03001c20213015012100c20940342002642c01c085106101c445a0f0544208489030028100000c030004070082c1980203020015054a01440e0200418501e652204e0745440d00151200d2104100111098194006045880d607803800b00c81c50503c14000c13030210200321101d441c06d40400c1c1d81c500034014100f8503030061070340e854034036641000b11086035100511a07080302490202050003102c0072011008196000019141c0e5010201d91601c507d4101521460042c1d0022690810607406041075490041c2c500415866030b0504c5200004980700781d0780e05030014003840e4002020b41d0044070428191403903269042d915003450341240403469a407810070b600c1007040030f0300500d0210105500700342440c2c4231805140340720b0743d00f60720b034403030928240e1005c000011412456481890311100501228485c0d0300200d489 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 960779010 1250 960777760 960777773
    0x5062511041401051512040b04051618181e060608010606080a0c0804050a12170a020a0215100e04081204140105010609050616061401090e07090221130807 68
    0x3c4c00f40f180251039240041042140724030440b003030b00440a5541181da540c564880c40c4c00b240042084415008450010070307042005080d045c0a0440721140c0300804d403d08071020219131040030404001550002c402002c98004a00c2e07203841035140d0940c9943d400ca40c02c200d0003500300769028203102d40c81c250f0001921680002c03024001d55451a050105409202c0111001c0d042520042c00d9504100320346400107030640a02c590900040c1840c0d80c3c87c0c81903082c024054241100c44403040c54001a2504000b0703810f010f920149008602e84200f2424100089400b145681c000e03240204011340104081c440e40d0801e84006030141108000345140a1408494031100c22400d80550340c00c02001003002c50041d10013000742c410141ca5a41400380c407800d2500b40340c81480c0700341c40c9079036140b440e0700d4501a91000c680c040e0211480c0411441804081d0f05e11305034180c1c2c820700e4030744d1041c0b24202d803045460740107007074088181121510a0312446580511607d4444009021050005001040254 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 960780260 1250 960779010 960779051
    0x140f0a09060515040302090f07020f0d0f02150c03061309080d091b140d020d0605040c1e0806011202190608060a06020c0112020d06030f050f070506251104 68
    0x809070b0f10f100d45210b080018029a014600009500041d014000f840e04106600042ea0141462040b209840c1c040d09030903060010340c10141c0c0000d81c003840d07100070b01501000325080075002140752107424a1321480050031400701808151042c5480503980108004a401440b0300c82e4010249076920fa0341400003800034900540100c44801c0311911320a4001a18017062040f01e10a0380b08001c20160001003201c1d12241c1f107400c0b83c3c08880140b2035008144c2c0d9105e500e10452080308070794042401d04400d0213809103905441200c690555000f44000c000c003058203411a03170b001c209907070700c07281500c0000c4082180304900c1d07961624007800000c08550148846000d40d50541c0c81102d09900d0b040c00300d8413025079007641d0340885c1301d860f41040b100c1445d50040034031110b00400052610385903542c1f1609070566490940f0a0b9000c21094540550288001030041004540c941d00e0080c0840c90080b00c0d203001d0031402c08440041080f40140106c0f03010076030b41210010420880d12080300404031900c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 960781510 1250 960780260 960780269
    0xb090a05160f0b0712030b0d0506070c1112071a0f220501050723010e011418010504120c170406180605130b070816050708011503020109140f0a0906 65
    0x1c0d05000503504030f60364100e560741500300e10303580c00c28160280c064000e40141e40304c840e0411040b402603404101c05000482c060b841a585000303196040c0e041c002001c880c01a80c081c4117002c03007560411100400101a000c0b1200a43c4410580b03282d2803039041d403400746540c044200d0070300052510b0801480350b503004200c8417000761548003c1d1a000116528040c62600510020480c10300c00e80300c040b402481d800780407018001140310861012090709490074010581540496003044c08008255208100c91020183e002042580303411707115040c1c00da0800405005100340000c102007401000c5449c21401c404d00b074070240c3d4a13076803108010b00d0199602d015140c0d04124030800f0038454459000c8a222181499241495604050700c4056583c007106048848050401c0080007801c2c0c00300818913098064806050351174030b080c990f01d0075a0181000040c4030180074100780300503071b049251001a100402d030700400e10064400851305402c604141e0640c0056426000240e5190a402003400d84 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 960782760 1250 960781510 960781529
    0x14130212090f01060e0109020d0e0102160c21030f090f0b0403020405070807120c031e0617030405100c1e081809010302130b010512010b1b060907030b090a0516 70
    0xd0180b07009542221150b0042c07141d061410401080311101da038000e4451600074081c00a020208400c801d4220f91000030301e040d81545001c0048140f00494080300003c0c40c200c0c0340d002c03080c0500d0542c685202c1035440000d0a1060444c40200501e2244081001030644180d00001180d03c0e040d00310460f0b00140300403407089091500081003140f0403072803030f4002c0c481615041014684065840003404001d208481010354540002c0c20703400c1021541e604030710704504005401410401005c0442419001600780c80d03200300b10030021030300d07040e907908050b6580d032818905090302450705841518040f814001e0712900704003144107020440c2c0040914114104088041c940d0030302c00d002390070200b4400a584810791032242011044950801903469105240c071601d00038143d01507100402003a00010036112010030030f000d99540780740b1807640c00c456040043c1410300d400900d00d0390300c2455001c024410505900403c0b48540100a60f1020561140139151154000d581034114a8220b200b8800c51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 960784010 1250 960782760 960782773
    0x31603270b030f060f180604090c0f060e01020f0304090203101224090c030f030302190e100305010b19050f07050f010c1b120e0d11041a03071413021209 67
    0x1602c0c00c05c0b1556203840c0043d100951190703800388900e07108940100515002500c6040f001c00240b03010880401806822844101071420504000e1064500145507410b5600051482040103400401e0350304a0b0b002e040090703500d55a182e2440400e007410341c8035800c0c40d1030b6a051901000604010b8055110721105030f40803c40c221452030701581d00f2103001034410515401d042c8041a214500203d020f402810050319015030304805603c413034035451500d07000a0880c02c99035140d1070008540c0e81e100020b03203020b000e59410801c40324000d100f42280141c140c0400c0480000d00703030280080d41e01406421450700d45410342400c084c0e440c2c003910b902003080c45d460040201d10103400781c2c00e030700381e051404081c1145800150781e40d440da40b11001200d03418003801030342440d0141d40d0404c0410308648110f40c0303c407403c0b1001e020b01040d01e00360715013584801c0050f1074100507602c000030f20104076800711400c3c4c0b07d41801c10001c01d8914404043c1072181f00c2c000103c060031100040d64660140c0307201000c503400d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 960785260 1250 960784010 960784021
    0x110906180117071713050d0c0b0f0f07050a030608120d06091803050309070e0703060303020c0d03021c170414060f1306112206020c03031603270b030f 66
    0x2140048483c50040758040000d080460204004658080b940d80714101e01280c09481d4289050204802940080d076500401700c1041452240035410012400c800e90f50380c10060755100003028002e04210401c0800300f008a01e041c441e411450050078860140c481e1601034001481040c0e000f481000c00d901c0c104a00042d40d07200700d12401c01c00c0501c460b4603111442d0140d404903030f141c0c4042d00201b0b1b01c0c442d140c404507501d184801614040c009175100011428a1441c0290038000c4036554039101d8110b01d4080030209401240800e10103001c01c400d5480340080d0740d001c3d07c03030381c26510181a001d520b941c100401c11149a40f4400002c10580864865588120701d50140050803140741e241d8207800e00307401e030008817190000310b025480c01000c5400c000410040c036804100c0f110b00c600e000031a44504000d517980521095815481c10341c091464480203200040c20043d1304030780181040114890301004c425183c150520350b680b0449104007480d9030b94500134483c0c005852200d5400b40c0074020a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 960786510 1250 960785260 960785297
    0x60603020a2606060f0d0203070e0a0e07140c01200703020f071421010f05100b0a1d030708030d02040602150f040f0204020f210a0509030d1109061801 66
    0x712800b06104014609a890605020445e0090708010138150001c2c051325440a8203800903511031030b4030303988034020611004204050b4103082d61081040750002c0701030200f0564410712101c1280d198800c40d60780d03811042505401030038800304c4800c0d0340034142000440182060010031406010745d0842d140340c1c152960240d1600380d244a00d19100070131074a100c00301e09003803844090030414520f01e00c4901c80007111507030035100740061000c03c0740d640b1170800100ad00031000140207010b100115a0034000d0025001c2c0c6843c848072007500c540c040701404a14140e904000d180c0c041c2041c401501d07113801042245034044d4100c0e00646d030150140f05420500071054080191040310381e2000d0a0541d02c1d01d840e104c100e003c1841c01a030700a6001c001c007100e9220310304018920b003000d4144104001c03560491a041c000c4010f41072549150400d8140420f002000007030f01c20001c88408002640000104041000c1c0b1841d211160000c1000c5105221090003a6004040c0d00e030a807251a241c0605400c1da1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 960787760 1250 960786510 960786557
    0x906061e0f050301140a1206020904110c0a030825020a030905190b0306032a03060a1406010f020726010b01110721050f070503160509060121060603020a 67
    0x40c00042c41840100300a4140d103507202882c1c4000341071042d5030794a64403200b48070600810103580c4c3c2500040c5000003820a44554040343c111a54258140640000500d0300c404500074050100450720012800000c600e04003510607140c80c00103440908103004e00a5201d518020090b00454200c1d9030010790340c01c0158059141051880401000500f0003048440301c0e04050305041d0140300b0808028200290001000d00b0401510480612880c940b0b080602c0c2010081020709039500344404c00584442000d6802e410104c2400c191070100e03200c1c44204e150034007a034060181c2c0c9107082c00c041040034a50648614184403c03000307110b403a04150041d5403c9140040c91951540058010070561410030005901c1015822103891100f042c0c3d00c0b070b21320340030100d0f0303021180740c0208204000305c0c50104080420f20490b50814009145420001104444000c142034144680b5101141e942004a1403000080201d00c40c20032006884140090094100d04d81000c04214240131032403074440c104550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 960789010 1250 960787760 960787787
    0xb0f0a060819061e021801090e0a0203040201020a0b070924090b0a0207090f020306032a040c120c0807081f12060902151809060d0611040906061e 64
    0x2041e640740b410900b8200d40140380003e81c0c2450b0b407699405403500c038401d503440f152815090090703100e030140f001c6041c541d01e039040c840381481480301d002c00c00d0054503802640c0c0b0038400040181c4a0340c0d6400141d0a10700400802006941c0c048100100709170400305500c00da41c2440505210001c10300d240c0c0750514502c00d24040811040c0a04100c0404100020003941c60544107903902591380310521390694151401102074503401004014542c24200124031031401070b1070359030441c211001a07a190550408980034002c544079640541c001d80265250321501c40c001000704200c0b406108001c0034105d0a9130701d50300140c46080441d0380b2100d0320b82d201050342e426000d0300d500189410301c80100c02080c02e100715926602c40c40a003001d83e1b1105003540408900b129950b9803140b50780d03a2400308801e0740c0f40041c4280e000343c00344030b440d403144040d0040450f8040c9000400220501c80c2000c9801980e01c01880356041c090007080300d95100881598025a001d104c03aa40d0400d440305036400851303101c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 960790260 1250 960789010 960789013
    0x200304021e0a120b0c0f040909020105120405210f09011107090207050d0216030f08070f050106080106060e180402010c060f0507050a0e0108150118050d0b0f0a0608 72
    0x22402624103614840400700026070710128040c407250200d0300d807910b070780d1122083c40071940c1180103018550110652100100407218079160700f5500503003003030282e4042c3c040c2d80b9944100110031640a031080f02c0003045101d0155602c1d241901e030a079507591490401c000400042814000c0000080042c0c400040396188001c0c200040c0600448100b80902d0640f480f80c45030007000200c0c40024401418501c1c0100003074604200d0620001c0d00d040080354401215603002001000455440700d8401441c5a1242c021692281d05d8100001d070f07001c0c20303c0301134019480d11400044c0020154050402c440a41d1503040001b2506010820f04043c524907001621810b0300005d4015841058040c0381644035420014081b55602c0e4041e044410031100680071410001d9804001a04451922462442403074400128070748a1101000f8031012540c49042c0b0402108641803401c021405c0c00103130001804503c40c1c0185030502920b5200e050352007800a004210106180b5070b0180030300c1045e16580d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 960791366 1106 960790260 960790267
    0xf0c03030801121703070e040606021b01050304050a080322030914060c10051003080f0a180608060d0602160c0305011d070302040b011b03050d20 64
    0x20081e15618000742e4000000908800e0fa55844034144da070100e84a8076000c401780d0f1000c000305081580141400c1e000306420340c0c00103001440c00b401482c83d40c00c0c0c40c68500155036600c019200a0a2504103008040c003040010004542254012404035000e0314240c2400041051003101280007803088041044034100009500b800c2c0401110810324080b40d81c0030a1303a46a0310304180890090311a800256a0f40a0804440045800464107941e4400c0814070242c1c541c80082030f00040341c0302c604680810366035428071f83d081c2c603100e032a4400035446103001c0110f010580130040359915000c04c02568407201191100005610071080101c0c1c0e242149015801d40f0300a4032000001300d0a86e81c0842d004000191403000c0780c1d0143e900050010310880101e441300120401c45040072500c01e003a00406920070020014034801d184200020405c6100f4070085102502c0d82c40000e03c41132 = true := by decide +kernel

theorem cover : BRFrame.Cov 960611510 960791366 := by
  have h0 := BRFrame.cov_init 960611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 960611510 ≤ n) (h2 : n < 960791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
