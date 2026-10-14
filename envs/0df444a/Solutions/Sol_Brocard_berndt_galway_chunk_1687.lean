-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1687
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:13:45.459209+00:00
-- url     : https://prove2.me/submissions/27430716-5c4f-4bad-8392-51f7649263d3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 303237410 ≤ n < 303417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 303238660 1250 303237410 303237439
    0x50f030607050429120405010b100203190e040e07031a0c0d090503090909071532040305010f05190b10032c070501091728140a06050105040209 63
    0x442640ca441d907003101c40788a441d000b0784c3d002500903000d8210284281e6115160516100f82074503c80e201c03181c051004142c803011150380100170741340f100f040c954002080c030107036480481d1108804103580d90018a400e100050b80d510114525040d00d018130040341000ba0082040d400030308003107031150318404090008045410454004d100d0b594010000c0341d0a1070140d0000941d1000151054426640443c10400c04880c150310450120740240c1020104000024442001442019012018030418808040d079030040d0300c082e9405140c1240082050782041140580200b0041d01c14040003403181100040c00c000c280a02d002c030b490046e1203031003074000462055000c0d004261031007901c01a00300d00b07107145081030000c6e66007041c0031a0050880502e420b00140607102d00d0f4005500491031100c00d0040c40d800052181c80182401c001503a05401050803007041d03001c20000180071180742100a001000d00042101355a8001c502c108080e90340d5808000491181d6198990090356000c03800d007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 303239910 1250 303238660 303238679
    0x70507020409121d040209031002030709030f030201050118060303020d030509030f16060501090903021c0c06020d1e20090f04020406051b0604030801032910050f0306070504 76
    0x8151028002040c1401155107074041c407009904040c00050100800c1a800d100b1000030310861401078034214600700b04000407070f845015162455422640000114004510549110005607000761007203141e0815480c009010388802e11519070040c00c84031701e010a905503489036200706c0e641a0018103258400d01c3d01600501002002d41c1e20320300080c81801000e00b42c1a00400120650005e00c8100c0d46285c60f016040381d5040c0c121003165407404151320b000036000034100c0351100001801d40e070b408600f21002c80c0c40e1403200c08001c1c503c5002003490f40c085c0029400c12844600b5020900c1403040310196000c08440c0c02905482c07440c1c2d02254500655920340c001080b00d03002c040c00d40d40d80f890000b03021405aa00036807080c0c0005100160b001c0355141c42848850090703168a02910b55420151401096108107000140c4603c3c01d450b200781c43c5294030303101410302143c00c40d40d6084e80d03d00050b8540410200e442094040c40c980c6d020032690f850045a101d10403400da44480b401d003401c2c0300041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 303241160 1250 303239910 303239917
    0x1e08060708040605180607020a420b040c053a0c03110408060103020a24050c030d140105030c0303030c1210030807110103230406050c09120d030c020708060705 70
    0xd0740110b9185c00c603103d250103001c03161242a241d0020403495142d4074144424000da8942c640b40910161504032022042d0450704240074281c0441002c0d041c6041001c5c1e00400700801e0407580945000458400d4039048400783c081c42101d60301418070007484840051804c00001c0c3e5070610004074141110444440758444000c4161500d40003c0e04541900e00a55690142c0c000d409181c1c4510700400440c5828235411000e4860000110314104180c1580310030403e07604c1001e002c2c0440031a8058030740b80c0c20416900c04804015060064501c12803030480c4101c0280031ba5030081c0215400c201c17490078000100c0c1d001e0350a200600f842c02c0b0968100c07644080c00900001d401f203500c00b00010105011101074082503005a1412025800100000d011100900c0c80000c9000129404611921001282540c400d03042100801c40391317540c0c00980d00505c43c40a070142d0000050a05d2800883e0000750001070600e1034a080000c1405004281d0740c0e0070700c6106e1110140d00c0b2400142c0c0d4140b080c0040d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 303242410 1250 303241160 303241171
    0xf063309190608030d06031412040e1914010602010c02012307051303150f060302010c20060406090e070203040e0106230a0203130509100311030c06041e08060708040605 74
    0x44103030f1119111802c591062801d82c08a0b92240018424000702c03488030903c00f000d82e4020850440f0786c1c1c14601e511300607031003250601d91421000800c892040c042620070901d480c081001440c1d64520005400402801a60010341c81d000c401c0400d980144542005d0421111303410840c00c202003059801c0c1200100b68008210080c05400000038000038100c01a5214440c03402140740003002c2c4400300c1c2c141545084906040003c1000540d030402c0074400140e8120410720700c0740c4550f104010390007440011440d0084000100012403540c042605026900c40a01c000c00a481d0000c003207940780254020348002202d80c6d001041854061103401001101c1ca508518800700102074051498020610640250b040014408251803d808600b400751500311480b0000342411540c2c00714140d15404018424521102200c10541c2d080019011322480185115a1503440e848618454410164490003c007000c050100c0c40020100ea8144117032074603501c1d4101543c3d5038a410000d00406081c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 303243660 1250 303242410 303242461
    0x213091104050d0f060c05070512130e06190b0d060f050a21080a09060f09030506061302090d0614010e04030c08160204090b06011205010b07140f063309 67
    0x40000003126401011b541d07400c546c4546032980402e00304542400a12040941d40030001c02110010314014441101940d510050f054031035500c030703408070b80c902c6c0b80c201c5104d044c09440000094110100700042c0b06d480032805007803101c5c0b59a0b0300c680341800c0041c010a030780203000d00c005004904141094001e01d40c0c3d41c00c1d0007106a18103403690f200070340c0029008400182480410b12160350001c1c2c84e0062a41c541ca00321018518607104e03140c4a56010380760030b1003041a0384035a011800c141e0180ca1042c60001c118440d01251443e2401c01040901d51080c0890385400000542d01c0107032034158031407505034440c80c412003119519541298014203820101e101060a40c80158565108030380110303204103000c594604080002600c405e082c0030701c4114950410006000789190803064882d40d6601081c500c6902003801c80441c1403c00d07940842c8101d00c129420011031229000302c4980c10180c1a0008420007025080300004a1600600540200100f008141c21203102c24001e065a62030a6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 303244910 1250 303243660 303243683
    0x2090d0611070b0a1401050906032104030b01140f1009030803060a150306090b0d0218060102071706160903051f0f02040306020304050601080d14030703021603030213091104050d 78
    0x343c51241e9041c0940c0c3e4a940c2d2940c90821000a1402c00f102d01e003d410f0480780107085181ca600020303a07075115400c0610000350308080100c06483d03100c00b554051507000c0650303070407582c40e564100398072500000884c0c42074111105440260070040030082c100d55403541c1d51444e41c0c0c290b03103031026180e00142016400500520001820b641340481d4100e0409899030003180541c03030102c11600b0b4907680d41c07100b482410b200c1c40010040e580c150b000320803019031a12001050791413400507820000030b64003101c104c541d2400c5094650f280072412522903160441e00407220115400c0440ea0404540401042a4060300c003800744d01c0368103803401c080f60f41160300210f14602101416000e07a007240c0d004071506a00031081c041080001e1082c2805060898014503684014100040c1a0203481d1001c1d030001d24008049805c0c03a00c030340c04590070011040c1c0303c200d500c1c46525004000350321204008400c1d02840d68041800e110034003d0360101560680c00714145030a29080000314001040d080f9807614150 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 303246160 1250 303244910 303244913
    0xc07050a0306090b060103060b04121b08060403020f06010b09060c070902270405060904080706150b1b0708030a0f050d050a1407050306010203190c0f0b160302090d061107 75
    0x18044440914030a41e4045049440c91800c519544e070040c06190605041040c00e1040004141c04da5040302d5075a81041c180e03645500782a043c02899030b080d0440c2614901c0c000c1401c00c40014800d003d03a10950031109062001a41c440d21800d080c0114114030301d040051b070002e40303003000240c459030003c0c10035140000d580c1c01850341240d01c8400c1d04072840380c04080c80c00d030460782c100070081011011340d814000d43c034207000090f207020f00c0140010301c441c2c400b00c6c0c001d007848015442541da9a20207038190302280c0e19004240107503041940e240711001c01c0310030b0f0000d404e14080703040c0c011510403200075400c3c804103100995002c02d40000c42c00812a081c0982600d1410f140030340c0c0e005204826001480390308012405020f01c00080ca40d005203e0200b05121003a41c0c000b049448030b1090405088144084c1c1104441d4148890000b4010940030600407090241e946205801020020540d00381c408440406406170f00440480315449108c500203000400d4480e003000003212003442c03c1e41d242c60400e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 303247410 1250 303246160 303246169
    0x4030f03050d14060f04021303020d03050c07060306090b10021b0301090c090b0f06040b041a12070e033c15010308040f05010804023a0b160801030201080c0c0705 71
    0x742d240e2030000401201401040c0c18800c2d003441c00b003501901c00f03514000b0648c0300303403030f80090702e2200a004003600e22034401414030a00507030b42e0784001501070b521400c1e611180180504110300032143c071545041c070b200d4881c1c90000d000b8009034040381c000e4080605418910040825040e41894145d5241c0c04c50f240002c0c440d10460b005402c07409000107814030036505004107508654100c81c0038880070801405004410710a5400f201c07020701d1142d0320031008051104050140003000401c2ea0000340601c80301c95000041c0c1400a84241c0482d0031b0513400101074207002e600410954031402c40b000d500c2003480021400608094821401c85407030b11101d103000c0c0ba44840990080d19951808141840002d59a550200041c0400d01c1c00031410304007038001501d50146e450740500e49174030f503501c1c4450200181500854101003848a1410500d50b03050400d10b180e8129105201410b83d140031041582c080c01c0ca050503240c06035140e00f01951105014049580100629040c900c55800001140d503034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 303248660 1250 303247410 303247421
    0x1120f02130f090303140109200904060e01140909010c0c03030510150804060e03190f09090204090906060b0a17071103070c08010c0e130c030b1e0307150504030f03050d 74
    0xf003640d0000e64100c80314403010306e405040e08104c480c2818407002d9941d40104080344580418184901075a452080000030300078111540003050011702c40b400065004005103000300d0b0560b05840d07064140d501c10760104c0c2240c68045001e0301150740311100f440464800e500c015480544d807030719444d106894254100c88460701500e40710009110008210400c240350140b0348240710303150021030810200042c50113400103002c8043c0100112a81c045482c2486038044200601070900115a81c40d151244400a0805c00a0544d0010306140000a104050700c00f100d02c81c0d00c20365500948828081810304203650b01400c500200051090691108207007400201040c0b80300d42000c4104e035103442501429100541000e0b801c0c004880c203440140d881f507001d50920707000c000c2d00000d000420b4071820360060100022154003c00380340c07803000107200842008002507104504a43c0b5540d511a901d012289070380601d90000b500a010810000e10381e5034005001c81d00ca414210f00700034a10164008030388 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 303249910 1250 303248660 303248663
    0x121d0a05061803090f0f041b0201050601090f14210601120201030f0e0c040e0316050328050f0d0b03030d0903030b0102030c030712020319030f0501120f02130f09 71
    0x104071406114016090858114851042c0c10103941410b4910300094803005030b08a0050041c04000b82c40082d5039615444003004261400500c12941440c030f100038000c1c00c0864055001c00e03000000401d6000c904041c020031250b900b81d080f003004504070180b0020010410800c0240c1803100c0d030350600c000d03043c800749000c1c0200005441b42044580001400e480002d00c11802c0ba07031030b00c03880403044a0003081c411001c0d00c050350041529100890f00500c6c6200300c08003a82c50041ea07051982c1040800703c01022220600090030180307402030050b592804406c0d003002d1010420401005040d40c1208024000c910059032000500541c64004a0300b10b07800005a451002c0d610310284040541621030518640c03800e20046041800c011b010a0f0780b8445e5002c00781540c2d1800301c10503500c41c4200100d0f294400c81742c00421000342c03000310140203091141209100d280c10407001242450694a55403e00c0e42c020006a4000c1660b030240308a90400404503241d0740d17182c40c2520089106801601c2c10035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 303251160 1250 303249910 303249913
    0x50c0a060c0e040b090a0b0a08010c05030105030706020d0206070c0201050706050103060b030f1b0d051903111011090603060d0b09031c0c05040608090709050a0218010c03121d0a05 79
    0x8003001c9030041103140e20100c2c0c1442907140c2070030a141500c5a88400e46e02c0004071030001405860030000410085090f40508401d41c01c000b14054150350006c06141203c1040e8100d450651f250003050707840b100b440c002e2000690045000945062150440400c06801818210b1902065448100940750243c109585064039102c05940c181030410910401e04880030242c0922101000700300305000300041441d00c00c03d07000e04480140041444259000081000c2d9001d2211040c0340141c0f0800c45202820860300840700303540e040e01d50340e0150200485030303d9a114601261001081200c8e040030f030805403c90000000302001a48103210a80039800c4c850055840d00410a41c043c00128503956141d03103d8105802802c445800000303541c1500c0f12410310781506d965000e0315a00d0014542c0c0b0041c185070411f018000059004c1c0d00030400e620700010303201c8a0942c90301c010348180800080080c002014041111021002c0d0760101c0842d8040304d80707840602da81e00c070140345400d5000400b503905 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 303252410 1250 303251160 303251171
    0xc0c120d14070c1508090f012c0f0a0302010e0f06060a0b030a020904060f0f0519030b0c0c0a0308040c050f0109030b071b320d03050612060709030b092803050c0a06 72
    0xc00003005140c6040601400070320264088100312406895500d100c00722180540c5007114401c81c042c40840608280241151890be105090017400f84c00d200203002c1c020f016031000925003580100d4928070039400030380500560b03450429100c00990008160010700c541c203110900e65691940a15001400c040c90002d4406047c5101c80212803120781c4800d105260405101c9207a1444c100d0340d50480307030008501209980c900b001142140714150012006000c2c00300010105a0002c0081c0d010b54000c3d44110840d036100c1303003400700101199aa09001c1828040c040000400b1102107540c0304620345040c428030000e402803040c04405d80c2c202254038010782d20214030030802c92200340300100300507100032200541001915890b898403079a55001c16840718001151620340c0c08044400c5901141103072079603d4074a800034514441c90104031110030222002c03400325440015034641d14072205949420912140b9514071024402d00e90403001c0c01000d2190044070a020f00640c0038603402500301159 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 303253660 1250 303252410 303252421
    0x4030b191a191809020307051003060e07050306010215060f0604081b0103180f0804050909060403090501030509070e041a010807090609090b0708040201140c0c120d14070c1508 77
    0x1000d02d440c076498480410100002c024071116000b0916060b40103101c00104d036a083d00200e4209401c2c0d0708001d4210300d10755034880c0c20b694164004422035100525801440d22000e02c00c645a102c180c4805005030300c550a0011701c0600c0d641e0460b0001e500a00801b201403001340400c1607034100764042001500468074404048003136039043c0c24152000d02c0c0402101c02c8607400c03640717010300880d800f4200e511881449001c200e441c20483e0090900144880040d26050310300d01c0c4d5509003290201d00107165040f0008155005e40101802818124040c1042a05121105500810040c0155604a091000401c0c21812910359234040c081c20b9019084990402e54554244d07031075507002440e010700d400f050901241004518a4020100b440c124401d0b07195400101c550780b41d4800851081c0100103150305c056040041c011960080545804080c08030510445071034411075000300c00401d0310b007150300013505024002400e015114080081640b5241d5841019802080708a0700100742c4c204180003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 303254910 1250 303253660 303253669
    0x40f050c07140604021c030e0603010312020f0105072723101103040b031f0b030a0c0804050a0204110706090501060303090b130b0a021f0c18060504030b191a 69
    0x40740c0c0b407010014903884c01c05a01041d001d08003001d020816050032131980381018403074509591100d50091041d503c83d6183d041284412501e40100c4016100d200150484804103001e40c81c03180c0c219480d512209031621813401c0740e004c0c88000401804500170b401180004000c220000313201c2d10301d007030454102241c0080c8000c811054110409100c4c0600d01c02e461120300204a4090f81c2c44d0b40c482580783d407941200d40c0790f241c40700303610b001d201040c650011803c80c8071100510300c101581c060611441c07881c92230503244981b05480162054100083c00009410a900920143c418650040d480c08800c0d0b241e4000721a198181120a030b51030350401c0040c140e00a03c2c4001520000c0c2e00545088000000100c07648a14801d48010300004200502514028040010308081c40e80303003070148003420a07400c0010440f00c1e201d4404525078050b1010301c2080050303013005035042074403507514203400c40c2c4414180210040500200c445500d041d0700358070344503001d41c040c0031014240c260740584c0d0040810 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 303256160 1250 303254910 303254933
    0x31005010e070c0b06010309030e1008091c0905150f0f04080106091811030708120d0507090506070f06020f07031e020d091707030512030106090501030501050d080306040f050c07 78
    0x3508000d100f060b508042044010031540000c000d00b80000c00c4900f901e01503401d641007400c030035407205070494080d0419030450407541c0f14512031b038251703110000c02c0d1482c00c00b09a11945034a00040307442c50f0038456820410302d00d035102d141950182d07040944020b204001d40e0300501d10500782910200d81005049024014034001e8003102c01d00340088031401c4500c40420030420030143ca0f404220000c0e141e2520180b0404c1d000d050054182c8082007a010b402e011740e5031040c1d0a070b072044da182000180b80c040c4076402440503980d00a2200d842e007041c1d0f0b1108050032a4401c400e454a80d802c2000c20000c00302d0380002c003091846500c030303100c1000b0701c0a85860780c1c80014003618259001016085101d03584484001c1c01d42d50481d030108074140c00448100d1070144580c10081c081d100b03420b6000030a20000b00a181294032a0340c4440f00c80c0d0321600118151074081c8641034202150400c1c0c8000520f03610040c5038014006000000c00d0b03c01040c2a4090b28000e030b40d40c0c100a40005803550500c15034601390b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 303257410 1250 303256160 303256171
    0x200303040525060e09060f060a0c0c15080f25080115080603030412050a02061b0f0d120504080d060b0a0e090903040b03130506040804090c08160e0a05031005010e 71
    0x422030307201c0c80c000c1c020b0700c4e40c034070007810502c04c80e0150005003881e9282c800e8121890b10150070b96803522140c20000d0b100c444408401e0b182210041c6002070702150080f0021441d42250b99451110f442e00344044202c114050050510210301d0b0b002c038107900200030a003a29030420340e9201d999951501007140103620f0842403100130880c241042010030b40b400004c880864030f0f0f9072101c203444426070510500741050090005d5100ca0005002c0d007101d00c1307144a00046d01c3c07096003500c1030460901c00555540b90801d04403c085510144e148805000744c3d48a140e01034001d8240602d0055040d80c0f81d412194603070048050b4490104501c0c5070168404840c0713a0018007500c500a403070074100204c03039483c002c030f00c01c0100f140400000201000690320441c00c5266015085a4550a01d850007080c20740003802080c00c114038080500118500c1240034034010410180502c0c98280c068204444461090f4889034002044410001e45506d00304103008600b5000303400040c1a506001200040f014081d00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 303258660 1250 303257410 303257473
    0x602031b090f0f0310050406090201020f0318100e030109050106060801120b0c070303090c030f110105040e130c0f080609010e01050103080301060c020d0f0b060907020d0e012003030405 81
    0x211881c0c64468549080d0418011a81c0e4500b80f02041d00091421800c21144105542000d06003c2001140e40103948064400d80945030703440780c00740100c1e41ea40126024001d800034100407101c45800e00c03812180c904403561924900e60761a03800442d0950300d500d4011100c5a546400411a803030344208e11a000d04649070016814801585610427860313805000f480000500068100c1054042d62100f204a548070704061f007043e07503031304040c03c02e100a0002a901c40100f048503220b0340d84a2030407101641d4101c0300c1c440c00742d181c024401c1186000d401049404034201103021403058580c000460040a0400040c1250714001c1602070a4584500865480382e041100500000f06c0b500140d9055900714a40410202c443e80001039a4442c034900140c5514070417581c2006000768100407a01c144000e68103401141ca8420049a441821413444030005243d510004099807040301071851020001c011940c2e03000b203806800c3d0440e481520700711459409002c00c24900300581d8038601200f0100301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 303259910 1250 303258660 303258667
    0xf070c0b0a051908011a0c2401090b060415031d01020c0706022103060108070201021e0901030506120c044107021501090c0c12080114040b1806010c0f0602031b 70
    0x6c4840311010510441c201c600000401d8180c51a030040041403444d5001c6200c2c5034901e000034011881040c428042c0490361b9041011002481c10020115021209030a544800081610b4001c074024400000d4401c2c2010103c05082041002400078010341042800074100c0640b60540c0640b414103144800c0b4a07041504581c00c5039000f0307403019660b01120a0a01c29a03680d00c500e0102c0c0203200e11101000c03519810700401c3d039010b010901806203002e080e2001c00c041d031200000c1150301e210707011030141e4035031020000032403506182d00f00c601104020034800c4e000e2074040c011080c80011410a406e0111100c40351030b6a031440c0d403a202500444140098a90003030240c0c00114007150500441d5500c84e00c0c0c0602c0900b46214542c2180320640001e2112085494040014a009000e100d046410030008104614925152203883d00c0f48200600c05d5454002c0c50646540540340240b005043c00355100800f000b040d80e0940881600d03101d81c80060b5207190504050a05003400034a0400000090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 303261160 1250 303259910 303259919
    0x9030d0c0c0203030703030e03040308040b0301060e040b030c2107090e160e06010e012619020a05040e0a0e070b03060a06030903050909100503030706090213020f0f070c0b0a05190801 80
    0x413048421081c0c15103804200ea40d44011396610b1071040d9030004100081c0010001040c0c6001405141a80e030142c2d540480d4400803410801a101400c1c20769505800c50360314950140382c6198031854103294201d00144403048000f001e0301341f00e02075102200c0c0d580c90300c40341c1007208001e000d40c000c100198182460b0301c1341405032486000c01c1c000c00c000d0501c14050303414001c607030194800c0000301e4070785040c1d0242890f08070b0300e05500d0201600c600c03421103a00c0383e513601c020403680241c600b0071b0b0380e43d03030362038101031605440c0c000e40c075405031081c0c0344665102e801c441c02840c2400004040d00400100c29a43e0501e007040c040078139030340c0d40b00008251400701c0160000c3e40c4402290004003040f98640c0710b40d2a451105030702e000065000076072610000608400304085a001804528001ca81100d41d0f07280b1010801c0581c41418403600c0c1c401c00c01c00141d5401203e86010309100d1380544804075417682c6454041a02e0b610680000e0003056000c58585201c1501c9406210342c0c0d4074600d050751580d45403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 303262410 1250 303261160 303261163
    0x9040807080702040f02031f060807021b0a0806100e061008191d0c0103050108030307090302120c0301020f041503060b030606090d05121903020c030901030b0d0b09030d0c0c0203 78
    0x1a00c4000700052000105103041d90b0b500d07081061403a1521400315585c3c01c0840300f0204c0c2c18411148500b0301001c0400000d0304a001d1000f545c45103a0b243c0140150403501828518800840d22a01c1d5014480e9036002c10800020050303944a002440851025141807a507003402402c401061144214410102105060362011200e5000200754881c039944800a00c504006090800c48c100d070303103110a201e05415540300291480c00c0343c00c02c1e01c0c100720603600c444141e80c691108641140c04070301024010001400c00c01180c3d10f07041010015910135a280c41d001070f0981c0e100c282240e030034910104003400383c18010300140d0031201742c0d4181040101d180c420036013558040148814851b11000c80c82c039240b5111000915145079101059844003400c402d41802c80742c00c2084c180303040703104003141e001c50385000e88200d0790400b0034040103504180005004401608e00c03000d1540d000700c4000c103010001440c840e0103600550300c450143d134a0b2601d40c0b901008032442050030324104040c2e02064005601d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 303263660 1250 303262410 303262417
    0x6030305030601021c020309040c121a011d030604030503040507030803010f030201030b0603040506010911040b0c0d02070501080f060907031116060b06070213151517010e090607030c1803110a05090408 88
    0x1003901c000c122b0b800700000580b910701c00981140082e40c00d01e00d84840d4400740c2840f20203c80001d0f2180d080c0c040c017081c03813040161412809075030180d016101041c040390244000c3c2d5400762190381181c607003940383d07500c0400c0ca400130391014030103c0781c0756403c0c0115a054050320301d2440041d5452811840d05480f107aaa8007010710400d02c4c403591700c419400c85140d480c012200034080c050310999469000020642c1d40e10009088900103000e6000c0209256101d903015a0040d0841013402080e81c450004100080070003070020001d02d581c8a104400342e4031854060041050039400402c100c40960030441c1c140c0700907180d4184214401c020400041e511525031248840c44104000b4101c11104101c24008c032243e00015100f80342c20138104002c0d0f0f40701100035500c8a80541c40907150340d03209022000d1384003da034071580031f4100c44001180e5605ca43d1040000c00c04c18900040d122418070100401150290020390300610f10511446d044d09001048000400f17041d140000f051030300d525540c1c020302 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 303264910 1250 303263660 303263677
    0x22090c02060c0c1506040b300705211005040b0402011e020a150f0203010e090c1f050c0c0a0602010f18020612042409030e01020a03020319090906030305030601021c0203 74
    0x16400300100c5ca00e5190395200303003c028070103081c154501702c4030004609a1410f24040305110b81c07020700d40f40400030000c28020200c4802815400c0c0f442c2c4c1c1c4441000b0099914152045584900e0404e030b80490060301a16025501421030101981080e00005102c12018015001c0d040400c4000c2c0c0c4404e0fa0001e207040c1c150740c0000d40061401c20b840da104c00600190760f032201c2c0090000c8004130300412031a40050048204200f01e0351046500000d006a0704101409148413004102c661204140104002d0100e07660030f2041d80c3e40a05400001210440f040c2c1200700140c0d580e400c0d04c02040b003541714811030f084085285080701c0b42d503030307000a0940c8070b06520101503103101e80120f0104500c0084182c1507981019401000300b00e182c02c4403005180541085e800603611032091212940003089080c00f8a4166000d03500c0d16001080b0311440c610078040f0305d020000b80c840000341c6203196100307800107507109070f03102c035030700c0c01c000c00021300d003540100170300c1c0110415584046840703800004644409 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 303266160 1250 303264910 303264943
    0x815010206070c0c17010510120201090504020d0e0a0305031006021b0103110c010e010b2d120307200301050105090f070305060105160b0714040f050622090c02060c0c 73
    0x4003a0711300800e0300350083e40070400c1101c20701c0440c00010b406400480c82050a0712020000940c0d441854021181c500b90190101d00003c50903c01401e2039001031100c890340036030214504101d0790440b490b0100001003980011404401d2141c0c010806083d9001810240300400c03c09000aa561a20800400580d4141581c0d40042c0f46600503010a0f118400d0a0b04000c00c01311001e402c1e0340c0c1c003030103401d04040c0c803520b000c5000c200000c602c8912403005546d00440100c40c85101814482c840d058080e0300c0e541d41c8818000040014400c07035232211505822468a0a8440c1000134035003501c4041e00034500c00e01c110010000c841d03015000581d4020014900484c454541600580d42c520859009100303140a071840c0d00f082c0090f00d191039008140503174420002a4041e004000e40340210700800540700031151701007040c0d00c1c1540c00b03440684818070520303941d443c402d940c08510402c40d0788444e41e0316450702c0408510030340601c40309911408008a5510b00140080f50381e450383c43c0c12599a40e031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 303267410 1250 303266160 303266177
    0x5060306010c0b0411030d08190c03060f06051b0303040201020a0609020a05060304061a0f0a0b1806190305090c090402041d030a030e01050912040b1b030a0906081501020607 76
    0x45a101d156032a00480d0441c000c83c4440c18541006010041d000074024021303c82d5000d9601f920f8850102d4520414048943d107046421001e0b24074040d007610120001015214500802d044411610b94001022541c035100c0c1d9565000c00304100c030a00d10542213000390014020000586d802044038408250f00c0302c80000d82d41800d1000036410741007a00300c90f800440100821040200351303407009603051104111040342c0001c013801c07c01c4ca0040b22040741d80007815180300304400300c43c07a400703026401c0c0c1b969156801700a00704081401c941081030300403100d0007000c0070007280a8041c4546a04024007001800100142c038011038402c07100500300078041d276502d000d880710404400c1c3c0781400c07000e520300640f5a035014a80c0014040d10117854444015443c01c808100366001c0000c1202401504507081d50509180240c01d0146420050b036403d69001075a0018090540a100400c4d40d1002e644034843e42034107101000301a540d0040c00d01d040354603130307020342e0117039a0b00080c1c441d0344801c1914060b0745 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 303268660 1250 303267410 303267421
    0x106080715120c080619030b0a140604050423030d02070305120903070305040e0705370e0a030809010207080a03030f1d070504180501051515040f151b0506040606051207050603 77
    0x40b003050b07c0e4000703032400302e40c8000d01940510980129081416070050325410b5180c81c4100811581d040c0c400034940c803060482900d20400c40081c00c0c21420600f41900d080405d0340410000340d9204540840000b100004c451010704070608034540c001d03d03520000c50400c1e0190351f001c1d106228501401c00400c0001000452451148085602012025140b14204820301c0704041c403ca1581c841c5440120140600500083c4103c41c0e0a5203607a0040503850007918680382d0001c198842200381d411805420b83c0415004d401300b10840c3da052013540c000074548103241518044440d10310201001031000294610407000c0002c2c080b003070f9030044500046c18910b0840620042841101c0280103500700303000c20114800d540022000541e090701c142280051619031a00584550300030000900540c20b030510100380c40203403501c5454400c0c207001c421750740ca5a18480c15100e0004044540d940201c08110070450b103030050703070300030302c3c0c03d45092036150300030070b46aa15400b2034004e440c041c0c5004000a01b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 303269910 1250 303268660 303268699
    0xb0a050301090f05210f030a09080c0609060a05090a200a030c0806010b030402060d0c1202181009050a030201080c090d0803010603180c060c050106080715120c0806 72
    0x100408004008000d100140d2900325000c0b84121004d54850040803207203020040700365528940e80e001c80f0320303c51610803c04c02060442e040036084009040e643c0304400001140300c0014241c071008600200343ca482c20750b1080703141400081046c2d81a80c00c3c101030105401d000181c0c41c42c12540940f29200600421100401c2c50381d00342c220380e5006400e45400800d10242c0c5030101b05864046d000d5618503a00c03070000410900c0203903030080d0022003c2207600b00c1804140c0c007546e00000a8074196400c0c103203d09814040e43c000c510016840102d007100700102e40750003980440e901540d420400b00c000c2c5410001181041a48170180c103105003100044c0050000341c0841e074607003000504d425404083d0341010035081d0800d0242c0c01c0424a014504846400300300c10410401e60b00010215205045c403800312039611066500715841e64943e03101052020007070000c000a0030710b054208850600100d401032818001000e124240340c98146440003035139100001c19070200b010340d2080040050000310310b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 303271160 1250 303269910 303269929
    0x3080703030b03031803060604020405150307121a1e0120030c120a120506131d0109110a05041a0f06040e01060203070c090209030a060c050717040303030c090b04090b 73
    0x998140000202050007a031840154400c5a45c1030307081b1803c0350f0725103003071100724400d9002e041d030b0003955400c652240e80d50107402198800802c0c074044410018141455082e92540507401d905031101441e180090308100030104002036240403c405065551030001c5c0ca10700e131010421803040c1202c2c1100ca407036002001140c03c80007500c011103010148280e007607007854104190f034400040c8540301882040815014844c02524001c11758284070800d88092401050307201890a1011f22180d044100d4820030b2040000c8140941002c5149840c41003c1201c0c003415600154869451b080c0007142080700400175240c0003406030703014001860007078002040da0099034850340700000c84030008120b403580031000d0030140c0c0c072801c00080309a8a802c1c00c04103900520750700300e0300f542c8103440c51400b1500e107801025154045040c400d00c0d001d0f03143c0302c4800486078116141034545002070201304040e0306120340600a40c040c540034250710b080101e84485441240f14400c040c2c3c0d1101001c0c011941c941144 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 303272410 1250 303271160 303271181
    0x2721020a080403060603050712050705010827010e0105090d120e1606021506010f051c2018030c0a0303300e0c100509060d0609090515010914010308070303 68
    0x1d803501e90b80c0d80e00d0001d010741072034042140e49004080000030b400c0311480e0b070081c190f035202c00902401d81c00c00b401181c140100810704a040d04881030003002c004035000c0188004441a0004207110301d05540160030340d0342c0a40500056408569a86007040d4081c0c0081c90000441d180402c80111006005103044810291070700001030401001a2454000808110b00b0111380080c0640e46d895030010340d034540305050700e840480e8041000080800d00f114080101480c21031001800c20b0000c04414144501010355082d002e0000880030500c0c1c2000b01c40201d031400c100c0044c19410000c40108440902e58031004052007840b42031125450544500c40342600c0c204a084250304e1170302410640079040c05050b0f05030314004d0004440c2c0310f00b020401c1a20300b09080e1980342c5010300ae14144040340d40025400356019a0f07a01c0c0128480099015420149004500400b00c2c426825000440818103900800c286490080e4040b15130a41c0000740d411a504218500d0721000982000e070054404240c0c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 303273660 1250 303272410 303272423
    0x20906030307080a0512010b040b030a0f150f140405130b0c070803070305160c03021924050403080a0204030c060f030212011e08150412051204062721020a 68
    0x50380004c00d9881805054880e0940b1203843e540d036a1041d190101c3c0c802c074018040d0140040001030808401904040f002c0003000c0c13800126011940e06400402c0b02603009401d100000e41405c2101c1d50762201e10b110b52400c112000c00150400040083c003140e100c510003806000d0300800241000000c8040d1644680c1125807070782c0d2803400c840c0050040004076260682160303503c14100150b480f50f21404074a95064005103811010200701c44a44500740008644049205d6141d0306250600a41e5441641000d9000304460800340341c041d0001800070220384045105201c1000841d0348205120200e40e042d081040d00640b5111089029114440c0c10941c190780540001640c043c050300d01000003140000d45c40d15058552108a8a4a4400b0341002c01c07034061401090108180210441d01e4910b42c1c18034038685600700d08080c412210490b42a0b0f100c03070740c8032440900d022602a80841002c02c0b06031682050301903a071359011203001c50140c1c0e444010202032000000d40208440c0c500c1c182c0201 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 303274910 1250 303273660 303273667
    0x12030f090e040c0e070810030b15120c0103052406090604080609060103050c03010c08010b130e0c0c070e06011d0f0409060218040c020d0c060b090106020313140d02090603030708 78
    0x1405900340384107100325950741c81d88000007020300c0c1c41801c0090081687c4546d4444c01c9140da19107103000710b40540b20f80d0941800300c032030310702d25a40c1018410f00000d00c4006030a04240070303400502150001015041b0090a140320750554000242036005010000c44216440c1c60036640401c0701400399802107062407203060280011400b00140f2141201e2142c4203c60000070303200e0906090320000d00d01200071039070550040c88a03240a0029003042d550b0610042e59042c2e07900e40c00012840213444064140f480014500f2124006000c848064280078800b410340c1c0c1840400204032046003040441c1c400e4240b41e032800700d5968000342d08100c01c4020402e010700400d60802c5402035000900d4144610486400c6003944d003024060000c0c0800035402600c0544041d0134161142901c81d0f404450103565600c2d000310b140d49001100340604116401141c9603002032541040d511501d400030803256000d00402c83e1503503a05101d00f507160340c0c195108150f540390700340400c0c554014010010031603035002c03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 303276160 1250 303274910 303274913
    0xa060c05070f0b0f1f0e0a0e031902160b030106050901091701021b07060c03051c050f040b07140912030c010c0c0c0603060b0702060a1115011d0112030f090e04 70
    0x210246000d16508100c21307240f40c0700c0250380d0130398541038002c1c0b04810311190741c100710240070750310203e03440340f4001004140d00810b16081401c5500003500110748010510f5000300c404e5040283c0e09003100c0d81345424103554101421416180414031070f805c00c1240019245100343d12820700c03800117142c503400d8040000c0c81148968080e4110304141641c01c000d07050112198040050040215006a01d411600d140503403402c03511703603200300c51604030081c90f542c4c080391180d140c1c80f88a118030007400c0d544001c1e04192a150401c803201500b194100070700c19008601c050f0288080715182c0c1c8003110084640b45130b20350407a0035806200f1a1a209518058040100c3d0781c0082220120500c64410200a81e407107440550444045004041340039400b4041d4200505140005206003c2c1500303001c03545848000d261441c1c06540c0030000c8800020000402003104070090760103071500525042072180d0304220450301100c40c0c0110190400584000840020b40581a00005441d000d5024080c1c1c0c13515 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 303277410 1250 303276160 303276173
    0x604140d0b19200412030c0f0501020405120303271203010906080c09011503050406020708181f02060406050a1107030c020102070902030c12040809040e0601030209010b03090a060c05070f 82
    0x410360b070b80508101d0050b80c50a41e030040001c82e4040d4290103420141010780c0401c948950031301c00c40070700c071441c60b201020070460321825140c21311802c0056071300c0d410b000510510382c01326030f60f001c00d551041c004d126420b10b550a0190051105c80c059808084403007100d5880c0900781c0000c03000041000002041c0c03106660000c5081c0c40c0001c007251024034200c01803000d610001d01c2001c690010208024802c10720a401950300103004c1c4070058180030903902c2e02141988860000300034060f01c440a01151b09100c4010081d850340655007125055141001030748461008000600c035550360000240d2401c990ba000654a0408030b14580c1c03a80000d1401401c0d0380c48462040c1c0c09481582000140f403552402106c0c8904680c407920b138213056218404180302100a031003120569400c0c4102d02154582e0304c2034080c03114000008118a52440c010b01400800c1a001060040420020040003040c0000c085144d56840380740000c4040312111b04803101d000c0c2e0704005103465200c1c1ea40505002c0c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 303278660 1250 303277410 303277441
    0x60d0e06090c06121311040c020c0a090b010203040509100306060b031806240d060f1512030509120106030218070206090601150c0f020607051612020604140d0b 70
    0x60345003282c0c0142a42410007481d40200c4840c9020141c400300002c444080d40382d040d2520701c3c880c14905804030741e40303000181902da081d410500180d0100c1d0429925140203c00728009000c0e00c04108441c941c0072000079141e00c658000c090160380d502001c03507000b0050b6449030000b5500103030100001c035102c40f5840620340c41980c03240c2c5401005456600340d105e010072041d0103482c0050200703050180c0805901c0c440300401061942c000b01031200e43c00410268012a103040010580c0000d802d90b020001c802c03201225041214803040031041800040d402000b11009500300b21803022074024509485409050b0540009400441704000c4940340c1b1812202c2a00503d440c0d001d854096aa84400b6a511142413084040490200d071205039651b014003001c441041c05900c001d210f80c2030301c3d004103100380d0040f001141ca580c810f210b403009481011000c0c034042c01c1c40b600020300c4100b060f00051228011806025600040024014219a80c506241c0c4003580d014821201d94a002c1025000300ea4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 303279910 1250 303278660 303278671
    0x8010614040609060807020f06090706030f0203060603010e06130c02061e0f0406020a230406020d02060c0d0f06050d050c09101d06030f07030803090d210b060d0e06 72
    0x103815103088501629030100781c0e42616074594542c603a040c98110102c402c8440074003803506600131406580368230301c010b0021600c16101c1c5d0000300740d070924143c0010120b0368900407101c0590320520611402d6690481242e04480300ca01c00c007103981c0c440000040001a280048012203454164813102203500841d941c5d2250001c440fa6200100c600960803259080494443c8080451040001d0005003542d019000400141c9046481072000d095810391058480c80740302003000d008030b02007105c50703410440018414000e102410f52400e1800c4000034038040c440003200d10b01c0e15220410804200742d4005001010b00406d891070791645802c0c42c6440b010745015040c001d146e0392001032a450714952401c01103484503441d40a10000003061075030240d00107016039516010702c10703107849090004c0082001450250140c5503590a01034585440c105c4000300308005d008410380d034140c240d58030710000c2c150982d608101040c07400a620000311144503000d458450a40b43c95034200c0151000a4218442d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 303281160 1250 303279910 303279917
    0x30c0604030f0615141201020c0d0203040801051f0312140f090901050418030c051e0f070f1508041716020a050409050a02120c0603040b07080709060e04200307080106 73
    0x20802c00c41c0340c042d907130b10600580540050184560b84a824507040c5084a4180000010b042103000109035041000306c0000c040160f1020030144203041080c452103070058911070a52051400d4820f448620403801c0c4000b800d5001070542c03035101c19000316400c1c0c070139130300c100d001c269102031183c0714640c1504040358050154841c0c10000c038141c1828490600001ca92030801000880140c1c0c08817030b000341d000c4040b1418012600c1061007200e2100e004000c030b417140c0c80035140c1d00003d455007031318102c12984081d6450780d0000013000340d0100ea02c54031035081e00c04d1604110300e40d510f08103007910303104c8050b4555100c03a002401d4581402140c0039020214801c42d12000506c0c0d8881c10041074801000002d403164018580160040c5050b50801010154103410f451035840da00d00000c02e42c1d00102c0d81903650b0145a01084842980f1007032240d0f10002ea4100900c950303007890802007504645000b01c0d40226a98030a0f24800085250010b80e12003000b00940d030303a890b01342001001d0510a00c5001c021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 303282410 1250 303281160 303281171
    0x12030709080d0c020f190b0a02061e040b04080a02032802010c2604050a06050f07031b14031513021911060c0d020c06090f0c101d030c0604030f06 64
    0x800740726014a841060300101400c004904510822030503a60340c001c281d4600402d03000010310304100102230001c000307281c1c000d0001407801080b40302043c804000d503420101c1c54001040001541c0445240d0080e030050103040d1030f0700440703d09034a140f00c1e84260000e41504400c0e0003400c00402d50b0200c0d28502c081d402840015210101a14140500c012a581c0000d0070a6801d1074410108411540140143c0841c0d4884620783c5580701110f001742c912902d0f1180c24410007160b00e405000c0c10b01109052910801e822480000003002c0c90401c100e0f03808c840d44e0010101d856241d034030007011418000144004c3e52101034911070030003580282c61582c0c02c0e0003088003080c07005016848141501c166180a45015034850700503c070705501407103401504039820701400c0d620440030080c80d440740c00c88400610341010013001c0e040c034040b01c1c011030074840c420745c000060100381e01030a4a040550b1525400c204180c41d080002d042c15800c40065405c280041000005e1141c18003409807040d0148108010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 303283660 1250 303282410 303282433
    0xb040f2109080102130b090f130506102a031e09180b010c06090507180507080a05190b0d021807030b100c030522090b0102060901020c0a03111203070908 67
    0x280d005d20540e03804103034480c0004019169a14004181d9990b0040254210541e0600041c2c0348860000000941d6a80c4d802040f1583c2090310f9400307801c900c2401d01c0e83e0300c11481c06400140b1a08e03d032078001d40702420041e8000300342c0240c15407040e6500d403818002e040500100002c0004c99244503890b1380744400507010661280b10b21480340450b0040e51001c24000d06503c0e860050102500111500c0c42000400201c0c000c041600e909600018240400c15040c4018000c0941d10040c2c4005101840c00c02030003110b000c03040e02e00101d01d84100c03001c5412944507001071010210b108000c0d40012428008901d03503400240210711800d11600c0411100d003543c0f0070b00c1540841e1140d2440840d240c564000c01003030080303003d040c5041201c0c0d00d01d402110000b41001c0522059071141a030f003900c41c43da80d039981d0307014025241c0c00903104000b113080c40c00603500e140e1344100c4403102509022801ca0400714069050000c0c50000451b40307007076590307424121801041c4413902d109030500d81c001c0c850f0040e0f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 303284910 1250 303283660 303283663
    0x4050f040206091002030c030f07030f0305060f100905100801061e09060813050a0308060a060c20060c010c0c11030303190f0e0f0604031b0503070b040f210908 70
    0x24062900600b00302d0800c080c0364180408101c50610540642c4001c0c4511005d011080004010050307040e0344c0d0f541c075003190340f40c05440b503851094081d06050611041190684400b20802c800910441d0880424092094299034051080c1c03c0703c0d03008951a0f0310302c64110303000721002d4101d1368188e0342c2c0200e40c891340c49441124140c140c5042d00081d41140700304869440f8601079038100b4414a842ca0456125960709841d054207080c1c10ac020031108002c12016151011001004140f40e0820802e41100c039074a00414040125800400307a0400a40d9400c2e5240c00061303c1048900a008000c01c06418a025002403d421401c540f100c964001492080c20040103990103040c2c40904000c20b500011884005001c02c071403c00d0001d5501c000709100107008100c2c5288014812019007200d01b0b02d070030001d01000c000905415004061031031480080c4001003110300c4542c015092601070b44851a10109055203c01c01500f07184030514a040030064a00c110001c4210607210032000e581d56081c0603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 303286160 1250 303284910 303284941
    0x90b09070914040506011103160b100605090409050a1a190c0e0907050c010f05010503061302090f060a05060316020f07060c2307150f0507080f1e03150405 68
    0x180b400691404051500300f0750041c40c2c11180505150031540b40d82c2c220b807491a041540703a0308a00c4001c1c0d81080030702441d15032894200015440310544c0702c2c01c0c160058100e210b2102e04501403a6512841410700009020f10408103602510b100c50070030001605150340c5406841082d007421003401500000400b500c104070030b07405070761500418a0020000c20040420007418601445002c004140318140d080c4129002040c100200142d20f50600c0145807030860001c24542c41207040b90714000251303482c402c54542c0024180034102c515690710002c9504401554401a0003030008014002c2865600e0f100580c0c850982c1e0854203e00c5070300100550300d128074800c0c0000300346a05090301c08540c0041000403800e03c060854400303e020000c0c00f5180190b030350321a010035041e1690035050b80350310064600c2218510321b070142c2060301035101c2583c903100310412100c03021760000701e106001c0c01402081024540080450f42c80385840c00b000c070400709100c201503124514041c0042c0300c4036083c0002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 303287410 1250 303286160 303286169
    0x311070608371503110307120b15040207080c0d0c02221e050402090c030709140d140c01090b030c0301050f0a090e0a121b03030b06070c090b090709 65
    0x140b404009814051a80108070b0031048035110301600148110346194010703060071111031241c0078695851170520712130a558100e2400e101c0d400581c0208102500594004500c940110030780e003090b21111801040c050380010220340160010801d47d040c4416034010348807220071003043d20148113402c06c0450b0710315420740d00294007941851800e03526510f41c001c1084541d8101c1c03800619041d09407007003500401940090030b942912036040004600700b10800a4200083c0d001560035400e00080143c0070f0030f268025800d512803540804a810b40d1801c00703562a132908805071080c070350300030100b00e42c42c0c5440c002c1043c042100c01d10001554920b0104480c410074001c0596400e4ac2d007850104440071404044065015a07001000f14056007144601c1003289440c40080681d40320307504d00241d005503c00e100c070382880840c0c8165010f00034071118200b0020f80c1480c000800c44e8003000040d02c64080c0c52005080c0c541580b9010880c441c091b07000c3d212069080302c0089140c0c2c1c4181040300d017524680903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 303288660 1250 303287410 303287431
    0x907030c08010506280902040311180915040c031415010f0833160e06180111031c0603060b0f03030a0302130b0307030902040e06010b040e041403070311070608 70
    0x813004200442c1c03032104840c90105c144900402541c0c1c41d0103009a8101c0c1e0401c1c1e9003807025061042580c036010b01c1c889840200b01c11545498680107684940b2000741c1c44118a007803c014001504204800c5501c0010f10391021417107800025601c0500c0d036a07204040b507045841500000482d920f030031071200c0404c44480350001c0540d410180c070380781090150201310b00045000502407200100c0c10500c071030b10411520110103003210407150000c01c990720001c800c902070340d0200f09520071041e2042e65030111303a400303082807007501c001d10850350319600c18007001c11145c840c0403204025107003c5030840700441c1e015400c01c0c01500c1e40301c2c08100480b60321070a42641544204182da94190017900a41100250310b03801411007580c071085075420b54411034915001950b600784810861506104084212200000600c1075605141c00e1401604c520300888a8031002440000e041281025800400301c0902c42901d4403111b4078a4043c1145580706c0f10094103005521001c2078552103030510380d1080700d1500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 303289910 1250 303288660 303288679
    0x621061f05150d0b040606051e0415050a0c0606080114060a0605090d0c15120f05040305041a07020d0b010501080108031806070515071107060801030b041b0e0907030c08010506 77
    0x380c48400d00e5111402c503c400c3c646a440d0401c0c199194400c0703800401c2c46885240c0d03207030030300c02201140c29481c59036a00d101505210620403140111003d174010717101e0303041c41e55862042c860162540b001587c07000b004113080500c013003008101908500c052481003e80c00105440b020100f200c400168024000003903414403081c5403500d050700740b050920303008425108503183c813010110110001d1082d50008204044c80139010750169201c1c075407509028081c20001801c250f900145903202c1d510032a00ba11000c500d50344220a41c520131034510b01ea005140d40010040d61400b03103402c240c241b0885020904c440b00000d00c3d00004812550807083d9004201d400038039100400c01c01e6003080c80e003901c481c411000c4c28000c25110600e440e0042049440b0032414400b0041c00615084882d0008001c1010f8100104000740784009072941040d4848400100800413001d10034001080c0d074001012841c0c80824000485000b140c0303582541c1c051035180d01c480c2e864440c074909940058030401e42001000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 303291160 1250 303289910 303289939
    0x1b23040b090f040c0f29070312020d021c06080c030303130b040c090f0e0f0c1e12030a050903011a0108040f06020c072d030f06050621061f05 62
    0x31a07007240e11600c41d9030341e60304480e100c020a006509260700a0300598002c44006c43c543c40030300718000c400102c500081854220f00c0d44c0c000b8803a01c002a4220610b42d008682012245140d4058a1016241852000f0010000701c001d03400b03480140310707503001c41c0110a00d00d0420305010084072720072036800d800341e1201043c6075110b034000c000c0140152000c1000c81c4020800c81e005006054807005203240104122148401d80e07428105c12501c294015803015007001000c0d102c1c00681611040900c0c40c00030300b45100b0021421850b03021040040d5400001035440744250050080c0c01c0d440d40680007003060181c56101120140042c8282502042241e000640000c0c90440445c490701e20405003d402c141c220400c80d440d011954004505062000c03030360806400c90221400c1c03550143e112580c54481c035588403070310b840b840020043e04080d01c0301300280035a1200180446400d0b0030420b00300c144842e10305800e40b0b841096400c00008400a001e107481c84180e20340303100c10394400812041d5042c0c0c04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 303292410 1250 303291160 303291181
    0x5311404060506190312050f030711070504020a02211209062409040f03090e09100e0c0d14030910050d0e011406210d050c1603050d0c1b23040b09 64
    0x11b038060000b00101000580044141c800c083c502803801c83d12a980b0124809007120b003800ca00c2c0c0c001c64000c43c0306010680c4403e03400110200c240c45580000c440e62060044402410b100308141c01451550540520140c0900021164071803001100c1855403400c02c1c506584508041100c003d500400d10713400300d80803540051038000d00034800d040080c4242c2d41c0d01540020542c0c110380c04080c1f41c00220000c1e188100c54012032200402d07000240041c0c51a940010b07840324403110340604110342d100040c2e40098000c0003160910580101907168102070394500415079400302150380003d0303050407140070039480c05000d250341145500c400345000356036003424000103002d11080d45400010b10742c509003030014140001c5401850b107580c4c00f599441d12102451600f0314504400460070103008041000c11004a00141e03018004c0c0742000d034201048c2421411450390400d241d9642c0054400000e010111250200d684000300d034070761810001d844200400c507803000105a0304045091700246a040c0c0303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 303293660 1250 303292410 303292433
    0x80108030f03151306080706120203010518090307060f06030312021c050a0f0207060b0a121104380a050d020901090902150d0c1701053114040605061903 67
    0xd016058544e114240b00040090758126400007245400c030704814080035a208184da00510401d00e03081d465549050003080ca42c4048030782440424880c40041751455006108031000c85802c00000d002c1d41c200000f40c6401004288011004503c0103072400c24840c880d03000b550318502501104e10fa0208a4004180160400515920600c1e03a500100e0725440d1300c51002e4103925001e1140000c3c1140b2000070701003c4e04443d00051901e500c81d840c075130000b800004408002c3c1809070303004507125001c84414058481c8031041c0d01c1d2505000148030300404603510a10484072000c0302c406d0300b1a591801441408210742c10040c0d04405800d0041c8414a081c1d04a50301440c0702908904d04032880f5410f0403d1070308120f10310050b03543c0b2042c4000c00c00d03a000303502100700f1960b540b203100702d9490240019070080504180d1000340301005040e0b132410100c1413a00010604401c3c00384034000c40c40981120204080ba0111744d550f1800000c81c001d400c05583d034101081c201c85410f09a03e083d616440388020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 303294910 1250 303293660 303293701
    0x21e1509030f1318020906041401021c020f060a0e07050607170403150c081303030c182603160b0c070c1403010e0d0e0114070606031101080108030f03 66
    0x1004001d0720b0040381807000144403402890f2900d0b282c41d03041142400c0d11400b007202c04002d0500510200826968160440e81101d8490460a04141407140180e01704020b14104010070701025000800064000c688400340d524074400343c40b0030b5510440c1d101c04a445901825945a125103010300c85410250000c0402d58000c606040084100c030a140340294055042252501c0201900c04900e14060060540309240e608000d9007902d4100303001004a000124040c04260300d890481c011280240941050f4840200300303c42c6e0583c5440100d000d85a02907405400d500e5043d410b85d602c01c00200a80d0842d880303011206012640ca6101c15908104c080d101250007101044a400045c601003413410050101c1030640c0c540000b07010406007100e0074502c1d20441504800d400c540515070080b1310762505542424031188a2202d10b04074840c0c0d0003114030041000f49030840200500820300705c01800c4203800d9980d40c0e0140c1e03e070990380d502d03401195608907801d00103002081d02d074000d0003c01010310 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 303296160 1250 303294910 303294913
    0x50a03060b04081e06090a060207080c0f0f07120c0603150f0f0f081b041e02030406090611070c14010324081b09012907030906021e1509 60
    0x141c0e01c881c1c107544140d01542c018900b0b075001c070b042d0710400302142008104040104000e00310610f00404603986903010003e004000b070f42d00168a90802180b03070152002d182d265822104800c4817a00c0b050340d02c01c520601c40c615031059040c00034510300d0301c4500000c4030f44d001002c1c0040324a0a80207802400d0b1180800d580110120b10200d2000e030203c003210b0003040080074425400f4035006040c0c1341c0032400c0e0040d071040d412502185803038600120241000d541c0075030300000d00f5036045008040d50005c001c150304020380000103100600c5401e8020960030b90250004000015494085050303070710501400030602d02d401c1c00b0820440030050030108400d03006060200f0b02d2500c02c0011294410b13120b244029061103000140240d0340c04114001d00ca000408210100c2100d40e00000c007131410512900e0607000320030094a03180c01c0400060000c440c3c1040c02d03c0c0d01d4801d80d141c00b9002c036149000380c90041c4a00b0742000c105000301c2d1012002003030300001500b0a91018403248842070b50090482195 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 303297410 1250 303296160 303296171
    0x405040e0304030f05070f1505030601110f01090b04020907030b010c0b09120c0f060702190605060d06021b0f010504030806040515100905190e010e07030e01110910080115050a03 78
    0x1c54424520444c2440c0700c2d001620744142000389081c2c03000b41541200035a800141d621a0000d0740100440c2c0e004102400c01124203500d9490301b80c07504100101d40c0f0415420141030800b048424103a0717600591003110700b020b1a40c1c0307807a4201d00b00c9204104250009000380451000f298017141e19981004554081e42d052980101100d18154000307801d110640d8056111100880024404540c0044441c070141c06018000c004082d040002083c025100681e80e00c0483c41e150b55070010a527071640d01c54001d41d1114582d02c01600c400e000c1030f50180300784c02151641503501030184a42c0d481590300d41c4030074540d600c50a082c4401040c1c0105007036003250508018200e20755403040c0081c2106003c0c2c1d140c0d11128105030502c00c82c40c4100e01c481c0940c0d07002030000c1c450700c0d40400300107044d1a1444c065030000d0b0343d8282c1c12070140080c8030610280d5440c0400408030807104c040100043c14082d14840201517216070100c818010910845400c4d032007407a5640c0909110b0b40081a081d10141340c041030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 303298660 1250 303297410 303297413
    0x1020901021905210d0f110405060c0304080f01090201081e04150221010501030c0c05030d0203070507170a08061221090301180b060a03110d14060406050106140703050405040e030403 80
    0x611030354a9501c440d410080b805c041d07485290b006640e04c2400c4104248251b0799591140702d140d00071030090780c1c0704020100d0501441c0c43e0400541d030080041c0d4048801c3c0c0402c08160390300810400d402640068114000902e507102071024420030f0710030749001e6528603034840c0c92781003100c96044a40b140080d001c0102c2da4910225482041040404080c04110307949070400141c01c4034183d401500c180300d60100344401040c800300c00d07645107408804e809030b584e0303841110450307040c410298014180040c00002e1104000101c01070411a41292142c13040c0340c80306010066100700e0020000800d0784a112211190004482c0400740850280460742c03c00f14008002400d41e0b84052040114401e034000c50401e000d20080c0054010301e058a000c5c002e80d0564540c0e21415003020080343c05409100705031010442e4100b604150f135040e54054a02904180c81d000d0094042840341c00000740340300294108455072042112038095168071081d291601d03040c20301c03002d444102b0b030b1000c0ca40001d000000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 303299910 1250 303298660 303298693
    0x309081204031106090a0209190e061f0605040503030712030f1a10030b06040e040f210207051002100906020f04030c0e100501080105061308011506020c0301020901021905 75
    0x280107074400e40760342568220603580103244c2000208130310039903808140c504015803640c00442e03411a204042c1110a14009084400501401c2c07040c0030b00781c41500204a060ba04809800460011003241d110100e80d446200302c456008601070329905810030484030300005e08000070340c1d00c4014941030100308404940604c4c800c403040b103110344118000383c18148210345402029403401c03000600302040218100780c0440d5023802140681c0168051a5000c102807000c1d02c05c014012590104c095604010a004502202e004101c0c00b4800b610603068003083c945014030710308207841042c1d4020300541000e009080c1c060040114262a02c07942080284084400100107001850040c0009404c85140ca4091641468005d00300b9001202484003400b0310303a0310995241c111081201c40307a881c0c1040c41c91403070144005501c980762940c41c0440008a8204100380c00c4100c0d14a03070291419804144181401c1c0c0c81350b001c3c0b281c0140c0100120340a072203040301d0481580e60048045805480ca8001200c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 303301160 1250 303299910 303299947
    0xe09010f23030118021203070b0402091510030e0609061b2b0902180609040f051e1c03140106141905031801090c1802130e1b0a0f030908 60
    0x74131404201c241e400c081d800d005003114403440c4132800840c07070101546c498401c481000f0300001c0c400c500700c101040c00c0d055842d00c84c05607075500a00020251141c01000307402050700c1e420903a01070280100190103144080380d018842c03c1d0804114106035518615007070700394003510541250701400a0090113031442d001026207100050310300041d071418240100b24400c80c2501352050105100010464940c0381e40d02400d8001d9400340303150325031010340e150013400d0010306d68014001233103010074603041000c0000c46085030503072070f01a1080d5032080d03071b4201c00350780e0040070f0a85441c0c0c568004100851151004d90b60701c480d80485e02c1c0c1401e01003240c0420350400c0404980000c2c1010085c840c4000e480100b02200766070304002004100c09507a20460850300710f102e11030200680440048020001d40c04959200c0c20044100900130f840340840c00c00312005440b001310400700710305100d50303811a94048861545241c0c8610901040b00442140506140c80f021150001c082c0403005d407000010001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 303302410 1250 303301160 303301181
    0x40e070b0403060e0a05030d050601030204090528090206030609090a02060316120b011d0a05121014040f0b0402060d020f0304170301060c080708090d030f0e09010f230301 75
    0x15036451941c20f2200955480d1201d00c1c0313140d00100c207064000b03100001240d074450403454000c1441d40d0f8010040c1d000f0f008540c0310301e0001c3c3c00d20301000000c1d4030a1103500407440021203070003050884841004122543c21708001d402c1002040070502c18940086d04a5000028504858844030302d6804074849410070341341041c0e08004950350241c226000040000080640304d4108503548800c800200741d00251000036045122035400e0b03001c6501c07595903c102070540980382042c800c20007000c4aa95884502200900500e071403107012a03140c866000307600a6410811069030300c040c40e1140c00160f00082d10407070340080100320907010080f00c1d00141480c645501c0d02c0d1600da25040c2080c0300b140905a600030018042000140140c940094068010070740216007030352140c000e4502035030b40744035100c41503a0003113024150a081541c0070840d40c82200c900c1d69000c2d074404060091024210f001c1c090a010341d40500002e11051a05213807070b445a00b140c4001031858200c5802003804c60341940e80 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 303303660 1250 303302410 303302429
    0x10e010216060615080106110a05011506090b040f0303050a03090515090d08010b030c09012006010501120504022407060606050307140c0a120207090203010902070204050609090a030509040e07 84
    0x80c1c003000e10450f48580e5004018032000c800c0805188903000340008414094242403148144442e03039121010020100030b258804020002d42c24074018506c4910050b1260740d0002d516400040341500401058400302c82c440d20800024506596003a00d071a00001c0d0540205903813010414003045042040d01c0f42050000307080003d03402d101d0f0340c032402e22658041090600c6244001003154007041c4080340d074064440e01c0f015031500304400049172507014010900034440503403002ca588a410200e5050704842e003d0301d40055803445040d6140070741d60100c0c1d001c0c0d4404100c42503407031403400340c0104480900d501c00b551841e011681d0356400480d5203980207403000450100c20840c110fa082400d00c0e8161941089850074202c40031040c03070b900c81c075129005014140311440c90740c0c0d09000700040d1025000c81c600541d1650313180c00040009402c501c2090b8407440c10500030a0b110308004140500510407c40a440f40d803a60791400d0724654041100c45403c65603a120a00e848031b414041e041c050503040d030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 303304910 1250 303303660 303303697
    0xc1201090b01080132030c0a0807090501051f0e040603082a010911060a020a050f03071209050d0204051504090308090c180a2412050d020c060f0c010e0102 68
    0x8001000d00310160444850400c817900501c0e44200222103141c02284d01c155444444a21500441e081504600d40d454001c440c1440c00f20b40d40d40086500026a0300c84802006260383e2213040000c4c80b1608107100301c103030810521612a05100e190728801c068805040171405595070340d02c03469a60b102500d440c100e0800ca0052144d81c00e8690521041444500020b100c40081303521911154000014034610901c0001b54210000f4002e002e00f807019604103050740d01d20300301604026241e5001d800c00301d94400e4101c2e010b0590900446040e000d44030081c2154551094603401e0100406029003500110035810600f0b50103513540703000740c28030b40e8402d81d1a500b15080060000740340c031008650440c401c2d6040714543c0307810f88505504650060811001282114040c40f0260041108003000c2c130040c1240d070030220f07035a040001031030308180c410000c0300d031114160f440c2280c54800c02000315a01000410008002c1d000c200003400540d560003000090100c20103800c1803c9038011001e0b0000c032407920 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 303306160 1250 303304910 303304931
    0xf0f0e120c100509030304090207150203250c080415090e09010b0111030f0f0a09050312120f240f030a03090f080d020309130905060a1b090f030b0c120109 68
    0x3035800b20091002400d081c1e0070a2a060300280e100d0007240500d4141c142d0100343d900034005410b19505203810000d40071592030411658030301050188400280c0c0c1c0d0400c0e82c84405600303101d902c003c0600764000130700c43e08160901c400f40e02c0181e1282004410001002030100b800c1c1003d10020f80640205800040d112000100150003617045441d912403c0d0018460a96010f02d220111161603110880b070b9661100c1002082d11800c0c216001240c0511841c5170105504000000a01c1c030b006029418050540c0c51101005078882d044580c008041030f004800100604200c241c12603a42d001051800c0c010308440c0801c1c03820300100030030f8000070340c0d031242000000703038050742c46c400790010501600800035500f4000c0e549104070350350720b401185030031481c01c511101c40d44421102c0b42d0000540302507080060350100a0b041010b00b4480b440c01840106100500400e0100b040311810541c01600d145507842c0c0d114072904c020008003032031030100100c44c40c5141c80e40515020308000074002407002d000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 303307410 1250 303306160 303306169
    0x30403060b030a05061f1208030604020f04080303070c0614040c140d14060a1b020705091509070e040c020c0306040f031416110f1309151a0f010c030f0f0e120c 70
    0x60740c030211013440b1f00855040850034860032268448401d031805a44c8910902519206200d00e9201c040c15010200a020100307600807403000b9000d01684c0184468059690b549500032810350700208480d504401c00c2003c24008450342c240d0340b80082c0915064511a11070704100e031100180156590070040400050f04030f180f0895861080d07050700e8007602c4000e1b49010399101c4c1140909482081a080001c00c041e0580802250401001d0b000d0036140c108070b8009000210201031051045040030810050a440003941e0f20340781a0050092900ba00d40d610b40d6080000c2c3d6540a41c01c0008503401258038a182e08000d20445d410894000c2c62144903050017210b2002d00e4107c0c0348200c891070306010b029030b241d00c01450100100d0b18006419061890240f4508828400319811075042c40107007114032503c4a1412040c4205841e2040007401c52401110b40840c66180100414064400c020341d4512031481c000b00d082c1d80b8144952090201e1000615032881c405504101d0362150702c904105050 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 303308660 1250 303307410 303307471
    0x108070e04170903070513090c150c02010e0d021002101401065c010501030f08030411030604080406031404030207060c0602070212010c0917030403060b030a0506 71
    0xd810080c054503041c10340e155056042a8103904805034400300301e00f0740e00d83d030500080e00200802004811005012a0107401408016900703a84c00500c4000018840c400403601d0507682c2201d640c0c020020200b03500540305004603440e115005000d02e014000107855850103840040307001d400802c0e0400a0401c040f0640b121800f00001301d426034401004040c0c0c06c20b00e0b00714180d030902c0083c4805628207041080e415031296002030300d6200c00c0348103d02e8025015000b27510414000da110ba800d444400f505003a55403c0c44000c0c15903d00700b42e503401240c01c8101541d007041c410101c161141400c0781c0000e18008007528181d0f400750000034100141609486103d0700c014143c080c3d03180d9803819480c040d403242074901c1814244404450010104030702ca40c1200c0c1110340c0148040c03415400d03150380c80d0003048e10304810740204116480119442c0060720131402c5126008005500e8075040d5901c1e40c01420110480e5501485030cc1e105a00143d82448410b203e030b510400108140e95012040459545 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 303309910 1250 303308660 303308669
    0x91a010519030201020d11010905060a0b040b030102030606030604150e0106050a0801050102060f010302190915030606060824060903030307020a02040b010908030d0c05040810140a0e3012010807 85
    0x4081e03a0100010b03600844c8a280a16103030500c595512081017031240076003403000f401480b90007030070104100b402c09035000b0303200440b060b501005060300400605080b8842525210740c00481440010080e2400d504103000b000242003146550b95030b150303854064114281c0241010034400718049039842d80c40309000c0e0061000748000c1425040c510f0386403440040602001e030044440318011050804101d030404000c08800200304000c0c0b260900700e001c074804030701044487c00e040c03480000758544107980340c1d0301942501621030001816200003045100141c4041c58201c1014081800c55990501c05544641e031942c002d4404e85000c1d20402c030403507200c442d190f8140b21810030144007118002054949002030900c0c0059940d0101500342c40c00d000d140d109140718419901d00d00d103000303010b8200030480040d0f0308010a00d600c0d041240070940e4175081000c0c01d140e000381035600a0665882c00c0c410081058013080341540c1d02440b10700119400741d8684901441c8003001040310380400c006040052 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 303311160 1250 303309910 303309949
    0x140a23090303040b150607060518120306031005060307090207020307090609140604110a0c1103061f081b06072303280c1b05210f0109020108060112091a0105 69
    0x154072100046c0d41c6024160b400b8000542d10400600c0d01e08820324002c10b00707812101290002034980402d01195801140d800d4005c1c003d444070360001c0c4907140110350168100402402c1d4032400c118a4600070740009406030f0f410304c1074000000d01c6030410720610007e00742e4440c01103030b541c4410316283c403907003c05460b96004500e0304400d0701d8007540d154262040403800b845c0907031081c3c10600340346404240d00040d1550501401050003941e1035420101c040c2441c2040c1048043c3e41c1e5038181c1358860f016205442d41106c540a40742c5024030381a4014032203544126009003200300c0d88201c0480c0840c9011a23071581e80e00000704406030750002c0310402d0f4039100c0c81c0c116842906040d4002000407690090080a004d0b100c02c2404c880745040c2d00240107004082c0c40007406020340c20614070302000c260b003d102d140c016110071040c040010300034046625010384440005072a401e00444689910b110b01000141e901c0204d1000034800031a000d6035001c072000c0148081d4103090400c580b0f00d4020786240e901 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 303312410 1250 303311160 303311191
    0x30622080d09110d03020714030703021e030f0a0f02150d09110325120302030c0a0c060306080d1e050c0304091a1c0b22060c080a140a23090303040b 65
    0xb03035001900100f511407512585000ca29008c0c040b03464140c180e00001c0d401060140c40e015940c600c0041c641c1680f00450440e812000d002c2d0b403150f02c6060803030000c1c144444101d40607000d4103201220310f2540d1110020070b03180510b1070b0341c1c5900712044000203c51600351084046811701d81049144100e000c401c075142002c0704080750503901c94000740700301c01180e51100b1302c88051500038000c0d070f00d01003020019106d111071185801361181c0f45234065140428134100d804507a200000400d110408100c0c3c446100c170748809010003055a10040c0c6043c1040420002c1c0e85041c0c000380054402408140c001003410202c01c007070040c0780c055001540340902580b019001c0324888450140c694540c0050041c2d007240c40d4054a00f401900c45480c40c10071602c0d88000c001040303d0b0b58041030904c04255100340d05622801c03008d0003a500c0d010f29a01c0000070b00c40108e00c2170350743c951107600c0305451281040768501d0000000c50404100300ca444034190004010007051122400c42c040d0302c21401c00e400100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 303313660 1250 303312410 303312413
    0x1030608030901200f060103030e09130807110406080a050a110d0c17030f04081b01020303090c300d090603060e01031e0203030d09150506030622080d09110d 69
    0x81c01305205000000e04d00360700956a0000d030920012101c0809070701615015a10381c14060300140455541901481c60040012008030031320b04800c5a459202800a1800619881d070041c0529203800071031340103a5494002440f16401c000c0e0703041140c440c1c0040c1c0344800103411b00343c46c0c07000c3c20800180100403c41d00e0700b000600914804065400b200e00318411509004003c900e1030003000382150745c60000182c0030407004400241103101c02c90850750065900004001243c40c2d0000303482d41400c80d8041030901c0c90600d0300c08c40080c04400121004c2d024800c8107074121000101e83c2c404c0b0200e541200b014940c3d50307544484a50058402402d041c40b9032843d03c0d00803c01c0010510019090b018070860303115200c0d41e903202c1e2000254004040780e85610310401c0d4200200f48c02c00c01102c011050300501112540b42c1c6c0a090b10580b00100580080d0b99252054900c000915034401c0d400c0504c2d1140000042c410000f0b0800c65070560000503400d2000e1030440304d43d40c035081c40c480c031400010031003d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 303314910 1250 303313660 303313667
    0x90610050d11100c05010e070f0b090319080705072403021c0f02030114040b0d123606020102070507060e0f03060901020904180b0a02031e041101030608030901 70
    0x8003120401c1d200361401c8070705070038100d09016203100015408203a515040d1070365948071303440700751850068000700301d0000c040b00d01c00e540c0d0440d0b1003a00e00b00304507182c0804ca0400c151003e030141d04009010780340ca0380c60340f0b500000419809441102c00c1030001c21240244002006040050501031003c4c945072201141350031b01526440140e4001c0540010324134504441c0c1116a1300b4556001d1814040322000c417030090040d4200340503070784c9620310340f0b24103101030710b0113000c1d019103224040c0689044c154079840c0c50085241c210266428400841c1c0c09140c0301c00b00305456049180c60716a108954034040307038401d452543c1c0b548024116801880000c0c04214085410320490b162030820900c0305e80c1010105238440900d003102949070044a00304903003000103400601400400300e0381004446889842401da4042e04040500500712950018020003201e900654108883c8280440c1c15007003080880c58500b401c44046804528802c82c45c00e00396018001c00002d0200200654100030721580002c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 303316160 1250 303314910 303314941
    0x1120803070c0219090c030903120e030702060f031006140a030c020708030406030b03070807060f1b020405040f1716021909060816050103020a0c0f151b0201050906 72
    0x644410000404204401e01030410004007030790180c41582c0d0702c0c440c200c0c0c45a0340d001900c0307011045804c4c40311181d805da100e8414441c01c00d625444041000911144000060800c00b143c01c2d000c0c40b0400c00031016035120f5025141003002119181d60703918104d16400301c100308030390141c0148051013417450342d40010003040d600f011500d490001141d54145400703d04c4e0810765844040c242c0000540445c180e9031580007888103400590494a0150b03032800e140d6940c980610600700003c080f10055040c40344100302544a0740010500305140c214207400040884100355400c640c614204142e40c0c0070814000301102010040c034010364100f1804050803602c20036104c40c000c0c40b984c0210406c0d90b41c0d50040c0402c0c2c028041255042042c10f80710003c1e259a00b4555400b8540d081555500180759031003402260184e460994408580b401196544000129188002c403488035844080400b0342d210381c032480d141c10300c01c1c036a00c0f0601c002020000c0d00b10fa4001e0107421068000008004c7c1c80d1144c1001d0307 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 303317410 1250 303316160 303316163
    0xf0b130b0c250e0f040204061502030d3218070e040201031a0609011202130e01061116090f09170a0306140915061e0a12053d09090512030112 62
    0x70b00d885c0e507144000340041546030411040f02001807021000c6650000c050001d00e01e81e90400c20150385032600c4c003480b007008020244102c4248401c01c1c55a0a02c000c00039400c20b941810b0400b140c3c604011150501c02150040c80e102841a0104825580c1c1801203203a40d08040c0410140381002e0720208501d4031440c0009414408070343d03004401035901d58100c904d03882c0814800001251210040440d143d028400d9074001502d03650500940700f400b18005200d100c4240640b00001d2510117004007507c05d10f541c103000c19945440680105009420215280320060590395490703000c010301030100d1701640c109414902d450700d0111800d44603081d10503042143c0d0003201d20b4074042c60300000c0340c6110b0b4007140d403040d100d001800b0014515031405401c1344122600c800c030703140a1500c0444102c801c216118040d9031362070342c1094809980070b869814900da5504400001c108298103040019a44d9400143c8031035a0310082000d000050103c85c070001e14040c0d10703c1c41d55160000c28681c800c1002070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 303318660 1250 303317410 303317431
    0x103020c0d0503270f0c1504140a0b03040303060608130203030708030c07080d14070804050a11010201110c1b04150e0a0605040614190f0b130b0c250e 66
    0x4180e1066018100d046030a078000354441c000c41001e0601a21031642017010140d500c40d40700303a94402d14010000d41d2030000900c940c642824a000d02030b51480380f01e10b42854106c007011101054602a20004510650294501088191401100601800d0001e1052150305102084840141e80100c125048030350084050380d102d4940c0c0b04e0003142c1348a0810014040c241c005440c034607880c81900407142d80940800c1004060742d8054040c2d4035101c04031002492074010201400000d21a00c00c0310503e0b100620001480401c0c0e0080e14100307a0000144042c0e0350302990020b00344030f428000b460405234090b501842103c0100f048d07240b6080c0700c2e004251044c0000c40c006424107001d030344114002c06000344140f00c2c16950300c03c1d0f071a84086501c070990007012404c030000c1a01180c05001030880706010f14900b0024503000d400380311034000c1d40150900d0510303880005828a015000341207800d034505d000d4140001c1c044070003540c0d8004402c0d00c0c0000d6400c040304100e00044c46030b0f0140c0c040d40862 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 303319910 1250 303318660 303318667
    0xb0f180a031d040905070602060c03060d030807021c1d060c0312040302011e0c030f060501020309040209030f0d080106180e0c07020102011e050a0b0a03020d0602070f080403060c0e0103020c0d05 85
    0x5078180c50418a001c140d0f50050b00d0040c4a200b8031400081e4a42250720b140c09a5a41c4d44448000200e0f80c40201c52281e08130f512150a4000244200e01080e80100341e441a01d5409810300860403003502c0418a03903000952507181d500007400c414100719074004049485625010112180c0d54881c0111000d50101c0c2d4800000507080c94001c1d00442c1c106400820702e08a000c240c0300080d8024400c20b6118000079241029200c8041c1140c03251a0540b20160001c5081c80911401c210195119014841d01800741807944622488104200c1c0e0078a403964550304460f41c1442801014000010258000d010600c0c504000040c00b017072040e5001070720204c0c40d55543e1410b000503070150000c02150002c0c410340031990320b107010f000d502041c0585001e81c02444841d0404080064409447c0400381d4407040300c0c1700301400502154000e0a510348103022461401880362506411034005902c1a0b90300d58417611440c4005901c40401d03201c000c0242000c50500908004542d0749100603440c0f6420b000000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 303321160 1250 303319910 303319937
    0xd050304020d111306030308070f020f060c030a0b0613090c08010e0105012006070804020f03121204020a0e01090903030c0309031e030e0102040b0d0506030c0d0b0618040b0f180a03 79
    0xb190044904d8001c04240155039591500402c8200100c55800000d07030403c4207502c0c0345201190b08800040c0d48002007521382c498821a900550000e001d04007036981d140307035403460390321280054a1040400b241d040d205910f4a0025410380301c2412003103042105181c010300c012000f1814481c19540280b030001c03506400140704070009240d03050005401e03c5800304001d0703110790081280340b082c1e1003a200c52040154400625540346c1240b10280e080023070030300801030b02d144610240341e803003400100b058100e15940c140b00b8503020b9081e0403074620151500d1550041c550140500b4010b000c9925080011980540f0006c111402c00e41c0c5450342c0100d9403107002a110f1294101000301a0303006e00855031240e40301340c0300f5007952014040030110ba080800241043c81c000c00c610508000240c450200284d11fa954909148401000c0b15405408064243c4141b100c08d6403c81c480d03449014020741c50b04140308400c00c2448000c01410495035031241052107550b010a9846040741d05060010301004070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 303322410 1250 303321160 303321169
    0x305220b0313033e0d0e0402030c070606060909151a070507030b16120c0f27302a0308070602040f060e010203070f02030c130b030d050304020d11 64
    0x120328000c0000c02e8400819030011141081c407154800c4c9002c5103400303203103041c003907a0702c902c00520840b0125010865035025810181c00466000b071500c2e40d404d281031196598081222035a820843c0041c9044809101b01d21291003504210044c0494010030540f6100d00c400f504c4100d0380e10224545400b258500810604008000c051540403100e0a00740ca0074403500007103c0700c1c1c0d10507580016090038000300c0002d903a1280e00d5041e41540d80760200815661002d484580d25414881803c02d007961407003105031801c41514000e064002050b11840f1039001c8500e64400654114400200c402403200c00090042c0302070042c607110100c40044550344614864104180030362014003400e40c00100c100810032164000d10a80b1840008500e949803075030411100b51000621850140e4000c0240340045411254075503402e0303100400b240c11408115001c21030104100782e0481d01145c0340d454040c83d600c0d0a205103c0a074046250081c2503242540000d00c0048206d0b40c0900790003809154100781c0c0d20b5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 303323660 1250 303322410 303322427
    0x1505161821050604030e18100302010503091e030a030c0806090f1e0108060403020f06092a03030d0b01020c01020c010c06020c030c030f0d060e010303080f0c160305220b031303 77
    0x2c002054902920342400c0107404600312081ea180300300c00b00304582010420050485018605403001e106919046034015507103a400540050912700c507100d207081c0340c0003500d1a8030081459800207141c0759007001c01d01500303a441c0141c07130340c09204518003080740c1500c45c0f4203503d40c4801d031042a814185ca40c00c04001c502c1c840c1d00f06108201e10200004070300e5203400681a8050340c0310b542202d2080d09aa00165203d06054410800640111300041051908014088490170180c000c0c80c400c10300d0320000a04d55448503a54040c13650703c416101803d9a01071050b81d41c1caa0b42030000c0c188010105000070540401501c0007080d00341e01017640c4003101c40400a031009691510b085a50303036690070300020960b410292140540c54102100412882590250713a81240c2c0d06845014440d01c80d4001640c030740f04014090b00544600b409610640750f01e0180042d4003601a85400d07645003d0030310740a855602c001801060818611001c015401209080301c1c0d0114486402d80460400d43c5008c82e071891703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 303324910 1250 303323660 303323663
    0x903020f1e01080711070b04050a0b0906070f0303150806071d0102100f0207020d03050408070602070e0708071e090816060c0b09010f0501030b0712050702071406071505161821 77
    0x31543c6c10103c1c80c0c00e0210024410b541c0221b4000c060640d45011400840c0f10b1030201c0d82d003004d42848031000041c0061550381585209060100e01012648801e0038200c4c0c151b40112041e0348107505026100381c2000142c0f80c040010303005134204429000001c3d44c1c440c08582510302059440512440c00c5442394155602243d00500b00e20a92045040040480d000f034024a0090b00901a001541c80d00010b01c20003203402c0d00c0108405070351100030076104040c004112105021280310384c2030801d14428140e401e5421141c0b540c003911810050010b2071300901c51220189640145400d101464024803009001c69208007480d590380d54240031680503000888800c900f80382044000b00402400302602403150001d9600c2d0301483c40d021501c5802d03100d00b904d00a0141c1c01c2040180100340380300300307038204444029050901e00740c0150345681c1c2c003441072001100020341e00c0d82481a41c5c0a00040d081c1004014900b1000621030412440b64002642c4501c0d82c003500c24100443c0681810816800c059 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 303326160 1250 303324910 303324913
    0x4120c020d0510020702031603030c020105030411040e100e0106030c0b0c070801060b090108090a03090b030603030f0f070c060507080f1b010e16061107030b06011407030903020f1e01080711 83
    0x8038071000f10700001c0d4000240480c420300510b0500f400303100b9400b6020741200e40503030350202088060340040da6154009030085d9400d00030001060b41986980c0106d5800d400c40d90014141252035449c82011504d42c42140080f0ba41000710400204403180240001c1e40c3d080022555950310700070005140198aa1005205500340f06000404100440182050300004c0c0c86540c550b65038481c0403512200e0074500100803484400e42070182900c0400074641c82040541201d207001000207078000e00d60048600c100c0e9074900014910100901e025560004004504000f0300b0030005a90340000b500403c11460080603010545078552020220621314186040d40204101080c0d03150303860f142c850b01f0300e40d0031001824400006540d4420003415104d0780119015100103819075554540c001c00142c0b00da03040010300e984400807020910003c0076994440d41728050704518510500689210f000085c030b11400c0303450541c16441640b0001c0e000d4030b010901e000041a901c980701034a02c901010600d5465 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 303327410 1250 303326160 303326173
    0x1206090604030f2a03030204081e0d0203040e18192012070314070302210d0c0b0f070c06050a0209090105040b0d0807060b0405040c090b0904120c020d05 67
    0x49000108019014602a90750400020444007040e28400d0402184c81401e0111010380f0501200b20b20111424503c80d00c3d016140c6990b516010b480c2461181401c0c814440c40440945000c00c100400e42e100c1c1603500155041a02c5c116041c08c0b4084010b0500321002c034001c40c4030710502402d0002c4864210000032034a44000c040c24045a16030390b104a01e940128851011007441c9840c620418004117214000c22480d8215620400180b08005041d02284036020380031005030750706c24924a504005485020815000c01505841c0c0710345851842d00f030100c8120020f01040c0c0001c500c503071041622a80a030240c658910440390100001009001e1714544000e200d0f2070007051700184511501154582ca05980740e00410044500d403012056101c0345c00740d20100050b85a00160803c2400f400000071158240d1000c01c3c01e644c4202c5044802c0310b100300051103030260f6481140410755040d01c0b44965450190b03111075400d0103800004003489114030480045581d0240725082039a4064240e503103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 303328660 1250 303327410 303327421
    0x11803060501060e0f2e021203010b0c120f04170a14010227130c0909020403050a0201140702130e03071a04030905010f0806040207020f06070b01050103150807090b1206 74
    0x1072144e01c1c40c03142d8400c0d42024040308030307454078100e00c00450705060f02d808a65071110025244108040d1025002e5020307220501c16282c00d18000356000b0801c1001040d600c10121010314107000d03d110151407a01000e015400d107503007405050300c05590084582002d8116400c0e241032420300742c1c40000302b4540c1d00a007580e20040c41900500b085001030f0040c88174051401c3c00a0080c0d050707050019800c103200c3d000302a00101c0940084004d1044c9003490311946446450950590340540c100b55800c1d80844501e00440d6400008501d15004d07640722181801d20a500140000c6401002c1102c020b46a2071965204030f030034012a000507030300c040c400011a030110710921214904407420750100b1b0b80b03800001001d502805841d48040c50a645105507948e68404020003034205c401c003a0380114203408240381580303030000240580c030301520743c0d82c549600d450001030035500c01d07040d440d89903011800204440c01002400e002640c0c910000807a0742d40ca40c802280d201c0b2130702007100310680b0526042c450f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 303329910 1250 303328660 303328667
    0x103020412060608190203150601030902100203030f061005091005040f0e15010c260403020904030302121b0d0908090904080403060f15060f030e030a0201060609090506090601180306050106 83
    0x90844080b807080d82c0b411741188040e211a9030411501a41680112249400802c020b03401294403900504000404011a030003294601c50700700f0340c41026034000414014804c180316903259015404441d03d42904600b910018864002c03400c2c0c440c000c02d800c90354440054050b6040d034018120400c190020740da61070855211016040c1e8000e10480c2c540906008154030440d40300c00c01a40011a01400c4d084015034003007009249030140c1c1c01c1e80c1007800048016501e10902502641c0295000758036050b9031040800c054002908008000650b0340200320300f03905000555200c4c480c5008005901c9140381000c004502c1160b006a80c4514201c0422040080c164013a00999004000030401231001c10805001c5170221f002150403100d402c1c1040000c0c80c41001c10019540d603518002c00c142c800c4407121031542c1c102c0d811107000740c0d44601302401910391141c0d6450003090940b0060040381403400220f036a42402030462410404040540504818200e540c0001160710140400140d0794400004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 303331160 1250 303329910 303329921
    0x140633160b010504090b0c0a020a0222150807090b03010906110c0d0504030f1e0204060f080c061c09290a0f020c060a0b010c0c030b010e010806070e010509010302041206 74
    0x7150000c001d800086501e083c184646609198010301a0941ea1070301c29424520f070b0011400402140308601c14100162500b1070200b91100720780903002e43c3c400500d100541a02d0000c03000f4a40710b074003008100954800020b11400b1a41181000a55000b4240101e400740142c00009440c4509280004150707003003900040c22244d05c42401d44000e4600d00700c08444901c141e06c0013500104241c01c101c07004c514a07522102c138001b00308070b003001c0d80c41041d4007003003e4a4450b8044980382c8075032801000040c0d410310100c0c2c40010b0440b950762810261071000388190f041c0300c038841c03510ba94510107481007020314000000303040103500a4842610013852002c030902003c49a0041550030901d542c41611031b9070003681c0349080d502c0040e01550b031340e01c500d80d0000c2a10140003410040011815004200c580801c0f40c0607601400f5a5036144d8103003d1200c1d4030140603803050099520003410440030340d61100c05490400c10920304256901c80540048000e03029503040100e0640d04007a0120400810b81e010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 303332410 1250 303331160 303331163
    0x30103120207050907020705090709120501051b07021e2106070315030210080703060f09050a050c030603070b0310150503070e010203030c1204150c020f0114063316 72
    0x2ca034111074a62041c00750300c01d000d452400c003503404190f00340f14030302d803520b0040c0d03100781103140101071a03030395030101a80d00328141c5068865035035600034446802e2401f810304401080282105240c04900e9020502c09824a450032a0200c070302c04054400c0d0792403150a0a100b103401000c01280250105a181c40301400d582c4c22001c00e103448110301407a050b0507141c4003120380040c2108240030101806980290005010000b050307602c0002180e82c1c2c580140d041c01402110390002200d251100c8000c046a001a0a60a51600510401c140c0303960019800080c0e075140b503e00d546940f15800c01040d603aa49800c00340d6829041242c1100003a4048083c600c1221907a0710b454000c08a100103a84a00c8144c1d043d4103107800420120130006081d9224907080742c800d0004040500c2d404203180229000c2040d80001070300541003c4840e00f80902038004c02e02605100003603a41032203800122101d1314000040d005c1441849072141d5545c0c1d0008041c4085600c41c18603030754228040b00074500291840c5c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 303333660 1250 303332410 303332413
    0x11b02060412121706060d0507021006060903030212030f1305010e34030b0a0e16290a090501080711060411040c08010b030109150f0b071101030902030a020103021e0301031202 77
    0x110f54407022071184130b90090602412680c45c000000010038045c141c000c01c01c00c150321400302501d07645445131180c1002030070150f80300a0180d0844c50000c2c2400d00c0c14812201004060040c850008540c480c01600b11304034040e42e03005020710780340090251928000310910743c02000841140100c440c2040484040c0413410a040300c6603140c4c90703003a00d00d02e90002501d00b1804000040e400c1034980d1085503004500412600f104115a000302003805450f08110440148041880449818441111003107040041401e04104007041c0088c082c00103442680e040240c10030100f0f00d02c6010b041d6272001d403a018400d1329000c0c5064108541d0104080c001640100d24140c00724011500c01c01416069a0a2a01c41ca1071646000141030281ca000500c2417003c00d0352840006030000042071020040400c002c183d500c0e0304860520200344ca10340e409281c149400d102903207006a40c0443d048c078110b54242001a11241d08003020094042e140c0340b4949a035600100100901800090605c01d0b08041d60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 303334910 1250 303333660 303333677
    0x216031a091506040507020307060207081306090317090d02040e060f0a0b0121060e0702010902040f02030609060915030d1e020f07031403131706010b09011b0206041212 74
    0x80400d0342d103400b03201d080b54000100301c01080a515203a044660800361070b1044038144030940c0c603142e003280c0c09800c040344c16060019a100c00d4289880c2c1002c018020fa040c1010554910f2320381041e919a0880e101580c1e05c8c0014280e0300541c0e5035100a5441600030b08108048001e42c003032156a03180682e01d001c00c82854400240c8240030038007030b51000d14010303910848140c40d084955206a0300792095480116201e900c049850800c600f109485404194000b04103244580103110480314090b002000b1180104100f101d075450313a4001c2c5130001000d40c0c10b2042035941410002446a00c04801030b450302842e51000d420700c0e4440d040484940c0300c1c24558480342000c00060340e07a2541c0b00441401500044400c00c0852030f000119039460036144192443c0c84039801c8a00b19140301a0801c1070300101c44550800910820070045000d0900c01c001d440c038064210300040c000d034200804e8142c2856500030000210344500056030020503000084800b1800a40703000c2111b0401082c5c60000911903c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 303336160 1250 303334910 303334921
    0xc02030706150b070b060d060c0c0b060a2706030605010b040e10050f010c050a02090f07030e120f0705010b030105070c050d05091e04150602030d06060806030712030216031a 76
    0x10030080048801c50403c80d0f20385591543c1d210001d00d00140201e0b030102c2e9001c041000724800740500c0900340e419a4881500401510300034a0040026080314045c3c04601028050451240b22a10b080c0c0d003055010305450710081002c0015015030380000700603600340300000500242e0700c006001a18000200e0030f000d6a04e421750b42801e01124402c150784840e0200300c15081e54080c8824014a502400548042040079000308003005010b0310001c186840305002c020f0a258948201c0308680040703005800413102c0c1c499001000d00a055842c41c91010000b8400100f000940c480200c440c8044c0003404903103001e038005072600c2c5007001e0650311400303200d003c0b0781494171403000c880a135900203011a04c0c40c07442e54001e05100003207081c8135030066540c00443c402c5e00e005907600780080501c0d500841d070b200103034131390307001520b5555001c0300c2402445414004c0c0d41e07801060399801d594002824901c1c08000d070400b00d15040c85031400e07110800140764048103001100070710114001143c0610cc6013501d0b030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 303337410 1250 303336160 303336191
    0x902060c0a0b150f0901140a0e04030905010318121101021c0204051203030f010603050406021218010b0301090f02060c070f060c050606010c0b060405060303040914040b090303270109060c02030706 86
    0x1c1a090f0340036030303010014821388207035034403481e400b03207000d000581092780b10660303a040c01301b05030703010740101d80c2c1040e08018661303040c003031010b84c240c0c1c00d030380b00ea041c601c1d981e86c5210010b20f07100f00303d09100c40e13500d42c071059903000d40c1038420500f40d400c206000419070020f00d00007544240591406420039542c2043c0104001088034050b62100c0340101c420781c0307001c0d0100c0040030040d01c12245a43c007001401744500c1e00f280c1481c000c1000c1c00508a0002080c0c00c3c06003110342d480300302406a414601c00c00c0204034250201401d540d01603650341e94580c1004462402c0900c603801100882031800d40c04220a54841c2d12518514420000c50385541c55040064030b400e41c0903200240600f08110028141c0d0400380c00640d00b0481c06000c607802c2c503856800030002e075840580010300000c070410030002405020080315410984001c007861650401e05401d20784074101e01002c000c152500340d071007000e224096000060154000030100007442c4c84180c025207907405400141e42113410301c2607840141c400d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 303338660 1250 303337410 303337429
    0x150103050f16120503070b070509041b0509010c1407030b0a0c0302130902090f0303210a0b060a0809071206021b011505010c05070e0c0702010207080d0507060902060c0a0b15 76
    0x156004500042c03490100310304051100e0b030f00115141c2c00b00303006030740004060400c0503000701d035070f51903040d00e403c02102804100d440c900400c1181240090344400c0e10340e042000c40c0d143d40c40c00e207000e444012803803d0502c01804440d400c460a032003070040000521612900d02070085405440902058881c03010071010303030140041802c40d41440704d004001c0540b00c0c0d8020009404081d0030144180c0f03084000a0460704840050050320b02800c0461907100080800c80e03a102d490308404200e10362440700420618040e00b0a2201808815400704440003801c02c00c02d8000c108090740295429094a0400c019410508440e010034115a01e01910240180201c2c22904106102454003030329050046446400040b4140c9083c02000d8005c07400d80101081240b06c0e0706070342d4886540745aa480020700d400007a5210031815080078680211040e4480121240315030840d1011512480c40d0000400c503200b00480c1007240c1c4603000d02c110401107100940b078443e968a080208007502044140b200c03101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 303339910 1250 303338660 303338683
    0xa02100c031422080115062c060c0703060b100e0f2112040e070c031e1209150e030406050714010e07060206060907030204080604060f0b03150103050f 66
    0x1c40b620381c51049021204050002e2141600c420f1004003c43c85521142c0203440d08481c03426512014030750440c6010040c03c40c002d00e80d62400e445440c54251030141003032a400c400500045440001e000269903080039240b80f85c000d441507600c003680d42d00d40034004045c01c1d0902406842c40d2000d18103441e010b800c1e2031700b00e202d001d0b0005140202c0c47c0200000c05030441c1c074002062520012803840f0701e40c10064082c030025007403040380e590781c28581c0401011070000d082c00d04219520358280000b070b6200c50303000c00300d07171026402041003071642c10103039801d4100401c1c060f141032405502e1030a01000c04010903903010314000c100300c0307880700034070180d1284218020803020980400000001401603040081d101d1703c151300028988594202c2641012010b501c0100180d01c4236092040520300a14040c2d0028a6400d003145428680f108458561100910281c000d80d604d443c240c20402807900b0a2291500040598848c007aa54880d6040c01400307000a4860384100c8401e10500940001c0740031502 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 303341160 1250 303339910 303339917
    0x4020a0206070c03201e010203060a060309030224040b060f030a030503061206010e0a060602070311040506030109060f0614100813050c060d0519060f140d0507080a02100c03 76
    0x1542c40d42000d941c41c00d00c040f012420004180411510014200f404029541802010b44000304203a103d255007001c040111410b943d04c1002032040310b0382c540c0701c2001103d45c00d0074041a03804807400c00b0390034408549030713560311040c210741001042011000c1c10b612542c402d0034103400d180c50f11018851900f0b01000c40c240c0560108500c0c03004a40074030f0180d0760103880101101900312100f50030038107050b002e0780128400803114003403180c03001c1540980d40103859580300428440745191a00070324801d0802400d400340b85d44002080290f2000e400a840241e00200280003050910411100820030b52140210f501003040d44900c0602e481d00784c0b624140500c3d0307160849270f01c03a00102e2005a1a40c2012100e80c896545084220345a403006400700f0111344500150f01c1c90828800c02a8000900c0d00c40e00300c906d00841449245000b50a410554640307050300c6081c50404404211160014840505207200d80c1100041c0b1850001d081c2e44c1182c030030744001012101204054a56000702040207010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 303342410 1250 303341160 303341173
    0x70302060d110f0409090507060807080106140c07081f09080d0213031407090b1f18030c2c010e0703050402040207020616032709050a020702100f0e04020a02 69
    0x40e44040e400600031000b241c2e141c145843c0b40740c2801002580b040c0d100c004046d4442400c0c8081c01000d00004004212600740080035141c010f10040c062201401140c00f802034107410f0100a101400c141d60b00d0900d408116101d0369100c42007661b0764241e003e40c00724007000007489104800c03000d00501c0021030340800321904110142c02a40041e40000e20500c0c80c2001441002020a10312421865801081c2c0080c1403e14206000d600940d0301c90301d40316010781d109003d08403030700c4086c00001002c90850b00e030642c1300b8108034603a01e03058056540b001c0c01481c0a0400458100c030180355605072081440c1440f4000042040b8494003c4000d02c04e0425000d01ca4001540c202e000e031300441c0d4000c1c40104014031704680f40d4002001600f048654011514104521104164004259141c20300f086412031a00c2401d0044941a1890030b02403808007903160000314402030001d4041e110303d941d004000704000c0c01c0a007001429000417624150010348100349040c0d05080500c21101d40d01415406410f0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 303343660 1250 303342410 303342427
    0x706090e011703070b0106031a0618090a18060203010f060c0507090509120f030601080f1005040e0708240c090d0308040c24120b0907110a051209030f07030206 70
    0x380320400d2850b2540720302041020100080b9802c1d0502d0181902d910b001440c5400a0560035610514010143c01400208140704e1821394030391808812400c2140e840007035035503041e036003000f4028202165024041850b030900030020760303030099030613540c0e22801c1c1c125007075030384008983c918820507000d0700030b802010702030041c1741c269005294012004000c0b02c103103074155502c3e400d1136800201180e1981001105002e913560703100d0009074208003110381040c4141808203205545c1c400c03a10070580314590300c240c5128040824810380340281203003c10388448142c0c03450b48201c0712000282c0340a2030b021031000100c5101303e060903102e14030030240070411422080d650648400348094802e07504117101550002f120040001d00442e22100c6011290041d00c40e00b0b0090000c8000344005440c050401410401a40741d62a5103507000741d607450130303465041c0704101140c2440e45c0030300301600d140108030180c4203800103c4002c28642600780c0c100d0fa16202c4460409480720881c1c00001d6022404001170344 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 303344910 1250 303343660 303343679
    0x9100522030c03030b100c050105070e0a14040b060c0a050f1903030203070e0d0303020c010606030203090a022407060605090108061b0f0903030706061a03010e04030804150c09080706090e01 83
    0x80c105446420b001811707003141d6000030300011000081000007192030035036070100282030041c69040007950a0404682c450314001808200f81c90003003a40701c014581481026540d80d40140300104005440340e95203030030b031010154850304121000c1e1154818070000e0305501000141b0a10a801d00ca00001e000310803e03507080b00030303600103020b0300c003041007c2d0304050542e9550300c220358000b4131a03180141d90381148803450342510041d82c000380c10304d8810b0080140c44140400c0c4220200d5040f130b180c001c82d855086540070100060022030b0b504440104171001001241d6001005451084035507035a070b6a6100d4885a0342d0f80110303099141503200302944200c08140401501c50a50900007090605449801003441c1d500282e80c01c0c0d545c240c0700d402c01c0160701c44200c031030790f91000002182d40c5150b040c44d204002105020348000c04015080002400f40308283d00d2040548450003001e000a020800d4001c020000303900800040f0b0080e210002071640c0145110401c80750f0ba001300d8440c5070b21b01700b640c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 303346160 1250 303344910 303344927
    0xd020303040f0309030803090a1511070807020a0308040b0a1407050d031a0312120a110a05070314040b0702010e0603011a211003170702090411030a0501050910052203 73
    0x3c07414444080340100000e0301100180d0f11540b01036009001010407818401d0484d9018000087e030580740154051141810200f2603032030035000303200b80d9555215440801c0c030f580b0080e440034046090128010450b11401c1c0010103059030307255a05030309148500704688642c03160210007030155000d800a05009402900618040300b40b2009001a1070074140c0070a081041c4260707403c8502900080c1034101080313490760250042c801c04005c01c00c1c078221464003511481810701c44410f2050214032003041520400e900a4040d0304a541c0e140c86a9450070004000d800c502012804228000c0341c4401900f4000e054034100e411030003149440903c00d0307401c81515400701120302081c000c9000c2d020049010501000d0040203024a1f011500d40b850a1082c0c48401100c48541407580c204100c0e009031313540d0390182e40c009411008401c5c280c40e119001078907054411800420f1942031000b00124030743c1c0812020024111038801748990350390030000c2d020a5464040c0d1494030006520380303901292061401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 303347410 1250 303346160 303346163
    0x7061d0f041a03192a0f060e01030f1a06090409020a0e06030d030204030c170a062903060c0417070f031b0b0313030e0103020f03150901080d020303040f 67
    0x1000c5490004402040540d03039031208a00c2224600010082e081c1001c11030141060b481e90800262000b49a0312090b92030052043c01c0940131106258420720000c0030104e2005024602880c8895596458040c0a804400e02c466010901d482d11007120754a243c011004040c41d51004200120207500412060b41c119003c842e800a43d641d04100c01a1941c100316000b600a000c4803441500e00300341007600d807413515019103040600620003000051580500c40c01036810864070384c0c07400d80c8001c0300585054829070024040d24100019010307281101c000100f10742c00b502851200f480c9070700e424140e40352004d40d141c0c11117500c10042084407003001000e889a5001c014161405d0581d500c01d00549450030303070000c1d1100c1e10051115282000541400002058520700355403c510700103600c0011100100700240920142103550f4205070f1003541100c200c903584100e400e81380cac2000041e84e00d80803203000c02035010b0703225030001180031900010201094141d0741c0c000c40c50b40d500ca41c0c4841d91500071100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 303348660 1250 303347410 303347419
    0xc08061903060509070e130b18060a090f060504140f030c1b06070c24030c0c030e01031104060e03010f05100b0d110c0123070f05031b0705100e07061d 66
    0x300846c07016500d10a01d4001d80c1101006900b0140b5410507185408010740078041c0d1280c905080c41510801003102c1f50700c00400c010004401005040003c0c0e43c41151000508a510701820002000410541b1320f01072890a0221084040d95034041640c038812008020b110390b000011202d081c0031001115021400044c1296042a07a0f6681d161109042500000c4240182010021402da424000340c501c40c0d5503441d0500c00f01c6605d04001d0605a2641000340030416900007960381a4000d40102850f501c0700c0c0300003551260380303000041005911210b00d500c694200b910702e00d10804940103080c020071002c100041c00615003148500316511500800c4002d540f00c42d0b64030704c2e0780150805022881c0409002207880400d84c1040000d4000140e4040301d0f011504041c4075034039070b2010b550352150905050181da20707282c80750040040400600d1a841c000381c0040d00004020300807800c1c80801d42040d90500c84841050400354490046009070780015490f507000a84400300303c814010300150240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 303349910 1250 303348660 303348673
    0x11090112050a020702032b141204030e10030c02071203171005041a010e0909071a1201170d020106051f050c1203060a14030604030f210c08061903060509 67
    0x10701103428030082ca0000c1d103c204140c01d211488040d4141e4414103c403192401c061035842d0550202d03950701aaa20503c1c9c07500c1010001010580039403010303502000700030210b001566866000130050f00720200c4650040c00381c0540001c5107030303480e000340141a90680b64606226286109a5078440c4c00805800070701070300310000540c9803214800d101080d8003450410501115410025000e42c2c0e1030f40809007c1d17044007007044001900401c10005540f0511500a02084090000c0340349005010f041032084c4103003800010b1004800ca4404100b020980984c2e1604090b240183e088550510820b60090100d013082e000e0080c075074242c000100741a0800034141000c80c0070f030600d80124514140030303c01c0000180700840c505808410024a507149a0300001c1c840c500100340c5501c0c0243c0000c0c144002441035554060250a41004d504e101c00700c043ea005000340c0010018000d601883c00c042040c45010413400d041c29503900c0d83c0c030141c40480c1d02c111460744c0c2da8000103000080240c942d500955 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 303351160 1250 303349910 303349913
    0xc02220b0f120a0b042a140d03090902030a060305030f09040509071d0403170a0617010c020304140609100201050a05250f031805070311040b09130c03081b0111090112050a0207 77
    0x24046c03003680114401d00c40c4c0f013890501c0386000039804580d800912a1058000c4034002aa00c17030894401d4600d480c10140c3c03291528042079001c0c0c211340d04001e2103030102050b06401e4400c0c00002c0e1941c5002164240312944514848039115121030103040f400c4036050703a480e0a0001d44603620340d0014420318001e106085034924402c0c50b81800d0f00c0c040c1c040c40e1139500412001d03115021081045020074001c11402d1080180030f5543d2040740301e070011060381c003a80b01c10740b0303603940c000c2d905c0820b07010700300034020706030340304001c0c0240422540c1007055864100405e02c81c60b018400c5c40707034095181c2c040d10400c0c4031402068410500a0f00a14101500d8800901003421030404040a80f48160002d1003c94107514110600960100341540603a02d40340e0003522942d5140801a00013503001d41c04200f1007207a0a10b259001d001c1c0e04040d0011030b0010340003100950300c1d04020911000b00300204aa80c803200420341d8548600c0c901d890005030000c601890704051980450703004084104014a481e44a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 303352410 1250 303351160 303351203
    0x412120501060f020c150901080606160803040b100f0905131e051c050301061202041508090105070c050c10020106051c1a13030c02220b0f120a0b04 65
    0xd801840016003000b00303540e00f45404002444004100300e445a807180c0c11590041000e02a41c80c0240c1082917603808200180ca6080803a000d10300f004103403000000a9080c040c0c882d900076502203400602510002d82080505440f20056404005940a4541c50814007078042d200160a20440c00c21071510440040c0010110266103034117640264040c42d0981842c1d0309100c188141004a800c20b451000d0305164880112410344030380f07003003000794a56403a61450003405141c2000c1c20b0ba803000c484103804680c00c803510b40c0c81a0a00030013445035603900e4038201c51101c0c48003c01040c42d401040550110700c0c1500b500d4440400a100002c0c0d01a0fa4034001020f1041044086800c413003c6031051081c00f220000c4400300300d5410044030880e043c041403490419a02110181c10840c0c0301c010881155184c02112428011a1004c80049481905158007e02144910510032040e0809506080c00c1c90014014240803004c040c180007150798441002c811001041207401d081c0a60000c07401c17158 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 303353660 1250 303352410 303352421
    0x45402030c060f36040204030b0f100f091e02070b0106110f03040b0d050702070f0e04060b03010510063c03111c06050105040503030d110d0f09120e0306041212 70
    0xa801307050000d441200310014071603402c13840c0c4940118010001400429034108050b5000300801500140c195120031031220b4a4034290014840c92003917210008405083d42c200841c02001200d0f0807940d00303041d0815031300320f10440e41c00400c0803010304010050700d8061002c5000510901003a2680034500194003411940a0381048100305800308030444401039602ca00f55018103680010702c03100c0c0c00c00f4011991b5600502c940440102100001802c00a558021003c0c1080c0500240628200f0b4243c03144121a94011000041d540749aa980b03064103403c8400704400d0161400d000809007018081c0182081681c801c0c2495100c1100c04c460141e014000d08090702c11011240540401ca142c0b40c0aa819690003541004002c0c0000d01141d03401000f107514211084000090244400c0e07030303440d040e02030800030800d403501d0161000d0340d03803001e6088007031078a1299950fa40d602c4c89428041e1802ca441649098156100600040015103d054041406100790814150080c0a00c0c01c40781502c0c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 303354910 1250 303353660 303353707
    0x51b01110d0503100f0501080417270108090d050706150308040e010914071b021906170a0c0504061209020a0f050102010f0b030309045402030c060f 65
    0x21000020081301c5000d003403001c800780000041d1086035514003000200303000c0c0d01400141c0050210b02ca003841c2e080c80c4800711141410700c00200900740115541c0140038006c4088400e02055505d00003911040d0007152000d4042d840d91582410400036865071001044902c083c41d0590640e80340100c049001107000d44018400103440e080d0540c180391000c07050342c2001002e03100e0f00c0c0704003091100e40c1c6d400640c0f840c06145801810301c1d1122440c00002c05201c8064850000c9005004c07010a00d43c2c1c3c0562003540c888a620910075054130b400c808038040301d100000780000601d05000500c0902c2c42042c540c2c003007004032600030403c05944d0b0005955050b450344500045240800704000341d58080c050314441030300c60b0404001c0e103034018010940300c0c4030348003140c4c0c231481c1c1c0d8200000101a210340c416441c429903c40c03007448042c44a02c0c18200e1507880b42814003400c07207942c0b9101005184d01101d40b40f5607018010b442c080f1541024054103800a20100e16458018023403017818100d40081e6203080ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 303356160 1250 303354910 303354917
    0x201030609050f011a07030c11030c041b17130209190e0a030f0203030f0103080d0609020c01020405031213090c0c08120103060b041112062b020901050d051b01110d 72
    0xf54541104900c0582c17030004103003007070341d070a00001000c242c100c3e80d0014081e4002c50801d01e0441c1d41800207060048031421290712510303108907054031002d03d51504040741555100e031101c030300c1c201203511138000003103c038134540c804517480400050400b102500e0300200541c800117035024a100130f020035507030040d83c1000b20764420040f941c185030348406035488422041c0055407960900e1140b00c11001c00c1400050300078400040c1020044905038082401001141411500e0b4080c0d80005400307580a4400e0a1080c480c004844e038607510b001d01200d84180d0f007030b00440c0310140340c0308490018003021541075051014100910005c40e840394002d01c1300000c0c008225800350f0561401808603500221f00d28047d0b4500042c803146a440241103980e091201c1c160090f00355542d40010304400075a814021602680410000b03070601c103480d0100c0300e81e1089030340c1d6016a88840c00d020030002085000f600503400549408401c101c00d8090040c00c400c18034002c040855000f040b50314083c60070340340c84e000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 303357410 1250 303356160 303356191
    0x209031c2607020a0f0c0b0d0b03070501081909020d0b070314070e0d030809010b120d02071406071209090501151d010e06030a091a04060b09010806070c020103060905 73
    0x22501c0000400341207506061001da075040801000f50b8921a80304003c04030540c1166140500c0354900304240140b1481124644d504001c010440141c00460806030282c031803030030301003410740c01145c2c0382c1c0c07160080c1c035500d10a100360189101e0203450029003d0f604400700501c0c91000c00c84200700c45204d40425140400d50704d15203411402d403d40001d003140100840d0b1644813125a803041a20042c842e0545006200da44079072241d140100808030701d46038006544080144000000b18218500c42e02503001d035554140d030b6640b00c2e102c3e1401302c4000380c1d200800304040e8001400d01c42d11404202c42c50702e0203100b0b298440110100304d42e400c3c0c00c0403901321042d0700d04207030700c40d4800710702e4030400303180080100544d01d0580080c250085601410703124900c0400050b03d40c01003603014411503a0800381811844403001c4001c40c1204c03003958240c07040340c2003980e503114600b80b1310079150488064000900407680c40c181c08440d62150040100d042507215a00007400d280ca50207203074000d039102d5100c03114 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 303358660 1250 303357410 303357437
    0x26040801090602030718030519050c041802031b010c201503010f0b07151d0318090109151403031204050601050f030a03080a020304060603140a0204050a02070803010302040209031c 79
    0x20145101ca10b406005603500c4140001440803803000f127070401c414884e450005c114588641001c110554580d0003d01c0d051100e94080002c07883d06003064020307815299148481d20720f00030f02c80018004a40800c10f901011000120441c0c00036000e40c1c00810b100440030080300004034080700808150900d10004001441202c0e0341c080140b000f400d0040406142990f00d561b2840071786103003143c00c1030702c80c0d48440030011071030003c18410084051a05480c0d8510700181d19400d5507500c10501401400b82100105203400c0c680301e40c1c00001c0900c2c000300007251034940c0300c40b21700c2c02d0181160340500050042100302e12050b841107014600c0380700174024a6062000344070740c2d03030b06500c0f1036882940400000808240c01c03090207500548600ba0160b601d82d81ca00381540030700116400202078416290411560740c0303003c030f0340105c4288222414002a00c407503c4100c16800345010190010b002040108014600369006120745500681503071001241c0f180c1c0e4a8a482030f1410020200e0054000350b207 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 303359910 1250 303358660 303358667
    0x30a0308040b0a060e040f021504080601030c05090108031c06090f090623070c2102010e0705010e030d18030606080a0b0a021608091f18090207260408010906020307 72
    0x141e00043c0b00c4000c0000c40c2c41c000c0030321811000a000904219030143c105410354a03907605031030000828941d880e03655540d851019548a10900c0181d440c110200404a03103840c025194a04070750b445402503003862a48007801501403000a01c40304090380e203610020b0410f9407402034903500000000300007044916400d02000f9100c80c6050b954520301008402d0b4910040c80487c10340000280c80c03e41c11045542c5005050304115011310b85400d5104280802c106505400c10100340120b1401e0340c0c265640e5000641d03521003445000d56140c1c0000d9018a5064070860380744030a01d184640d8a12429600d4885104445c090341003420290030001120091101444045030007903265801140742c5201c404c1495525070401c1e2004203c1180090301413103e60b51200070f0301c0103036070000009103420004032028180450b00071080180907920180044c540000e4400d8510154114000c1c03018800c0450386d42c040070503040152501d100e400c0c000800c101000b4810030204902c285001a540d04080318081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 303361160 1250 303359910 303359933
    0x8030903010b0a0605030f1e100501270b0a05041d010e0f010b03060f0d1b06170f070c05100c0302031902070f08090402090d15060e01080c011805030a030804 69
    0x70380903c80921041111580c00710480342d000400c2c0c00509043d489010300c1284106050101e4130f001d906200501c070b04140d0030340c008022140c090303e4064040390855905914646103022841001074030910400c00300e04103400030140d41106203001407905450307050899400342c0030300c6400c2211408200503c00220700c0b5464035003010701901000e165605d4000700c000703140300041800c2d010312510410800c103501d0b00c504282c003940c3d005280079552001c0c3c41c8101041010341c8103d81c0040d0036842c1c0c2c0005140301e05c0340c0500402010010302c215560305070054400c1c41048404854600c1800500d4181c1c40c124803035140034115955000d40c0c3c0b414080c00e0400300d51052000e9201441c0b0422811001a00004915600750707070001ca10340e154400000040c0007406010251a0440b035108950020008070300d0b490ba1070410040420040c017074991030800c0d480d50703090003181d08507800000c9186030b56004400201ca020010203044c0f04e001e0300d40e80401d00341a03a06104030042218542840200b00d45010300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 303362410 1250 303361160 303361181
    0x316030506010e090a06150e25030b0a090903140d02130b09090f070509030304080a061b0906080903071406060a0614091504030c0303050a020c030c130f14010803090301 74
    0xf00710141090b01c0156184c00764281c008008541c0c4944403641e0f440c95180100050001c2c140101c810710741309610301503014071400d480001d0300380e2800700690709000e44030324030f000e08000d0001801d89040200341c4008041034030003602440407918a4240e0038862400030f002c09484000c0240c2c4862500c0360200c002d8010703400c1090007020a004035141030301c41c01e1842d03500c204183d00180300d41d150500c0a40d40c82c480d0602258260100240103c0e600000060f407010300381c450001040b02000300d802da6071110b2110b90f103240c0018005e040c2000940d1003803583e80d800480300810b0742e1a0524076641d04c05003015407460fa5105400080812032a460100d03035941c001e24003420129215507088040122034411610b00610855041e02030006641c0008150307409942d001c1e9001c6400c3d500c81c10060540d8211205180041c8a1000400c400d420003007003504029202405150003d403400846c440504559174144605554600c0c9503400c0301140c86865000348002009141e952052500b41801d4800e9160f1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 303363660 1250 303362410 303362429
    0x90e030417070b12070c0210050406021501050d0b0702010e100b090a09080a0c0501090501020f0424050301090e03070f03051b030c060406090203030408011113060e1503070e031603050601 82
    0x103003089080014004c8800c03a20060540c41c07429554100306494158207004040d4001000c0e442d080c081c0768000b0f00a000b502c2490702110115183d0002030116041c3c24080e5540120510f84c0c030900143c030380c10070740340c0100c0140000f00f00301d02030040d81c601d05104072202c62407140c0c95001140050070300d61002c54010030303030034414070034000180c407103681c00e1058210301803c000303540c148901481000e60000f04400e40c400000d41d075a10180441510941260140c2e044a04104806c0d00b1054680310a04100d448662a80f80c00d5038030709100140100f1b0b82550001590108200306000180200c81c10400c2e24400d442f0662078070b209141841d600010024840c6140d4001c005440101c071001520561196004c4408942c80c0c00503c080381c00c40c02540d000210310b600b0030407092448040d0001800040c10a4803034080201c0c0c1c0c400b401c84440014101c2e00c0c1c0c004040000308100d00d4840700003981c3c003603041e0914541085c80c40d4003080c44e188800741d4101c0c0280720f0140c1401000024810203004000c107e1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 303364910 1250 303363660 303363673
    0x714030c010206041b03081801110a260408030a0309030809070e04120212030a09050c040203040809090603010b060d24050a17010b040f0c1103040b0702040f0204090e030417 76
    0xc00107991001c0160002c3c00e09505a5040b03c0081107650981c4080d55221070700301d0f10b9040920080c10b200c181c814005000c6400d4100c807a0b01c0030400544001c03003d800440a07948040d403501d50f080c80d14440d540c140b0740001d040101190000c0d00300000c08619806650008101440d2b0034000e02d17298010341000d0094200c070308104020021810025003158004200c003100a1858400ba4640044500280b42e481000301c1005085102640111600c5009900340c1c1e04101118041100303e01c01120000d00101d4184022003041c02d243d00d09079030004010f000050403d035854001402a00304110729039040e9166002c19111031500c0703c00d24581000105251901c1c1d00b0040002d00c0d1103003500400d000c484410500c0107104400350041a02400058810172040b11014803060182c014048500003060045040007d402d800000712000c4894807a03080e400d01311140d00f040040d18595500d451075640a000200c0c0720070035440303060400824880210b41e120302c1c00070740348118000400451896000311 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 303366160 1250 303364910 303364933
    0x4080c010e1f030b12251a03070509040f0f0204050f0301060803090112140f06100f0e0103020708120c04031e030c140f071502010612080a03090206070b09071403 71
    0x211108103414140c2000300f031009203103011171a03010344c14800e04054810003003010b180605508502e1903044450145041090701c803010001c80c00c41240c520080e004003040041c0c6d617144181c016140300f042c014004200a1800007050041d80d074841000e1000c40e600041c100b10601d842c8441c480b040c502680244441d42c64030100588078021414001d0500c02103a0b59840b5007141030303100070340b03010350181040818203085e64468802d0408450b002c1c0502c0009085001c05806000e1541d06103165544448140b504140110041d400c03803003048441c01414801e24031222207442ca0b10380f08454500758541c40d40c3c614182109001000c0400c241c4105009404001103540082403c0c002500006144402204590340030300d0402004a9a2241d0140311800710343d074030000d0700005590032075900074000c044e03c0d10425070243c2c03590742004241c140c0401510410a002c0d80161040301d000510741c1d800e110341a141d810002c0c001311803401c4650440e00c2c040c000d2400c7c040c04950a907106400078107600446 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 303367410 1250 303366160 303366199
    0xc03030306040c0915081618150309050102041202040b01050a0503061c080d050f010f080709150e13050105010b0a08041407091503020414270102090604080c010e 71
    0x15240394002ca4a55402c080c0180c0901000001040308450400400d5100707000100521416070300304030007030070740c200c1400003038440c05840449042015130040d0203450808114600c086074000403090648880460340400c000b8405000100b4405c00074403102c1c0160310400c81101e04005415040c070505001c6541126403040030780ea4000c1041c2c07490340858540c22032014401c1c0c00c9110080114200250400603440700e0b0f00800e0141c4a1170362201c0c0c90366240c0d0b4400c0144c50a81c066802c544c1c0c04403004001114080d00300c51010100c9403080900d654680d4074043c0c2018003194540c10558641c0c0300c0c2000c00c8803d00c1034a006012004540e070600140150080a000d1702810192020704610301c004400c0c1000c1c08000c00034a4141800c000b0107402013030310394010302c03a444240c0c841c6140c0301c0910b410420b0101d0340c0d4851001e401c1c00c5814502c1344000c1459000c01441008901d65092007951460348541300108080c0c14080000c020051030a8001020342c03011543c0e03113009405041c80c20105104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 303368660 1250 303367410 303367417
    0x3010e0109090206070c0902091806010f1815020d02070b0a05070206091201020d09020307092d09050712110406080d050d020f0d0509061b030105091305010501030302030d0b030c0303 80
    0x14481d0110300002c0d00d000203241c1d405000400b038180c041046d4009002e14403540105800201134480758a0300c2c004002d074095824080303070700e5804a454100300000c8030740328000714a4180307815000784501d1601c48501d4009021408c0000c1c0140c2d20145a0348082501080080c004000001d5081c0c94035056000081081c01040e100030701400000c11701082d9551141e00c0408103410980c001c5444104501d41e00d0040c1a034614141e0180c010034001151040060264100030b007401e80103081c9001194480751803000000004180850381c41d1100f20014809101510041c00e00d005401e01d041010b08102020f032055001062007640351250400030150f000c12004448580d908100740c640e050701c188034001c5e108001d208401d811000a031160f403184d40e41c2c0428050149001165110b50301d6641ca9003400d13081003403c011101052004011914004100a9024103070300c0013000c0c0a2040d030754848c00c0d50800e8100301c02580002c01d070400310031054801c1c003480c0c80080340142035064110000c00e8a074403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 303369910 1250 303368660 303368669
    0x10b03150702012a03060824040507080d03090308070804020906090702010f020f04151b06020d0b040203070e0f01020c0a0306050c0712020c041404020f0d050f0d020a02090c03010e01 80
    0x6031200015803018001e600c00901d941c4074180d0a007000280200048101c00d141103982c0119161010214005600041100b0f054214800886d43e481894010040c1c099004000312070390b02c140b52011510440074071003041ca03000c01d900c0c0494480c05610303024165040083c079610820191004110142e41c500c20780540020090b226402d690716005004c90140030559a10f03001240001282d0407102c004100800454129060f191100000d40d24112201c84040400d040301500d1100104017080c0c0540c0102401501c451002034510005004174080c0c1e04100c4180c004640c44805c543c0d0b50782411f0144080642c000d102800b2244901c03000600740c00700c030340405000d443d550320000d040501400c084030006e5070881240c0358065401d000c02507454020043e228056810041c242503040700d0044030900440e4010301441c081041c40c410f11043d6101d0110981d054420b11044005032030042c024000720300c0c0b00c0d80c041c11030382d42c03540103124045001a0510038090b81c2000100002d01e420755051b4190fa = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 303371160 1250 303369910 303369943
    0x90303120a0f0903080a060b04050112020f070c170d02060610050c0109081603030b0409080d0902010207030204060b090901080c092403100e0f0a0335130212010b03 72
    0x1e84484070030a008056040c0c00c2800d05181003424000d05400c403403501c0c42038014003424440d50343c40d034688045038003541c801c080c0410100d42820340300c21801d40241500195440755103007080821340302d000e070024059220b510103280341d103045452010240039000d002020b1303000038002c50404001185e040080c3c0d1166000300000800c03080d40350107081d08000d040580100109032124460b10207a0b0300310f203500380c048001c00c1c50310302520b00906180c015400f4481d0803100e0700c2c0c14102100340d1700c0090148004128110300403a0004001646da0b4400c41c0b0260162040280d203030003889040c00744400341a0080e240ca0744c0441030b81c1a0f240c0d11682c803a43e201d407100703860080e1803a400344001c0900b03041542143c4e040c040c0030850035107000719900a18114072040225100410601007464450745080805800541c030b94120141400030f480e03401c001e0041c07088910f50200304509840c0c0c0081c20a8404000c0c00f02030250038019490b004818100010382540200100e41d18500042d07540e20f03203270221034680b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 303372410 1250 303371160 303371197
    0x506060a0e040902100e03060108070608010302090403020f060103050102041a03060a0506090a09050403171f09110403140a1101080c04090921030b0a0603020c1005090111070c09060b090303 83
    0x1c1c0e01c4603000351901c0e41d0301a14070004105030034405844c1010392208103010b03210380c0e0300004001c031000610004440942e200c42d46c15900390b40074402e40e100d004000380c00398821070600c800002420014039008600802c0016220b03030408034480a80303004011141c0215409209006a81c0d0380c0000002c02c90b9401c440c0b282da2000b41d000071500410b110344c000c0000074070305400c101c00d0507003004424012007900e031040d684540d1841d2246500d039404000099541d4010903003400403440315400451050085a201070070903503648c2d24000d0485400d0f002c1c0c1c0c0c00c0d800610011080100025405040c5074003400c054940b49040701000c001030260b071040c1c03da801d448030140414408445004550641072001c41114164107000140c09072410000c03071802203400940010304180f00e44266150715941d5000307011100307040b01214001d800c0151007140255070b40c0740581071180083c0000c1645510411103c00558900f2031510111030f8207500031030186000308201000d95401004454000c140810701460 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 303373660 1250 303372410 303372437
    0x7140a141f15080d030203040605010f030807020f0a080a1407080f0a08030c040b0c0c010207080d020d0e0f0402070b1005011b02090a060f0801142a0a020a080a05070201030f0506060a 80
    0x742c141e11640b04445a00a444503004640c0e496002181b05070b0040b03805000c5a640c4900d1800c1e203018511000c0c05222040c0151001840c117401d014a042e070f0020400841780e5240e0021500340070040c1c0d012921a00c10180103401903000b070000b44000c3c2811405080b1044c8041c002d9a2070b81103880b40280304590000020341600c4003841560040c2c03210700314260f1503410b050b1000d550740c540c07940c40c58007502c18002c0000c0d400c040080d41d1001031400b58044c1100c03102410055417100d411060442d07010f1030941c40785142d9120383c409007580c1400340c00340103510704008130148140c400c03079040315040140c43c40245000c2c001c000817004181e23034140c032003038829912510600700500c4e85070005820302080780c000140550054116040e51400c00b00d03400116161031601941145422204041c8402b205032240301e100b54800140080d04200e0040d51140c0f0815034400307d480c2c4c82012a0404100007052220555900d40b04000c1050f11716901006181040d0f800142c0d94025034448808020098000300c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 303374910 1250 303373660 303373691
    0x1505010602150a020d1a03060f01030215130b0d09020913020612060616030306180e101e0e06010f05010807120c050903060a0f0e210d0207140a141f 65
    0x5807029034140e020002d0046c03070342403002030481a042c040d111784941c2001c1080300d080641820b049950041c2000844180c81480b1803982e00400d110444024481e003000840203408002411200074403000040d080c40d082c81080014280544051400e02d8041e040303100589610088600b10001c1035541c442c40d5440000050640c4a0700f40042c1102d080100344600f01601608110150313081980200304d43e0600c1e016100c210b40b140140e1440c41c1e0b1001907024040c040551120315402d65000d400352240c2c1040c18010b080c1d48001e0084040d50b8401d41c01002010480529000907160903e003465690502d1702d8000d140ba407200300c0c0c10401c0c50f6502d141020143c0144200e4a6144001d001e8450914100c2d4410004002c2c2407600701150341400600d103c041004a00038030f4604101c0108a10320b15406458011074100301041144a68200800c0f004030f0814500e02c1011075100c001020600075030b16003c408402c400840000940c00307034440e02000b030203000f5000c081c0c07244800000f91341a49051400c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 303376160 1250 303374910 303374917
    0x9060e031227030c060108071a0d0c020a1e0605060105160303050712060f08010b0a0e010303080613050a051906060c0311070312020d02070e060918010e030a0c1505010602150a02 78
    0x420362100003401c0c0c891010106605e8102c600440c2503c000e150f892040110154140381c0c02450908104080c000c0c40c582a40720380c040c54800c0c03045a400b1842540c031704030040900c2e007001c0c120041c140c146101b048010701429a01c0202840e10b141098040312100305200d0030100300a05142e00d40300000c000d54400d88440b84c07210140401440580d940b640b00d02480300d014006c0c1c0c91503509000d04c8030b0180c1440c07840c810071956080c40d64038690786182c404035101c00c800741c040c07684455006803000140d01103006684c01884c1003c2c0009403403c010114080b0000041c0c0c40806203410302a08100c0b07660400c41410003150181042d020141c2005032841c10041c4c60340001b01503e41c43d4001000341680000c440e02c20314001e8003281e10882d22881b189280100c1200c0d442d90020b40c610000d1000d45104d03500e030101d4020100045451202040340034250342200f800c01000a01c100c01c11424410303007000c80741d40030040132010041c6505200d0002d4441e2810f408080120481c100841c03806400c0e541203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 303377410 1250 303376160 303376231
    0x601033c12020a121d060408060f0c09060f040e062d0d0c090c0f02070e0c0a0507020307032d050c2e0905010807081513020904060909060e0312 63
    0x3c00ca070400712000540001818140780c003a0105d180e0b000c1c1c4250900000b210141c5400c58001e003029600c003540000b000000412403540c480c82407103603441c1354035003801403c0d24100a40c45185c0341da044c042051170310a030007402c0a110f480c0a071880817410392601c801200846804e00300c08003000c51100446e400844041c4010003c8070045d000044e4140d15038040b0b0030b4002c003640c0c0d00002050290040ba5a292180240c143d1100c40703001040c40c2d48440780081c00a094070717052942c1081519000a400c0801c40c0d4019510038101100003c010560b090007400581c6c8a00c1d0480001c140d142c031801e6881c028142c019002d060188c1c4460042d100c1c2014030700c1e504085002c8680c40401c00c02c0c00a04503812442190b02140100d0040340c00107014150b464494003007141e031003440010040c100044c0c8078003007004031061503080101c82e10a4480303000d8000030f02048600071901c450f040c41c001c4110341440546107143e0304140111031074040e08002e86c1c1c2d000440c514415140c800c401c4000b40f000c111f596134 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 303378660 1250 303377410 303377423
    0x30b2101090c0b090907080405070e06012c0405011505090f0f0303030405010b09060405061c15020a0201240f0902030a0b0405041407090c1209140601033c12020a 71
    0x14000b46811061000b00309603582031750300c0403c2c0d440762041a14410804d1300c0080c45c2d0b8005d04814004103d000107030a5010005240044520300c07041c260309200f0402d602d02403010308100c5004909400e06000b03207070042c4507a581c80030305a081000b0081042c041c900509100700f0005482c00d13a1070b5109120344035000401403c1d01d5032420646800c40c0208580c004542c00340c5903e000080c4680303814030403141b0414010301061100c4803184180900d81a03400f50846041400c0c0d116488008054800303403017140a6500000740c0010380c6010125204110801c01d2130102500385d003400310f8400e24003410100c40200c6000750b16520f40003440d0001d03000c10200c007600107151500300024805092100042d42c070542003500e5645440c0c01c4c8071001e03546250324040209440220908802c81594805c017043c41c055084040b1100c09640c0042c1051000e81c41039501d04405180000303030000403c00980e80c15440c006048290035a0f403070305100e260201394042c1100c0200c4c40c00f01d024a00134056820031640c0b00d80b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 303379910 1250 303378660 303378683
    0x604140301060b0c07150c0c05040207051c0f0e03070b1b0703060903080a1b1b030e03010c021510050f0f060706050103140705040b0f040e0a0807050616030b210109 72
    0x6401315951021881210020001400900842d5010f1110418010f130003420065483d810081400b020b5031054104417168490014030401d82c0314071900420310201300b40d80e40720305408040802003049541e0300402d842500704450030400340e2800b00031513226154140c500e2400c1c102044009081021560000c0c00c128281300004041560040a50340300c4c6a001d035003005241c85000720000344011132451400880d0340c010b0303c24040d80ea000c0344c04680b01e220380f405e01e01081000011a037526084406240564800158510700c9004800c603da031021300701603510180c9203044006407904c4c0407901902e016045000780c0b00a0380c0c486108484210350401401e20040d6500d103042d407440140010000303034500660303401260f50f04d410f000e5208240c01c020300280c07050310000d0400000b03040340e224040443c072490b05500d002170707005805060304500420151100b480c060700300e503903403505a4030318200709450041086003d03615685071811030302c900b0710130761100320031140550300404407aa030142480c1c1515 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 303381160 1250 303379910 303379927
    0xf010c021306030c060906030b22090213020a0f02030c0a151122080c060f1803070b090102060a0605010813060204050d050f190305040e07020109060903080a050c0301050604140301060b 81
    0x2114660105c0b001942c6184450381c0e00d040c100c00300e500019041c0da10805941c2d800302481348081c610f002d441c0c464000040d21141641c0090308800c48002440980383e008242075800a070408414910800c07280051403400750181c0e426500c4144c61040101144c5a07881400021003c3d80e00c000c8104810340042d42e560070010b410200c0000e034400441c1800d2107030b107402080e00c80303010075040010750000d40942d0a01c03003280c02c1d00005400503a468102c181c4140c0030b80400c0d0354200900402000d820030141d0755101648002410320b540107140b02da0b01800c00008000a9074841700c60390384200407406001c540b14451810304080c1c410390340400d5210710015420707014488003094950100d1005404c8500007101141c621207030a01525015021134004d100401a44d1103280c6c010b40d0101e1540b000180702c4c001070351540c00315101c000042d000102e5100410901140f2841010f411a18504003182151700d4100001c1441c030a42c0602c0ca8103800c111a0200151025000031002e420501411030f110b600700d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 303382410 1250 303381160 303381173
    0x91113030f05061014130b04231b03011e080106080d081806040201050a12091505070c05100c11060906041a1006051c0e06011802090f010c02130603 65
    0x100d4001c0e1002d00914001c90301558034544401d01701c030b040c002008080f032080020407501c5001800007024003030310b60b812910982e4a511800640142984071180c420030280c075688034412004103440480c22003c0c00702107403681010260390450f5002c0c00d654001d083ca4440034a9114641e5000303a81541c02c114000c40c0c018408036840c1200340040d03403004059079550311098607a080c61010340e08150416808107015500c2039008016490b55410003a0b0360480d0b0741840e0701240c048180540d00c900303080d4440b0411030070f40d004458000560f46000d08106441e41c4400351900b40351584401026603400708a05110b0060804002c148041c60640c1c445240c40034a5940f40c9404032001c507410b484810354801e1618120f500140160801c8000c1c0c0c1d52a420240140c5050740800100d9800840c402e8182e210011180a0300d440310f24168060071440d49003800419094500302000020b543c01404510395507100e008515849003000d02c1d20307810408413400452810846850020f208909100010050108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 303383660 1250 303382410 303382433
    0x2070303020d140a1416050a051209211903020d0f0e0d26040b10080f07080c030a030e0616050a030201020c0c100804030e030102091c0b061909111303 66
    0x103000038086000040b0a542000b00101d48013940035030700360746c5404554421001760040d6111400c1080c07601030020100341002c402201d014981781d01c050070703031914484904413050800c0d1950b0f8103c0c1c00c10080710814950840c42c00090700405901240d82e64031400e694004241070295a10f0801544610040b84c0f5101d84000d100840420078442d1f40d81705030110940b0200b90064440c08550294603103503241c0e90500c1010301188560310040502142015003400011200d0301e130740005181c803d2400540c00e0420b450781c20541c1c440d4000da0900c801182d000f540081c05840125940da80e10006c00c28025148914550060075510070314401004042d0150b00620880c40c0c803074119040c1110080400c180d40b88500030040019110304082800a801007075243e0341080300038005814440300c1408200e482c1e400132101d03403250304410091000d1201c040015500410f0035106000c0d0b2040041051100312078a10a5500295440c5407a200d00c01d03442040d206171000035003003a114179a80341401c40d082d40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 303384910 1250 303383660 303383671
    0xc0303040b06060a0503040308040812190c080c07030e121203041e11040c030603120f080c07050a0803090102090a030606030b070e01120c09050a03060501060f020c011202070303020d14 81
    0x4000c0c0d020441514007281684e806031019a1180c1c9580d42d1035504650841d070140049402d55005d1040850011a02c500325102c2c036040d1114601c10b89482c654038094840d00440001440403801c2445540e19580f0110b403051500b40c1403d4110740700c0180882e0714000003c20059150141c0318180c813044103500011406035004d02d003010702d443c0d290b412900d00e87c810000c0007400b8280c01005a20349042a0300102c2c2d404186050001c3c4250341d9496046c44940d44140506c0050059480300314000d4211040c070f80c0280c490640c0505000c42e5a8410356900401100a0400400800000c41d0808250101d0b0003072040900350070300461340c81c6081b90140c40715000880390300207000c001034425813003805400704070300050751a40444100e8450340780040030110807170810444245000700300343d203482c00c001c0300440c4600000141503140050081c42e5a1740c203032520341107420004000c40c5030f80e8012030304191000d4540b001660b0300e595142c258020310076628641d42c00390504403020180300c00307804210b2044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 303386160 1250 303384910 303384923
    0x10e0405040c06111c0f090602190b060d060504030f02070911040e040816150612030e040c1b080909010b130e0a09020d060c1404030213050c070816020a05060a08060d170c030304 78
    0x203032312200c3c142d80b50200c1c0f03052108164003041100000c11009803045421400161031000e40c000c1d02d0300d900d8252241204c00b5008580403e101118040e41000000000c1121110401c07540307624030b40320811403084e03119003108505c000002c941030101442c01c0300d008401e50009d1580d61102450000300030050b00b00ac0d5040711345881e00010742059805481c003911545645c6406544100d01c0400c0018100c0a1a4800708a4500c0480f04056040e40080110700d00444100b0740702c0011700c0c100441c089050300000c000c1c040502c041032405001c1140c41003552140220440307103a40e2800503100801c044100650b004010400350014040154402c140501d456502c06212980e81c2424003440c1c1315a01c4002d42218a0b1840324041e41c07403962025070052814035040c0e29024203902c0d1000a9040000c0075841c0c4d902d020f0001d4110b01e41600340000501040c0e41550030615056009001004010852030040110a58140c2000a0100b12000039520700007440e40720444207400321f07038a070070884044400 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 303387410 1250 303386160 303386177
    0x6010303020709050903070201030f0f0c030207110a0513020304050114130b10050319020409080f18030a0b1501020c0604060e04060f120318030506040303020702010e0405040c06111c0f 81
    0x401c3c3c503600685202d40002001185000c20b194011002000b240c64407042d101c0c1e90390101c041403140c500413024104002c0d500561240da0b1410552804002106a00d2041003d40b804003d02d444a4800509043c0003000058483e40c5078208280036010404000205a40110030030007603040e402e1014603128000e11601d180383e5548110340c00219418054154540d110340301026121139840310403292a44050004500007490742e0b6202d180760070a6640501c00c210100f000e465002410300d4032b150014080b00244105112a2108003c1e0702001d0071500346245070304030720840d6074020000c0c080c0508010b024641e03500d030b903680e00501c2410b40104142c40390341051400a090100c0d42c0100701661011035507020200780c1076400340c82051a8021200c03107941040070000c0442c07414040c55111364061b490241e62002c941c170004250315004c0c15041d2160749408284800b150ba5040060107640305820401030320b900701300b038031480c1c8102074521400b100809980002026403002c0c4130440c5141545980a9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 303388660 1250 303387410 303387419
    0x190f0e24070302070e10170a150506061b06071403040b152701090b0402070f030e030f0f010911060403110103090c0b0a03140603070f15051902060103030207 69
    0x2008080501030300c0340d001029514040050411005080303003440390044808140d41d490b0204206081103c0c0522075000348042005006295480d400c0c454101002400840c0fa081e5182d50031209400c0420200070340d540c00050650f2036040440304644000c84926000d50a10400555070b00401c03152500040e03d030f10741c2d02071603600c2c50050700c0c0a5580048540600d5071801003421520b240205003076403081e4006100c4a941184102c07009004c83c0940c40b07001c0d90760402032094282d41c0d4a00da02409148104509404100500c00c06003040b98503280a4105588110000c0c0c80c1088144614000740141d0f864040030140540c00718040611800c2c00030307241b200344c8041003014026448050f040142d41403580d40250320981c440c2c1c11240c81a06041030a58076000426226046010042e0100c2c0e511103175109084000b8104540c0481d04074000d00110303003401d8801c42011840d1148035a0b0380307c101d62264015000d40103441540107030b00c4000540800d030020085d40c070702081c8810760150045000109 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 303389910 1250 303388660 303388669
    0x131413090c081e060c0d1104080a050c010e010f1404170615010305070c0b100f0308120a060b04030206030a020f0c1e010203040209060d03110f0a110402090306040215190f0e 76
    0x5003c0000300c1c05000180c2e10703010381e4180d540c00036020b1030550703641d1000158920445809031001c0d00074440242214101468078a18240103010680c2c18808007555241c0300b60f03446803c2030401512840d1050300ca004148061a0b00d0003036070001642201d4209482d40704020001d041e80c828074942900ba801c26503072000540445e07605a6002001411010b034240c04540b542c4000ca17000310600d014014825139400300d0404c0d1099580044811000000d140c0c4e03a0720000040050708010a5a810401f041c60907903030280511072848001c0c064038010002942c1114280c0c15101c9446c48460754a1781c2c0c241818215443c5c842c00002d180ea1120003080741c01420f8070520035644030b15805401d00341642c070356104010900c0d0041100703d081280360700541442c400c00740040d101140c107240c02041510020f24142c407118240e01110343c0130754411b00121090b6900015065002501500d0543c4020f02c40e07840d2018034410340302060404440c403142d59002651100c4180401000359a84520341901c050412 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 303391160 1250 303389910 303389953
    0x150d050a0b06190203070b10031a0601121812050a18030c1a0c0d090f060c05060c09010c1e0213020711040e03160503030604050c131413090c08 63
    0x41d0004014086543e000d906a00d001c1c4034404140100c03420114550741d0b0020000c400c4442c201903c1c844607082041002103030221580222240701c0c25260701d0b20200080406003801229200d003902c0c1c0300080342c28a0601c1005103510342001803440b411382500c5019102da8802c50b200c5001900c01190a5130580141c8842d0003501d62110320860000d1603c02074601c25012050710308041c18041200d585818030070080d00324081c1c0782d0785481000b07a140000c075080000c0568071a900f0300c1788154150001a00c0420341c15840f4032120180b0381c03100c1d00d00d8012103980c0b41e00e1f000144600f0302203400c810850044812040c5451084a0350101c041000907030b40c050303000f82000149440c40c58581500185015000031144880d00400c8038189030814000d00c03101c1064071425a81134000005101c1142403500030316038004120b01999107801040e00c00002e1450807480f408100b11a4800642c40f2507176200c002c4012445500018000800c2c03d044c11045d0001500c6115103500c541c41d4814109040d40410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 303392410 1250 303391160 303391181
    0x9091b0909120a0504120f050c010c0302031b0a0f110406050f03030901300504150203090a030f050433090503030d18020d0b0405010f270c05150d050a 66
    0x2614a00031210b103800202e4000502d210240682400080f400d00d40a5820203521070107840001c106814a060440c1801491340740c06040210940007140842d40000c00c4800d8910004070500c01c0c01055078210307041c40005d1800600c8000344820400500160721800c1c14001d50444042019a5840040182a035156401030390950001e215541480d801141481e6440c554201e0032045a000755525400441b5000014a0041e035076170140320034801c21804190351a10503107000c600e1400c1042500f07a4882c0d5004005080001c0c40d6200c0180510900640b0018002400c503074000004103503540d22a510015030855041c0001d183d01f000c2680b181d09000d0031640e0107005035140201b908034290191036020707400c200d14032020a070303440141c498280407002640180820445400c061400c60700390740100203d00c004c0d070b0030301d801c1d07421441c2032031804900f4001038401c51100c3c1842e031a0031640e0302c0c25036000300d500c40d12404a011958201100070304011000502c2044155106004401229035040d003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 303393660 1250 303392410 303392413
    0xa0606090e0708061201061502010b1e1203091c0b07180618030f0804030c0f141c051b1311040b0a020313060504090c020a0b0708130209091b0909 64
    0x101d502d050190406a812001c0600038401031002140d80750b0a507030745580303d2005015440c41440383c43c1e0b4284600d2100030022251003102c5040c0068112488048000c854070031040c50b000e01c1465002001200c00709800607000e52020701d07110b4600c40c0c5041c1c42c1c000966400e01c10100080806100d038551031146154444604d1402c1d041c00402c6a000201d800f6004c002e041035000440820300c407000450042d4412555143d8a43c2541b50a414044480c4d02010041400000c240003001203030301d4024002d03134146e6410b5110f000c04d141d016812403010602912034000d291980c00484030003c4000d108020a48003020f5240b4403107451411541807849800300007006001c20b1084041001c01004515024070459080c084e81050815003414a0340c410340118000003000c01510701e4034061044241401e00192000c0740440c3c88401c444a00142600e04000c0d60301c002800d6100302061909038150013900903002031912495041d078078080011059064440d10112040304e150001d4482d10900c0f0420 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 303394910 1250 303393660 303393689
    0x22030605011d01140d06020c16050a180f0209090f011a0a14070203120f0409060e0114040e0f100e07170d030203280f290909030717030a060609 63
    0x3d0384c1030340450b15008035948002c1c220b00000c08100980064410030b0741110240909210221019400d22001d0f8440390040c600c00108119682161030070304203807a40746502041304070b2140354050003441600000c0ba030290652052041520141d585107042c3c4007409400c030703018210780300c1b1050580900148500010948116a4030034030084026044451010702119805141d070801e1106540140c5c01c5501400310200303003040003209500440c4e00802a0f00001072f09941440850010890780c0c95445000740d480d020b03204210501001061072442d0080c0035a00c4508208090801030312a440300c94604ac841d10202052441c0c0280007e00d89912072001403124105ca08000c1d0060b4200504101203c05401080319803907140846c40f1030649500d81c3d0010b0b403070031045500400c4581d0812000504144010010301c0752409c8400070891000440703540f41c10340d0310044503524510440c2c5000f4041c0c02e01c17000400d1b4110826010314040c2c54102e01c2070140c80e480d2201101c0394201d5101c0d6002241c50403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 303396160 1250 303394910 303394919
    0x2071203060b03013f030c0b0705130b1c0203010602010606180528090c0522050603061306030f0602040f08030909040201031a0907090f05010504050f09070522030605011d01 76
    0x5102c0400f160b0780790030304560f5107100c0e00c4402c07405d00341080c0e00b075020500c3c00c1600010442e000341841ea0108036070074400d0a0a0303210031052074428803401181c0034110300180041d45036200d0090124500050b0800355603d68442c40300038040c0c40c05108190109428801d0f50403c902400b0700c08042d500068a45012503020102e0705010100000300c00c005041100c202280c44600c2c0c0c018489005483d0711391558415165925980010701400d000d0329a00c8070000500060f41c1d02001c40303410140886807421445000604000104002d44c00107060b000300f00015810041c5580191040350700301444c200c3c07010b43e9854101e0b103074441d2645082d4004c10350b100050066001380d0206090700041211001400c00883c0481e94150041e11040c000c203512007001c020144441d44003a004d0403080c60014181171808000c10200038440104070700c540c50b244002056217108500340d8008200610007541e4001c0d58071180f400c600c010380000e0714103d0602e4008078400e2410904a480c100083c44511403581c80c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 303397410 1250 303396160 303396209
    0x7020c12031611150a03020702010f08100e0c040806090d030c0f020312190203090c0405160207030204020a110a0f030e01140304060903020c100512010501170c13050402071203060b0301 81
    0x224450780c1d020320030118844c4a0343c4001c2c0608640805914016038465040c0009004003140d0b034141c03001c0142c50020480140d1040b08204115400102c1402d101d46031140710904600958108113954410041000074400c4001000101da40c0c1a403810490b9001d80102151510740c005040340141c0d10400003074426000780c07510140e01010002288402d410b20001803030a980c000e0b11000c5040e40300d001032440920f0503124480e000100481903100300800c10304041e4403a441e6110280c40b9a90104409417080d0040f5840c40c400044923043d83c26003411450500b01038241204107500180d6600725a4966501800170b10300c0104100016506607a100d1391201c1c0070380181c2a048046010380c01c640e00703440d101e02a00c003030305c40825181c69803110703400032882a1001059000d107040110540310826101c0d1100c103a00c0d04040060700302940c4030003c291a0a0809980e8401a0031a10010300c80044c0311069600c0c40c20b892055805000742e80c0e0740c0ba00c050150001b80901081100c14100d184800800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 303398660 1250 303397410 303397433
    0x70b01060c050106030b04110f06030910020f2506150605071415010f08010f0b0603071209050a0c03030f0f02071403150c07170711040902030a05010507020c120316 72
    0x2c114000f05009480f55039401a000041d2070803a61070782e0422119820b4038000070f04e0114070809640182c114a403075541247c0e02c019480e101c1003010360000300070b54400701c0d8104684d4241c0d40100200880004143c0d18a00a1608075098660074948403403000a4491005038030304550703042d55001d04100640d00c032031b00d103098280700101c0300d4860184075044ca078400d0a460760080c840100c7d40b81c9201d15042c80a42550344444034107070200d28120703d580da00c1d500d10090301c8c1c00009510709221200308030440400208003a180103411881500441c2c1c04000c21079039103100707980c07213995145d103080c0e001c84d0203a9603c690310300c880c0b0150300050014405400c02d001110a0768000034211105003514680700c4810038410340b00c1140c0030350b00048800611440c0701040f08020000e9000c1803402d0041c0d1948182c0380d0381425064400c5407245042400d540d002c1000301c04242d007000003000305081c0803c0195850300281c0300c06005101c02d96a8021008000c41a034820b00d13680b68020148040760fa64a859061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 303399910 1250 303398660 303398663
    0xb010812160210030912020106170105010803121801180c05030c030a150b060d020c0d0206010f0b0304150c12061208120a0e0714090a060b16030509121b0105070b01060c 74
    0x40e45c51000d200030500e5015140803021840d00009411828441003e900c0408070184086903818400100441d000000c22108a00f010488986158035540c544484851384001960850341c04e0845920100f0385100c10300c00340c0f500c65945c200c0300a9880c0c0503d41c94410000c645681604882d0400c0b02040c8248500424a0001540011486d81c440300180396a0005e20100e442d465003c90350650390002006151086401400140b07810340c54422485c3d1186a50300505190b610048003081c10407805603030f0001c0410040c0e0090000f1044c564006000040180c81d002000c2c0c10400c0004000d44040000706155800500302c61034108061500707025400090400d5454982d01c07030103019440c400340440300203015071391288007541c00c070760b0100104900050840e0450602c1c2510801c94289250101c2c1c03810307091488800c041034054107056403107006920304690007140700c0c0c40480030f10b00046000541581c94184070741c0c56806000045805000303202d40101380b90003e030014060b16018881d0317036458a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 303401160 1250 303399910 303399917
    0x1050d050c150c161701020310031101050d0603030810050a14011805090903031807050d060b04060b1323030303220807030302032707050d060906090b010812160210 72
    0x3012480e440f80c9000301c40c1c008100c50302d101d4441484607940320500380701650b42c0c980c0250b0440c1024003113042c2240c0d032413000a1034450b00340b0040e0740d140d008405948041a00c0403007005811741d2401c002c1d0071402c08440315020004514004952843c0c000100d8040d203104d800b40c0342620703848100648280010b140c82051000c2d4110001803643c1e105540544244080005141c0b03a00b0410180c20b01c9442911300300e800d68105030820300c110b4866040020000b6040321003c280308a40001003002000b103a04000da0b0b41030000341c061000701200541c0406c0b5601c0d8800511006403075001c180d070f03a004609160b075044e0401c102051941407800d40440007516410f111010080305581c0b00303a4181c3c0710314401c4010235004810480c0746070070700040c1062550b50b03003620b010090001282a417160040e02070325116200200c4203405000c850751001c1c1003194842010840c01241d4209408602e400344900c141500c204114a00c080e10108140c0e4124401706009032202e04903a420400e031340c04440c80d60004c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 303402410 1250 303401160 303401167
    0xf0a1d0d0e0d0803161e080a1109130606021911190e0a0603060606020c0a090e2a03010c0c0804091d0a0f050709020721021501091401050d050c15 64
    0x2c0f803035110066004007a107251810035105020000341034580001040b01114070380128030071030720740c00c100c00d25441900c2d02030001c2e02c030f400d1120384c003107038001c00d61900c1e04100c0c021950f15902103640e00090681e840c0343c003198034070b040034104180d13041d1066030003d0620306829031901c614140f503c0440903034010035400341001c503181d1041100a620459021002540321101042486400e1080e01e01800e914806415810303c0000445d2102c066482405242c40d40e403c0501c41c2040c003400b024680056a00c0d240110450f000040c452140055001d41c0c030079441c000c044c0740c545010b000f4460f074036a840094142081d00d484240c04c000c000c10851319288101c50311841c08010f90500c45020841d01c5010050350158107820264945445504003c1c0c01c14410444200480c2c2d01c2c00100511040e1202012065010404101c2c2041c242c140c02d160310750f40002c0040741c400420f81000c0780c008034806222085a0744c480400c005008564009402c64002400d0302c610750600038001d185900c480080e4918 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 303403660 1250 303402410 303402413
    0x150915030209070903060507082205160f08010609020406141615050901050a0b0604030f020607050607020706020c0126070c051b01080a09050d0807020106030b0f0a1d0d0e0d 76
    0x302c40807100540051944101441084180d00c0741c5508001507281812040c42c022001c0701d61141105c130411800012030280303104002080003172084140f00c1c01d01d0f040e00c3c142d5401c66a0586074040c01041001e508182c4d01160704a940d10903170701107855550b80ca2400e00c040c7d880358071099104810114090400c0200d000c00b280812140801c401451303a400200c62504080d01821954090002c403000c0382000000c207016501d8038180c50a60b50040c00c0c0300032607070142c400078800d0720400600030a60302501042002c016000300b03144040b104950251041c0074040c00044400e0200c60361005a5010440c3d0f089d00c203004045480d80c1d1280359810403d08140303403611010f181001c00000c1e41d0351004000516802940c2c800481600b11860540500085400d0783c3c4203500c1c9d8604511110412070720384001a1030b103100750000302c02075411031880c803010700300b4074174540d20301d04100c4000001d207040c0701c4001100002e000800f03840783c40120207060b507007154080c03c032202c0214070440c41d4094021481c440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 303404910 1250 303403660 303403669
    0x30403032a1a06031f0c03020c0d02010504140303190b0f04140a060e161110090b040201081f1811030915090a050709230f040b0a1509150302 62
    0x6014a0003000e200ca070b105550001c1680c0703403600410f5079009411101c585a01e6034010402490040503030103002c1400c03028010110024007030b40158410b0ba00c1480b0040c40c901e034065000038000e501515052101e9515112100d580b44410740c2c552000d8025111800c0d240c414603841421195030081500c00081501000201a60080c2c00402900304408041c442000340030320880c40280700e000c10003610361500800c0210910b80035582141800744a8011b200214002d000c289040c05c1244402c01c5640081e0400800c03d43c41100c049000c1003028000c1050340511100105120f0018940c4080003424068010380013a003410003c4003e030b480304422401800ba0034044c5100740307003031802040030720902c1d40740c0c44034201c3c050141842500540c0a0307801142000c40c0311400d4881c00d0744081a01d548240701da0300d8613000d040d211400070818405105c6208800500c0500035070103418001260b441d4840c00300111030384900c109024011411082122045c40c1c0c00201a052030300440040d00341d41c03600481c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 303406160 1250 303404910 303404987
    0x204060e0906070e030c0109120303021c02040306050a0203090c0d0206040b0c0c040b0d0c1418070507050114010609060e0a0e010f0305100c08010303050304060e030d090c0504050903040303 83
    0x1c5520b410800030400c54580c440390308180880103d00030324404080300c001a04d00202030050208a668288514050500980440c1d04003212104942040c1c03403807800c180002d400030f00040b06e2a41c18200413802d1103905000b0349019031841806072500002d241e08105a45403803101c200e0b0816070521000070b1030300ca000064540d8140d00e4002d0002500d0527401c210442d66000c0045102c3e205002c40300005c6218220b075031094840da0700d9240c049518200002d40c054600490102034103030301e08100610300e540807003c0e0280d80e200304001d0003054401510b49424090174050180020b90a642c100800c0d4420341e1008401400a000048500c0d143d10110020850076000303076144030591002001080020070600314100c0e00c021301046507403a64030f40240302c5401884094100301b0301001040c00d210566201d00c420800b00030440f5a1100c0382e2341008040c01c15804241c0c3d0b10616800c0c0000c10b0308050203100d102e6061a8065031510b4113560f41540e111003d8107086818860003282c2c40b00c011032001c0e14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 303407410 1250 303406160 303406171
    0x709180c0c12320304030503070207080a0303020d0b0d02030606150c073b15030f0a060b041d0604080a050c0d050715020a0f050c0a0204180209010f0605090d0204060e 73
    0x1241140812800d440c0c03515103800026001c2c2c050400050000351500f0001d036500240e040c5821682d940f1280403c070f2904201d0b4010308800d00a14040500f0541c06178002e08180d0901c000501102030700e90104944400045000383d05a00036800244043c500007481c0070350700c01d41d0340b0300380d081034030421580c2e10b0400150014132000300800c140703180c2d003502c80310fa403480b80e8904c1d41c11041130294807440c03036254040946611490440c6401d242419a001d0101c6041400101c040714120103042c14818050100030401600035441c0c4803201e025034504a9800d41003103242001411b0f280c5072a92510031a07848403032035908200b001e010552603c8000c0c801d81500030301c50781d28282c881c42076083c22082c180c98141c40e10820361040104202d03454004580180400140c18596225240c0000403424440c0750107000754082d00d270802101880b030b45d44440030f64460080e16014a9682c039103911254450301c0e070145c100400e0052000703032100e10349004c0c0c016056101910105607a5500e00014041c8082541d2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 303408660 1250 303407410 303407417
    0x1807060302160f0803061c050312060a0806091608240a0207170c06160e310e01060504020301032609090103030c06150f030f051509030a03050709180c0c12 68
    0x18406d4a00c0c02c480c00610312004c540741104003002c2a44c0c4c0544d24410a20f1a8a00d001204002546680c440c086800108104015030350075140c43d1100c5500e600512041c0408109001c6002c40c001a000030840c90040007101c1c081000b206240300000c0b5140b00400441da070750b400b0446500050380b000c104400c5010010445504c403005000240e061140003065100c074120441c05815070f03c5d03804860892100700507550800851040803500040030b005031b4603010015001c6039604021201135215030ba0b001c1161000b0402e0b940c4840030001648402c1c44003920301c4507040741400c02c07800001c401060303d0810b00e1071030385807603002c0c00400d1000b1000da00c06c0c1c0100380c00703480318070503c0107501851009042c16100c001100c1d041c600d040b8082e1146000c09045188001d0b01c0d5400c1003010806210744582520010b0068904240c41c25a254070080030100009d0502011951150080c0f07110740650b9035109554401c00c0000c500c09008140341040074003044240d001e43d0780851141c0c401c0140c0803d0a030b5 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 303409910 1250 303408660 303408667
    0x22090c02100c1b0305180a080c120a0305030105121f0f0b0a06050d09050a06050c0c1209060304030c2a051509130507021e06040b1807060302160f08 65
    0x1815000ca0785400004030a1001d945004200c0f83d58602e99540281d515050403615000b2001c240e4180084400c0f003a6041500b1220109440d003001600c2469980b085a05001103404010505e0311030b107002c280100894010300040c44540b40210300c0b003084540c1035046602c041030444082840741c0d1001c80000300c0702da40c4c203641d141100042c000c820380304400b500c0702d00610789030440081551040800501d03105940d2035070801000300030f0100c2e07000c2640140c13003070046081c910510300041c1d104070941d9a01d0710600600086141d0b80700103640d60f500b0020a01800d55a0b01e48064580c005c01101c103c0340201d101c0c1c00800d5001c04000000602140c214a1001a609280610641000e41d001d41040410b0600c888421551040c40704000d1003245100071485445000b0141e1900d41c042c1e418030b151100040980806450004042c0d00c07460182e14000c401e500c90201203100310080b80b107030402c26004000c09001944c02900104090310f1040a000e4900d580ca44404061044900c41150981c4001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 303411160 1250 303409910 303409933
    0x91e03081009020a090303031d0715080709080c10030924110405030703020409020409150506130608030a08070905040c03021314090a11160803100b0306030322090c02 73
    0x59031041c00703400300c40030851600700300c180090242c0500b0700c070060804d1348503a0418085505820744000d00c9030160304450000da1201c00d8550f80240002d02d0302e0006404c200000e482c144a40c00d04421202d84402401060003400d05110641c0001c0d40e02906050f1100740d41400104000741600030f12081c0070740a81c0341a91041d40390300795812129640c0c030855090005109554011070040100e0b03604540000304010076101040c060051180d015000181003034200c15404082c6c1c00861283c00f00300c071400d080c444403040c124101c03507550042100070f41c018019440554021540b0541212103401c02041c815681e5001074141d410b4280e01c800042e03004a1a8510503c40c1046034000d00b980040308805950707074401048034408020130002009849180101c9064294030481c1c441da80c0039a44a0b255540c00e04024403140e1098800d0b416641601d00e0004a444581b010750b40545c10050203186410b040790b0489c1900460700468005150030b9110014a41000e4419180300c10400c3c2c02400c0c246804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 303412410 1250 303411160 303411181
    0x3030f0b100305070e150d0917070c090b1e0d1a070215010b1626040e0105090a0501060e0103090201030e07090912020609030706090510050f01090f0e0a06091e0308 72
    0x206129402001d0800c1101844c0c0041001c0d42c0004c211f20038001940b403011b041409603031049424240c82900e00048020a01650f000c005050f80c01c07160052102d84210f4090002114810084240410700170303070340342c80301c0c43e00941d254055801209445038103120795549449000d42034400f0b401690090410342c8003501088211030040121101c0c0600302004582003102c480c40e208001058414201c403011003021420812915009000116a0321252210600e0641d0328003809554401c80056001a0002000b07004d942e0585480c0ea8500390030200c0c84006401070100d404003241410b40703940104541e6141000b460780240414003002ca841049070404440714420140c1c0c020854014500b04078540c8800000ca030324643e4080300004002c015420b1403414070b01d0b503803442c900407800d02c41800200322400e1242c9050300c5444070704004030240c00040780d003195040120000550400111600440c00b00c1e800700480724091b41740b01c0205c0041440f59101c8410742c080c02c4002c0b8940b4400cbc000110030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 303413660 1250 303412410 303412427
    0x10f08010b01030b09010e0c0d06060824011d040216110906010206010b040315140a1a060702090a050702010b15030f0c070222060f0305010209091e0403030f0b10030507 74
    0x70282401c21205106401144421030f05001d6000ca0490740300106074042c0c143c2c802c852140a007180c0801c6041d40b5641d000303003540000c1e81c3d0040484107100c440745188016080b00100c0317200584600c201402100c150001d582c142000782c5500603070901058a007070071415003030b400503885940603030307120a24642081000c00b4098283c5045510060050241c0c0c42c0080484d01940d41008000301a2280445168060320f92660285141e6030078800f4050142c0480e0001c1000800c00404030144641c0d4000380300c03190041c00710180d40100010085001100c441d8080f035048101c501c004a40d0703092140104501c007601101d80300c4060000000c212542c4042a030086d005070b1840c450500d0821150005030000900303011310400940e03012540014102254031241c024400c03015140c0101303a0b0b9017421070003174101000c3c03d4001c0c140d5000141d14100100050149501911441c104a48803910204c0044c41c1c58046040c505588030311a403000c1c2d50b80e001c0204807110a6801007130301c1c505407c3c01051001c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 303414910 1250 303413660 303413681
    0x301090e0613080d021306120c0f020c1203070b10030507240e0a0806010902070c0b0304020d120306090f0605010f020f0d0c032f060709050105030f0c0d05010f0801 72
    0x41044051112038000b40303031501541a009454140c4950130100660001c1c418101010740d00032600e280011120b41092601e8102d40000c101004007240d0b6010036912082140412070041e048000e0790120f80c903094011800141080c0102c9040011559441c4540c03001030700c02140299000790700b0420020b00700301000203070400c00e6030349500c044201c02028184604e1103444090010300c0c4048482c50700d070b41e0ba0700c03802003000c40225401940e442c0d0003000258001c020075941c450300302402007840b001c0d003c1181e00995001c1c000244901d1603484101011401341080c00801d07460359030010f032070915030003500342944070700000141c9589084005001e00000d448820195040321142e02c003426004100c440e1413420380e00305045120018a0b00711045070228903118919103410901140c40f02500403110418410741e41160055280c449047d0b815090034890300e40000c000b0000030b0714032058241101d4020324081981404e02035214070203070035180260010b0341904a40311080240396403d004908610 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 303416160 1250 303414910 303414913
    0x2205071503020903100c050304030c020613031b05010c0f26180907020105150f0f030a06150807030b0a18082b020f1602012706081006020c090c0c0706050301090e 71
    0x1180800001c7c0490000400103030500500031010001e54442c8411103075200c50042c010081c041d102d1511008401c00011040110018050702250719405403201500040c0c02c5048107400c1c0ca05a1b883d0703401507100382e240c03600e521560b031070292000c04039402502c201c2c01c1c2d03100a015854050300c20700002c2d0000030300840031603040500340300c55403104818240040d6016604110041c900e64003040e5038100d0451806c0d0188610b000030b00074040e1550101140000180380001c81a5440501c140d40b10014003010b00403503d010301149580505502000e0303c1c26440d6a19000003100340c880c1062900801c81130014114442400700701e201c041460100c2d40038010100b1030900c4070501408180c1c0c05a0403400c60850308502c6007500b1f6a004100071401500b81407103d51b02c02031000c01108004c03010b407148101195000b80820b00900d0b4a08086003500d034603500508d841101e400400c000410050041041208104106890840b09000240c06028903465181c2c2c1d81d45000c0840b0100c480c0030620b20001d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 303417266 1106 303416160 303416171
    0x50a0e010f09021c090f120f02060601020613060b0301020702120304060f08061c1703070f08010f08060f15090f010501030c08220507150302090310 65
    0x6032800100214107041c2d0380c2080c00700364003581030741c41c031550080c0f0425a40030b44240e012568490203054816070107101900d480d50b41c206184011780006000480c0ca03804140c0410030586c1040b8203100030086460940003c110002d928400140201e886601084d00c955007501940d064a8006040201d02901080410303900c0d40603204000114540c2000e0510840c060040c40380718000180a02d500046103006244880110341c100f119802d18100084d01c842d1300e0350010b035120f0b00b4a9144c0303000341d80e10001c025103d801c050340183e0601010100c103100845000c0782c4c450b00201607a107a142030b0f403a48040c01c80b940045508840d00310105d6810031481640b00340e0074504a84081e00c0c108030741d41a002003210b11075801c6410383c1108942d23110601d1140145240000500d004501b6140c0c1c041e19080100341c5d505d15801c036400065000320b2500e1f81c919042c450103050410f070340e204110 = true := by decide +kernel

theorem cover : BRFrame.Cov 303237410 303417266 := by
  have h0 := BRFrame.cov_init 303237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 303237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 303237410 ≤ n) (h2 : n < 303417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
