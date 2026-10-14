-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1133
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:23:14.926899+00:00
-- url     : https://prove2.me/submissions/c42ec171-f5e6-4429-8256-52abe846d3f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 203597122 ≤ n < 203776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 203598372 1250 203597122 203597137
    0x9120503040527060f0d0203010f060f0b07031715041a0f0d0b010e07020a1707051506090a0f02090a0e09010b010e010f030b1c060509070e15010c020a0306020301030503 74
    0x225003030720310a40700d03016011816003c075580d50f842050340001e60310b1070000c0c10440c10702c1026120034070403182d9401280c01d442e0410b04072000241c0b601c00801c142da609689030f038020600300354810304101d400e43e0001d003011103c483c0704800b00110f0300406d41301c000751140004030b00c0d00108104090300e0000001c4405c0d804008c0c1e0a881a150640c58840600307001c03076024041d940c41301030705016030708200c0c03014028040502414214859148141c000441c94a045503000c100600b489446450078544185001500288800049001810b000c13464440c18202c6422010700d06008c18400003e4400d5402809540392150b070008000c1d000081a00d0446801c0d0301500403000280f00c960550b1005586840d502600140040d03135180009400a1203540001c0c5032000050040c86814862460b01000024016044e501c1d41d03a03071b90601a42200c00c21101c1c00900d000910a401e5140c8a401401c2441000100b241440030440c000811581c0f0080410b001d958000411512540c50f810a03a6903600a403c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 203599622 1250 203598372 203598379
    0x1209060f070306062f0304240c0c1202220e070801090c1a090301050c0901080709080717010605030f07052407080c0c03010c1107051c060b01091205030405 68
    0x8000c90003507803280c003d520580b820798544008464414242c125060703484820040c00c1041008202000d0380c0502c020b00080122036042e416000101000e00c0001140d03100400501820a034403100103121905d03900200c41c40d41c0010100c3c0107081c004280d40718661b4010280b54a041201011140469070080300714202001c111405103031910306003400c84040c103c0150109214001c100701e0f20004070704402e4081040c0030038a00782000000407a0944200381c9600210901c08203d0494a5a1041010781d00000c10710380b0019040c80c08400325155143c90286400d900c41d4803420241c030341c0c1b003504240e0041178050200e030155000740152540b50304e524051b0034814030480c050a40320105500140080c0304200f4101440d181075550380782c0c030316070081d80740c408240100c11a000b55541c003849200081c2010380c51b01c00070722000d40d07141030a06102da040300340305000007ca056424240c1c0388500c072036281c1c0001c0c006240d504100050350700d18001d40c00751302c40400b19a0807604110700400034004445068 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 203600872 1250 203599622 203599651
    0xf0e0a0c021f0e0d111504021306060509130504030f0807090f030c05011103042301090801020307030906200306040207030908030304030302070302010f0902061c060f0b090a05040c021005040206120906 88
    0x5031403c03144028004804c005c1984021408081485c600c50b507107400c240b00411041c1c0000d01400180140c030811386c0300c44081800441c0601240c14420031900b44035034420010045d0740703020b43d8058000400360411a04020482c0c0c001191103005d0766500d0b000e0304150690340d54003981d038503241c0e04621042c06928000389450304200550100002034805544010300700b5094440e02800898001d2203140c0c6c00f50402c1907001c40000e9400082c80298000c1c0510768000c41c0d0900d81d410007106584003040c03240b40b0030b001440000c0134840c0ca10f00b502d8012a003160056925801410308864030004c0c1e810003403460100005000c1010740641c02020118402e400912110104100f510200d60403584007a40280c7d003002200724910400c82c2e201c0e2a4400000005840c54603020000c0e58224544c0143c56281d00016580c1c03510301c3c05101d046c0082400310303005e0100c1c55040030000d4840300b207901407180241d21400400c0840d0303901025950400021400845d032807a1405500381d5403e01951646441c0d0f41c01c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 203602122 1250 203600872 203600893
    0x6040902030a0f021918090e011a010f02070e090102090312030907050f090601050717040f080f1212041a0a0207020913081c2004030201090f0e0a0c021f0e 68
    0x3c1c000c0da44046645482e45c1509098928107441525004861586404221001190081c0c0c0c0c0e20a00300c90745aa0741c00080c0540704608485546550b8081007410301c10f50031003216040d580045c4000541d5001c000047c607989581001501a000d0b24924603410f0003107500c0c4c80c003901c0206e000345108804440072030b0700250b034450034080010401e0074040e803c462000000340c1c2ca1f50154004180c0305100c0c010044a000c00d0400400c1284c00c0303138112450069404c2e004107e60308080100703091080c0000068004000c2d0303810a207020740f058015408031f16042d440020140031040c600300c0b851004007801a056490106407000c020f5100301d02c124400d51b1a00c021411405050051402181c0d004950500d04122282218441113000d0300f0b584c41f254543c031805003030034080c050404c0c1c4060490219912541140700240000d500c503000406582c450034404c000c040344182c3c0b9150020211140001c540e0400709003241802c8401d4242034859212034000221f5014651010400c2418001500c0c4510304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 203603372 1250 203602122 203602151
    0xf0210091a15010212160b15150306030a0303091403040603090b07050711012313060206180d0309020103092009070e180705040e070206160c030f0e01030b06040902030a 74
    0x148060540183d05c00100c02080c0c480c5600142040050548090801e6845da0344100b000328080340c4100d0b0f4090108108c00701401e22079040f20b0450301e00c0e40c981d0f08510b07061001c80d40e01d100b00c540c05802c00d91a1161038061045e500d20906143d042d802c103580d9a207480303000c0500a8401d29000303c62201200e07001421061088043c1d50059511070822190401c4030401100c101840711085184c400422203407100c402c0e0544001c0102858120311000b003503244c0350300070781000780c010300c0c0684182c480c00304070b42060004030384a440b030700850500017030403041400128024480e4500c01000d460b104400302d03091442d0342101c82d0510b401221071015039030f6070070002c507a0b20700340059041d0048840702100f2417592000300340541c81801450030310708240c1d40f048460311900007030b180900585c10220038004442944981d129280760181800344262529136030041080041c40d090404100c0c403c10300b0070341030f07100750403201a0000040103941c0b160f446121080080d44113441c19140540703000e0300410f406c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 203604622 1250 203603372 203603401
    0x7170306190609210201080f100f0305061008010501030b1317040803270d021302191e020a0b040b06010c0602041710140123040606030504050d020106030b06010f0210091a 75
    0x7076040c0c7d00c184054a40e020582c1c0c089801600c8240703034001c600404a07243c8000c04007100118080c0006109504041c1c1d070303101c2e8804698210943d240d041400500108050402990b004a0004028485c084150800d08003030542e4945e691114400001c0c00110740500202805d40c40086104080140c50a0400382c0149480100c001350809442c030750080c050f01e86000f901c8013050285001520380441401144040780c03134200d0b144045950107070608141c8070a95400d10f40c00381d049c0000d01e0f41510300e89440211000040001b01f11500c41c1e000911264401c0d07180806c010b03400503040d9141e90f141c0d00496181012980030360500c1c0300341000703c040605c19002c1c0d80c0c1840300038100304403070b42d0a02c2c152503036840411401403003028607051204c940b41c5451107160014611a90001400d01309031178014100001c80b50301c02c08680c14224140041a4086841a0080000d003424608a0308940c0264140360405a404602d00d28003107421061241c14000b81080c10307022041407007150742c0d0b00310003400c0e039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 203605872 1250 203604622 203604689
    0x1b0b04050d23090f0d0305030f100617181e0f160e071b0602070b0f04110f130e0d090503070f12081b0714010507170306190609 56
    0x2c1c8007140d410b035441d2100610110002811000c020503210740802d101c0010740b1000c50005200004101c1207003c602070485d00444405030643d881c3d0b28054001b480748401004404120001001058282c06800416144d04082006584145030007020030240010102081c510718020b000c0940c1c445400403a070f443c0300003440f9203902c0b01282011039801740c0c2c0e14001e0400050101c81035a00c09444507075041031010912602016076101040d2400240511000e007242c1605911503007440005901001d1040e07008106070743c8404000072900c001031140301c4050b00420040d20301340180e0f003000404201605ca900c1585c6500384c0051307680c000d16076035008600c102140421040c106016074118001001da02e03034044d0440743e003007600c0c0e081042c60000800412643d40d90205504110f545c1810503c515085424241300f820081143c54980a100284440303080e03040000002580595540b07a150300305d40c3d200d0b805000a81d403a081c01072b0a0304243c0c0102c101900400a2520794510315000540b5003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 203607122 1250 203605872 203605907
    0x60f0c030c051608160809040c0504062c2d030f030a0f0203041a1207110307021c06090f0507081b06070c0b0c03090405090f0a030f1b0b04050d 63
    0x81001e0b000940c203c811445408886190302005400440000700115904550060003100d582d4402c180c1000102d9141080c00c01c1484424001040029080b0f0305040d500d4030a594507210500341980380c0c0001c08065100507510403001b0710f200021440020600182500240c040800d07100307040e0406913a40e501917001d83c070f0f5074009c0241d51002c0e0310070310840b407082c0918011a4181500d0791008907510388040f0ad4180310349404a80c0608400c00c0030540c82c0c1000c95810082d100243e407041c2c040d142d220740d0901a000b2014003103441d41800310f6101e40108950803010400c181300007440d0415803820505c0c0c0c159040d20841001143c9032401169002c031410000c54000c24034074941c42402100c0e0401f02c029201080c0004000840d4001d030f00c010100029020040c65844c00c0c2c50081000304c5070054001403480e4000c05240c2e8001c00c00266000406402d41428810b042001c001160b4071489003d02400300c20400d01c0c0c030700030814514503460066214000343c80d03401e00c40c014102e4082030790b503410303000c0e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 203608372 1250 203607122 203607127
    0x12150506030d0513050d06050406051303050a05160b0103050c100e0109030204050403170405010b1309021018120605180607080f09100e0f0c06130b030a02040e04060f0c030c05 77
    0x942801030000b052004d05095455844a80c0c9500160a4a050000507140d45031101c0402c001c00c460ae108450b4060f40140c562006410076890040050142c01c4013842445030018007071100008245c1c0f22060240c0c450090003466840e458150707220428504820300500e801c18843c0b41c91405141e851301c941006035542410380e45507800308000b600029100b0341c20300103601c88100400e08946030103817055000e9400850465504000d0001400b411031450051510305034030400140d91321042d40100403080d2a05850480708136031128032111140e80040e1011262030901c104004240c2c01682c4920400816400c0200e885032005483e000e0844a4100003203200000038038907200e55450130740240c00d48084480191618400008451800c0042040350340101060015890200202c00b030082054070420b0419075002114800042c06000b40e1070b2110000c4005800341c100f9505640040c43d58001e0100384c1d040030700b41072004204190140300010b080989401d0502d002c1d004800d09054903556041c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 203609622 1250 203608372 203608393
    0x40b07060b060405281d0c0a0324080c090c0d09050f07140a150816050702040c05090405010e060a09020706090609080c0d14031501020c0a1215050603 66
    0x40050030307401c404540c400c10501010a40e40c590702c03030301c18285540004454129412882c17010300080da5501075482001104030003000071881442c102d401402c03243c4001e8a5864061080d4050200d10381500c0e480000100600460400b07445040d007140c8506003955800e02c201c0c8240101850b00700c1d130482c0c070355001b0032208040103101c1e4455000c081c02071003a00d0503000b0224040303042c18a5070380a80c1c50783c40300595a0203185400c0c070f0403500400404002c0030720304003004000ba240b030340300400c0b030720040c10140300f43e14109014904981c0200e500810800a01c058030310060595005800d041780298a00b5001240c9100740f03c40c0140990002090313481024a0010018041d5008907805c940003070b1154001c03000244c40303000c1c600d0701c18441c0200c540c44601c480740341c5d407070000d549182c0300800040d00d01c0d02084213005000c80760014a15881c02c050101c40c0c42c0140d1a10760307216803c075003100c40100005442014a07204140300f034031408003019009001c0844005440c010760352140d05800441405 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 203610872 1250 203609622 203609633
    0x81c0203070c0b10030c0902040305010b03030711010809030706020a1d0a0803030c0708040906030803041403121501031b0305090c0102072d03060f0912020f07030303050901020d05090a0b0c040b07 86
    0x40758003c664030084c0740c0040c0c0f203a43c4d498084205621132a01150041810f00030007000780a1280a0f0200350000c1d1700b040d12546070050b83d07814141a460501180c070000c5410450140100c901070b6030040d005545d03520541c034004100a94420260700d150070f158182103241d203844901e0001300c81e03105c40150300395102c6188a507400d070720039007040b0344841041200180e500040d0050078000c0d40141ca00795101e1400c0e040100c4001c1481c0c1c5018281c4d00100048070b440d4460311451030b001000d00100d1551a01c0c400010b80043c0101005d142c444201d100a20b0a000e9054001c2445003041c1d0701610a4040070100590741ca0302e243c0615811480c24207a0040301e40b24006925801d411250401404141c0c1c1ea2103100403030340e503082d41380c95441d1544d0051050041d841400903031945540300a1006028641c00b6a0304d440090000604042c1c448011848000094040d1501032074168030030412410700c0480d00b9aa20540c040072660600610006a03514042200b40c4d0115200c546126282c500541d580 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 203612122 1250 203610872 203610893
    0xf09060c012a020f10020f04050a0801020301080d09031e02041d010c0e12031e040e041b0e01032102071a0324010c080d33080309180a0b0607081c0203070c 68
    0x47d4a80030305003c0018a80e88922954000b0100c0c80001030b80c95042001450426403900190024801c034188200001190103a0a81105240913140320002110348001400380c135005604003480403600003031041c0104103601400540800b91140c0c0b003484084008c0c4104054a042d144120713800511416447c1c4942d00107912203201602801e515007501c4082c3c1c140c074201c040e64181c0300500e2100d40900e44aa03680e004102820848400408030f6240d83c0d10310681101c803000014181807039010301c8900714001c11600002e40b00b06021001c80001c0304800842c0b40c0c1041703a8100c00400c040a14404141e40d0788412180640b040e5503802c0d50041030703107540d003507a80701c8200e01c40911743c5e40c0d81580d880007014112842c0600070070100401c1000050030400c816425810000450308200300c001015903d0107407450700341c030244101b20150f9071201c1c90300c0010404503141503000b1000280940c2004000300c0105000c000710003036109807460300c0031300c802240011648180422050920312002c91818501d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 203613372 1250 203612122 203612137
    0xf0a021e0d050d08011d040305280c0201081602071e081e0d021c0309020a05150702010807090e1b1605100f020f0f09060c012a020f1002 60
    0x821220000c450340105901c54031004060ba800e800145812000b50340c000c0b0005e005100510013400c0340c5200800805440304003400060078030400151070302c201105a000c3c4800201045108041d041107c40083c0c000a9000000c80c0014080310004000c128100c5580034111041e0b402003010a007000c106501c0c40c6240e6800d074070215030400000910403010480321100c84003922042c0c50000012400918008440e00144190342142036004001c000064043c1a41900b0f0314000c0b170384200d03600110b0010f0000360041a000170280072070b04a059100002070440c24801ea0356441160f0711540e04130b03007030282406441948810400410b022105045101072443c8207428241d05e04590124000e40139101040115411f400ca443c508200130940d100340803150840c05415071402035403954016051240314100c4181c400003181e00c16a603101c10043d2035601d03105600821084d521001e00c1105201d000c054400841d1041104480c1c0303a10101e40d520f000c5104c9c1c1c0040458103d0b4103c800d029420803074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 203614622 1250 203613372 203613409
    0x1302010c1202010b090106020109110f0109030b010b030414120307052505060a060803040501020307060f062327070c050f15041e080711030a0f060c110f0a02 69
    0x200e1010100e518070390360000c40d0741140c000080105516084c06452a4140e1201c0150792401e011f020115101031481758102c1402c8511000403401100180d603036403003607040a4201e840030400030400d6043ca0b002103010707a0140c045955150b100076045a0784070440c2c040e40b0b0890310180040b40c0490301072006010607101c1c0070000b60700c0340130a14244010081d110390a4886900000034811040a00e10811015081920155103013a082c040042e41c0d82c41191802450a980e03695076545e459866481140030344241c0c4808141c1321103e4090302a54080040300b24400c154003043d42c082801040c4060214211030142c1c1c1c18681e4814106544554072110b00352401e00a44a542e12800b4041c001002d01080103c00180c442c18142080c0003098010f0407030080b002d00303c60381c000c0892118415144202d038401122080c905074840420300706540181c3c02031a20040002e03a01c1005442d0f04801d400350410f69940321514202d141040d5151400700085002d40c00c140500c0c2c1c05400d004c00c0550300c003507400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 203615872 1250 203614622 203614637
    0xb0d0308070509060c06040201181d0402061b030304060c02030901090501030905073c0f030206030901020d020a0309120807120b01050c0d020109020a06051c05150d0602040503010f0204030b130201 86
    0x80c801300308650300030580b00c8416045001003000710760304200d22a090200070007042d491a03041ca50010705d640c82074400070308048a03a00000c0c0c1199240400c562000314491618108000d5440840380e4a030400c1d60121303206800c20304031406003480003055806401e0165141c2010620b8080190014488143c05030340d80c0c040d16102040074450140c02602c8420a031010170300e441800e0010303039042c503803482a0140c819000c1c8010404004000f503d5420781e601191455525100c0401182c024030407180b480f8000f0307001040038241680c05034000010107002d04da600700054070444e0111802c640c2110b610000c514291015090940076602810441c01c06040035444c06001c45180ca00c1c001405035007000503034451917034401f1030601c0320b580c4000781001c1c280142050758139040b16600c41550404199a158cc3c2c07000203484c0412840a41d00d90007010f047c1441c0207925081140282d402070044034040c0d820602040b01401082c42141c0880f60421a0b031000b5440703e000c421000e0180103410307410807603030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 203617122 1250 203615872 203615887
    0x8090c040c05070615061b050604020f030a050a0c06030627020f070206042907050303070e010905060706060303030b0a03020f0d02010521011a2d0f0409050603010f0b0d03080705 78
    0x80340b00721409107901d0017803e00ea81d4948480180024000c4c18107001003102c0022940002c0c40001c1c019405c1b5130b0440d80700b8003000041010a2608001c404043e00c58418041d403402817101a0b07070320300c06840c6250ba01703100950b16044140702b00c181101248d4007150b42194021000c40c0036a01904845400104d0b40e460300c10141c0006a2640103600b2802e810061100483c10058100461119202c64000c149050034096216151203000080c40b04051201682d180c0c1c07000d030310036106440900f0b4000c01d020380381c00090505400400e864001140403914284503d9511721380030302071004590f8020701e1803085580900c14014490700c042d10032418860148402994982005503084120b4042a90354007c3d6141120318032f04401202d80c5030f24501410404000b80000000b00d0300307245801400c0707140c041011822200c4091240800080b02c88001140103e03940110350071090140808400a00890010307e0091040341d01801c0d401d5400400c400c03400c800240911041c640c003034240d0400c541400310 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 203618372 1250 203617122 203617133
    0x2011104082515050315040504050c09010602070b0423030706020d0314010b03010e090a3203040503060f0705070602040e1608060f060702030c120703030f08090c040c0507 75
    0x15004065540c2040b80b28001c88252403104441200041040040d0949030203d0100c00301c4040c0115020420300000080595105450068002c100644108070703510301414200c0d221400c10040c50f20505600b400000c000d480007d20382d00b40d41410004514092920448603c00e0300c1c0e03440040301d0302420b2040341c0403940c0c0c284420801031487c2c2d0090001b06050440040c02c43d800b80c1040c00450310640014403c1d20114019641075600c10580c1007180d45400c00b500d450f10300850002407413000d44440e4a814203261060300f0b134161501e902428031900000c040c0c582c0b00c0c0158040c10fa01603010000190341031112440c1c158102c525030401030f1a02c03008d600c44030181c1c0c0c0250072007280d550f000740c00c2c402c400200b460301c0348500c00580380550704c505007040094840c204502033584a20b1001c42d148080d55024041d101e000880140007400792826000c2c4991926040d00c407e40c04181038011a44c03000d4080c094441c400c1c0c20f0318000c0c00c403c2006204000040401034407880421006001d007900284 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 203619622 1250 203618372 203618377
    0x40504030e030f06010f0303050a030e0a1b080105090c010503040c0807060203120601021c120b040203011d011502070509130b0a0501050a120f0b07031b081e0702060610020111 77
    0x180aaa510320200c1e1107101458030f04122600714201c20303802800100807034164403038442e0560b541450030a80c0d81819400c21070280405108981c0c850180344203240400c81200e24514200302d19240318401d0b02d50303030100c030742c202c510443d502076254106944001103980b09800440c2d00c184610303410300361203403280103603031900c9016044100564400280110f0001502d4444c1da4440e100744000c0503610021a405032503094080040c5040c050800c4000501c1d04058003c03012015020b4411910b940c1d43c2c4c2045000b85c0681000030480d1003c20002003000210340203113502194007500108410351804052000000d0010140700c60b1210700b10b032850004c0d078404041c5008601008004c20a9410039040142c2c1e0f031210742c04079101b00120404100002c111948180c3c00b140c10000307590305c95460742c000340c0160881e40d8120013000c0c401c089161040303801c10b10141c01241100040c00352027503001c03143e0308903280503100900517038041c000003012460f0a07540b285400f030841c0300101c2c0280940d5880c90594 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 203620872 1250 203619622 203619631
    0x10c05030c220617100302010e0d060204090f0b24030c0a050f030901020901030605092e0503030406090623090f130f20030411060a0306050603131e0506060d030e0405 73
    0x1071404900a289416007008050300480610b19905d10b040c80d650000e040c1070101ca1f034450003a12183c0300607007800001c0e81076800400c050741c020f0041100501090000b482010f802901c1903500e0303c01c0d1032852240054a5042c03880c0c1d00d80c0e03e403640c1c031340040c828110f41103a40568200302007002554940c211035000340d8011110381380056294482c0748000340946020350040d90180c00c8540c104003c8a4505203580f200e02405070041f24250101d408002203070080d904480e41500c0000b4002480c1c60344402604100e551540c0e981c2e1019892581100c40206005580c0010304000c3c0680d91a600e03116024105402004009804901c110480c0509440000b41c00000c5c00340d5400750070051400400d550507142c6110b000c0c0500d1f510b025903910b90509204822540540700104a001d80c41e0b002e035001d0805030034014207068403840c200300031100250545100f150515104803c200040c0301c42c0042032171199020b4058001d541c0c500050091002210f042541001110040d450803902c4600c2303410b018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 203622122 1250 203620872 203620877
    0x8070809150c061b0a03021b0d0f080f0c0f09031e0d0207060203120a18150b10020c01080106080a0b061309050c0301060804080702010c140a0311010c05030c2206 71
    0x4801010014904082d0010300350300c1c901584c0f00b00d509030b80e01d01e00f044a00443c036604006895400d102888000c0c01849000070b655482074202900755580c01107098800706890f581c0303410413666660320014404609481c00e844004050142440000d084000f40c95101009021581c3e81c035501d541c402440d01041024030322a420010070b41030038640c140510004350200b800258549441c00c01c490020001c000c2c41806103075525040c42c880b00d034080d0003050805401c640d45013958101007104030010040e142199201d003030b90303106845110b4000300d081440e02e02d05840b4146a60710b40717030003540c2d480300051942c003035650307a0042d40141f80d54103006089420000c400768034855003418114804c45d0805091503020707000900c010480b90f58004903d50340a2760100d003c9841e50401d06c0140c034508007500c030081c901000c5c0002c100701c0ba100013a1100c0070a01a039111030145102c00c003954200c40c81e1001d0080040c00c10030014101d150b06e6030042c1401010041103480c00024180e5140201e222500050b00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 203623372 1250 203622122 203622127
    0x1050a11010c030e060c0913091a070f080f13030e1306090203151f0f020c0901030605060310110906030603030f04080303150a05060a030b031507052808040807080915 73
    0x4d6810400c04654860107204002c3e103451400d50000b052201200720b82501c180c0c9800c18002000542c0100c10040c85000c58000300d281030094000c1c00101c00d00000b580014907200009101e010300100303090280700440c064014003215520101c43e847d0307401285a4204a000091041351300c064030550b0014000c0200050300d07418880e40442c40100324195440c802e11800d80c039216411070700c0c5a604c049070098180102070300f00052090f4103023402440541c4c0d01080c144000002e0080c4d0350002032103890210250b0b41c40e8103031541c48800300c50004109041c2140180621503840c01e01900568205034010f080701d00306075259200988a900030b800c542032a40021041c0489140f0240c086e824000044504046007820207000c24624041c0b1207420041585071842840740b44c4090000e4a0b40c1071107911603100742d240418006d0034a600c40400c46050304000311902c1100c0198114115801420b960b038412203890303545400ca09a00300182c1500c00c00030810504c407055544454031503200740c4c000c07500707074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 203624622 1250 203623372 203623391
    0x803011511030a0207120c090213030302010b04051504090212010e01020c240705030c070b09010204060f031b0503040503040b0c060402040c0e0f011d150904180f0201050a11010c03 79
    0xe048807500d400c201c049070b2081c0b000f844002d0b004509a0151150703104000702441c203e00f0000a488020f901a000e405e1001500040d030054040e801d0f400e80713029130004d0004c2e4000100780004c4880440e00001190156124060307540350940094003580d000600842c001404000d0840c00c6500b0302c4d440e4080741e9030000b8100e503921020701500340d031902144c1038400d40299011000852880041642c0200940000000d28045c6001d0989400c80d40050050f1250300d00f5110450003544140030700008140c0344503085058502c20b0042ca17166a070400d102540b20800300300c0540321600b01038030407244c0d800705100c00709191822001074504480c1a100030021400e05006100895042412480402081005a0381c00d0b44640300d50950388403080c038043c001003d1202849038489018960580e01c44140c07506c40907207812880240060b510211810400703401061074584100701c150350010b080302c08502c4800007660061002c2c01002e00c2e01d082500b100c0059010240c21640da100b0f103000440d68402051 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 203625872 1250 203624622 203624627
    0xc0f031305091008061b0d0c1d060705070e040503071a1006050301080c01080601110a03021612200a03060c08090708010c05310f090b0609010e090a060308030115 71
    0x50300b002610015404144c1004082a2204170082601c10340c0f58251020884034001d5408446102400401c1004005a413640007010701000410300340600c0504c18030b524182c41e00b03900301e0345802c0d8080c0c01040c01c9880d00a070845141c00c000c00a4450380030501c600e03004508404d2a044a101c101c1000e0f00007454000110000340740b043d0014010000180014004400d0014080346c5d008803d080041c030542d101d600484821042c0c0c040321142d0701900300040209500040d18482c403102c402000700c5042d4840c1484002e104843c07502030071803641080c0111804a160fa07007081c4a183c0030b0080b00076151291074000545491208110000e8803031401c100c1c000300c003403003038202078229540240700d805030781c0e100181140512201180401c600b40181120740b035242c0c000d0400300315110f001806065886101d603900c1c000e940700c1d0443d00307802d003070030000c05242000880da2003060584440c11510940010320004210040443e642207641d0200840804d084d000954001d01c110306965042c1145174800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 203627122 1250 203625872 203625889
    0x607021f020105160f030e120408031206240d0e060103030503061804172d0901090905010803070305090d0b0103112b03140d020c0109020f030316080c0f031305 70
    0x4415102c01d41030740d01001d0741d446000c0c9640701c03040b460301003640010031f00c2c3e4038109810390081c00e00300c6000190000b0b01c08004070240000e000e0f08c01104d000f5503102030600108c40c0101407102c0f048a00c00c40602d12119811015103644144594001508034040f8a8546009002e130429404944088104081e034642901c07908022402d0038280106801c040d0313210f4500d07940c200c0c10080014030114040c0d15561401001030f80312880140c010280c6260428103030030b540e124a813428006030a154020030300d030700c45000d480d0480b00103070002c44c40c1907007a03101110150031009480b41c1c060445a0228007092070ba034020b501031402001c0300d2808038210010091100381c07064820152040c408205000b0f003d8900301c00c241036825007062446020b00325100c0c4918407036868081e5805201042c264111081584800b8445109aa850342c498441d001056603d00031104064802a0980380007000128094054903105e0380709000c40382c17401c0040300c1507802c50f0003190074065566031841041005180c800f41c3c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 203628372 1250 203627122 203627131
    0x633040807030b011d041101030f0212060111030307050a030902120312070801080d050915071e03140405031009020102010b1011060f0106050324100815010f0203090f0607021f020105 80
    0x2502c6400e00000c0204221001740140090f01c0002449242002079000350014440410300100855958100700743c5110b00c603200f9551103001440c00d030168000e00303c0000489000e03c60320307200c1a09200c3c2000c411400303400e044070f00320382002860500d02102002000a0301960380704d410700304094909504000c110b0b90341640140759952148541010154010302100c821034006c0e940368024a011040c024080c0c0305007034004050034031410000003242d201c40810900f4034071130f540b40340d5811a400050700140c0690300407540d054215a80b100802c440741c0d804100860710600012800040500c00101046203800280010500d1901140007440c0f0034041580c2c0403440034403030141d40d41083c1c0c0051040c00001d0030320400000064150b50320503e01d109546501d003004008001030140080010f0001c101901c148054641d04846808150701400001c01c800741903500a5041c06101001c0080707400d074400b456508050104440005a11501440c031386426a202510641241c1d42c900242120030090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 203629622 1250 203628372 203628389
    0x1909030824151e03070f0e03070501141b0609030403050705100203040513020d0504151503020f1012020a031d0a0f06020304080d09061a06030633040807030b01 70
    0xc01c0309020307964a001ca1a40e00440a0150703844180d207aa80c02c501240c2e00e1280c0d0001c10020040141065101900f04550b40c620740e28480299840e070f081c99526000d6025050214190700c07007074400e000c1104050049001078031200d00514824000480c100141590314501c2904000381c2031091000030040c07000184411383d1409114504c00030f000f5200d00890084910412101e00707110b040315681c0e0180d41407682100000c0025040c6840c0010600b01c1944a800001d800c3c40c80720510b000e50349502c0c2040340d8004e00b91a2148100703001b003140c168600c000003c14000b061134800004841c5101403c0703c8107107500c0001d581c2c9000404405050b80e00d042400c0c00d0b90100c0800700008210000c0c00d890107602800140e26511350b840c02403030720702440c241e49568610700940072051240030741000717600c0b421515082c1c00785140401400110301c012145a03030449481c2042c3c110759003ca0806121206007050501520301c901d0701c0c00510381d840380d4003c0003a0b500002c014814415241101401010b480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 203630872 1250 203629622 203629681
    0x61124010617041a0405030c0d1835030c0105011202030105091b040b04020702061222030e060304170c0303040b0c0703020c12030d06030606090b03160e19090308 71
    0x3581ca00070b050058100e04c048400740340001c2401c001e010000d4a8011803040165003150302e44420082c40d548c0c805208020b5548808400980748807081d015008003803016048060b4080720701120341e4400c0c248000c0d05542c0c4410007a62006120030301c12540030f01280c6000c0c440c1040e0500415095035000780c014103190700050301c007600304181d40002c010b079244280c4d40481c04c0c26070040090b00a014140300030703412010000e941c2c3c0b0b24005046e01c1034803941c4203106600c02d1441e40380c0c02c111420000c10000340400c0000809a0052034004091540f083c494050310744980c240001d05850380d0803040700c5508550002c0188010404008a99540540e0740d400d01c1e42040d80a4400941d100125100c00380515010050f8003c100c40501c1100c0c0e500120302418882030750f0301d260000090405120b500541c900d060b114101624012852249a40311107490f603078030300c2c20316840d1200d1a01c0a004401c0d0741e00314103c54550228a4042e52020750b000b0345030091285442005412440000703a900d106904a4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 203632122 1250 203630872 203630881
    0x101b081e03060a1a0706021c0e0105070f0c06110c030a0801060e09010501051b070602030d0501150519020a0b0a140601090506030711010603140c011404050901061124010617 76
    0xa0103c004102c611050064030000600c0ca8244002e20a192000d01010700000b401c0005c9032400d54030301d84030318140c181003003024110800c05003207c8083c2d43c0000002c482a460516091164111000e8240100c60015440b4110b4148030f41c00c0d07004800300d19a070740004c00c401580b00e81100c805401044503043c1401059103c1c07002031070b1130f0814064a4107210020440f507040315101400241648000d82c2220a12511a44040c0d82c941081d68900715442c1000c0c00820f1048044000c480c541400d61101410090b000403d08250402a8070344400c61080c0c102d04c1e80800c2440f0402030040c20400c400141c52203400000c415940700040050b414005848002c000700c1c1c80304001c0700d034040428904003c03505e120011490140100b0392000c0c04048980d0365000d041c04010450051213039090700d1b00f4074200300141002c10240034038400c4a901c0341c030366401088001d01079440c110b41114102c0c1600d88601400c50340d00c202c10114101140c1807024075006102c1d281e00700010400d54400d084190341c11749070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 203633372 1250 203632122 203632129
    0x60c07020409061d0f010f1406010f05120408040510030b010818010b0307092705071e0504090b090708030c0a12110a0803100902070302030306101b081e0306 69
    0x20020024000c981d50807840050003040e0748918918420341c00c551a114070007050841c0c0d0740c500e4002e401665443c104c0c42024411140c801e0068009aa54201205030340f503800664150751170245403001d1090400c40714035090f40d480c10b40b510951290181940380d504010521448103565141c035401d15140c02c90102a40c0c2c2c0100f03540c3c2c4d00c0128580100200404085100d014002280c00707150540701e01203010401400503006034101c804c1ca00100100b0000a244041e1f00070300039180600507800c401014007910071440c08407000e8100707e40a0b022401e6480020808803551a4810360390704d4540030910008840074040440104400d100560034804000d241c9901c61425100c000c10701185412002c8405000c1d0003403801c40702c0c0c10002d844c14a480d905000c003480d402101c2c60b00e10240c448002003003440300c81c07080c1e032202d07a0564011400c40d0703107400034410f08002e0650802c003440420042d9800c2c800342c445000d00a03510441c0c445072500c0d1010300640038442181c0301701c801120280b080182a44 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 203634622 1250 203633372 203633377
    0x40e07050c0c010323180d1715100507030302040506070f0c0b0a051803071d090622061815060305060a06050d0f061b0801030b071e03020703050d050106080612060c 72
    0x40c000a04805c940d2600b0f9048402d2052042c840001806400a80c2c00382c250004400a01c45240c1d00d92603415a0340c84d94141000040c4444541d0b0007924040381c418120b00c00c20151000070710030f0a0040c907003030321100014400e4101c54003ca82030300b100c181e00781c00c00c2015440d500c0104800401c05041030842400601580900030247c1d100340d040350071004580c1d0781000200000c2010350318003035110840014080714400c0c210354003041803045401044e1403001e07400c00b803001c4442c1d401c0801c140f04400d50f5884041c1009084401009260300e140c680400d403210400a5141001240002c4403440c5146c00d03414440000c4c0300f00282c61520074104080d07100c01814a0096038000c2d86944150f5080c40d044000f0007005d23900c1c201c40c1111071940c0b16000d41081c0032034140e0740501c040304055a9541c00c00c5502e44142d4080e124200228010149158001e8000c1c2c1041d5220707040076418010700040610031100b09900400000300e00c142070142c00d0070043c2409488120300342c080c109520340160041180d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 203635872 1250 203634622 203634671
    0x515040e060121020a0e0103060b12030703050904022206120606020106050f060c0a0611030402011d0109031b03290106090e0105010e0105120403030903030b0f030c060a05040e07050c0c0103 83
    0x1c151960f150045540b124590700140180354070355095941c44c1e0402200030048004414092612001810090f4100200750f9a4840e4140d0310f052502c0f1003581880f02039003000d040c80615070042002c13030420000800350840a0150b540e14001c0c00000c1114040640d0400c2c4d00090941e4500601488a502d48078030074544440d0a446140d0b40782078903800c0510340120314201400e0030307240154030300301c4800b03020045015030f000760303a00c03400c00c10303400b03502480c25061343d14003400f01d08050720420000c0c1c40d003030010070540e101c42d02c1c091205940e51182d4074101c0c0b080b41200562880c1c044015840c0c51940480d0b0b0140c02c0c14030348400c0c1a03007040c40c0604000018080e26050001c11074210341a680300d0303411952082c502c4480e01d84542420329019000e899001021004a82001d500c0081401c0c1220480410800280105201d4070303018180801548103054200030014104400b1640c00400143c07540108501d0383e416503260941d02c09a0f080c900300090080c10141002c8086022540d13080100041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 203637122 1250 203635872 203635919
    0x1c030905064209060103021c150b0a09080f15040602030a02160803090c040e0d080915070206010e0f04030906031d0729090d1b090515040e0601 63
    0x400101c0d0340036003a0b120b004070a1002020030303091008125412003204428222050328101c0258032041e005400f42e015070b07159084544c510260414610140380c000304009820004000700b0380b5110040e02129611100140b00490080b0100300702c0d02c0350811140c56602d0001c0080c115000141c0d126010500e0050801f90000d500070012601c0703d00703150b0480301400804002c0d0283c0d03041c2840c1144075604120307a00181030280c1f4088800312b0800d4003580103c0f00d1400041c03c0300b18040d4505844d0710b0070140091545200c1d04501e800c41003607190f8828050141a0000c045940c50040440202c1800400c070074205020501800f000070f41250003d002d0314118140400d410140800808060410300e10b028028400c20800044801991044814580b8868803c00c124000305803400c6040c40358541c141c2d04119079600002c0440c920021480c0b0080d1a15000c942565484400c40140c1d1000e44000c4081d640c85102144103280c1031107150f01c0d28001074058007056141120342d8400075195820341c1e00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 203638372 1250 203637122 203637151
    0x30f0b07020c190315060605040605161a04120e0303040314030d0f0506100c0c03030c0317010f060806090907050105030903070c080d11150601030b0a09020c1c03090506 74
    0xd1641c001d0152600c8490302400483c91062880329290f41c2800500c019982c1407a5a001d21407490303550701508050702c0366a10703441d1a161500700c04492a6024600c1c54000400e192402e0001400c19a400c030000e034214000149a424581498440c10383e90340c1c200e02c01d0100481519140e500c0c084241c0d41207981140c2c450802001e1081c01a00311301c141500d140712103142c0f80419089107a1540035038061001624000030655546005a881846280c00509100c1505000b080080c0c0f080c800740d000203200c1e02c2c2890460001340d8909495103000e0f000f854807800c91810502c1340c50f84c03100240e03601170b40841e960030a90804101c030a88901d01405a030b81048000400280c0566003007040310a40c0b58841104c0b0380340d80d0740c0c03d0f0144c0c40d40300c0010f0304400103400403501202ca600000f10060580000e1b004081c01e40c5032000194024003000403010307088180d601000850b00028406401520b8441e00641003481d80300c081403090b99002c2540c401807610302001c45001c1000018856449580d0014104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 203639622 1250 203638372 203638381
    0x1060c0b160c05010f0504060b010f080114010908100b1806061c0b120f06101809060f05010311040f020a0507062309070603111204150902130213050a030f0b 69
    0x1c82c0b080c60701001401c65800e091114031404090f42c0480d100d00d003c1d40b010000120f68000455864a1850743e080008690200600c2040c511080032410464141007862045a490700414101500030300038107000d03603031000703114600c1c1400da01c481d984006031800c400c02d03880d101e0001403090048040200b01d00c500003045115820841d402144148401440d82500704d00c80d080e800d58075805000060540d0080501144c09331905400044c15038543e9109c01ea20a401140004000c140740c00040d2007440e00ca05c2c8800006000388030fa640030303601914104407544100c509020595414101d14524031303104001c403051181c0d00c80183c540c1c4580c491404144038002100e81c0c84c2c1900c9080c03007240340204607007e10a010800040c144120b582c607031410700c64440480b2012040d40075540034101302c07561042c00640098009078052612099005000a1000e0a600800c519205160b02c181d07200b0342c009030802c0d042e841015418014081218064880742c11769403041034544009200403c440310350320100c0e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 203640872 1250 203639622 203639627
    0x807051002040b0d05070c0819030609090c03120c0c090605010e010e01050a0c0f06020d0203060108130507060e12010c080105030f0a0507050105030c0d02070830011806080601030c0e01060c0b16 85
    0xd0a54541040b00f527030700d541c08041d0410661001c000d103400460b03c3c22000054000c52800340138015500500c41804081c42c503201d01441c2d089401e400e00c200910400148009038540030180040e1148800018070f040c1444005401414410f10301810310201a80c0503526a03406070496030754040c2454101c1384001d040c03030014a6024091002015580040307011455207156501a43c40b80c5000d036500d201139281c010100503403d01d00d0344044c080c2d4000d008244541800b403000990000c80280c48848003441448805085440708004c0368000f42c802030040006140c20002a03c03400c06080c05400001c0707040d0794003035a40070107109030f505001000c030018005070401000d07129241c00305070065545203554038051540e0b51200032009460701e804007036448014459200080c800841c5855280700c1d03428902d121400003143c580d69109107454001c041001e110520015009501c0740c1010048581030911020b007613034050300601d0030801442201800312b280403107540d401502204038107a4135114007004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 203642122 1250 203640872 203640887
    0x1b081006120b0402070605090d050408070e060f03060a0e06061203041205070503030a02070306061211092208131a07030309262212031101180807051002040b0d0507 72
    0x582e075015102092820a1200540080d841407541030103550840c1d1919105494500441c011020b86a102c4a01485200d101400458000340001c04031002e103103d22000919140044407003510b1141c6410030703800d101c2400c00c1483e4000c0740444022040c01d1807070400941e2030080788640d80581c40b000030340505101c42444900b01900300a01500d540e41c0c2ca40300007a40ea014035200031185140343c0fa80000d00d00600d064191032080d4465441c03e8003180040070070807000c4000d894100c508505081d04002c800108000c4444103118110451719500082081140d41c08158000c00310318900760194007003811440100e40a096140c200003500310900d040ca24020151908d40200c1d0180c6140c00a22000102c070203002c0e04004122001c541800700030b840e041d002000e104001e403c041502042001a024000c00a10010840c000142d120b942e07201c810460078004d4030656150300002080e0090007402d0016160040b030300d9005502c3c1c640b41071a440d419100312569520340c0303030380d840c0820781291080c0c81 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 203643372 1250 203642122 203642141
    0x6091810030803010609210209040b040c0b0a030c03050c070218190c2f06180307050304060c03020607030e15040311070902220b031501170a1b08100612 67
    0x80d82d5229030b110300c4050441d010902a680c2c01c03002d2908824400115040e280000540c080d05c22070320390700c580d920090f4554024000300ca608480740400b065401100d4090700000e00140d4000c148091382510103812a9006090800d101100308121400741e202e20300c190000502401c4840c1c43c542e9164990214034042001070302441c4c0c20442c010001540c003c1c4640d441d40030307402d0719403280041c0308103c2c0001000d4950031100740d00f080002402d001a400038040d030388122001a2481c2c01f20aa0b60282035034080c0d00040c0114101040c480e0030b0540c1000419480003150034100803203402c10712500d03a651000a0a48005565000054101841101e28040d00d96803c0c08071041c640e110781c2400040d4100702158a45a40150030206801c1c03141c007525822a4800c40029195031900c1e40800346281148001078140720640301c900d05102e5004074824450196014001201400600ca20303181c40da280b260a01004900020b012804200024402c11180d49040440c034103114000302c072016119000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 203644622 1250 203643372 203643383
    0x4090303061e120803190507231e0307020309040e03040f050303030c0f09012a03020f21070c120b010302040515060307030f180c140406030302031b03090a0801090b01050609181003 79
    0x18140110a49c200b80400c60186981346048170524050000c584140214440d03215040742c030790003032030700d0409105c01550424180e2065070701d004151030204065030038450000f407840e800000c0c10440e5041c4503c180016000c2100a1480c43c2003248900c3c6650065800c9071181d00400210140a81e00501e6541410f450180d101d0f00245c1081d020124100034040c0e0940144c083d0110341e07420584040344c2000035100740042d16590f4240110031303000c540c01141044800025291020424107034810398011001e00c5440c1004440d030440c418042600e0002e8200420540c58020500b0b11782e5820096075405135051400140c60403e01140c40c0291010360004100d015900c815601444a6500a030041d10300542140d64540c0900d03081c03008071042444007400581017071244180e1811011045108114041e0482e400c0c0b43c030020019058004d60b903c0070116a550720301d0304040120b00b03e4098018003013250518100080c101c0810030b0001c03c10762011065442c000084c10302d00c14460100003540d08207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 203645872 1250 203644622 203644631
    0xe04090c0602100b060c0d110a1a0901060f21021302040909060e0c0102062d1311010c0209190f050c03010807080303010503120901050904090303061e12080319 70
    0x100c070041d49906100310b107601901d003003410600042c01c0a030b003151a00812900181520100502d040750f200d21044c0f20412540601c48440b8042080894080000401941010120300b0a4071225003141c049a102e21a82e4040800801000740300300440c00c0507c0302d1618050b4103104510000c0e11292039101483d50951010501103540b0320654030000f0394512680c010845064030b518296aa081d50050407030050b800800014038a900300300c440c0c0f460b038401c04401d0706070390f04125240c880d02d801111826202c1d04200c10110a0104509803401d00030400e0030000840c08007500480c41798040100341c00f00c0c1c0c80051145c030000c1202d0742d00c4142c1e4100807a40400c05820b10500008040d402131244040c0d43c4920400030039940030100440e0f04952004004120500e0000c03901c13104c41d001201814180802800240d50036216030040c0e040d014883d41d0005000c4c2d081c018845483e0720701c4100c110340c10602030001d01c4031a489140264603140c0002c0c0c60703030700d070744c1c901c0b401c04064040e40d803040400500300b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 203647122 1250 203645872 203645879
    0x150c13030606180b0f0d02030f0a1101080a2a020a08030f0f060618090a0e0f01060f0f03030509061e0c03030708010e040f0f050304050301020711040b04020a09060e04090c 75
    0x2181d211070107841204003c1d41d80301000d81d106805996400401c0790b8802c240c501c56045030f00d8030041c0122000e1004d010b0314060b10000d8000c0b800e2507681c4c5000d4590146040310404a5a40f0401c03555004140f40c404001c0702c0b801d058100d06070840701905080c0d00090180e41850179000b0040800b80c0b691208115949103407036030400c030030744500740c90300f07a14014044007140e07446c90000141c80c40c049100d50714007500c143e076808101e0709103000b51844401303e81d25007070782c2c0c064102071100308042c00d016000030550034900849030018243d60ba128241c420340d8808180002075024048a40301c5904552064841400301d50313800000d20070aa13901d0080200003500d071061034010001d18442ca54a8075007400076a41c8440074120001c085030010412000c0407110000100c1d84400d004440d07006500722401d103901c0d00d01280c01c9a200510695030429034800c644c00e01e152500412410304026201503060003100200a0070072196409940d042c2300c07000078030101da0784407603100407108ad40214502c0e103090744c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 203648372 1250 203647122 203647133
    0x3020d030522240605040605120604030e042007030e1e010c0c0f030c0e09010c0c060c020a0b0a020705161a03091c05030901050a0b100e030f0105090d02070f08150c1303 74
    0x117442018003540c149103000400d4504011054105520800903108507503d41c0d4080341d108a42c1092164004d50b508100c556200ca9101c80304a62a00180b00701d0b40d803401c40c02c01500740115038080c0c6101c0d0400ba0445001000c04250040c8810070030b081c21048841245020807103800d207600055103040352858000203200c0e855240408071f4098950b5200c054981e00406401c1e9403140d002000131801e4100c02000003195680020645034135481954604540c42c0d8580401c00c42c10782d0220281600412910207100301803055010130303120b10381075422862900e0800909501043c8801c0c43c2c4807808800200c4440c824400c203424030000040184101c606c03104040c1c1150030039118114550700c0c1a0016103041160700c600c40e0041002000c1001803500790b4001c0398600f0050740a1034150185644503071110303a0034002c6034080d01310240030380144814164000d02c1c146a9510404060401c5001041035440100301d1200348600d450200000e507a0700c0d102290344d440342010f0000f051811b901c000043c0311 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 203649622 1250 203648372 203648381
    0x1290301020c061f140f0f0f041d0c01050306031b01020a120503010608150a0513060f03080c010b0102060c041a160c05030c1e06030402150409020703020d03052224 72
    0x41304418207480315201c01c664074000340101140c6400c40c0b0b07081e60400041ca042400304074906802412403041c0605100400c0c03c0d681e0700160101c05c480444c0960401c05002c1c0301403e5001401e02e400c0b070a516003000020340d100d02c8d0240c04006003142141d256800c3c1d209005841c4050b401c00803203424004d2008008100d90301c2442814009454100424103400ca6a5402d110a100081840195900f030408000407400000d50110f181581d0344400602c039101400080c00850107100324603261154402004d0965180040c014115000708042010354121030b000d075030984016801881c0e2000c11440714400c548210035441702d64600d414001820464140c1c0c07400251141070707054030080e540c00001e00c1007601c0d1481080020756154403500240d818503c01459006000511800078448200c1e64a445c5601c80e4006000f0035400141e810f00381601080205204081860100f00ea8600300e415001ca041e04402c0a5652003000c0c41c848041c080708004900d20f2200003036030031211012031a000030050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 203650872 1250 203649622 203649661
    0x9080301060f120b01050a03050907150306051905090a050601030b041425021506030a0f03020f06061801030f030c0c140a0801090c05090c04030c030f060e01290301020c06 75
    0xa0344640c500c402083c0e05000d076182d0036406071030715420641c5525050300078110007070105105200d104000039060107103110310000380d40c281c0c800049040c20402407000030001c0c081d002d009000405401c03c02500c500000a0780121200c000280c02c0c0c451a00480281801c06a419401030400218494810102c0d41050042400d06001c0d000d60a0032a0803810820701c0c2400078015822000300c400110940100041c5c0c0403100030192160380d511a0340e0040c04201c080000d80c0180d00c100141c104500040000340d41064007250001520728203030780c9a00105e1014040100b440d8107120480040501a0b03d1501c151030384041051500d5481d1040003005610380e60a0a1203426140800070300d841c018852540600c0d008002c18140c1810300d401d220201c04040c0c26181e100f5802c0200001007a907034502c0002652080030764115104181c1011019035038240a804480d034907005c03d20700c08104055a007115012490320080c003060301000080d00900520398802443e000341c03002c0000302c04d800212400d45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 203652122 1250 203650872 203650877
    0x1021201090f09030e01032a020105040b220f03030b0406030b060a0504110930030319020a0e010e12100b0117040308191b020c030d030b060301030209060409080301060f 74
    0x201070001d19a10b0603507142950290100722204450f1801c0d5209410201002c20610b07850142d1400f030300715030103488c95034046200050b551001888100003410519a810101c022000320150101190100b50412200801810080c2000403001014081c0c1c00c82d04500f800108200095a603d0401402c00c2e041210803070320032124a54085513924080c81007811140c540c08041e81046841802e11412030007210609001403140707142c1d4865413445115208600e00d41001031601c2c3d0400840d48510305102001250180e030041c04811a60303940880c6200400c0d600740303030502c021301e005e0012890907900d240e82031300c140c0541b400795100c024803608481c40241080ea0303500054083c011807103000700340c185c8005001035041d9000c03c0d2500c4036140703009909441c0c900f0018070000c80062805000c05100100405a08080440d14441c40c2c01d0000d8505007010303040600c16660b04c280041c1c102d00c0305000080c41682804045421900c480c4d002042e0a680b140415580c0d58403600050a1800f081c1d981400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 203653372 1250 203652122 203652131
    0x151d160305010f18060b0f030f100b060306091915080714040204080303011712070302010e1515061b01020f0403200d030f0e1918110304230102120109 66
    0x261006180304d071030f43c202d02c00004010fa950444d90b900c0c005c0c00100c008264040f0710711a400c8110764003802028020b040a0008106603544004802c0503501e8554010380308a2007401000010784408000590003000c1540c18165031001060381c0d4014401703203001202c42880008081032841e0300281c44c00548020340700c011950002c820801059101702d00407001a504140010858401e0700b01d240ca0307411a5450581e400e150046e0409081e94100950075030050303465158008031098140801000000360803001c03401d03440c00321105a6044100c404070f1340110000101c00c1d440c040c064400804903480710009554a00303c1e500300c4e40c5203421038001a1074030000001000295854640058602c00e0043c080184072075180e20240d1307040740e1744d074402001c1c065424044000c41c2d48201d4603a0503102c894150600c0e403070800040369101c0349a19110003a640c40d160703111042807814020b803540180c0c4420a01620441050408064521204100180d40c000b040f486460500108024141d6007144410407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 203654622 1250 203653372 203653391
    0xc1505040632030709180605010e1002030a1d040207031110020a170406020c0f031c021305190801050108010504060b06120408030604111207090e04151d16030501 71
    0x7000341107000504002d104401c20a1001140c4480195074400068149014403d6690756030302504402c844040301000e82d644030502456801c0710002c041444190303500310340c0c8005120003960b00d100d44190030043c4803c0c3c482806907101c401e03000f40f02c46400035005649941780380c0380c0505a18804001c422260181e111402c03030303441452080c0c5280c4603160f0745c0c10010100c201c002010400014200303a41042e0200a080d001d14000c1000100c40001000290f0f5205084002c0c03804100c0074041e00d0740211300401c07411300070b14102c01c0340c0300079030700222071254120140168120024005a04ca6212542400b00000d454941940701c544194041e1805210710f41006d0108820b61043d6072140d800110080003140c0410310103c09154410b9000d8000035440c460004042406d030407107000171181003c0c1000b0064500d910061070401442e00194088103030a03d90b661810022880e4114243d0640e84c1140700c110101000d03840740410040e005440c014108106207844441507030000b95041c1d8204144c42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 203655872 1250 203654622 203654657
    0x3060112050d030c09210501050c09150d020c07060e010f05040e0f07050c070902130506041a0904020d060303020f0f0304080c010c0206120c0d0510210c15050406 71
    0x92603440d03401005004410500c00c1c06500400c00b180405041145044002c511080c00741c0c3d000c125210309810000450442d8034100d400c1d9000104080c81c1c1c3d032000d00104207103072140c0812801a000102041d500e0b06c4030074904100174050000f038850503200f140c0d4001204c980214500319002004c0e44c8800c0121800380301503540d4422480750407000309031800011001121448084c3e0031111600d0402e00d000340d080145450b00c80c2a8000b5041e80e9400101010f03408031b201204002131030262041420542b40505c08024003840350007404d141503000a00c83d0440d0340e1a81141c417000304226041010b41d8881c10004c3d9100c40304410305500744291b100c201d4402c1c2d40003064800f1104900c4c0200002c240030401104c40d40d440c03600407038001c0400c0c400c8403014000e440803248911101580e950300e80050341481c0083d20b1019204c0140055412028000c83c2d01d07011080303605d10800c4014141000e5940f8108120b88131aa0040b180d640c0c5003100784018550040041007128900e58556403e00b5030481203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 203657122 1250 203655872 203655899
    0x1401030506010e010f0c063902060408030a0623100305010503060621060f10060309080a030b03150403080601090806010509060d0c0f03050102070b09010b151e0c0705030601 76
    0x9642c081414070050400542c0700380000a1443d00c10f2601d814a415560745000c20340311203c5d810060f4001d0b00300448200444141c0782031045580403400c8100f040c0894000e501c480300644050a8404004006030180d800b0760071610040000007200c1d100d000b00c00300307207501484542d9000e51050a60403221001644a030042c01c0c1a980d00030042c00d52501e4030002c010704095175104818038100080d2a901c1300e18424042c050cc140307084124801e007403800b40003500980306550410024103140202c80780214480500740e5040c101203080c002464040c440009240c404d802c0348103403950032103008110402d54411903460040038280c0780d950186840701d2074030792246000d000b40d640003080c5400062461401c01422081c039070281e0302e840c102a485075061114041d85400a48071a034001840f14104019a0080c2c1c1d40015070000030000e403c0031200080245604002d0481081e401040c0514032420148500100d4040c1070f460a030b845070ba0510a5071942e900c1c2c880c81d48a07001d844000103110754020b02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 203658372 1250 203657122 203657131
    0x418051504140601080a18050601050907110304050f1201090f141f020a110a0b09120c030702011d0406090608010c02061e0403230712050906070b0604091a0114010305 73
    0x10b03032810759503c00004441070300000341200c00440c1c07a41004100041c13007000403c3c81b207010318040c104039070608007800300350400a823042c0c08010920381c00f100e001c84d02000740d406442086a078201240c09035030020382241c00ca081058500c3d46800905020400c0b20390407100030071f02ca0103008041100c800710640d00c2e071025550b40b000d44050000312183d154001d90003051a6082d0b0704013482e54008406c401c51420199807030840c0c00c940ba0301c0070b0002828042000c03480310441c00040c94a8640700281c2d2540364003800e0402414085d2180b0161140300310010b951011800140c01005803030365a0703020348c024003610b129800d815440c0000b02480503201044031880303451000c61548281445031000064414001c2c000c0e4100407052210f10100103201303a00d04a1510040c0780151200c1c0c0c0b608181008041c034a5404003442010000d1403420b0b114501501ca500742c00040050b10fa80d50240030401404040710002c203046150382c050815020215000d9058880c40d001c15074042920000545c2180c00555 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 203659622 1250 203658372 203658401
    0x31104050a0b25030f02060627060a0305010c0e010e040204060203091207050603040818030609061308120103081308010207020603040b0a0b031b01030c0203040b040306020f0418051504 81
    0x4400d01c44441c1c1d6500a0010031459003400044540d07103c080449481c007200c080300002d100025401240303a0410259810000c225080c00d00151024442c81c1c8203280844120700041c982000110030380e465441a200441d0004028450181040401032048a401c90752901040b070000c1044001c0c1043d20a517400d490301500294548403a107410000300a0250f4450b45951242c1140810692620b10145010301c2c4550115900d03902c104510030b42400d041054107010351300907005c000d117999001500c2ca4020040200640b094021070034480c0d0184207050980c16900c02c1e0030f0001081090344001489003000250130301005039100c0c0781d4113090b880f4620000e548800140041000b0840d0300c14030582240c155000002c41c40b801c00040381c05d000940c20000300703001c0c0c3d50041008558040c05000b404502c41d1016528040c108504010680142e00015000560105040c40c2c40c04002045038040e00c404030b0602440e40030141c8110141c08100c800002c3c2055058580c1442d0400c1c0c010000314046a9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 203660872 1250 203659622 203659639
    0x20a0537081204080706060303020705120609150702010e0601030b010603060b0c061f0305061e0117031801030b060c0109030210090201052b020f03010305010e0c0306010303030908040302061903110405 88
    0x40c01080b03114036000d001035828100822510000940d5481040015442600500107685c036003420003481110001c0b24140b51f4110300100011408003180e03464008060305102c6025882e20b0300201d0040014040e560a60700c240360000c0144840100014100c030200e81d014045180c403041c1c01e00c040c0c091104a09201e80c00400860059518034030104680c03070407081c40700d081682d00d0711420300c1c0040c01c0e10360f80260114031110814131502c1010340350142a01030004180080c82744011556031044203c0c400040d80b00c1c2114804aa00c42c6d0081001e2141c01803501e070700d44030f00b071502d94020308503504110054450894400340a44290246e141d8054050315080e08102c80480569484591128101e5201c1845e41030701c4410109480500350142001b81165202c2d030461a119084170004003524403144c2c0b06050f4510995000039100d419694140780104a9202d14a0000d120380100d400080d4840c0000c03079101c4288904c2001c0503070407030701580e00f40900c0500b01908002481240285030f00003405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 203662122 1250 203660872 203660887
    0xe0703060e1b120c031510020706050f04030c030b09010506040b0d060e07090c0201021809040206030103142812082e1a0c16050916020a053708 63
    0x2907801a510b41c0c1d8054404614200220b5155004141c04580d214020000481409001155010f6420340e442c3c00743c40000f0100c810303c401035a03a0301148120820408005004000c0040110603a00216880001c44192507100e14040e410300400312418142ca42c40c050000f1503514080c050200c070300d03201400c4048501d0941e00c0e01e1003e4110391a456a4520640c000050160360b0380c85041104005507000503180c144d0341070f16003460014424a2807140340400c1c24000580e42d200212811254010b070303c00510811500300304d04085890f01070031790020b84c17015801455010001558a914402c0c0d050600d141809282079445031380603a000e021008080c0007510f045107051119004000c0b188985240c9035545082508200415068452225402040039410420200804001c0e02c0d480415001c2c158241000324100c85001005800403a604c0e20040c0e16036802400213481c41908030060b1001c81c0c003450380684400c2e24041d0407440d10751009202c0005070303a050406559041c0c4c84041c01d40381801 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 203663372 1250 203662122 203662141
    0x23030103020603090a020a06020f100605280b030a1a03060f04060c0216090c0305060105030403020d080a0b09100305070b0702030705090618090106050102190201082410090e0703060e 80
    0x70000021481307851a02c001580d0f9070547c1000811055008040385116104901c3c141400411580350450404d0f100384107554488203050004840c078030284104504160354091109415880b407580800000300b8005520030a40000498103181e074030b054840e5941c9000c1c1a503450b02190301004c100594008140003410035002410341c0c0503213104a0b014400b01d82d4201e105045141c0c0800d0032150798104940d2000e030140500c9522050908102e400d40c44c05441c040d40b035000d0040c1c2e00d0104002c920004040c0300da16801b00000c6003002c3d01c00c01c110b01d000712000c041d000703090109441d14881c2c0c140c0004c1c190340803c21503440c207034064080d2100b503160005010482001400103584a1440b488042003a4403490080d8460549000003041d40d600c0d00c2c1c00139040c000c0071841a00000e101d5204080540d8002110603042529084101c4002100508142d40c007042a840c035580074941c0403c0c07070701d0164408107090039203180012100c45510340d041c0913000c1710024401c010781c06000400040c0c0c603c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 203664622 1250 203663372 203663377
    0xa0b03061c020a0b04090203060901050103050106050d020f0d0c0c06240504020d14040312050903092d0a08030706050109060e060d030302071a011e06051602030a0203010c0f230301030206 82
    0x2d1000d8000c40c0f003aa00d546182e285074020b41c000c0304030b0a40c04000c0158601e008588640100001c0c28104469414000b008100e4815050031a00c007a0700002c035040703090407a0080b00d00d410942c00042265503002d040003012040c000d4400d440d02401d2031600c000c0d0401c10300380c03004c000e008001207112081c5442d0130711000e0b40003400c58940c03140e595007802c3c070f6407010702c00d50314402c0c7c0c843d50f500d114405055910600b01c6602410220b0581d100f800071110540b1a18200c6038000500350311022110503200804104040b10303000241c110150240002c0d000f0400809084401c0c4192018881a80c90f0308220b001c82c0d03201d20401030410905008918603003400010a11254041d207405858001943c80d0380c0c0101c28440117540001c0c0200780100303c020404c4104400030182410142400d031f140020043c40e601a4800300c3c5800741003041070b0800c41d58100442c1807040d41c06802401a9900b504000c0c01040e010640da00100b4500c000e07040e406403e0441c4180000c0d0718451080c29039080d9001e100c0142c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 203665872 1250 203664622 203664679
    0x50106092409140a030204090b01150504030f0b13150c140f04030201030b0a27060503010b0d0303051315060e060d030c0b0601050f1206030c061201030206090a0317090a0b0306 77
    0x84d44004000c0090b03103d50054440d5107000384003044084d45490004500c101222030a801000424002030001416082c4000c0007503400c02c0c0c100559445031034108205440c403c0c00102920444801000610102e40102d040070540d034660030040d42d000c2102c04100e110350605584040001c0000b0b00042d070017a48944119200508050704068071003250080c80085090880c41d04c2e410030804c0258980540685805004182c0c028012180c101012687d0012001e81c02424182c90b1070004a041115281b42405150007000c54031054611851040003840c150044640200103a8000382403070030944c04018026a00d03541c0c15901c443c2e1a2500842c11502400c03580c1002410080300070105001000f428542d141d4480303103115806d11070b00705460107030074841c440c3c010300c41446272500604021129904603a01070701c404bd45c078100704000401b031100da508014020944900c2050800f100080070306a00361080c0c03008050036480b402c08003d5404100c03a103903400400c01100c07a0083c3d20b0600c560440 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 203667122 1250 203665872 203665879
    0x1e100e070e04080409050a0605130507030f09082701020307120306030c14010f0305130b0402040e0312090d020a080d0902011e03090b181e03090405010609240914 71
    0x3161038003829102004141e81c00d480003400410b0902200a082c07103401c1d00314000310303c10040c0c1d40c03400380030a0b0603140c1d10180812996407100040c28603406a040744186c202000e0741004414641d1500d94415040004d075441c070100d00f03219001390105000c60700e04034854160011070800e1030b40e9035603002620602c1e000303504064131b4250000c0000c8410881c04040c088181c003449000b0a17010004051403040112101018180010310850700c0c0f04004941c5450707005904004070b55124000700c2c2c0502401d4070085c0c503602c0b00240c2c2c580c3c500c002c2e1601d20b000f0031b050002d40d0701c3c1c84032801c802ca03078502440101402e0140100b20301d6042d400d0980c84003804c140b060428440c1482c030503504100088030700610101081d16041c034042001520308060358821903407280340c64000000400c40d5134400c8ca540d0f1040900841c5450805561010010703682004401041404190385421004064040740c2c440c019060071b40100107607034041450070042200d18581e6804400928182d103c005045400345151f80 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 203668372 1250 203667122 203667133
    0x1212180c13020406080a050c16060b0d050303040309060206041104090f0213050601030e16060818030c0a02011412060f010c0c090903090e01060801050402070c1d091e100e 75
    0x58070340712036075845a0742950010041e102c51030900050043c0c01c0c02043c0c200b4940c41d003010401d030b8440c89400d0310108510642c4c5003115580134540f06006040c3d00009560020801d0424004c103d40080194400d0780f00b9030310b5100340d0741d58400c240d0703450100380e400400300c40700703d20303030501d20308180d4000925603000d00042012030046802086c444d40c00c12a00c070051541703580410406580600500301014240001810040c0d41c0103025590f928403405040b0811000c1804100d951040c144819000051142a41d569150720700d401541c0d000c1141e8100c1c04034241c410362968007002e44d019500500c050b00840e145035034501c420804052580070b000da0520203101c1c0204040f440c44042c8801810b0a030784d000402445030b0078090b2036840d095210380d10100203040103100003070340014002d045441c00c2c0d60158454500340f6002100902a8001c000d0110040601030408542c800c00d550040c4482025115070116071840f0024904155a80c014240c1c0101a240300d0441d8560107041c0c9100c401c015141c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 203669622 1250 203668372 203668393
    0xe1f051b1c0b06160b06061902012301083c011e020c031605070e090c0109050406051e0d061b020706021902040213030b100305121218 59
    0x10907400c00d410649000d00030400ca00300c20519803140c009041e000b103c0d4035040c000402c601c0e46102002d45401040302c2801004030f06241c440c81e0689080410080c1d1008403070544240090081900000b0142602d9040d4514440080c2e0724a98605a5090b030340034103001c02d0760b0032032441340424080341c850100301c0458582524a40d00c1c4c0c10424660300d460004500c5c004481d007001c912400b04030a408071580304018030382458400008071524a1515941c85611007483c1c20403e05140044e444090a030212808100c60270a010413404000042607e0b0289040c0c0c6503010b003c00c481d4140209500031910360908030703669400b49080c2c980c9a01c01007040c1144561785d0b544005172201d40e18400d401640f04001c04105680601422002c4e02451005281c03050482044500d2540f803503402a014a50000d05c4100c0b080c41140c002001c2c40d00030b43c0c001c62504007619000d110740385030300c01600c0f10700501c0c442c5c040c0043c0c0b943c00c6890041000b0004016a1514448907898032101020311315148528100701 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 203670872 1250 203669622 203669671
    0x80606070323030108030418111b0f0307080c1b150702040b060a020307030f02012c15010608010501030b060705030301050f130609140a2d0b061c0e1f05 67
    0x3d5001c0c2207500041e54450f89040a6032600340d10f8203840084050601c010703907080521800942d2000001001d076000555102403036a070400d03038800b200824a0100150700d40501038010010140b404024045820070380c184806e144801000e0381085900101c800001d808800c0740d4800f9000880c002400001c000c000080092125444021070304096040403940005054000350380c24003c107214002448540da452108000c0041a403071004400d0300c1c240c030014001e803010007180021914141840c010382d40c40f8503029144100921a9a0020b4200390740310300d003410203030241c07401e50b0351200c02141075900b0002000b0483c0d02600f00184c114a058407241e1420b80140124001040301002c00a2a0110140400c01f000c0004111002c283e04184005a03402d039219490041e1000d90f9003010554005511044040d040020308581d02000200d101c3c0000c09648020701c1400320f6401d000c01c480b201000840c3d0321003d04e0581c0001d40c13440c13940d0000c980079581d040154860807108811040c107501c1e4808 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 203672122 1250 203670872 203670877
    0xe0f010312030609020d06030501140f04021c052b050703021203130b010e040303060504020c10050a0f0e06100e0105130f0204090606051b010515010c06140405030a080106080606070323 81
    0x2c4c002c030386407554010000c9c0402807160309010141502414150b140c001c1d03158081c1c20000e04000d0081d1000501280340c0241e141c22481711aa003c419102c002000ca00e0140d10281400070703031501e0407092042c01a00c60300a00440d50342a5040e000380c02d91107000001100b00741c1009182840810303111044200103045d41652901030031003104490941d040030708004080390341980045002d10310402484168071000a08141400181400812603540f0122510003924101255140700c509080c030010b400304000c02c20f01e12920140140001d55661101180013001c000e1107440e412480642d020003404c03031240c01180d264102004003624091340c41c41e0320317002c0301c0555002200090000c40c00031000414069080c02c03400030003000340401c1c200001b91540046840c01c8076414021900302400c10003400750003001c901c03000b010799804a03180038100f03d500c0e45c0c080035449001904a0002168283c0691070b881e009441c058012420030000c1d907410380790b502c48885a00000c001c4090305c0e60841c50b03203200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 203673372 1250 203672122 203672137
    0xc010c120b0321090409140307170301050a1205070b04060903050f01090c140d0512190206070804020925050408010c17150a0b0304050c09010e0f01031203060902 71
    0x11949614a00240300d441160350748030300184240c0004243c0103080900203108480005508000c564030755990000a0007480d1003c0c00809144240051109800f80030016004c42402402030000760b2000b00700b0701a0714802406410392054041100b40139013000c480301c0400003440703441140e0000340c03a40141f642070781042d0312400008014090510402c0f00a01114030b80f0300d50034000340580c5210343c2c1c0314007662602e4058269210348441411003103954030074044144940240a40d01820881e1540c000c4950082c0c1100700040c40c581020514684001102c510404441d941c00809407150350800c0b40c1504041d10581c8410300c0c09449032540700e5018841030902c403058950ba0b582c0e5250000b0a400d5411510082c414406502004880d007040800520780c41a2425132040c010404e1800150080c402034100044010011040204010000942e2036002c0412103190103260384ea100c1d00d204180c4c0441d034080c5201010001000010451040c0c4c6030031074980d082c04900e0f5a100c05001c01260020f50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 203674622 1250 203673372 203673377
    0x50301050607060513140c0a06030207050d0f020703020909161205061902040302100903020a1a0403020d0203070308070303020903062203080702010605030313090e030903030a05030903040f0920160f080c010c 91
    0x9810704504c5c020323030010014549401d0550901c21180c4071991241800090581440380d00c808500390a0b02c00d0209501865004000030060305041c017601d5602e01c545509903190704c100003000309138024003c1108448a60201c0145400d5030303092a8021034004411000319115000d100c08001a07030340c515251002e400c0b40d034424a54a1a500410004000b140c4c400f405031690000c0242c01560004111420390f50146c0f1064400e461f40e101180c038042503a80050316409011600d101010b915030002e21025400710700312030050321440d1802c110306120082c0c0e6421415030080d400c0000e4050507901c0d42c8403002e0300001a600f40d50742c003c24110f9201c800110f0140c80906418452210244205585000c50750010350802d0b582c2c0011941ea8403070b25049005006000c00090750440c810021140500a1600902e21035903480c0c0da200f0180c510022003880f841804481050550160000d603400206a003101041505946d201c0d41c1c04922843d2065030103900401c00000402801d00908100c20320a5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 203675872 1250 203674622 203674633
    0x8030c0307080a060807060c02130509070306110a200a050f0d1805011413151d040b091f0308071110020c0a060f110d0503061005030105060706051314 66
    0x5420080260100502c0c02030303a6032918001740185d51000904000340c07203540c00c00603100f5141c0e00000e5101c0134100410100c0509100420103071100200f01c50003160300c00c040507c07003044008583c4000d8040d01130088000307030308002ca4034400383c622140740b0a01000c5030b0503606018070b1500d5060510044200c003c455a00020850103542d5100102c4480a560241c07160101c41c1450002403440e40d013252601d09480740132450a00105203404003500800c00039100400105000c0005009000b4020100c184400300010031f0325a400d20780110741031210010406400c81e504c41c1c1c0411140b0308002c003241c5180d58100004000648104001c0c003565001e1562013503584280300400070301100002c50b00f000c43d00b0103494205582c03036a690380c0307090760041d0500c80600b4000f00701c1103500f10051200f01c0d4081c414103c900da80181c02c240110b020304c006035035100c007000c1144803c0da4248020320038641c00c41400c000c44804102d4a83c0082d410800c41c0b450b1111034030310340d141c210700c0c000170001040700798006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 203677122 1250 203675872 203675881
    0x17120a230a02090118050a03060b01021608070303080f07080402040c020309060d14010f0303140a0327060507020f190c050a0b09040b09060907300f200d0b04060308030c03 75
    0x2010135080717035034240c1802070000303030500c40403483c074141070302c4000c025a0300c40c80313842c050340e00906c52101c000030343d240c0e00c4841940c1c0e2030150340e66240903c010317004100654003044250f000700300511302c28034103a290115540c0b03640d404e22008210b882c03c03600c1140000e00c810041e5607103d00087c00c40c1c80f029038022605101014200310840b2044c0c0c4804180d82d21a00100002604801d0142c20b18160108441c0c40d61000c0340150003a181c0300c401810844550640b402c610603005210f0341d049070084104102036a151041641e0341c2c42420002d80a0f03a01203140320580161400884105520407500780d00306940d1070000c0341101040c0d420540c40c0b980013151880d542d061034841d0543e03866040710150790900b4488081522050041c103d0000c20071552500c0840c3d8221800700300d42c80300014668410598143c0c1107000415000c81441e007014100343d048814442e030344142c44580c500726502c01e0b03d040400e07021040205003441c0003075006501c400001001c10440c0028512490150901e96540d160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 203678372 1250 203677122 203677127
    0x50d0e1b010305090d12020904020301080a0b01050901260102040801060609140126180303090f010506060c03040e0a09020a06090608181b0103091401060317120a230a020901 76
    0x6003445141010700d000d041115210001402c81d00c290003d04103c03410100214581c8003034840c0381000c1d504240000000100325800058421540f030080da40060b4a0343c8070000c01c40b4031300d028801c464881e281d4013102c0f000c54414510890381c00b03403413200051814bd990300f6554295102940944040340c4015000c000300880b001c4800c4000c4400d10f0034042c0104600f013a0464520004520000310000d0b400148110807402a403c11140c180411a5203a1038582c1c40c065079001081d000080070350070440403400c2801d080003500d002035401c0340036604090400c24161035049000302082c0c0b00b69220f03410180940c07079414642000c0c1406580d030160490a020028014100c003901e03140100b91400010b002c000004100c0074441c0f0580c65101512662580048010302001c0001501601d01500550718030141507000714100ca12420401201064556031a03a680c014880d5012001d40c1040c00500c8180d65075018288034140041100303444e4560464050300e00030101c4204c5002903000845525640c0c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 203679622 1250 203678372 203678413
    0xf03210304020a0801060b030a0e10090b150405010e04080705070312170f040201020c04051504020f04050306070206070206071b050d0e04060f0503030403150e0a03121505090f07050d0e 81
    0x18218001c6c40200e1404a02e0f95032803100038440c0e042c03587d403140543d841e01d1040c40b4041780d203c1c0f03040050004c1445070030610860300c030585076030700c241c6a480e40c1071010741800d0181904031fa40420580200d40c2d05e50320340e0030711603020a00888440c020550b010001034480c03c0860541c1c0351300c0d42d50841500d14506110f0742c14001510b0350b503124070b1603000c001c01130b0381c00a11080c8110040c5c5021400b5200c13500d007031208110800d04540c1c02400840e401c0180c804038409402107c0c1d040b821a1400d13280c0c078005984444050f01c0b03000c0160003180c0000c074a036008400611309908000610079551585441d050300b442d42004090700002c004017042c881d40d20b842d01800c00038110b40c800c1d070302d0850b10785000241e4030721407440000d1034070b200203030360201581042d840b10b0a07079440607080c2c81c181043c1d454000c1042024502d410511850b0000860414000c02e000d2820740310060300121903522105411188020b00505800410004109100d42000c980c00350342c030143c5c4140020007903454011301e9484140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 203680872 1250 203679622 203679629
    0x90a05010b0d020603040f050c0604170d0806180405071802030601020105060f0a061103160503030403140322060e0318090901020c03040b0f04050a030804180c0503060f03210304020a 80
    0x3202002e0000001d80d079107004482e001940400068a241c1d074501d0f2481c208030110081d549c0c80100850006843c855200b80c2d004410b918900b900c901e80c84501040d2403008041c0c42c00da400524565407500d241c50b16403021500700c0d0040007121781e515071fa0649403c40f0802c0c04149114150040b0511009580901402d80c00c120b0841d0032a9869400a000c1000000ca5114840422100042441104e202803080b61035090051a40c01010710b80d0b801c06560700d074810b5808500103114803688800f94002007059070700914448001d142502c0021950780d40740e0b0703d01001655031a60303403024040036030010001860740000070f007403620300160014108070b802000204000312b540d0040112005807074002c402c550039161448a8582c50300c15060400c20315014503000140c10254110740441400311520241c011506ca25008190b9071501035001c00c00d0f6401050090042841807020540d1881c102d10000540c8c83e018040f9584c0d5881c048425542400c4040940c5c2d140b8030000a120560074440c0f400e0016 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 203682122 1250 203680872 203680879
    0x20711120703050c1e0a0b040e0901090302120309190c090b150712050c060a021201060e01090303030c0e0409060501051215010605070221010e01061a0f030901060e090a05010b 77
    0x405140d603d4840e100c500b10842c0714891310181e0448650720314840c9803a0030084020f0040070613180c440068440340c2e8010302030560814451000610003003414094280340950541c0600041c0f000b4058010080e04058030074400c0d4001e50942412000101200408240c060000004058603201e040000c8a1504000e64003482c0c001082400207002141121000c0b40d020402003c1007000b840100c41078069445040e116000346028013440010031740140010b40c00c9140f180c1d580d41da0b118020794804040f440724601080c400181000801e00030345c40009624958107143c0c13401544a0001012600541812541169100e00602c581d041110820920558940003800e4000c201246181c505a0502c20141046400524402107440e4811800806821044602c0181c40070310003560281c98040c0c2c00d46140d6217014400120468480801d25081d4003680d5098500010503000200039800140700940d04d648555001400c0f0b500c0c42c038401d11954000c000b03400340458134035099007520186c1081c1480b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 203683372 1250 203682122 203682133
    0x40c02010603020904020d0602160308010e0114010c0323040807290301030b07050909040303050f0c0316140702030a0b07081f0506091207080c0a0e07020a080a030f02071112 76
    0x140c980724813460f01305030100d131080038507807140ca070400c0a40b28500015140ca40d80403030a004154200c01c41c5410785400140c1e5a61582e02c0702946c80700003248244c445d001850240255010074000c0071104000220034010015040a1090b0614181e102d640b05a50780d910680e0108610000040041e0f5004c01d80c0c444c620700c60000e0320701403525001c1030202a0107215074801085035a40520304840305e50030050503841403403406060180040c06c048984045a211035030010741031003400411640304205861400310550291002100c100c0081d1401c00c240040401400c4090385d4200310101026201d6011003440745480000103000c2d010142c02030100d0b80f031000038000007003e00980d40c4251030701503032170a8848101d040080e01e15021410305801d54021242c1c0400d09000c0032450004249013518183c5180b591420350141d1040308440c8100180c100344030303030000100c556008141002c40d03132030701040f40d00e446000c21040b680210f004030344190041c1060503440c10800f04d008840d0103041d01904 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 203684622 1250 203683372 203683379
    0x80105060a0e07022a030d03151a071a09100204030201020a170d090b1506090a14120303010b0a110d0c0b090a0f050c01111b06070804090c0e040c020106 67
    0x164201524000d44403942c540500080c00c1038400c211481101c15020f00040030031680f5002501c001603d0a019030103402080d84054903030780a070044200d44400d203034071041c05910385002458034103004041020600710401000d000308a600d8049801400c5600305903250b42440c0c04c0d114540407000c035082c015180184002c0000d0307a00030803281c0c1d003180c100600081081d50391811942c1071040c200340192075803405200b030040c09005803110b80729030716811124411140340341c20801d0350700844200320b40c04900c0c254217104010200c00380d4085001e014049102108901100c523046400c03d80110a0680c400302d1083c048aa00803290f00b881001c68010344502c0e141c40b070005001c50840100600300300b81c180c01081c104041041111101c039042170030403140c2c815130701c0c00d280c60340100c01040c3d0010704034001074040392002241591210065580602d0401801c42c1403000395080030f00305880300841404000b440d82031034042c2040c0c0d18459920659000e651004000c2200e580c50350f01c104683c580802030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 203685872 1250 203684622 203684629
    0x1006020d140f0f12010501120b0306010b07140d2d0f08060a090e0102220f140102011b05070303050708070207050103090c0b0a2c061602031e030a02010608010506 71
    0x38100060380780c251954529044804542d50700c50341d054550810760010300c481e840080d511280d0705842e000d0703807590b013800d030018415815545483c2407503605401400040210500e40002403481c14481c09040140070040755219080402450048021420801d41d000c43c042c0c2c8280c2c620403078501c40780091080503043c01300030712619040f58040140001c5502141b001e40e41d00414800420340c01d00140400760172000094041d400082c4001c115880390000361034130080342c1000c40c01791610f504800c0480c3d880c101c400d000390b400c4040414103556840700071030700a2100c0c4001c208808556164250740e003443d468000c085030130082180c8104402c943c20702c2690b59021803180b040320000d2801246100413410324101500d6140c0c0282c044000021f010b03216035400024000b8005000800800c81c2134604400e8a81d41c4d000c0240c00e03600003803c203c109600c105662000b01e1090003c4e045503011218280c90740301264001c404c00f2829440030902c81a0170358240545c1001c2c0a21000034812406c1034400b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 203687122 1250 203685872 203685887
    0x8010501030b0f130c1b0803190902060304030e010e01021b1311031006020708010b09040609050f01110c010b301f0209010906051e030a0f0e0102031006020d 69
    0x61604040d12502c81c680265116481c4020521008142d09020003503810548000c09000c101003010a1103000160407100d10900b10362162500000d20614603920a000708907041505114a695550b848262001507107030480698880d030320980f242d082c11030036030700098882d0305001000d80c11940b088242c451000e03d8015003981151050350185015141c141c941e4002c0d1003012000020000040108178203504051400350450740301e50240c0c2c0c1d469842d00c4c205401d070380741c481440e0740110064010800198550744400040390255043d229484404040e035801d56420113800f0010b5400400c031000c2440080c41104221401103030494104e00042d2800100c0d031550001030920711410084c09402d11505100b0030244034881101003200e6079040c90200700035046204103500142080c01c000c03031464007800c125115100010318205a00300c0c64460b407105503000403c11121640c482003910103200171030180d60310000c18a000940c40c0d10b44041d001d92040203070350200c8219404802c3c4007480907040900c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 203688372 1250 203687122 203687129
    0xf0b060c070e1512010614150301061412070f090b0c070e0403031401060f081b09040b2b02031204030b13020d0c090903080a05010f0e0a060906031a010509070801 71
    0x24585030340701075140c03c2c0301c440d9500c12900502d051100645008065003c04162000c1c01910503c0700d503514103100b0342088510110504180030401170100a020703102c480c5020810b02041b0b8038095910719600e046007019a0107402181e10b00e5080303902d00d40c02545d42400307840d0b030000c11810100001031007a40c41842d41702d86120071102e5000b1505241c07281e0014465800380800d0380d000c40d6035401005100c240901084000a046030f004140914054800e440001c0040d00100307060a020004000081c6a407848955001c0c0c1400801c800801c000c2c0c0040700c20000c05040c05000d20824010326042c001c40b048507003c014409c0100b40001041d00506a82101d203051540340c1401c2141301180c03c1c074000503005801c1d04040f0f0b2001400508a40105004030f100b540d03090982d85580355a04c040d603100b801031703601424104005004d00c08110307494035809074003900042aa1592843c8000840310b807900155580000303c036070340950b51801c0b100540140025034072511a45046040100101030602 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 203689622 1250 203688372 203688389
    0x5090f03160204060803040b0c01050609010f030210030608010c021614010807050c0a0812060315040803061311030429010f03080901020307021011070506040e010608060a090f0f0b060c07 82
    0x24468080d915a0751011025202c10170403280c1e00d94071964100d02c46d8000c41c42e401903d42c00c100005043d41464030500c1c0c120790256000030021411170f420401404c03c040580b1081545d500700c00120050700b409001511441034000e4800ca0f50042114020795005030010a0a0710780c848401c00d150b42e0001d0701030f50040891030640d40703c0f200da4902c42d051500b84100503140000201d804d000c06203405102e107004090450440d4204006985800141e100c101e50103018018140001419800c01e491072a0022034400800114090b41c1100d0441c990801e503400d840c0300c54500320102c00c1e83c951410b15060800d20880016542d89000030401c0c08650741e0000406644012501541c10b034000c2080d5429a540107007100090034078080e00500d00e9007201801c3c4514071890f4070008550a01a0450b015a40b42c280104003603802c0c8001038492901c003809150b0030016074000050003072483c2c882c10911110744000401c03c4008018800c01703944c01894400d115181c100014440c0b02d0000135038508a40400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 203690872 1250 203689622 203689657
    0x1030c0504091e050d030e1b01080c070b01080607021e10090f061a0f0a0513020a23030106120e0a020f03030d02070602071a0603071a0d0204090e0105090f03 69
    0x1850310460003071580c0e50f020384008001040000b005004500702402c200c0960701040803080014405582c0d2141d050300b1a10481080031444180d4458441c030b5502a01100c5d14038540406030b5160745581400768000001c50b00114103000020303505118034800c030f48140d9080300c500364010782d00f5070701c82203210241c1000796a640b01940070800400c107400e50841e000342040103041c017980c13034280c142d91034401240c1c400c0c03c54007036100d114038103202000306460001e0b03c28440f2071519050718000794000b01246e0b06000051041c8208070840718001203840746400e510b00c0d1a0751500502605c0341c0d2034503031072801040c20701407030715094000003440840aa40440c0c0640002d4a408042401c511615110420144c000507427581400015001072150510580160f0b5506402c45401015030780c09503581c0c0d501d82c0200408001d0296541000f5a82d600308030082464080d01c000d03240c04a0780140d128140a80d11910010103840e0300b8030440f80d2000b07081018041c911780c0c9110254a0b41318161800d403004084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 203692122 1250 203690872 203690891
    0x7020108071211030f07090b0f07030c080c0106030f0605100608040b040303060e0a0e0c100504050603040602040e04060b1f0f03020a02010209040903020705091e0703090602070f061d030301030c0504 87
    0x5811084040d81e80c42681030303132418907000d940721901301200d40c2000300b4040700c1c00284106054048992281c090361610f42040e0340c640d0304580810140c2c1094a400c5030034003849017012401c2c401e0500461040e0481c0ba07002d42c49140c15800d840d00205034071101d80b0500b0040121903004503959900a80c40005c80c40035588524040c0c00810b40c9070402140520b00200300036090035581d125140052000048803c20140403040180c1002180300400000305c060104012504090000c2e54015114800141c141030321150000fa135024100c909680080c2c46420008044c140300c015404c039140d03803918051341e00000d208040c00c00da881c2c211000c105030b4005019000c00b0b10130340c140c4444003401031090200c440e031800c0c025920341041c003400d803265080300042040042c4110134541e00200050785d42c1c800343c0d40c0c00415002420110801e9407136603000c01030080091040b00c02204214450740000409465050000a0300e0084a20200c0c0c154820001440410510134100d4200d900407600802d81c8000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 203693372 1250 203692122 203692157
    0xd090b1006020303070c150c11010f0e030f071716060b011b021009030b04230f070e0c1b07061209150c0e0a1d0c070209130c0510050c060901020702010807 68
    0x5402038074030380b81f071328242d454030040398031451544800012800a1001d8a101c0c40ea11046441406120300c05138402c00404810000e010081c0c01014020340b40071500c104c22030340100300b9500407554508024800c42d4014104500340c810888409020301e481c105034620040804124181c81c50301074403070000000b84450041c4156006005907920088400319800c00d45440178951200409404c0f0801d00e80d40101c04c0b407070000036003015440e5403400410b00507103031060994107900080d0260b0b02c0c0d002d0400506043d0000c1e00f80c0c01c1202c0302d6a40081c0742c100c1c5071200050210740d012080082003400c000110000c601b1216161030505603810000400c425452000d644942000c403090342c108110f100c000600800c4503041034800c05004680304450394900352a03140700d01c91114000e40c01000701c40440c17801701c101c51214030024450700012070842c4d21031000a4040780700401c504001000025615005d030024040e054000082100940c01e2201907400039042c0500203040720104030009004019024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 203694622 1250 203693372 203693393
    0x613060b06040306020702090f041203050c0d1a0a08061509060a15080901111306080a09080408070f09060b040e091c0806010219030519140d090b1006020303070c 71
    0x103001000241d885a89240107806908071a40a074454041d1400203081a041d50707504500c11940420546400c41c1a15000e4000f41005880070701e8000040c030a8110642892140e040f40602c035100f00c140c0c11507010700b0401c032060b8503044646160080001e101c1d242060444403400158211400d22440d60b44c0000300c0c00503061903020b421055000b9610010f6150480c0155000f106090000e200b41c03042000843c01c00c0c41260200d0f00c69102d050b008021152007040c4040d0420f40011020610301c05035150401d80b5000750b00500712541220b44100400d0082100140003800b40c0030741400001c8c50b01c13100001601175481510031450340200020310984d000d200300c0c40050001d81030245501c0f0b074440c2c01002124111070780e60151003040b00c95082e0350712410a001d9901d42c950b0381d20b07241540f440916100f60303810794034400034481c1d41c82d80151004071070400303403c210818440c0018185100d051152580101825404151528038000d0108643c040308495008031141824901c108051600b5000c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 203695872 1250 203694622 203694641
    0x3020d09052e020f12041113021911030a0305060d0f050a021810060f02030c0604050105061011030301260604060b030105072a050f150109060e010305061306 69
    0x18082c642841016441000c0e1000e0007100650052004900418140040744602c1180865a000a018805400c454860007550252003007200c444030490610214000c94104e0b024400d0241c2c01040c0402d080c0d540d001502e078034540340d18198014003505030040f03480c1d01c03136000c0700303000c254940c1700003503c603120568200c60b15a80240c42010411f03003402c100d9240c01144400700e101c0e407168558941c0300461301d01c800d80945403a9010070741d110b150410683d0790742ca000214a055000602a0034000744041c081988102e0140d03002044034602002040040c6000d24030340310034009416078001c1d06900000540b410340c0d581c0c138200380c103c03644142e04050240c06c1d042d00300010b100d80703402c001c200040740e0441c0845070420740091066031030f43d400a5030750420001e44800d054005a107501440310351840c40d2007180e4090780954843c0c030040c00b203041c11715502c80140c284200c100401089640300794070641004091521242e0525411640d40e162500c8000d442d094902c10b00d4540101400701950050001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 203697122 1250 203695872 203695883
    0x3060e0c0904060614010305010501051204050f01111902070b0414040f020f0c06071b06020d09020301150609061806081f0f0311060a0804020d050102040801060e040b16080703020d09 80
    0x29140c280750203c0907044a02601000d03c41d03010701d0400d1075000b40500341c181d80050711042d0070641d1045900100c140020415503952140c02401e0500b4142842a0716a02040e8014999a130a083d1740d4019400f0180001034110742c8404000c01c140740c0c2c5442660b054800c00c51240d948003c0c0307880060003800c84408106002803002039074040e0300344520020100f0035012000d9407079507503c0e84c80a80c0c04c216503822081d01d55041907200800680a43e00030700710000080c000040c5001990046804c565a850a489880d00f00e07004c107224030303500078132200000c040e00d00e040c030b81007890354081d060401c4641c840c40c0140041140030407060307480442903640e403880003502160915039a10180d0402184c502c402c1d1104e10340c0205400d00b5007451412a0789200341030300d079000c840d1681c0d820322014040ea00030030b40d11550309110125840600b802201c0041084409001140c28582082413a00300090480d000006401c51b5510003690800070349640181942001a10364040b90145000342c103410400401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 203698372 1250 203697122 203697139
    0x30a060e01170c0a060e010f0201090b010314100203040f1e02030d0302340b13240b030c030a020f0a030602030f1f03030c15060e1602100c080103060e0c 67
    0x45400c207000c1c000b4100000c0c081124a0740003910103121182e00d0500802c40041e1085038045919405401103030040e12103171000207070030f45050700d480308494001e80048075028071000407000003110070804010700d0301c020b090843c50740c2855568040c1d039424400000f84180042c04448800440e1211102080750f009030503140c01030085d101c014001e6202d0184991000c04000320b0101c0400440d80c001c1c403560401c4001100c01480303880748d50b040400105941041042d107402000001d02d010009004800104402d1441d42102041c031810340b070a00901902940c8281c229200e40d0342c0005100f10b9241d0151010580c4107942004102582959040603011900000038040044082e945240c803400c000324404404c29580c5043c0700c2081d01e54803000c3c001540b400c00b5040841e0650801d034100d1121801d002610907039a007080301041030200c6072280c20409064000e03401c83c3e0140a00308010003203040405c41800c40c0d48000d040b03100d042c08094034030b9a44004590005100300300c560030300c8000401520 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 203699622 1250 203698372 203698379
    0x50912010b010816022517060708060409080703030c0210020c0a0507050102070e010b1303060c0309020f0f010504030f0609020d0f0312020f0403020d03022a04060506070f08030a060e01 81
    0x502a00c81c400c640c5001491003c001140700402040f01038070200d40ea4050800c4d0301260040c030650902c02d03200d0a10850320b180000030803078000022a198108a038000c0c200c01d24203040046c0c00ca0000800300c81c09241014000070000704080119091140d060400007981c0100c03800c200c0c90080c0e11204240004e00c0090f007034100020002e01c030100030348540c2c03c48055540352070049840700c00d1441080c400c0145040144104012100034003903042c0d080c0000e040d81a0380b07848003016103420000400100e070340e4080f02004d50900c102441c130b5580303041c1e07640040350f0700400000307060340703d0780c407024201c0403820150904001c00c0350443e070f85494004000b4080541c40e8180440d95980b00c1c802107000c29603200480c02151650b00a6440f040d2181c03840c0d40c2010701d10340a2205415440c00304904500420020b100221014250740e4200300c1c40900458500001c2803e00007222117680016118080600103d00096092643da5180580c00914075480380c43e012641740203041560800c0426014000020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 203700872 1250 203699622 203699659
    0x60c0a140717010e0c1014040b09210c010302092202091201090308070507051609020a1b110f1c050a1112060604020a0504080109080702100807050313030509 69
    0xca0640d40d0741c4104111003280c2d49929030807200803040ca03045075040036030702070254686604450300c0b815007420004681000410a140a94480d0300328080d4540080b1b4000c03d242801b98102e010707a90141d000c15080c01c0726110f02c86e600c000100301c19041503000102c8a102d80c4401c400407103005001c000725030282c9400c0740240c0107500142d4000b0300402e02c04200e0300360480f05000b6002c40580549903e00d07503407100d44c011502d5a00481090340c07248030301244591211b000b501c0c22001440100340051700c9456000c8020264031241c4408a180c8800c4102c40740410310710303044c8984a4501700c81c174408000c0d007400414803201c002480900b0708203580351410f09000c00400c115030500d10401003100c011040d082006198405003d000c001d90303002030001050342c1407650041105180504010341040d544010850944203480011990028082440d208500b045c055140c00d8240130300b8210031324503255070b0042c81400020920402030110703001a1082c140240202c418808000d004901d03072b0316004400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 203702122 1250 203700872 203700883
    0x20a020307120f031404020306041416180c0503011202061810080405070b0a170702010902060307020c09062b030207050307060c0c0b030708070e0117010b0c0d0302090d02060d11070f060c0c0f02060c0a14 89
    0x844411070400ec115000e281c8a80d00f00c90503161095812100c0c506241c00f8017200781c10545031092441281c0038610140d5440c2c05001c424810705544011203842c09141003820a01c403548070001c036250601003414081c0d008200030300050080c3d9502c00b0781d03680d02c5030203d000d802041c0d0047c2d08544000144442c59902065010113458150380c0c0c80500e844813800e000d0800c00d50138030320b03006040d0f03910800107940b102c5003521a410300a00c12141c241c0c1d29440024200071040d4040303130100b0715070b501d100d0804c8800c2c07004200804d2000c480070300318940608003030090a001000e480410032050b015241c668042c41c007203a000c0043c240e0141d200c1d03850b02d064070070981c45041d4805e22071042c03407000180e0314428001c0b81c0d40d0b45406005d0000250040d400d20450360032039407007050032035195042c0d5405169100c01905605009001d01e001e1081c0f581040002c603000c251000040007540782e040c4000ca44c11485880e0550340c1500d00640d15440b90300840c0c180001040001c000c03810301030495030034420000c2c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 203703372 1250 203702122 203702159
    0x31c05150a0e0a06050307032001030b13090b0a0207050c060d0e120406030f110a1d18190b0a0302060f0c0f011a010206010e010306020a020307120f031404020306041416 74
    0x301000301a80355010951f5034204c6100040021000000000034801d5020014230002410b0402240d80035040c0001080001c04119600c2115a500641c2e000e10074820310850b08510301443c21072900e049519070680310800105203d02648000904060102c0d2a40c001d41480000b14103a501403000c0441844003a8010b1241800082c100024103441d41500e00c6010702400b00c2c054050f10b4900e8000d004d4802601c810000d0b10505201407402150382c0301d0106603c907042295407513060303514040384d03a08944281f4290503c02c0528150b1000c4180e1a00801c100a40c2d404a40c1c09031030340e000807441c4005118000481004e80200220044400015085480c0085608401712750303003a104001240d803440c0c00d10900e10745500e03840040010507070700c5e4003c0009440c03a00c140c03480c5c95500e40380c01001212080c0c4000000b240d13400c005045c80d40c0b6201d01c1000620b900b84122035428203800181d0b0380c0c900680007508203041a101008104810440c005403483d68140c0340460941d2070364040380141c031030710 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 203704622 1250 203703372 203703391
    0x190c030c090b2704020d02071208091606031104050418150e0a080906040e040c0e0c0a05070b0a0608070b03040c06090503100519060305100e031c05150a0e 68
    0x70104903030079080305a0750024400400700b541d9a0039040032120303000c3c09582450300540e00b0000d43c0f08000c0c09000411043c0e0181c290008140244500109805401031000d001a00000d180075900d000e9030002104684141c0760218617004541c503850414401d03640615405031a011050041c000c8055030544800e000314400748840c10100358810503601c110f40480701c50340102c0c0c15000000c3c0f045002d8800904042c0c00281026158000070340c1e0300740162025a084c0d40386c1f04041046d00448105598088540310034203040c0510f03180c5c060000d000350080208864001000640c5040307560380840001d243c1c0908540629984400030a0249d001340c4041c2c40084007203402086281c0107035002011124054010260020f4181d680002840c1c05001d04440c80440c1c0c10f001c8502509001e504043d40c001d1000e0010810810445001c07520b043c0c0c44494140c205100818000492044c801100242d810010815a440214050390201d0745200c90b0741c08007000344041020610300303008510902014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 203705872 1250 203704622 203704637
    0x8071206150815030309100819020301270915090203010b0411270a0512010f090c06121e090215070501050603070e1003110d0609030203030702010c0504030503030f190c030c 76
    0x91003413580301d118650401d500b1035806668407103105d10a0140d5907010301400c40f04440c0480940c880d0060b40c0c03084c0e2011060781f8407104c5c0b0b03020030680350805031503001803d0000c00858405560350142e5800540140c00300c6591201c4203400e549083d00120744c21140280208982c8103442d10742e02081e00314842034400102c13800014406200c1c00c4901aa4032000101100c4159107420708000341d0a88106003c0c5455480700f008156045182c0120b003400d0b4415020b400c099400c0c004c00410402c0901104d00025040c000c01094609100030400d0000d0031441020074840306900120307524101012400018450000701142841320660085005100413426140c49568955010300402d000750788015100c6104442000024844601250030400c050100c1c10765003460386130001180c001c000250003581000003000003966080c4a240b01c0020b8a00b04142094255190725940f80001005462040c812070003040d022001450002c0c0612481d1758188400c003070b2540000c0203031103802500d40200303510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 203707122 1250 203705872 203705911
    0x51005030c030c0603131704150e090a0b01020109080d02030a20030601030207030e030d02010609290907020307080d1517030702010305041e0507080f010c080712061508 74
    0x30841c0081ca2070018010030b6100d20200820207a0350000d4081c1154003c140c14220009004404401640e00d1040485480f0345c80e00e040040b1038100d05040a0421103500301002a660701c101d01503802c4005504002044101d01c0c0040c2d004060782c440182146101003000c1c2d0800f819900250b10910000b40240044001081c0466804d4001400c07806000c4083c00041c020b54030030350141c03c00c3c3e8020328210b2141200c400109007440b171002e4200c40144d45590091000f95254041d0900c0a86504860340600e511003404401c2d1000d5440071034070030408040880c088034820810380348a076402030941c650b50445125564010080c40310a1101d402138400005944c1406441c00c080001c229805076103413030103541c0118000c14000f4000c55100030203035845400b20041c40600d00d01c00d0701c5000100407c03424548550716100b80700c0c4548a45038140302800a01c0c0d130740710910a130054010704240d8000c3c0d60400e1010b0103841a034000c24242007160640644195006483c2c80c003076001c070765032100c54043c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 203708372 1250 203707122 203707129
    0x2001020726011a010912020a05060301080102030a0501140307031401020408070f060206060301050c0f1b030307050706050c16120903050102072d0b18010e060f0702060709030b0105270103030201051005 88
    0x84a90b210b80404d030400806c015030301d03070344040f05c44080c8000c003030051a82d1110001901c9800c00c0e048000070b80e5011042100b80d4089204080c0544001d11f4000b001b031140c980042da0700d244900009001903081d48550084900c00d40581c0c000d0710303203801139803040c1d038442c540210980d195114100c018441c20022400714101846158050415002010f00c1d0010f00001011a680500c0704003500e02c00d104001c0303880c2803050016600400082c0e441e40e40c4c2d81010305041046c2c64002c1c0c000720710050100180c9800c409800129a01c55500603001d180b200c200c0002035440000e2940003801e20b500024070403081200811003401c0c510444c0010380a20714102109440d400c42a10006021044240200368221040c04044100b2240c9200118a80317501324041801d040c002d841d4100f015508005000340b090b0184903582d441459860291485455038580750313000c00040c4506400f0b10001d554640c040b0b2850251400c0001401800381203650390307850028020803044070000020002d281d80030402e4503 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 203709622 1250 203708372 203708411
    0x3090609131b02060a06061d01020c03060403030f0e150a2301030b01061202090307030201080a0b1306050103050c0a0e090711061602060a0908070615030f08121003200102072601 78
    0x140d055136100401c88d100f0305084038081408143d54194803449825441c0c1d0b940070040c1902c140c0c400c1d600864151081c3d1030410513030f407104461301881c3d00810841000e041c0440c1800e80c1c8030a0410b0045010b06c50800c10234088240312842500300100c520020050043c40340f28181207401694550181190760360301c62089014801480342d060f000f11000f0030142d032090400319001901d0b4400000d00108420004542540d5042801455a240c41c400c005668240c400e099101e0b42c1d0030101e0f4580030302d61030000c0081d80e180c141c4620440409000c118081d20508881108100201c111021428002200f400d04214402d0000c0107100710b200049001c0f0203070103a110b1180d80081203e051034000d40e0703844050190441d01d00e03100e00c504030000000c20103251400c9022405030b800b00355103440d4183c681041c880000c0076907c0c8204d60002c1000083c504c7c110703440044100854101d00d51099000403030812440384c0c0003080e580030301c60402c030303a419902c401044410340c014002c200780320303241c244002040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 203710872 1250 203709622 203709629
    0x19030528020609040c110706030906060602070f090507020316050f0105150d0809060f211014040903020a06050106030e0f0604050c12100216060b04050903090609131b02060a06 77
    0x40c01440f445546081c40d411808119030350f41422004610450922071034503d8950100b400a920303400e500741801840d10480c400b07081c040c400b402e0742c0380c104070244241c18091b106100030203544500043c0d003d071081c0145d506000140c0d9507402000d00f0340c1400e036a90035203807100f2000c652814002c20309118031102560301402005d4030b400d5442d546601d503500c158001404164021800b00040341d4108030150007050951105d0079100c1d42540800190881041c1c002d00c50944443c1d074000c1803014140d0042200060842200c0114440695140c01c07403d20010907801010303142000008141c09070160081c2000c0c44001048500390150100969a501016a40588075810198090001d8100b240c00100321940c0350045503030400010004134102d0703000030007900c80f054032204440108078040c01000e030f1202040f10288442c0c00d004071402d40780d02c21210410720540000450381034640300c541168801b240090342c104000b45079004c06c55150384243c0400c0c0c006010704400149020500e1050400342d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 203712122 1250 203710872 203710879
    0x6030604110d03110601030317070507021302090418060e0f011b260a0b090624091206040b0603010c0504030308040803060a03080a020c030d05070308151903052802 72
    0x6240d10400c2c00700d0080c01e20019003c110290214564a28003005401e000314400c0c4d640701c440f08040c4827a801c021078050410b07010440100074101c05030ba69110170b500f002c1450308006a841e061040000c00404e917466039a1200171080c403030f14007440010381c0480319020800c407c0c1c80c455407a00302c1450032101e5030343d01042c218200300313440d50b0702d41c0c440d96039000c880030700c482041d401c1c41c104103d10762808805c8964000369910f070301c1c44110f5814159203041e0840804e880d40c8141003102c9090b0810044490342e4003407071203804100051241d8542e5400f28141100c80140e41040c1400c0c00d010b24210402c88043d4069801c0201e01030405100c2d000f00c50807680c040c0d4403507034a51103940e51f40030568400740120740d00c001c0d000008804500d00c0001005001d0064004059078500102810709042001900d00c041c1700c018030074000801c1d00301e8030183c0e2110703050340750505010440c00084c0c4605a603901408d940049100301204000001402c1920f00002162401115a281e1081020305c040020020341 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 203713372 1250 203712122 203712143
    0x30f030f0702030c0a080c010b01090e0441061b0f030415020a11070510050f1e04081e071401030c020c1e1207210510150e06030604 58
    0x1040c54a54100c0780c101000c0d106480c03400040d05101450481240130030394801034009a43c00b4005000d2044034540002801d280310760620305140565000c40081005d81050001500403900303450004c06d5106a204500c2898040d0f200c0440d0703208043c0145004000300d201c0ca0380032803850b890780310050030b40c00008130203140750503113400da03021032a00054000c41e0a012054664960f40c000350000d003a40d6a80365440d4452000c04401e00c0389054120f6210500400f2003000c2410113980c0482143d1007210020b024540e11403500110b07640c08104010016038821021a001c1034819010810300300c014010601d5007400f00d2144095905c90502e80f00303101e005450303854220712650080d000444809860b0041e44c400c004e078280410b510800b03140340782400c5201020030000501d0f006611409900140c0000c001c118240100400340d100e02490b210b1003255000220404c010040107103900700c00318440280304031a0107802071030034164180a0029400c84007800110181400655540301d5504a01c45a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 203714622 1250 203713372 203713381
    0x614010906170c031c09031e06050a050f2a0d0e10140601030f090b010f0501030c020f0613290615090d030e030a020306090f250510030608061009060602030f03 70
    0x485e0300d030100880414405500d07000000314421401032200c0c0c020100c2e168144800c1c52030030b80c0484038018000016140717230000f403182c60f05420081541c0f203c1004d440300761601007411100503514404646816940000858a00200e0280c005c4488811844100d54124841c4090041a103c80401c000c40c0c5010b050f00003845503100740c10541a0252803400020801c2d003c0c0c94030038054030241c2142c0c4c07100000f0141000203503410300c02e800d80751500c0e1019090407500710000685440e0068820b85425498080c0d213814040b074004100c40301c4d2401440c2618100c11b8904003548400c013268020301c41c6004524000c46051400110b9207000c20061880310b06d4115646c080d0351001c01d010304a60140311300162600140c4040010718010a45013006103070804010540c1131a0500d448008401400e0131110117282ca04500380e124180c90080f108180c045d020181c04400400543e8840078081c802e260a00001a480e100000140d07072176503c1c14800c80d42c075000c081c2d07a24801c25600718111341c401c20014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 203715872 1250 203714622 203714653
    0x603061303120b030a030c05061b090409051f0b092412240f0a0902010801090f0212011508010602060105010e011b0807081207030b1c0614010906170c03 67
    0x690b540030360040c001902d4400e80c8040b030714007004544103c0125580e5801081401420048103031301c10201800c0c1c00381b100f0501036841c200d0064201680c007540e207880700101000000c2c06112031481d40c881c10030211b00403590104019269000000b4090000c4001040820217801501000000c4880280c030410b0b0202d07082c800000342001825529008a0382040c8074104c41e1400c6945201a5022541035400d1002c00541041d00161070052004e00d8002044010303604017050b81d0464052000c00985000d41c2d4120034041c0c841d01007185489450480085036582100d03d0107030040105989601312680c841c1400d80c0d40300000e028140c0469404e200c4d01d00150b22a003040a58225810101101c90b113942d0745041180e0450303042120303206400705031014030741008412181d1040c03940c60240304601d00c0001081c014003185040258038100d800b00c0400b40031854201500a00b03e4030902c45503036a49040c0d440040045000b07034510071100074084132000600192007120385600401503d000800510719 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 203717122 1250 203715872 203715887
    0x42001170403170903040f09090c2904030c0e1021020301020c03120601110102070309030f02060717030619030c0603050711030403030309031407030c080a11060c0d050603061303 78
    0x1c03400c103c9100044400c10407403050f4103018040c42d20095403a0340c28480c6051207299030780c024000726440c1c03100c0d4501069002c8031030b80856130501c8050248141d110b0103407001c03041c0c180b0848480703100010000108900d100802003110026001080d4175150a061326462207000d10426151031800c01c03e1040030403e80c014a1b14041c801070006152956445030503066420031404041d442c09054100505943c101c1041000f4240c2036008525020b59590094a01560b5000261074102229400d008645420b02120303811504000016040016442d01c4100ca0303100715002070140525004400c0d5a00d00c0890400540740e0080340d42000b00d0504104800808004050000704001400c08420556042c4000c10240d8080ea501207526034403428040c05110030500c114001c004100003c10101c0d900500b001c4010340c2c0101141c0d42e500802604460001144040709501d0050a090000a00075172004040c00002c0800600a070703a640300130951241c41c11540506144099039040000902c207460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 203718372 1250 203717122 203717131
    0x90b040312020702031e070f0e0c03040c0e04110103060b040f0308070602070b0c0409110903030a3f140405060f04020307172b0f1d061204200117 64
    0x1c00500300032590300080c0c60500441b103a180ea81e03400c1c100840030172905201d81c60141440c500100301c00f41ca00346508d0140e120050602c0c5440724040081810842182c3c42d01004100c0720420200b0f42c1800d00b0240501030690402a011a1030140c0014210b007042d1705640485800307184940c0e2440c55511005035a500206013158001da0030004000082d0101840b14080c4a0340a507154850341050701002c11103010482442c98104180300302c030056a000000c49504a0061401c06020700c1020860722500c045245c201c07011115900d10b0141134172246180030706103e8010000c0c40a003000c1e80d80b0740b0011b401910068116001103001a8a03650040011a0020310190403503680c0c1d0390315082540b925807496000400c0e40c2000c100008000700f00d241c000e001031030100380a00e0cc068110300240c503820803886001d0074000b200e14194503540c039803860008072440c05442640d4030086a824500c016200f2102110303101e24000240b1342046640d11100140c04042c3c403091081481000c020105010003030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 203719622 1250 203718372 203718407
    0x180c01090b0f0702030115080f0114070e0a1a0904060b0a080609041401060e040b1e061909020d0e060108070b0405220c090f0501020613082a061504090b0403 69
    0x100080050700c0902c6107c605068405c01c00701d4907030800b00c031a030624940301d440019503030404400381d90b50761004080c84c0c2c010720641030005a40ea104004a19411299030000300c03410741c00c45003508800a101c004002002c011141000030755100c07000c4070100d003d441307900c81c005440b030000103045040100d04d40341c01c5070080141000e0041001c880318251900740c1c1003110308400d02001d000c10009220510358202d41d004007881111800705580f48041c0800502052003103c3c2800b102e815048078440c0c04003d40704211003503585040007106031707010f0800d444d11040c10780700d103100000759602c01068450603100c89001003443d041c035020030400c0340c081003480c4041c800c8041010008000d0103200d10f4a681055231038010449180a8584041d650203a00c41419504a081001004103c1802b0b82902607481001c181e21101104070154200b10641e40c441e22491b05040031440c508800214641300384040b09981142c070340402c00b488203a49013840700a00c5d458810340420002402030354040701040280 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 203720872 1250 203719622 203719627
    0x409030207030813261b1315060f08010f05131e1b02010b0306040b1b030406050907050d20010302092115190b060405060d05180c01090b0f 61
    0xe858041159000e00c01e00404010141c4c0100001c8040352290482c0c080c0c0c580786007a0303c0c0400340505031642408074050b0701507610070351055400d030b403118482c01c00d40380720384801c202da00e644014114001d9481e01034100840c02003612489902c0c810300340c0078140c070182c210f140c0940e0300d880c003400301800107107020207003490b15003259000013002e00d000340c0c08a401f06000820001c000e03110194000271004245821a410f14941d0301460b00c000400c940c00070740c40f500303804e140e45c1e60511211504041d07200f606880c00d0b000041c0014080550000390080c1d07608001c1c0c5441690702c60401005400c00180100f54585807e2202050410b031101c40201c100b060401515180070400080c2c240307089104200c201d07102c800c1c14a50450400c001115600c19045020700d45400d000e0124441c4d135840c1032994284c0c039194164039180b9142c0005a800078000640f945450f402005c5141010b014100c80460a0b81e040000042000c8400580742245800685544180f13070700340024100c050f4080410510545d41c01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 203722122 1250 203720872 203720879
    0xd14180a2006040b1206130c1b050709140f07030b0a0302011805040501090903020c0306010b1204030c051002030a0b01020a02090a0e03090d030207061202040b0904020c19050607200c0409030207 85
    0x9800178982d0b20078000003408240f80220802c20302c860140031070800030f85400413000f0700315040340c0c0d404000b00450410b084000075030301c1d00d20300e00340c110340251520a041402400150440c92043c5004070100e02c0d000d40c0e26034844008608a90b000d0080a80c006a0b460381040503500540d0745600c00d601002c00454519100e40100d026950283c1c0504402aa2030a055040c581c0c1071080040d01c5078114007a2042d545070070304000050080309a040d0750504400049800c2500903841c800a1a600005584130101c241c00948020341046800320201400e040360711407207620202d40b590000f5401031901d030264542d070550400070b041284010a0340d01c400c10a001543d540e0312490003125101c0d0b802092460b0420308002d107494065040e660060b40103020520585c1c550300c0c244c900e081801da90050312000a0302c90a4a80807001c143c800689040000d094140200403030010f200305410746480703903d010301d00306040c0d412403003015203c4290450140214a0b140542280580902920450345204e49 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 203723372 1250 203722122 203722139
    0x1030f0b0414070f05030136060e060a05061c0f0b0319060605091003020f010c0209091507050f121e0a1e1b03050c0d14180a200604 58
    0x42c24020380c68000315a04100d000d5600084030707810300b403203031902c2d0b410744d454190980007020314601d0b10b0002000d180d49281400c0700200a01c176152002c84014010240d4600004005210540d01d517400303050424808a02404d103403003260014000614030001807440c80010310010208108041260754495050010b9960104142c6102040c0440b9044ac0d41c030507031070010100d0300c1907030095004250350340400228010f801d1840c02284d8040d00c0340c41c1d8503000303880121408450190025400030509061001c0750800040700080c1001d407040314411900c40003030a5509024031500210003010400c85103c5c400503101200d900207500810b1500034940c2c1c8291030302045411510902220340c1c03441c80005a10700310485d0364002812610800c01600340c404404908048100d1410074075490b640800c41e8440c14501b2a11030711810364041011410f90104c1c02c048074401d4403a1940240400c215507890745000c65003e071065400703103261092103c411035444014070105034543c1c0c031680a0000290085 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 203724622 1250 203723372 203723381
    0x909030c01060b0913090b13080906210a0b0618030a05010e031201050a0308030106030b120708030d05060603090601060c03170711060f09070918080f1b0f070501030f0b04 75
    0x20b02810b16118200300017881513816101072060000785c00d040900000c913950102148c0c002001880002215a10303040008240c401d400740c8a40085001849031640561700c1c144980540e011010070301c081e141d1740c8080047d0b0300880f840306c0d030180040000031b0f8080205900c1f07004401e805025582d090090752900e90840d241d041180c50b0355000010440d1034040600010703409090700b212070700b0490b825502c40001da80014003543e802c1c0759491540011079555a2140c04c060ba20344411030f0078054882c14541d8680d009080020700842c10280454290701c0d0900640744120a204018100350f8686001280c080b503407a4002e60a00c842000081001c150650307100e0b109100c180c480d0030031a0703840c01840e807a10078010320340714814440380c0c1440012900410a803040380c000182c00b20b05c010781c05028198071820703c8030007040f035030780015090f00c1c01e013000d0b000e0b101528040e0b940310015140712008580f50304c814540200c8d0b070b4100500500070366021b98403031500c401080c000080c0c0101680089006c89 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 203725872 1250 203724622 203724629
    0x304030503010314061b0918250305150f150c030a110a020d02010e2707180602030f0703090e070909150302010e060a0201240503010f020301060503060909030c0106 72
    0x610020040c802d10015203111060030340208000c14051070701c0c0710389a50340b200800e41b4800f1401e00080c6415aa0348020052450503001d40000c10f0b2810001c1d0711296100c2251202c0e1501e0400c1e68610540764002c1c0702d40741c45041e440c426000e081070080d08000c80007607083c0146900055298081810000100c003400c55145601d009503070340d07007015602500c801c0d01004500c109500200e1810f006803180c880c913059043c0d080c20b1044500841c0400103400443c501c1c1c0e01d0b100110402010b0300c88070212668a0301895598444c0007012030b942100c903262207030300e009034009a8001c01104945104180040034214048e103003544030243c8a1000080c40340d015035041c0006490004280720314041340c4101682da07040f40d1240149c1c68a550f0000c0c200200003280c4502c1003001007202040075000b90003885002520030755030714a1000220220120320303424040c81d400380d031800e40300c090403461501c202e80c1692915103c031410b40e6140c800f082014440240900280d01040c803070200865000d0203180090b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 203727122 1250 203725872 203725877
    0x9061509060503060609040f020d05030c010c051b03030106170a022b0b0406050d0609080c030a170901020f04091523011706010f050c0c09070c030206100f1503060803030403 76
    0x2a02c2c41d21003018036050f0702038645481100c007442400002003908250428065064688070b891444d181000c600354020784044103900e50a141c5c1d8220020351140060080846400e8614940440c0701804c6944c0d000900428002c81c0d16424600100714101ea8041d80c0000c24001c0507250044103220280ca01081c06628000d4110a20f403a40d1122218000c0e280120001d40301044454980000105100e00d4003802815181d134a01d2042c06002c41e0350222008100d034070013225921210184004d109528104900907110842c1020a40e41901802240c000ca00c41c005541e06250402c40b16000170134050301c42010078810b8a20000f0010203d0120a001a174002c0c0d203070000011610014190b17140c101c0d5074080140149041000c140e0b0071142d00580405030b45000c544603540407401c640f4001c0d8007440994072500d46001c001140d075000b9414600703203100e83c0c20749200b91101c0400120408550003400516913207008244030802448403200c1e140d064524012906540e00d580103411a481610203400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 203728372 1250 203727122 203727131
    0x70c1e140d0201110d02130b03132a0504111b0d02010f021303121101050a0204180e0a1502040e090a0309050a0605041a0702100c0605070e060d09061509 67
    0x8100005218806030a5110b000a00124015807800f000d584101c94900c0701c0d041d40841e101c03040a090306400030180c002031200036603c2c10f110300320031a4030318811422070f40005c120071525826401b4081b42913245a04032180b00b0810f00705000c01000d8000035805c071a4111041c480da9600c031034a28070410412410030b01070244121380400081c00e41e14240200e10400d40100a0106501042d01d04003044035080501107505000500040300d5201d40c40c2c00340c06040d030a002c14019560816402482101c1418010030340020307003200864103a651103e030744800c1d074002c00890004122070000890741d45400039001850113032901d2914030350110640c0c4e4603100c4d9104090001c10150801e129002400040780d082100d1071074100000c20328401c42c01104140501002c00d41880080c08054400541d801080d40480f10450a801400c0d100c0800c410740c0c0c107909010100f80c9050144840544d440000b5000900d440d00000d014400b80c981e2060444010359501041511511300104007000b804642d5000326 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 203729622 1250 203728372 203728403
    0x7080d0b010216080a0b0a09081201081b06030601080a0f060f18020c0303010b07050705060d020306040f0c270e041b08011811010c05100b0301110403020108070c1e 72
    0x2440c016505041d90075418108205001d0404d000828120469218540542c00d585550340a000341192000007044001e01141c01800d0204007405c843c16038004c14120341c48607150300144075041c400003d0168210754100b0100b11154400e000895100341e1205c0045131000414003081c040b15510360101403040304d00c242c2445004800300d600700c40d40341c000c1c005500b031581d040400c0c3d849110610411240c84030002d248000c0000038030103880105802480c1d1034a5640550056019600031105584038034681128072a400035140300d100d00760500ba95507400d8880031841148640c4480c4400e5804050031800d000580303003100c1100314070840c03082d42468902c3d800760141150b000c0c0240c0140403140d042c00075000c900004441030140541e000050702c811014182d005803201241164060000e0088120540540030b041e0020b040032712054000300100d43c01c00441d10098041c500000380000d450340082940544100340c0000194000d00b0f22401801100411005c200c02c845000c541351080e10b407251 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 203730872 1250 203729622 203729627
    0xf01050105060315011d04140612010c020d0507061e0b01140903060c09061c061409010302090c2209051801150b13081b030c0a1202040f0207080d0b01 66
    0x2140140820307140581503080000c0030641d40081443c0560402c00606400e20341e2440c100c400d48001c1c0340c040c100b000300180035840d08440050407035981e405104040284946450b0504c00c01c2c00e01c80f1540c2c05010070a0303002c2c808561990000d001511400d4640d411021102c185c06061000700b9492100028402401c5001515005400001c04465801403180c810541c40c040741441d84146110442559002d50b980060000d0042001c904503400c01d003c083c1060005540c012000e603000806682c0861060301c04002c0307800c50902000350042e854030045841c40007400c026060b4800c0008400388403040c07405030010a00c0081d0300c80d407007040d101c10030b011440f46100c4001c04031111140c000c1c04014000b0b20214800d802c030380300c0c281022900144880b417401c00c1050ba20f01909244040c2e03038480400d604890485208403103010311074000c034003410b00703146003c026801c12620000307202d18400c40c00b03400b000000d0580c541407000e000c1e001c10071940000d801c1c0c0024072444503040c100180014000000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 203732122 1250 203730872 203730881
    0x221e110a1809080f070516090c0e0d06060b03040c03020901090b01020606010c050c041d070f322206090204050d060e07050303030903211902090a0b0c0f01 68
    0x12405544412401d00441d0510000d030186995000c4010a08a040d4a00004207204040344c00100820200d500340030014045030310207000d0000714050011a80b501251011135401c41001400300b4901d11800040d403e141c0070345043c1c54001d8800145081d5240d00604c05503104031411102c000c0070000510461070300d00c1c4100d01520880c00c0422610100f00c00107503640703c01400e0541401507070010358040000400a48100301e0000d881030200407020305803071130454041079481007280590113011698a40d4a10f0201c2140d042c80340010341c034501c03c2203081d0201e9400c4403014400c2500c040e04141c3d0f49968034141a03040401d02440f4140240e161841c01301c900355081094031900401080100d9521031074401c11503508075900107118483c8000c041d1030184036501c84d981501010041010201e03020003c0c00115060721004140454440d140340c44080d41101d8105070700186455458070b052003640507210184004e0b1400ca0311649944c02c0701c000d6000700b00c40d005158452401080d50340d100303025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 203733372 1250 203732122 203732153
    0xb0703110702090105040b15180f0303092b08030f071701030201080121060c02060906070e090a020315030a051e0105010e1f0306090f02040b0603070206221e 69
    0x99410718415030b000612502061007a144681e0b00e50a081d8015543c1891202d400d18101400c40c0e43c0d001e0742454058400d0100d4001440381a4615280c590f0381008000c50329141c0000b0849610250746100408881c1c41000307159111108040303616001070b0400e0029806102c10313482c002801d10b448980100151410244161082c04030401040180d03000040c0b281507a40142c815050203220321a801c525044241d8003821040c1000030040215402140c458001c80c1e900301560a5603031140c1d41614004144050079400c070844000040d0740e140140c0c0616042101711989441c0b119148002900d442c00201007074074150003d01c0a40344010001c01d8060f8688807000c0240304c40e61401240c4040c92600601300201000c03070312081d8a0440c14091444040c640c09442000a14258102610503c83c03002003280520f15203d110070716442d0145c02e03240720300a540e00414080e81e40d03100401141d90840364003031b01c2c100301d100071a00162040f000c0060780040301d03114582a9515040141d214158040f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 203734622 1250 203733372 203733401
    0x3070506010f030b0603010c0801060807053903120114181e01150c06020c010216060b040c0903051e0f070e09100902061b0c1e0906090702100905100501030b0703 71
    0x1105400b4240c0190350270341181e8a82c1005400740d500e88900303580910601964031800c891001141050700220301d8101c28400300811000d038a009001c02042c0c1d81e20500200700004106d2030010044014002a5200301078800b41c841590031034010200004c9001c00d50300f000350101005104c0342000012a64140140f102d003220900c601d000f0300d00945141640d040280c2681c0d0009036801d0700280c250101c440b943d10200f120748440426040540c0140010f4002a101d941002d8400c01c41c588a01400c105882d08480504864962180303a40c1c0c00821039095804127000d5482a25488181031006d10014203640502c041903141110059052000ca9070301c440590386007521642c0547c4841050320010b18003900e010f05141c2c104070300146424404888554462441804030810200c2010034846200e0140c1e29804540c03589010031044881c203d4910b801030380304000504100030582c01500c0220300a406480424045080d0300c070584809070000d0309c0c64495101803000290340f40c4911103c2e08040e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 203735872 1250 203734622 203734631
    0x90e06090615240c030a030c080402090c18030316020f041b050315090a0c030c020a08031306060512010203010611060103050a06050901020913150b0414090903070506010f030b060301 80
    0x30120019520205a500740940b00c0c000e900101d0f000110300560f42c80318503890b40394541111429059580d032042c03032202c3c002070414143c1c000c8113014441b414041c5500500700030560341e9409014080e0380201d60700c2030601c41c140e0720320f19203514103000610b240c8881c2c18140006083d0b8bc014000200324055080f400b46d850084000140c071003110911042c60032514103280c0c3c9407030b04100344022543c000302c4030303512078030b42418000f0a540642c800854010303203481c103100002180314166201c7c408048064505802000051440d003072210764250308034480e0030001102919407000c5038800560741c00e03140c0660b40c00001400750641000000d8404c10003080200400c0d811a40c6181e21454107100003000c42d45c544010600701007080d01a1030703003154081d000c05907001007241d02ca0050b1086400c10a280068a1000300781107200d40e048070141e1b020507501016083c548070034041c1401c00240140d80e2400240108400100c05220080c020048071a055507160b0850070300100309400500500e00c80e0303251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 203737122 1250 203735872 203735881
    0x106050114120708040203100e030403021f090b0f120c07020f0a03030c151107061b1b08070305091507060c03020306010210050601090f09060e1303090b0901140301090e060906 77
    0xb442d80d691014440c40d0118158940d48042454402d400000140840c1002c00070032100000101034003c40740200c524002134101581c00840c0b008070110f4032000903009800900c90102e100d8018901c01207041940d51030303e405003105502d20171058640e580e40c20000100c0f402546450700d248184140c0c200c85990410346159406030604c01503400092041e40e028000c0742d1010b840c1d500440071804c25030303802130765000301c0c0c5407200c01000c0c00c40001310f03800e184151580006106135010703440c0c52140072040541481d00c0e00c40000a4000c0301040302080001c02c16282d4a0711240c0020143c1001d8600c0a6124442443c0c00425500c100a032842098418010030005a0340060180386035501088001625150707000104c0b8079080070f070005a0390318965800001e02000a9101c401161a0010408405e80741c2c0a049040d140c1d0b510780140c00a803882c4e40510540315a6401810084014104540241c840500303109864009078000c1201b55500c207800c600500052010075032140981000d403000386007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 203738372 1250 203737122 203737147
    0x3120f030a050406060302060d0b0102060108070b07151503230d0504031b0905130203150603032703070909030315080d050915040807030519080313020d02120106050114 74
    0x401001c600070261120041814010554452805940c01130503e950760380f4403600711805010f6035005a40144109400002e10000104d1000142d80c1880c50152800e0f2454441f1030607264010820075009d55981c004126000008803500000e510502052803210260f084608003071101100000c082d4100c00701340c1000310b80c0070b42190144c90b4003c1000540d000c0b010b80300710794800c40f41c0101c0e007114944000d10803075003807440c4402d40d0b036482202120050021142c50480010055030f8650f0183d01c14011254034480140320005035a43e44468100f15445d5800003905c1c0003225800321903010340e40e504060070300d03605024568102c882c050049080602e080714091f40c591519802e03130104034010078820a80e541c0da070110043c00648812040c0c43d2a141c602e800c0e03d41d0b00c1032000b240d06218a01c00b03099207055540e00c2c9003500d0303007040b01c13242555240f54000c401122050300481c0c1c011310700b5941c0d0006a86000503101401800d0000054650400c80090a11048104844801c01e82488000d0440701d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 203739622 1250 203738372 203738377
    0x606010f090b030c07110301060e090c0102031c0506011115040303060b0306010e010f0504030b0c040608090a030206070311040306051005150405060304060c05070b0a021e0306090402102601030203120f 88
    0x41342d5000340f170f5071a401400c0c070000c40d060510410307505500b000d000040741040840300f140500d5012094070030355001d0000580c0e9034403407054260b02500545e078041c5030415159100300c0c0c4c000c4040c1880b90201200940860070300b5050240d0b20031030700c02c0e001480141941840303450042c0000c0c14070945581449800600341c2c031034500742d540c1000f891401e80381030349114805840041d507110b082c0503101e0511840a03151030300b0501400c000104400001000b156000030580045901500942400c1e12201022006020070003000d0800700d60401001000405a2007000e00c1000700c020901c803c0e504040802030b0400c903d1920b4510184284009c3c0015136890301202d400550003800082c0d090180c0074141c2c1c46004007003001d030a000c0035500f0041140311640003483c065074089103442041d12034850643c0540001e0ba441e5400c401c0300f000003001410103000116003040f00342002d550701146032030920740502a24104001d51a0030b00700400c118207007000300329074043c07286140508000a21400400e5030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 203740872 1250 203739622 203739631
    0x31a0f0f0d060f020406110607140403060509190b0a0507050408100b03070902070b100504290117010f1d0417070804050d0812060409080406140c0604050606010f090b03 74
    0x60704040028000c2152a0380582030801000320299191a503483c4054128a03104407400e07030364051440040e5507103210300703589010358180414650804d42141c0340d1000030706005104141c0c0b803203004002a003d80c10900c088646a10400e90b40b03000d0f1401d0400002a02e130f0141a80c414080140002d101032a0042450410400303285400555603220500007446c10f20664005c0f030045200044030000d1202c05c5048038851080d821003940301e00d950304148021914000c210303e240403400c4201c190144081b0000c0b050050051400b02103550340e03800700e00081002a0b05c032110b41c1000c108204062404245030300c61800300341d4114146850700d6141ea501610003400310101100001554a080200840646010303010140c11031408c40c3d040d1801c0071840d072103080504241420003000406510341401441d00309507124021174203080c50700300c0540d26140c2000700400c2890090282019141007000581d202e58020402000702e810540c0002d045560700d05002c40c2005125001400607142d03403c00c59401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 203742122 1250 203740872 203740879
    0x1030305031305010603080705061008030c19020102100f15090209030d081f15110c0d030e01120f06150504030c03020d080f030f010311060a0c0206091807031a0f0f 72
    0x410b01d107000b500400090300000d03c04040401c030042030007000641c151140c0c43c0c5101c090400c82e00d48449603640c0c0a8031614001075409080201c03041d50b04200300004561040c0103e03660300c0020000c41007030310008010b0116641c0e5070310000740107402c05110703800102008002180381c100010042915050810000c6040c0060003000c01c440401e024040704110041c2420400010345503036010303070001064542d00c07000800c070796030b15a600a07000c00c88000c4954003c018446c00b149668044d64489d00030445141030000702d46c01911102064014003880c5003280b040051801c0c204102404509070081481c010090140030500c0090302d038151200079290129a011040038a07071412640510a91002c400e503c2d07404070a03c01502e20000da80c0713043c0c911400109103c80d4110342400158051021807000040c558010040981070110003801c0c00c04010700031000c0d800c055106103103070b80f4044c0da4003400242c0d01d01d22003010440345401c01800f40011034011492019080015091042003141d2510 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 203743372 1250 203742122 203742151
    0x10e01080609090f06150109060504060f1101150303020c0a0920070809120a03020c090910090521130b0301120b15030f030d0501080f030403120509150d0f050103030503 74
    0x5062504100034241e04081504031703881031820709410b110148049010390301146036100c012880c02d014805503000d481e61039403041c4165168500403150845001004116550b8948a80c801c0d40031040c0f503040910300a40040410303145690600c04d035a610b40e80240710842c034084910304803c114800400c1100c425403c40c640712142402c09040074880d000d102c03603104440c20f90901c3d50640c01b0551710b200e54004d0302039901c00364859040c0700000c1c00486440b540358001600c0c2004104c034581c03000d1a038501410403141c8115004a00003203d92415009009505010441561118480c4841d1004d00707100c41225003135502d001106e400f007640d0000010300042c0c440000489134005c4061090013404000e080321031610507000c226480780d00c00c20174916424100300010620004c0000e4214a1a5420004503c0d1078074580716a24214074281e50b0b0001c0000801210030560f65085400c1d030709890880c07046d0354542440c0e52140031103a007802200c8069081c2401000420740010940340d1114490000c00b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 203744622 1250 203743372 203743381
    0x7030210020c04060f24120e070801020a0801080d030908190e0d0b090f0a0c0b0c510106140c0601380306040c05091e03060105010e01080609 62
    0x90601803000502c0707800c58582600011556680000141142c6211960400c003510b083c6200c42604020059100400c2083c01c0070780b21780003a9400405886540300584240c0f075111790415003a6840442c2c1c1c600003a442e24018020110140000144028981010030074881c442d56070f803400d405070b14402c0c4c1c0c40005000d20040e0540c0121090302074004004d04102e43d0400c10701e403940f0001c006072203084007441840750300c0a098030005015007909402035038007008036182040d24809944010f083c0e40060003000850407030410351030307010080001604182c0050009900340c2c0004001440c00790303807224205d4a4070000074142040d040d03042d03508900d460b0000c80864101c032503580c801e801c995203544c420b0800010701c1c28841504010103a001544000422020454680700c1000c4a248071030250010008190149050782c060550400b035410014108102040002d150080030740e00b601c0e070f180220400c14103d02d020b03c07003a0301420302400c100341280d1452000900300000280468003650040000c03a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 203745872 1250 203744622 203744627
    0x10030309150e030f061605041409060f1008060f01080114040e03130602010204090e060601020607030b0102191118090d030b0f040c09031106090105070b0601141902060f070207030210 80
    0x651182c0107012207448003410041d8540c3c444084402c44000c007064522000864407910881e0210351b612111b072007050034079404104000001404140d071000f0b400c101284551211400d20b040060356071506030f11403400c0303403d000b00c0d4610060480d04001560b030041c030400003072030394095400328143c07000540500031050191031442040300c4601044242d03240010103942c1500200261441203e0074801524200312580d9a248152002da0250700984001200300381300c0e500412204c001441180d2404544440403903111450700310541d8002c104c0c14050450f800c0800340f01e440303480050350043c0540361005c190303a1203e070201014010103840e004045c0950742e80c44049407062400031f004002e100d400c610f0103003201001c1d1104132160300303070080c42088500c2c3c50030580d80782540c103071682441c260040e6110701d041c150061160703040c130105100480e0502c10003000351001302500042400f880702e89610182c90810020005003200002c20100100198007058140840b070b4141c46240c942c01440305e05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 203747122 1250 203745872 203745887
    0x9031215090614150403050303010501120b1003060806070c0c050d14030d090c0602060402030703061d060c030a0b0307051302030403120e03070311010c1403060423010603051003030915 81
    0x201c07a4040c100b042c04590b00b440d14840303041c42c0c88100c0b5051403401034081e01081600592201a225801c02d10040006500410365544491107480d00080d9080349480004c0c3c5030000070400f040001d6580b0000c2c000008100241900140142001780510300700360b4400c0741040860245601400303140d5920b130100003900e6000c149204204040d40d82f5001c40284c120010b250009056403401c03451400055411300101d44c95000b280c018002d8160941140c5442014081100307401e060740003180002c442d48641403001c10700462004800940da8213004100209980c030303240318107100c0e820000c410002651401000c0880c0501c9100240c0c40703565a050941c0e8600a04404c04192400d0600010104d00003000421100d80b00c0c0c0c407108880342c04104020b0803100c2601800000c5860388400c900e0300721444021b107030702c1074009101044540c1c00e4040b031003203400d110000e100405c6511005000564040c010741b0f602c024420300c5880c15500d5924010411072940c800c0b9074111000340b00804030303144642031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 203748372 1250 203747122 203747129
    0x60d110609121509061006020d030513060c020d030e010209010903020d031b1b09051303140405130e0607140a050c010b0603010312080603030c0c0603090a0c081e0109031215 76
    0x43d1001c0c4002c1000c504031032841103520210742e0050000080b490041040014103079121a4024110040201c10940040030f02808040718440302e9500000092802d0154415161440d80900300282c0319610180540750420100c0c10340da4014400d1840d80d9034002004011603804850507031160403035080c29a400a000606041c6081c9415040014464030990041c250341290030700000d240e549100742812500c003a00d08801c80102c000441011030300c01d05900201d081105003481c505a515800604142c07800c014060406031200081000940c06119080c0c0c400b074181408070410407141c40c3c0c40780ca44210100007043c04000f1511003590102544070040c04103024050715569612030401400a81281c42600c0002d002000060313800d003800700684810102c00e000505800105004200c05504004c204138051700c02c040c142c0b40400d10280c41c0a0081600e0380c0508000d070509101c000070500c0022203005580e050010042c00250300680d95800c521280c580012400d01d4800440e01da02c0440c0d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 203749622 1250 203748372 203748409
    0xe04020c01021201030b06010f09060f0314181606051c02040308030f040203010e0714011d04020d0b100f1e17090c1804050709020f070c09060608060d110609 69
    0x42e183d401c2618100e091816240101c0c45500b190341d400f401101d0701e420001d03280380000c20f54082040494020000d40c0741411042c03c022030016001800070b01d6240085416030030510080c01840201541881640c26045540040080c0381d03060100c054118801c1c2c3e412445040103a1400d40c81d28152a03041d1405954408000ea580341000b12060211030b405880c207901c29480d155000c0b01406000820200300c43c0409003003440300720600c00540f07020081000b1500c003030003101840c844a03aa41d00c02801d007004000707000182c031545401880402c1d0760005900c0180410030082d40340c050341240c0c00010326a05264003503181e40112908551401084681d14504c02c00d600a00244e03220115080340390b0442034620070040d104080c001c0b0f5950101742e0700640b454001c40c10a021101582d001440074019268141c1c1c40c0601c20760b5040b114180c1544404401d41d40c604e014031180c1d42c403400058000b0000c40d0762006800301501d07001001c00740c502c0881e00c5003400245029031a21003232124220700040c2e4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 203750872 1250 203749622 203749627
    0x90a0905130b090109050a03030f021201030515010e01061b110303030a0f0f0b060322080406020604031803030512042303090301110a08180705120319020f030a0e04020c0102 76
    0x100380c0d0100c14005407011242c04401000003041060148540382c0c01d6034000005008560540e1429002440000240d01102d5000c0002060f01c01410030f0850003123100d000105a1a040358454450050041e0880c00d0445080001080241d81c02404501c14103224050391003c5c50322031404001450700c01c0c2c221034040c00007008214076419140e00200303a08030b00f117070240014a18013641c001110151414650b00c600140040b840c0e0901080840700704603000514500820101e445d4a1202e8009510410041c0c0c011002c11042641c001080540440e000e01210496030960380c0191440c043d088914045020140000d02070140b6502c6020800c00c608419071a0700245032140c9031a684a0070100e8002d40c01c1102d010000740c40c141c21502c2e00d900d40d07540d41500e0b40703403401140280882e80b6116032039407061110216540c0e035403031000d00c400c07443c5800840c2d440440610b941000c1120044020030f540000c26070b5903a000c4007200312050b1581c946042208480300200180003070040e0503800081d903202 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 203752122 1250 203750872 203750881
    0xa02070e07030209031b061e0906041e0806060f01121b020309010305010e060906060309010f0f02030103061d0d14071a1b040f06030515040c02070f090e030f090a0905 73
    0x1940180769500c0d054082e2480300e0191b105d262102401d036005c0e81e0f0442000c003d038480440c03664a0280003a500b841046151188480005481d42c0180d001500103841040700141e0411801d0402002401141d018200ea4540940002c481c4103074580d0329418407000c0c0c2103c3c50600c60903807081b1180c2c1414180d480e4601d1450500a40c0e9070046502070713011034034000001c1540d0046182e0303140710f010020302c1d241d110f503956414407119800c0940180840e640f0340034080c420150600880848d8100d031540107860f0361450900c20180d0364000c509820480030b0360140d0b41003190214b0008018441414080e803d0240c445404001e0303c0ba82c24050300c030316583d00c0c0c9030b403480840300e080794000c0c1a43c0401c4070702400c1e0031380b40000601c0360388038880707140750b1041080149a000f03410030fa0b44080d104c0e039865081070aa80200381035500b24401000181c10141044c040d801d01001900013514114030300300900700d01030050b03660300c0c442c0c0c0d01c0c0656403080200d10015603585160014028041e0a201403010341007 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 203753372 1250 203752122 203752127
    0x16060b0405090303011d010506030c090a08150420030604080901170a02040e0105060316030c050d02120a0c02010e070e091e010204060905040b010804060b01030e03042301021c050a02070e07 83
    0x1c0c068482c001c0c800d0111882c6d040b41d8060717801e0688030000c100070701c0d540303031000301c011250f00c130480e60364100c2200180094404e505100d40c0702c40d4031100700c1060f01480c0c14949902c614540c01610030b541d407103043d529041500c0005000f075116511400c0c0690b283c503000010380d0007801507980c0891610302c010802c4004c2d8400d4014200f01c0b5040c180340e13000c0b039803500c04015081c0022120090617552601d04685050b10a810028601c400c0d424810300c0c10241c02c0900082e40d009440110348200602c0601c08000c549100b0b004002443e40700030803c2c00000c40f00f80d81c0728119071003101d44804016011541403d414030549109000c2c0300c0c41c0ba01a0b4243c5000c0c01e000c0d400520502d4041140c2c41e0000502341801d002d08800c2a030705a480303d034541d0361035864200800b80101c0042c101540c80240b480364510400060005c2c100070401c08a08952a00060340d51564800b0003034110741108102c1610160302c103203043e900358082e09090b40c940751071110403894101c0507800980c90300001c1301402001038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 203754622 1250 203753372 203753377
    0x302090906010c0210050f1e090306010e0c071502210f100302010c080a09170c031002280c0203101b0207080c0f060d2c0105090316060b04050903 64
    0xa0040e5810030403503440710015240b074415520003a40000580c4c481c0d1098910a41c020800c0c60b400c00002030a050103003044e40541800c2c83d8070b2056129000400d501d092400b049041e004142140a110083ca4180c054172440d0048410081820600e00079171f141e8000940c06030340001e030502d8080304c40a4001203c0c0601c4901c1aa08822036401c40004274941750002280001a41e8042c4c41e5078460341c1080e070b202244c651001400390300300300c040040802c612217603441d04403d404d858401403d071000c64404150174003007010625080c0304e10401186000215240d29240d04407869042503044400b00c9000740d840c0c290780c200081d814011446000d20560346035000200c04541c0c00d945030f00050004400782c0c0d0301c81c082d000c0c20090794004050100980713000000c0382c000b110040e140600300544a90500c040d07a6070f40a00c882c6504510300035102d20881901506c40b100c01440c0240020308150740520b48a1080c103805180094106a98100b8070286400041040138060020019032a00d0b0900350703103d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 203755872 1250 203754622 203754637
    0xb22120c15030b030307020f011107030c0603060b1e030714070f0c05060901120506030a020904060e0f0d05041503060302030f01050105130606082e121101080f040209040816030302 79
    0xc1c1d00c40382041d560310302c00c2c031443c03d80b0000500110725140c89502002410403103030103003904000501c00c3c1214290414003101d0300451250103582003482c140381e0003030140ca007141c0003008207000500c41c1024400c000ba00a101102241100350b540751151311040b1b0701001c12003503121351050001005410000010010000507010700c84105903180c86208001307040c8031f010000d5000401c40d02100c4080c0c2c92981c842a000000107080706d160002ca503011414001c01150b055a102e591049003408465042c021607500d005a54040d00140d24810780150050045000f180c86401d0940c041e140c1460099100c41d000d1a00101183d581e80d01407004607000c0c0100f40600d40c0078100044403150040710300d0003114255501c1c0c0d22002059030340c41618070020300b05a4001c90a60982e488000d2107500f8040d400d0014142c54407442d600d0300c003a4140145c0708444100c441d410001441c04006801c01886030b0a078001e079049486003d11b450f18280040d9a00030108440001d05280e03021000300340d090b5004001c2d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 203757122 1250 203755872 203755889
    0x912030703030b10051c06091107050618060c090301200306100311090f040f06150e010203180d020a082a040b0a170a0b010b0d0e01060b22120c 63
    0xc000b040512000d140349455804c045a018007003101110321165103810003c0301320000060b000d5075960132805a030300144c80d001403a00c0004c0d90005000c42480090703881114624104206d0306640c5c2520340d00e00c0c000b00750a04280010071700440c5998207400244031841c022065000d03040040213035141c0c0e54400d0701c14510074407131a0051285580280241804801101d0856080c00d201e00140503522050740140d0f0781c0540e0360300508000d141184180000342c4004410781403485030001c0e008d400c1034580e000c0c250540d401070118100415000b501030319155401d40307810a003079105201040140405421289980c00f816480606142c001c1d2501d0340c801414030454008a2481824041299002c280301c981040c1118010310410001200d40c501c170029200880d8801e02d06901c40074115007084c1c000d160312000c0080d8000202c0d000d4020100d0800ca014000c11013180382c4008084584250480558013010400c1d0080c00840d00c80291802440b1840d05d01642440c0d0b807a0280018855001781100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 203758372 1250 203757122 203757131
    0x30c0b0c0408150108031602040b0901080a121d120a0b070203030601090504060806041b0306020403030305190209010f0f030f0f060920030103020609041d0d0207080a030e06070305091203070303 85
    0x1429a0340390180e04840d0303108040e6103001f15550101c1d815460070082a40c007e602d80e906940b0303549070196000e009003491382c060101d0285d84e282111502d054030200004022052000440c03462081e40d101100260841c2e050100100840300203051282681029020f005904200180590080021481010709a0b12003001644403c01c000441c1d28030300900c881940f04000240015031102039840e414200840c582291541c1d80e650135040c2e0b0b02c02d40040b0000790f00d4a06018800440001c2c2041000507030300117505004a8200003000c4140100c044010403603040c810400440c025404a5407040f07040406100c00c060340100036014066038822504041d19000f10001411084142d400080d0a4000d050745184d1030343d002c02c01c60740c00c000502c41d030041d9140d42c041c0c02c01080d00c0700000000c4580002c1c0c07409551096000c0d0a00041e540100c00311703006840d4040000c6e03407101c903075004054110380042d00c891160608803603600401070100d4114101d000c40c500d61003800409484d40320705c81d560038031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 203759622 1250 203758372 203758393
    0x17070906020105010f0807090e0102040807081507030b0303120a0e15060a060201090305040e04020f090a090c1509060c051507090f08010c09140310020409020403060e0d0c0b04030c0b0c0408 83
    0x105c03020900c42c0038910b8000480c00c0c0120f01540e00400002403801001604040d2504e00850800e02d13a40c0c004e00790342e0b021201e15401e9201402c40c184e40001c1034142088140041c3c004030342c03640305281d07060301d400360b030140010340c1104541e22a141e1110b07004210344c1480c104075441c0e9610b401c1130310890f104101e900c4001034014030500400d4051030f0705a550ba420a460001041580c8601400c1241c0c481c500c03401e0300420380c176600c00f06449607e0400700030404111904000320542c0d03968014418100c1c5c200b620b4601c50b81c0000c4007108441c00303451306030000c600741c1c108142007505060040b862101030310103100c2915801219402a41c0008440b942d00b15541c0c2402801c80d42100548404600d040d07004000c0b42010701da0b00d840002000d420350b400c10286500d042c040740c1c441d030801221640e01240500074085035100d482d40c00075414004080c801040e905c0580101d00d10400200b00e00d0040c0001f808041c802c4060800c59980700140c10000e091070094150250050701440565110351300d03880303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 203760872 1250 203759622 203759639
    0x1903060902070206070b0415090b010519050306061509060406111e0d0807050705101d0102070c12020604081203040312050402010807120608030310060e01020a1e031707090602010501 80
    0x42e0000c80e4003c210740d1600095503201407802a0040090303640b8510103980005c40c018a009144403c1c0c450141426158104400c00804402c08503298550940c44003050042c0d86000803801c0d08280e04071070755003403094043c2002417140324000e116030b006400440e0000308260410705403540d40c2d0200080da01c10100c0c1d0004801180c4128008103442d5001140d903c02071405500c0c02500000d851811901e48038540d10744c0d41c90000c1850340e440e01d1031350310010350107082080074405103503003a410000d624210558445542012040c0034003074407007850300d4807a02103589842c200c0300100710803010b440110425940341e6010b504120340c10307000318003120f040b01606031444c07041c1da00c1158161110071307058552400c00c58164032110fa20400c1142e0b140b402007820f407030030000785100e1484070900c0b001075810a0401841c80502c01c8055065510069030f400020b0704241001d80e0905210b0107882c003188603410200d41c02c0c5000391910030b0080c011810301240c1c603484882101914a0b6400078001641e172100c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 203762122 1250 203760872 203760877
    0xc070306050f0c090d1a04210201020c03030609220303060e010b04061d12151609120305070302010b06030406200c1f09020a06020303071701050109050f0112021903060902 75
    0x2003c40200003000f07041280e00d0071401118403a4003030700c120709501e0102d400441e40b0707660950b020f40e4042d090b074264010703e408034610383d031900c03200d80700960500345010340c51030380c90202400d40342c0b0400949c0000b425103a02c0540440c5a040d40100f18030102c3c41c0ca042c098020010b50258081c04042d00e00041064400d010850301202d105613920540b2620706c0200100201000604a0303000000d600081c070040c0b020001843e6845402e02d2100060420b008461180b41c1503001180601400ba04104540301d44010000041901400c10a41d100c0340e51400b02c0c010b101803034040781e1283c0c012040c0024803005030700481001080050b088403102c400c80c920482405007900c40801a40f10841ca91440f11003e1800c42c40094102c10204903c50640d00081480c10035400a00c01a8008000c0050481d4403503010250309600305410407481d4101800281101c02c01d00803140900b0b43c0f40300c0c1a0030b91b489007038103801c82d02800e801152600070090001e050450140ca901c40000e007007910100b101d4025208 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 203763372 1250 203762122 203762131
    0x108010b180601180302120c011206150516051c0f020a0b0c0c0f030a1107060806130504050f010606030605270121140a2a0911070204020c070306050f 66
    0x141c680d001c1d03461400454001e569504194841002d21100000607102e41c2e0f6a03806440e544000f819074004848001404120f0301c030001c81c820741c2000d40c1085000a40710041034060004e15116589000320390350030b00a60440107005000c2d1044401122403403602e911a0249807259503982c440b4401810f4080b40c5da044000809402028150003150360001403100902d504442d02064542d159120f44801d070958106841400110340c2c19a5102d00d0510244008009000582010f12a0b0304001c0c01042805c1c40040d1101c4084c0d650f02d001c101800b00800c41e09960940d280024043d00c0d884140c02000707041c8034840c550050050a20111518003e001e01e400007803a0409511941d0f0b01c0d205030350854010740c810480032030380d4490040010943d0541100703a009251001806140c0d840c0c82d05008040c2e500200c0078003440c800c0c618001009070368000030116420000c0200b441250302002c1215440751740310003540184001031000242d00c01040c500e086a00072402000784c0d40d5000e00d4941202011075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 203764622 1250 203763372 203763409
    0x33002070506130308040e0a110304030e06030403090909030905131103130309030507031a06040204050607030c02031905060f062b1104060902031006030c050412050a06020708030108010b 82
    0xa40510140c00c2c0000542110b0080004000c805540c070384684465601c95084100c948059200b013220840c3c0f076001d0029402c2801c08158a50300c0d264500038584504924220320841340040441d061601c51822b240145c294600d00300142e201502e0081c02001d00e51040c00d000e14405044000c48040900c034140e941c18440d82002c2ca0343e81d5080c80441403d8200400f102845800100403000c20320421000740a10301c64000301c000c24260040745180290000d00b030038071450040100b8882c54a485007034800a590500f054040e011580c0b000074289003500d0900101c09440081140030702200207881c1c1d0203000968915242c070740316031007408101c0082104041d600070194003400d0000401004500d02240614001c42e808a00d2a0015050b01c0d25075028180084c1c010084c4007880d10b02d4104000108a1810204454140304d00302030820f0040303204041c1550000d1300c0b03241c1446018421600250f0f40500119640e0441c0e00e0909400c4d0002e000b485100c0d80b03444482c00142c10102d0540c10f020b0b1428 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 203765872 1250 203764622 203764633
    0x40e010b0f09130f050109140a0c090203010b0702060313152405010206010608042d050f07050f150f030903030403021e030304080315030a060605030c04050103020d111801033002 78
    0x80d11101c1d13004102482c04c850a44d620302c0c2e6074011030940201416013003003000203014040c0c41c5080400580a094001d412160710400041101a9414085032801641907030001d40725610200f031402c9803600e005024105c21040c1205820781401907200f040c56038000500c200d024041d01803281d010740ea05009050141c0e209100501155000d0700900e07901600c5691501d500b0007041d0154400c0c00c4800080140306030028005004011051100245400e80303000240485498200016655111981c0060140d45003c0314490030081044c100d420142e9082c10030f50b944d0512044440e81c0c0d42c811182900140505600807948140120f281201e00090000071819a19181c844107000d52000e0110034021038601401030564405104000061b80940d40c001801858281458100f08107224024802c0b0310b8480103000507a40c0f017151a80c03c5400015060a0164160110780280011030710741c205e0a120000010410441c1c0ca010102a110b00b4501445d15507282c0940121110800780b050158102 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 203767122 1250 203765872 203765911
    0x10605090411030a1b05180f0c0c0a050111070b070f08270a0501090b060d021f03060b040e0a0b061c0b0310020d0509010b0f0904060902040209040e010b0f09 69
    0x1c00201c02d140860007404d44018000d103641d0100303500580807501010348041c8008100a1038400d41c10007410720b04000c900d4440ca02028007030040c0000400360001c600d40442e4001e81d5130303001c101e00b209003a40940204403029003400c1c1d01d1030680255504880030000f02c400a039400344540520a001221074640c8502600c401300390658001801c810452808108040010701490401c011002d041c0039030000182c2c900b0034201010b40714402406280141c0c0e44072550b40040c0c0750251078110a50741401402480000384004030007400151340b220080440100d8003160000449c10740e18054001010100800ca1003442880140d02840344c141c1560018140c00100300301c0399421024103110000d042d07400b16600c104040c1c3c12a04064011058160b540f010001082406d00c01c80d02800411901000003000c0b1400003400d01c40d0044c0014088e98a070b1004004548440e0159900c409000b0424070a404040103114000d05001c08114418082001c0c25141400d240600f80e00911008410007006201c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 203768372 1250 203767122 203767133
    0xf06030c09030314210f010e0105031207050708030a210614040c1202130f050303030906070f0318110117061509010c08070501060f0603060609091a04110a030e0106050904 75
    0x5684000d2004c03208004800b0100b410604025044000c20703031507455802c1214880c8000c9070160441e070354a8041900601041d90f00103a049036088800401c03d544039003619002d81002d9140c0c0c0300142c01c2c0300210b03502c10702d650080c00213229801c1544030315240d1990f43c1c0011080c0c500314400ea05c07004040041002560809401016100072a810040f0044d20000440d01c102da102044c0130383c83c65080d200900c034548000c071021000b0001100191b0035401d01204154072550b000e01410107015024140d02030b41c500a030403031700180c415081420700040f11400e20104034080b1040d45400a40010030704844034446e2506240509400b4201404070f01034120028100d038040ca9509061284840030140041c4003c1d008000c0f15204030004540b04d4a4a0604c10803280039401ca80c05040c20403c007801050380c1b04019104a55009202142c99600a0041c11148000424040c1c0250814080f5141170068000401030014035a50070040344101910607400c881c2680070751580b1000000100e0301146 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 203769622 1250 203768372 203768387
    0x121b0402180907030b040e011b030c110d0f2717030412080c0f19060b0d0f0b06090703110909060111190201020c100c021002011112010f06030c090303 66
    0x80924541900480750070006610100b00300e650030002511004548440d08050017010303140300300c000080c006c0d80b6900b0030002007860b00c0c069030410540e40f1080d09240600c1100c206111131005010380d0342c1802020790043ca0390701e0900000001c20070104610006a80c01c031070000e08004039000303418490b81080c80c0c60030008485c0300115820700c000d220100e408c68405555044440c414260315a07103a40c0b1000050a00c00032108881c0079400c01c1850b04100b004508102000c07e90040002580c0c942840000e82d0640c04040003078001044006200104017405201601a5400b25078101050381e03502030880c245c1d103002da100c407440030080c08030145904080b07030001d4008105060051580c1c10743c00e2180d00d4202c01481400381e052120065406558061040301c00d00d600a4880c012004188800503104060a4900034054041d4680210600e4401c0d4407600b00000801d10956985a92080309441450280a018582c103000c01d030014001c0d010f44140c0d0b20608607911903401d0380c1c1c95500c0c03da0729007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 203770872 1250 203769622 203769637
    0x10141203041505041a03010e0406090609120507020f0604080703062a05040e010603050f0103030804050c090702070e18120706020906070303021206040509210903060f0105121b0402 79
    0x40c4014030000c19034a81c04100034058607225501e49071910301e00b9032180d40754441220107100243c0c2c00c000601c451040c06185a901c01d07003200020580d0142403400d480142103030000509520150340760344c40115404001003c90306e00072144c01a407050042c0401095100750f102d45049030b0b11081c0c0800024000380c00826450311518040141c98810380c556040d0b08071440d0461000510028050018034041030f00b0720702400700c030310341089240b40403185140d43c100107000160030322005c0c0c0f000404014042000e01154003014001000604101c2c101a680342c881e801480040c202510008412802040b00100040ca0803401414032015511901d1138a0b8407080742600c0c1240c003000b0024150b104c0800801500b80310b581c0c016036980c8500482001000b01400041c0b20724282010301000e07200000ea1319030740c04810500c038200382c2400d111030002e40c4503040007540c060043d9006c203c0e0252000d01400d049030030960382071007400343e4541061f4607540c0145082a000404c0f503250b00c0301d81442c0d030140000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 203772122 1250 203770872 203770909
    0x1909050a050712051920040f06030c080d0e0d030f090e010803090a080d080c030604020702030f250312080a0204090e06090d0905090a09021909050402091014 69
    0xe045500c41070304008058008840d81c85480360f409080020810180701740484566a4403154000c56450902681e103103000c1c900f0310032008142607500d0f40c50703600904451558000412610703559180101d41242280702d030030703664050f0109400c59140103484803010008010100e04003000d40d540c1c1640c580c411607081804000c004403012460401b4140c68078040c02d5820001d41e280d1044008128404a150f001221103401080440d00707100d400c1600c0741d80020089508540301d641d100c010070300034050031380c000c2e40c988901594480050404074251000950030108101e00f410b04075202e0030000301902c40104400024000c0c460918860141960064000c82c000b41c5415600d041c008151400f1404020700307a001a0300744112588100468038101805082c01030705a894840003480c1010010946c140d42500c4034191402c6540d00140c2c1d00c02e1000141d130340305089481c0d8003080b004041c120b4080f030103110490023040032401901200411224040c100662a894050078022045090300b00c0089 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 203773372 1250 203772122 203772133
    0x3090b030c040b0c030c0705010c020d0b0c090604060c0203010b042306030a0f0506090c040e030901030504141c0e0901030b0c070c261c020d21050705180306190905 72
    0x40d1410f6070350040c0981c41d0180000c41c0c8030040100403034182485648564180120302880400580340c0c1d841d9140c9150300002c48006a0f038450341c0f1000184140c80e24242c0c02640001c0106415421040005015000b44c0003040036103903190922007110316082c800c58152044108070000300c0c02181d0103540c001c1d40a400d460b07807040d6540e20660150f61418048803503420060801c0f1301f600041014840c3c49030112403c1c0300b0340d00c1194440703840313101d18064141010b840d10001010310440191020a00d03c000d4101c0b12001b024105880b14662640002000161500c100b15007031720342041224142d0342c0000c07041855485a0001c101658407035841243d80b40020f00000a90030030100201e0340701d541e0340c6c40c0320954450f08030340c10f402c0c0304002c84007a24070311015146040169001803c1c508401c940d003003801c18441400c640340d0049400101802035103040104010443e0b40c00400ba0050322420621542c81d0304600c404c06455240031500103159540d95042c44a00038150b8000102c0c081c0210183c41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 203774622 1250 203773372 203773379
    0x1a0f1812040807061e020a0215220315050c0a030e0a05060a05070f0201090c09050a0f0c0807112b0504090c0e04060e07020a0318030c08010b030705030a0807030f110604030c061803090b030c04 84
    0x114280580c000c0d07407050740741e4010400c284490b33003e00c242d0300782d0065420421880c10100d5006207020700d11742c1c04105560385d4032282d043d413820400c40d10031540041c1150564903090710391802500f0200d0f43e500024602c650000651070050150028041d400010100780c94108180c06c0000c00006040302d41440e2947c4070011101080e1042c13a001190f1590f40034950700d03002501610030041c80c0d2081099170b0200140a41c480c3d0031601c3e220481c0004581901800c00400c0b00b1601c9000f183c2140c01800d20341103903050801c0d003128868100c8902940c1c2881190340d03448e0300681c0c0c101e0450b9000c002d83c2140c8a180002403042c2c03908c4810b12140342520343c1d101d45a031100104048603803c00c8450f613560382a40030013843e0400690300240740890080506c100309540d00d00c0399018a04006052100031480103100e14050b0003850540401001264041e250034200104050340030a4203030780d081d14194540c01c004469441e04102141c054030360f070701854034241440c00a940000c011419a00c000d00010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 203775872 1250 203774622 203774647
    0xb1008071404170616180504090212070602070e07050c0d0f03020f0403051614030304150207030210021501080102090d110402070c0b071a0f1812040807061e020a0215 73
    0xf1031202c40010041080d841c0444082da442800800100207000c00c551542c12020f10f90030b01c01c000d03600d05072030202d40700032a8400b00d250b850049a2002e034500600c60003042c1d00d42d000032585c08652801c0204901138550105c2034072580300780c0000c180913801180306542d0003401070520813080300e01d03403400601d004135030f100e03644864002d904100e441d5000300e440540c1444890320340c0f03400707170100e4140c141c10000c121300020703500e00c50361040007170511080d0813800c40c1600900c00031008503009400d042c85030440b0b1074000c4d120151240b003c96580071010000c95030b15014400c0d100300030805000450701e05816220000c184002507452640a030b000c2002e0000942d014024100910507a0807907500c50305e0358589141284000b55418020394a44400c0294080303401840e19004104080c1080381641c41c40c2e215410030042c114101551700000a0020b2201400642c08044441c03945d01e400c0c15042120440300480ea072002d80e00011783c0b103061346902501e0400319600030500800f241034075001111421 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 203776978 1106 203775872 203775899
    0x50a080307121110060e0f070e06090301020f0c0307140d0905061612050a0306050406080601061413030c060809060402090a05090a02060310090b1008071404 69
    0xb20515010700f80142500f9405000d81e20840351032116803002d40f19503c01c920914820b02c00050780505060034940c000e410035a56682038200d00020869a60016484540c0c90756081084000340d001d140000c11403011304401070354030340707101d0b041c8010400d9805a560301c8039005103000d9051980d0003590700003601c0c2c049400540720301341c185c0564010400c41e00c00810032440b27081100c0c821074010024100500d40c650f400c0c41015240d209100642c0e00e0703403150b10340360350004006100290145001690040c0401001410220145c501c028448000d61040c1c9030b0008a000502007190301920096200c030030300c2c3c014039160415a01040c00440e0050068146036036440224000a6040c0016040140c000f8541d90700c2c0d041c01046000e0f03103070092244403501890001141501c1c24a00000608807150780c03124091a65241002e0b0350705149480c80c403e41c080c01300700c0070403420b014246 = true := by decide +kernel

theorem cover : BRFrame.Cov 203597122 203776978 := by
  have h0 := BRFrame.cov_init 203597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 203597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 203597122 ≤ n) (h2 : n < 203776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
