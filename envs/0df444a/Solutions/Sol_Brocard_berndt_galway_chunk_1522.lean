-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1522
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:23:37.985966+00:00
-- url     : https://prove2.me/submissions/8d3dc69c-8a23-401e-814a-0992008364b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 273561151 ≤ n < 273741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 273562401 1250 273561151 273561181
    0x20604150507031d01092d060c05150c0306190801020313050d110309060a180b0a090e070509090403030b0d23010b18181b040b01031b05130e 62
    0x41e00490355104d0b40d50a0626150550b0381100d6060f034944034800d141a05501034001e0210380c4003c031440425913401449445110038004207201da90b1401205e0b001e003003e60403c81000600020301100d1006c0010101410048a400102c01e68200840410707284901d400340303086401003d0f01e940000141b103160f040c02c000c4d500f1170500480640314a402c502000f03540c01c400442074038405410a22020301c0ca89407000150090f8416070800d08076100d107840c070742e40c1c44222a03000078900c60f4010842c0c1300c801343e22a0040c80948241c3d010a402d03824042c0016105001d400a058840c030854000201010f100e83c1020000480107800304941d2950751a201003418050210501c3c070b58411840024082c0050042d080c0280007d4901410720701d000b445e482c3d92281c014410703400382983c0884000540c0c800c0103102400c034407000c1031620b40714800f01040140e4004484460400d414010020a00300807180403100c541e1a504000780c1d80c461103841883e520324261f229250751706201041220f02e02c550010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 273563651 1250 273562401 273562403
    0x40f080c0615100503090a0312020c071503060e09120d020f0307172406070f1202060901050c270102100f0504050c060418050712060303021509030a120504020604150507 74
    0x210700c802401d0800884c0d4901084800000d10390081d0143c00c0420302851007000f044440700005031070010b01da0f00e824948446544602491042d209001412a615200710f030090030501e40c01da18541061b1174220b42d50752010100e00c0c0c200c1c000242010b445c5649a04031141d0039958642a0b4581c03420b940f01400c481c3c407040264984200744000100c20790b642100c6541644601014541c029402c81c00b40f0416801012045481d6640f4100103c00700312103e041d00d58810b410b03070003025a490720040d441d085d43c4000d0004008290700341b06414001c940314203032051040350f0b2207800400b0f015a00040740340801002a000c90341c0d1404413924000809500100c2c4103c0c011001c990751605a001808040e119503c0341403400e08800c1c0100d00540015009103800c00f01038a0030201a40c030288090303041f15502d51048000da4004807400ba280c01d804107846a110301070002560921005407400703001d0b05440c6d524408081e50350000034045590345000e95000c0c1c96600802a0b612035001c01c0a840c41d444140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 273564901 1250 273563651 273563659
    0x112d040b040e1042031a01240c030302070f082106060406020d0c0c0e0a02030414060f011202150f130b070807030c0602120a06060f1106040f080c0615 66
    0x303440e10804d984500c4c0325400c041640500e0800c603c4149083d45081400303c626002441c20800004220300050240100061485d449415490708401268001c0c8144000e032042003c40c03031f019000380d00543c1c0220300c0b07030305400c025a548000349001030066a04540042c000880810010f02161035182405035030b031401d407514020380c5c41d00700401030349000340e11031000142c1c02003200c200103a11039920301101b18400d40f0704458007601d40d10900709200c412034004098070b901104000c144413a8044a09500024801604807801c03c9114400d402c001401444411195043c054007151100100d0202584040b011036171250310700641c00c1c0540c0c0c01070700020302d80c0512075800300b10420130108a40d00d20ba40051040e251500994080d5410002a5815078416a0a0080c0ca814100c8010824454410700c0783c001805400c0c001d029049100030980350313040008404000001650025030203412a0700118014404d0003140b6082013544078065801d4824001d0360b00780410082080110a03820500f22 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 273566151 1250 273564901 273564911
    0x30a0f14010b0102150a1e0504050a020f0627030f060906040b010e07050d052e080d2a050c031005221a07020c04020c0604112d040b040e10 61
    0x40c01241e442090110140d4013169801c0401c500591b190712900810301c80c002012a51000d41c4100d10403031f030301190280c8481c0c202490400c00c40c50b0000c10600010b07007c444507070824a5a0120f80c4048004044d22038035103451908040031a40d041218802c0c181102049a90718540302ca0110384074001928110340c610074900c004519006811580f6120300c01a40d15141825074202e2840302a10001d0034840c10003c0c000213020600040c0120200f4001aaa4042d804285884c0c88036203040d9a0300c0038041000840300d8043d10303c0c06481e400300001c0c01034074048101049641803207410620018410303035040c82000c0c10343c20f0708407131500b185103d030381e0190602d081c11050703502c2c000f02c0d00344146006144c038213030320503190012003040c6002c0e030019820310407141c04070103250200f0100c0c0d221048a4607558802c03010032040081007007000000c02000d0381c5220251020300c2d4407421034100a41100044181d0203a40011521164401c5041c0380004006118080b24010340603100c2c8a1512950300303c41c240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 273567401 1250 273566151 273566171
    0x40f0f0302030d080105060a0c030905210f011b0e03070902030f01030c0801020a0903030f18082802102003070c0602061e071202040306020406030203011d010e06010e030a0f1401 78
    0x40c91038141207803405400c00e481c2c030a10048c100d0b9001051201102402100400440c81e5265000f400e841940381ca6422401c0041c0000ca03507180280705084117a0b40d03070400300400001c0a0307100e815001e035503160601200b181d501800083c200340d000c1c0c2118003058404010044a00d100310803290480f405681d00c01c0300c058480007004d00740d04c42c0005d44004030360125001c1000910031981d034034400c01d462030031a003918444a032190361180035600055803544100301c015807840307480c0940c2c00b584d0015103107072001a201e64045144480c0001f01c2c14144030700500d42d01c03048400501e102c1500d1404600383d0b0783d184001d182000310700b1524018000144140310004100345c1d841c1c030420b41c0c0764003c50084102c56445440450350202c1c043c1e940310b80c041c1c00340800000070301c550020703101030314060720050b0b201e41c1000c14070b151101c07000051400140c8250010080c800b218201940c000c0020721381a000002c01c1c1007c00e18020240c1c8004201240180031581800100401a40c0600008000340040001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 273568651 1250 273567401 273567407
    0xf0a0209010b0a0c0809010e03061602010e031e031009061e0b120f0a0e030408070e0718050105130305030d06060e0f010813020301090219060306090e0606040908040f0f0302030d 78
    0x203410303c40004a00025100404103c0c80c1d0041c1c00300c410145040421010080702090514005841c40c64100042550030f0780801e40a0090760440285480114146440804d650b8044903c82c04501c001080c008081401c52032490009006003040d0141807141543e191098000081100d001801c050540c89001c1400c42250301128180440000c3c9040d04e0f448a255001f00701d140601a00160390340c5200b42e21005c2818000340005086020240c58003520705054403980c20350040c000002c2045c1014080462064030004d0400e440007071030010344408424980c100c90214507040540984400716900c849907016400c51415a60140d480003500003260301406490544056030901041e0960005207907010a096403044c000d0005002081200d49500460741e0100c00c0d600f41c1960750f2203000c00307025640c4c16002d0b1100400203580100414240f07028020344a000c003404444c8580d8840160f46d0030700a20800b030b1405443c030b901c080350355141d507000c0ca5807450b1403510040307000b4000c20440080441c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 273569901 1250 273568651 273568657
    0xa02030c0c0d11040506011209051c0c030c0b06190314100e0c0913170711010c0b0103030f180b070501060e060f1201060906030b061c0c06200f0a0209010b 68
    0x29003e807040b02504040070400c070103440002d110904000c507080918a0a543d42c0c0901c03603040d8001c00240800002e500b180000c1c0711200903108090000900d66000000e500c80588500b098014130290342035203c080029000c1c01d140c02e005840000c0d1290040188401c0310031041d941c0b055401107801030220305100001b07441207030f442074039640c000001803081c500b444e414095200d601020300c01015003481d919810001e40c610003080040e000800c414080203000060058480c8090034a05c10b0003280c0e60312071440c0d240c1400001c0401010b41800b0200c130b401042d21060849060080140c0c168461203039110a401040040d181036082c910300051140703c107400ca5000d101d001d030410550410a80500617543c3e030348600000340350343e500d078005091848e901c200340103503104492422650900f00c040002c40034010684100c1450480d030b0302000074855072002c40840300a0b09100704e11201103001291041d52842d000000d82c0985082d60728030090110b140e02559108640b071800507601e0b8030f0104d540380 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 273571151 1250 273569901 273569903
    0xf21030b0418150c0311042702130b07290615030903040504020f0705100603030806031c080a02040f03080c240403050d0b1e040605180c1605030a02030c0c0d 69
    0x1201c0b2800c103100110f01d40c02c0000404490304022030506d2440700c1e0f0041e0f60f4000d07403000b02181a416105042c5800f210980202482c0c3c405066007010840d010700908200789108001d0a010009a28000c000ea40c40340680600c01400e54520140242038000645200482d2054401e2800d80015546079070b481042e20701a42e1018002c500f040d0400090000a5101d0010712a22070003c3c4001c800040b002c202081c09080110720102d840740c80d42c40e029001c0310018189038425000076800e003902d604481802081040c29191240b0241c4903031280030024442c0c0d4200d6008010752400110030301010310b0080940c0c2501d64220780c141d079804a008510101c18102c070a0441e1021000704d40800c0c41040a00b006201c0c286000480440c101c0c0011081c04000c00780c41c451a0040b690032040e49464452140100800d642459a202c031340000742190300d8009240041d0684003107980190076444042e4644c0c6541d000c82180c0c0e6500803880c0c081d40c1e94002c801c0c00804da12031942d50a0703041c20001505c812030303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 273572401 1250 273571151 273571163
    0x1050f0a020a1b02030a0c06031a0105160605150301090305030603100501030c1a040f1518050609040e0f07260a0807140c03030a1701210f21030b0418 66
    0x39528000401c210383c48a9542a6414460780920320085640c8042c0d0000030003c80d18001203103c040302080618003802c01089050086c2804201d0181181c00401d0507603030b42c403080000b87e42d1303120f50030100528031004090f900356103001c488504241e040002140240401c40840e40020040c3c1c103150103131142408024501c000b107803400c10005040001004249100880d018240350b20303045c1d80600d94600e82c0c40104081c51030300c100268140c00c5001003507000700c0c201e0054101d50400001c00c21620403003103010300559498030380400581c0c2c10300010742c0341c404440641d000244d0b40c40c0c4400c00c1c040400c07950b00300ea02c010040700f01042c40010b41c404085034040105030805007140c44000121b0013200c10b400e600d02526907803540720340c1c1c140010402c125403034403100c0c40214400c4c0c52560140050300144000d0f400c408480105881c00224103040590192004503036590601c0c00d6840e01d102612003c101c1c01503141e41543d1903401d6009501c125500340d904000c411030b0074450401c8102c1d40c82c030280031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 273573651 1250 273572401 273572417
    0x1f0609092f03090f0d091401030603031d0f031203071101023a09030f02010f020405031213080601060c0b070806130209010c020316031b03110603060a030602070501050f0a020a 77
    0x20703101403801079603100ca2400306640401c80151046030909a150510380c00248101c803080c80a504101850b08010031b007032030204040350440e5009054070414483c0c84081e049a0480082e1581c0c8001c60002610350180030ba0303218000c500e108060b16042a240400411640d86802c00002414400d0b215200d41e08150345a00448030900403006000140700043c0520030302d800c0300d810300e40f42d00a48040314070035610f020b020540f400d0001e0840c2c0316a10941e11060040100300480d07540041d080304001030704541e4540d500c00d088420b94000c0b103d035001d450980145000098a1038108504800050007007000c40320a43d02d00404031800036048820990010340e094003141c82a08550140c410804181070508079080c054000901e800780c212960481143c451009001b08005040d1075403448036031074090b05006042d03a0f00da40324503035017103400b9000310070101c00100c481d42c0d00d008650003150008421940d401050070614040d25044030103800b03d01050000c03511512140c404c0380d5203411319a03141c02e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 273574901 1250 273573651 273573731
    0x150302062d181908060f0610091a0c16060c0314040803070f020a080304030b04060b09060108160512041202010e030f0d05041104050f090706081b031f060909 69
    0x4120684040e650500b220f44000c0400c40100030080d8600985c1900e5408100d0710340242005900c95011040000b00194250204146034001484004030f11151180350788601c175114010b0701d8001d440d500d640d10034000e0040064065041944211400c1c0a9a9070841c40750620310180114816440b40b04800d520410041c80410704055445103034900c018807205059a03033b10880742c80d50300306400980700c1e101c0e02c01c20701c402c000b21343c071903180f20040c19515852289030100001e04030210040941c0c10b101c16484c840688036118108403280666120b08400707084c2840c0c24040b005804464050001d0340c6007240a4001040003c00c2d40d01c420b081500d25454441607202c0380014110182c0308649440c01d0070401051607589018152064140c140d0381701da10b10701011410b140c004150b02c00000d00010a05012080d90964401e03260800440000703543ca440d21012003204034412003105482c5e0351000b03400700f40035500043c1002280c034010828018500b88403c030580141e48208115000c1e0340e4002c01700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 273576151 1250 273574901 273574909
    0x1050d030914030705040e1509060c040308130e0705070203011a030712031103070b160c0b2d0f011805011203030905030d0204080304090c03140604150302062d18 71
    0x51100c03020f015035000030783d100702050994840e0744949106030004450241c0789114100001c0d030142001c001000305040c02c2e511401c2920942c0400b03807042900207649146004011b182100600011b002d103030861421030002032a80d0403d0f10308034801e50900301003100c100f580050120142400501030042c0f10b24005600c0c01c0345d001c0700d004805010300700451200c0b100d824006007200d64010b44000c2003a01d0302c0c0003440301c4200700e200004e050100341204440442e0001c40417903403101e2201114078101ca0728101084000711a09009900005104200850900c03050b40039812904000880c1d420242400c00c86815903409003e494220360515800300e0209109422407034500d8040c04c10b0300d180422610700d01040c3e074401e401c03101055200040c1042100e20750300ca400030340c1446142c20400601b00b101c40782c8a03004040c2600d4429520b608010000c030403007601c00401142e0007061965a00718450180c101303005010309002c000c0c0b00c107000c2c2802d00d403e144111001c3c859429100450941420700f00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 273577401 1250 273576151 273576179
    0x703020c01050a14030a02030a0608070e0a02070f14010e01230c0f040e0907050f091302040b150706090c15170a021312050c040e0c09060409020d03110601050d0309 72
    0x1100030049400520543c44d04158000c600a00030b8800141e82c0303241c2020032109894980d07000134402d038810001040341d400724104954201c150103101590740c3c842414061103160f60070300041c09055000c99807a0000b0f90540c0003040c40d00c2482c0081c44904900441281c417440307418284c0569080d01c10001d14140c1300c98000b0200107800445081c00e107510f406600f80ca41a0171520503144c1d0703010540600c054609040900c1c40da0030101d688032844d1504800c040310542540c8802402181c442950b0311241d607680c8840b45443c10b840c5200341d01e950740b07414000060200c100e026580c4e400c10490105142501c10040903520030583c03500742540f107a800c0040c8a458004000d104c0a0740d09104024001d06040308440003403a01d103072424134101690600700e0500d03040c400170b144071758505081400074140104d40180070b8101203814200303a81d2040e0200d006064040002980b04501580070010982c2000003141c0d0700710241c0442b0310980c1c0306c0b014405440b13500d007406404036201100802044e1142100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 273578651 1250 273577401 273577417
    0x60e0c1c0e070b13150909050a0515041a0910260a02010c03170c0a1806140d090206071220190213050106120f0207021c2108070e01050703020c0105 65
    0x141100340e943d2601c1750884030416000c0b050000b120b21000300620701840c050b03a500885400010801401c1100410540d07142495509000d2515044150710000842c03140560300c0002070f00318806c61500340d454007140300d000d0064400301e940c107503003410100b0051030003a2000071041d0014605d50105400544080001c00780072801c0041050212a180c0b8142c141d042c092080e0381c0c0701d6034550229100203002c0480764040741e8820f0303001d00b000300155070f84002c8141070203140804640d6100012210b02d0098480c814010f504680e0000705034040144400711060340c010300e41c0c4d42c0c01400c104800240c1c60121021420340760f80e449001a42040761450b80b414070b03464401800204c1c52000744100704161542640500c1c04a0f03251803034088142c1c80d40c06800b00103810b603a0704501d00390180d070001e10340300070060b040094502d940804804009076800c0a021510040307a4401d011010040c00409400d0100d48000000788000851555940903405a90501c0d600d60094108180318000441e643d03000608 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 273579901 1250 273578651 273578677
    0x603050c0c031612080403020607080c09040905070603060803040f150e09070e0a060c0506010311060714030903070504500f0c030408030c03070201060e0c1c0e070b 72
    0x15001d0107060030001007545405108008181903520304094500c544245003407400d01c88141c0804c0f0000360301240e5690b11184c0c80c249484251248540d03001140690361109810501d03200c0c80c1403d202c0002039002c101c60081d82c0501030300340c681c00034646034040e920804111200c9030200340011200d0007000d446018491910000140d00040018035001099910303602280440c1a00d6003541040314a1038050405420180100281581e0b003e982e400d0503c8040c01c003021030444803981d951504c044270fa0070368100e6140c038054608418840d0312907103d0b0000c14802e00c2260800178546c1024001d900585d0940300364030003080e809006125070b1181c81c0ca0103c000f60002621401c0240e24488000d41404c803003801c02840f4a05210001c201401c06804940c8114042c420400040c1b4064201d036800003c40c2c01c0c03e52242c558003810390141c40d10740c01021280e80e40100300b00c0180c071600e010f004160303805a10801c1c9a03e220150034101c813460060300c041c5401100b8240012004e5a005003003401d0124 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 273581151 1250 273579901 273579907
    0x3090d030c051f0b2b021e0a0b0c060a0b0609010c020f04020418051308040302120a05120307030b19090207080909010303171510080a0e1e1011040603050c 68
    0x207003031074454403940041003041076941c440404003030505c2c007422204800c01020150707150a58a00d900d0b100c2040603c000c1c401c0c0d80d1500e4500b0941c5911040c502d01100103041c0c0201c00741c8802035881d25800048140000d44a14000230340702120720b0140740101000906124980030082c00112100c1c0c01c29281079030090a00098030440d42c44a00c010001030001e42034801800740c005900314192200a003206940364460301d040c1c00480c2d200000c0302d045917412110700c1001e045402065042c5000403a01400d83d00444206851104500f80194818003a5590401440f0f02c14010411301404151000300c06903040d103000d0060040c0341c0e00901900d8081e09415007489035500c00503400802c241c00c00c60000311240d840d1141d030700d094511543c001c200c01c03482c03402440c0c99101085c80450464250030800c06290007090080c13040b80c2c050810441500240d0342c41140f10380d40c92510100603841d150142c031690030007541c11000b40c0b00d02c030b1100400d1410140741a01d072000071070250030081d101c00031103d410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 273582401 1250 273581151 273581173
    0x112060b0d0f201e03060901090b01140f03070e090f0106030506010903050a1b0b0f09060319090507080f0708030f030702030f12010609120f150b0315010509070203090d030c05 77
    0x3d8280700c1d464010f1040301c0d40ea1011500b8480f50105444103682000407801e20502005984540806041d1140c03440b0028101e8820b03001208c1000b40c480140c22401c40000381c810710800c0e4440110b1107041680c0329005440099402d07c2030840f0308481c50003200089000500c01d0705c0c803a410258001c601450881e4040e80c43c2d840707150508140ca03c00721042c1c8a0142040880708001004500505000c2c040904009400c1c0200680e841a06010fa104050000009007080864000030140c3e00916404212203036851800c1591085036010348409031007815011464818000341040683ea02080594101104c1409203d0150030203010102580400d01010070201c0042c1c0c060f104c50041c5000d00012549002c80140050b10540c004045404d80c00c4509404100d001015009596000b01440b450290030404107006051640e41b16902d401441070002015980d00d0040d416101d088565440c151038520082e66a03214940c40309811481c0003032480d001c80d00444000c070205000c0c0c41994022010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 273583651 1250 273582401 273582431
    0x120a021021050f010602010b010516061805030c01061a0a14040314071e0e040803041502030703090314030106020a150f0c050408010c0c0507090e03090a0e04020112060b0d0f 76
    0x48001021010b607514108018101d03d400d415004040c2400200300a01e46000001e0162268001402c921a03a000304441044020f5010000010076080d6507108400303185011503ca51152401d0034803582000c40100c2e03102e58214484c40b01521011086150880d008819100300070110ba800c0c801c544280030010114031270a98404020b008400a0208503081003c041d80c1c2003180200c03010840880401442040341c520829600140c1141419840742d466141010440d400d44003242c0c0491300100c140501560075402c205c614910a803034007054072426082030b020500091080900580c030070300c1d01c030340801d0308510183c90280c9044008510a504455140c0c01d44032921940c00000d400007804000070703407081c41054414006403402c004800e003151a45a6150b940e401000803055840c0b1285014010800407100301460140041403035a580e5a040d903800c950844050b8041140443c8075803080c2e069224070b40c01d0312180340b0320b54184031504400400030501c031007120049959507080c564980c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 273584901 1250 273583651 273583697
    0x9050f030c130623010f050d02090a030605070f05030f15011103030103050a0c0504151a07060e030a0806090c03010303030903050409090f0311010204050108042603010f03020f120a0210 81
    0x15442c40c01180c8185840088001620000b4540d01c03a075000c0b000905040e07903c1090403030200305514040351982d41052201c0000c0c0310311918580e012344d80507000000c01400c0d03042540720f041c690f1101454034401c2801620380f4402210308500186080c030019a0310084001c0e2000b100d2410314207040341c4a000d0350b91506c0c584c400c0e00705494540c4a00b02d80001c10000c5045040a01400c0d03e05206002400b2072016920b00d290103509514040900340c4144401c2d0042507408181d0804801d118424410f03008071348039400401c842e0700251181000582504050b10030030300500c11a0300e0385207181c0c60351b00c0440c010042840c08600b0440204800078800605004070707180103015160701c00200d6540d19000c0c1502e007084942e51f820307034014041040181e0700094415401a0000407403483c2d000740c81210405c0c4903104012082040c8040004187c2046614103030041d40c0c82500c415051100040c2000b81da1000028004560f034407100046006007400e9403221080c000c24180041203040ca150008000e030303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 273586151 1250 273584901 273584929
    0x1009050102040e010b0304060b040e0c0405091908031f0b0f07080409110307020f2d030c031c0b04091709130203011203030501050f010917030408061302011205060109050f030c 77
    0x8400801400140142485041c6c507150042b04d0400606c00074035007068072860350440d207502c40c664410005d40021824420150540181e0410940b10312043c03504080c2a0015940d40c04203822610a0064841c0810400b00641c2c0340600e8407403c0243d00041c41500b680100300803100b82c08203100028209015000b80794018820040480d102d1400ca40020700d8080c00d481c03020381e0f82d4440c80715246030920984c103000b4101008030365080c041c40c18000c06499071042850300407031444005420014103046400c58091002c490509210041d101800c1100342c2c1e48801c030141c01e918440c940058849580c0c40100f0140001912201c110280c4450043c04c0343c10907800303940b81c4516071901d10308141e49403280d80e02418040300d49902d1f2908003000200214441e0207030704003d8649020684c0c47d00c004100782c5008229442c1100ca0b640b620101c11704d100b0103041e8049011409600003c0f01c00d176264021284200300c10b035208070156140c5420010309039031615440707415004100415266844800b450300e581 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 273587401 1250 273586151 273586169
    0x303010e1513050a0c0c080315010c0b090c0108010609270b0a180f06030f0206070323090405010905090c0f01030e01060e060f030312060405100e07120c020a051009050102040e01 78
    0x149085008907040e28086017400e0200300301490303130380002003c40741500d4109030310b5201c5414002e0704000507034189481541c050a40817140d010481110000155505804406c2c1d03601002641d03920001c0d0f98000040c010308980c100d0035849016403c0d0b440c8000f503400c039240c0384082480310701c21003c91011032a980081c0d00b00c510070140c5071450b410740c1c024500c0e501904801000715a01c0d40c0ca4020f030752940314070300900c18030001400383d0a0500c02c02480310b0b20019a40141e5500425044524243d40a0710600d40581e04010000401e22030750722425200b10040400b403d9142c018004005800d40500042814150355400141740300340244640800742c000f5a045000605121081141455003200d009201b03510400506142401da0b8000940100098501003115114104103006000e11500507a640c010301200f0040c20399406490010704041c0c115080040b4420800b080307131654501240540785a000130000c034800c0c40241c0c4a0409140508001420300d6150a05401c40c0402a4082902 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 273588651 1250 273587401 273587411
    0x907020705013906021c0b040b0406063c050c1204060903030311070f0b180601050d0b1801060f030308010e01031a04030c0b0a090b060f030303010e1513 67
    0x1196000b000042ca0f200401a0f450948500002986855030240c6420f424142c90141c16204004441e0151210070f00c107101e0043c102c0c034201c1c419000601d1071000300381c411400e040c01c051003410310748594070940d01c203036468000f4050030300c104902c65118030500c1c2040101103807001c0e0500da018007102c149111190380e441d5452034243d000c81e1030054210b448140b0711004100410030560454800e4086a0380f41c1004198054002d48010351130113008009042c83d40c400c428981003100c40c101161040320682d034081c2c2c4003c808440d0310f0351108240134407608080060000340204d041011200e80c0300310342d41942c10074114408012820b64009078054100c801040e6801d200300740e0008951405065a1b210f04000ca41c51500c2d80c0485005102e405504150100042014940700313550000d201b540207008180c980c1800c44a00004284000c4261082107102d00420080d01e840c41c00d440d1481c6008008501b03503400d02c080c60003c103001070300141413181ca443d001a003c0c0c50341c0000c1941c1803115000025 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 273589901 1250 273588651 273588659
    0xe100207060e04140708100b040605120a0c0503150a03060614011d0f060a0201020705070609170114040b100312080a0506030a0203100e10020403060e07050102060f160c0209070207 79
    0x100e04019280d500ca2030030401c0e0444540e0148013034035480001d91918204681300c5101011801525401c801000350002901240303264001d80100280c504500045150340c0c0c44500d4602119001c00c581c81c0080c000f040400e0149000c0c42d040c080c104402003001000541d40c1e0360f100c1c00c840c102c1c1c1c000c1c01816003551141a00e03682046001484040c902d068507848803c1170001401e60129560040c490320012840c481464400d5041c0e5108540c4282210001d43e118003001d080035a00e482160072800081400c81c0c64080d060003410700c1e41901075031820250710307140ea0349840c00c04010080c015083d104280040031807650241d00348050620344500c0b440cce00713088039510140d07403000742098020350040c0b0844005803400600102c21090600000138a944042412070a114aa0318100740c190700114000c020311400d80d01019006010300708481c0c502d507a80f801641c131101d0455003d4000c0b18003600280510140c420504210f283c076140005208845600103510604190f55010050f807000d10280 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 273591151 1250 273589901 273589907
    0x4060b0a0503150103020f01080403020d3e0d170f0a110403061e0504050d0f020c040204093201030f0609080a0503161e2307080a17010e04020609010e10020706 70
    0x8522107e0a180c1200c0d01d26043d2406903841c0080041801007103050f14000c043c20031094507000381540400141000c080c1c0303c2c001c0700c0d1400401c9010049500446004801c440d014408480b41c03c10baa562000d05e82e5a6002c500c80b042200030204015142c44005241da0040a20020400b552142d0800101c0e143d00c000d038071643c206441182c0c52030078980018400442c40006211440901d1490030504010762050100d0070701440307481464115001140200325000a9000080400001031450021540310b80070021365500107204400402e80c0390005001007182c802c95809000d0064070041a00c0080e580c440c2481d82c451409100001c00120074400440101300c00c20030b902086141880b21010074005403412500c540340340c0c000b403041d0018a446224203d2058000f507403030150066444910a040a40c401d920080305000043c8200c04c0f1594188015a10103040c0c83c1c81c982c100704160307201d60a01000da404000ca042c14440784001e66145940d8141c8882003030851580a004031a1034080c0203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 273592401 1250 273591151 273591169
    0x605010b07030e0a05130b0427060e0c010509010c05030c07032004060b18040b06041e0807030309060c0206120a0f11030402090a150312090e07021504060b0a050315010302 75
    0xf52003241480001c1015903a440f221000c1000000c2c4009000360940d40064002d0040c004041d1040a0703054041e802d400340d4640c500702c1d00313015005c00c0c0405100b91a4054458600044090200f20140140421940700b040b80500d0341c1c0c4101c044902d81301c4d4112180f85080850b906c101d40a40700c40411218084500407400700b0840c0a4805006050404002c8400390094500c828003950340702c000a540d5580e10b070042240e0080c05402240e81e65214003002c0d0b140000c18080a172804002c000004014100240203402c036505540c446000a05040b4200c82d50034207140241d80c09030050103401c000001080c000d0340101003500c000606262412101000d41c0c030089010504d4000c18130401001d6161a8000d550080042e0800514600110352540c10410583c0020b00300980c4000040c0c265a040311485080e120ba1f034404410720741d00e00b0303401c80c2e542440a40d2403803059103d401080009009812245c0000c0009003005100c60319000860b2403d420040740341902084100100154108a010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 273593651 1250 273592401 273592427
    0xc0c051c0207030818040b030a05070302091506120a0b09040b06090c0c06131101020a150c0504170d030614030d110705130609060506030c03010e0c120403020f1005090d0c06090605010b0703 83
    0x20740109d0200361142e039200c40c04d0b80b05c00307405451850f00180f11002c641039400c02c0d0300401043d068944860120310040e52030f04641c2c8813555403424648c510f19141c2414054030403640070f400040380303030790350024003d00b410301400501c401c0506104901d00c050041c4a094801c900c1c0c00010300f40c18840f0308100314010080d605e40c60564012041e06030200b6034103a4010342c0190000c50204911017900c10444451140b43d0044070185000514200316410101b194941150700d517a0034000580c40e06a0039012305e213110440c3c2d41c0352340302c0d0380d40035680c0340035408071400d000403d400e8030001503507030010402400400300c450a14a82e07030b040c24800c400c80d9200307080c0504030079180e00d0f01310300c1c0042503c0c0080c0b00c180150300c50300280c400000d5400f5402d104070f0f0710841c09050050b505041a19002e0350b1140c80d540001640c1c000d15180d998407856520a1603c00c8454100501110004120650320303490b81d20701c140e890035150940c06c008a40c2c50b025103802810240d5410f59074100e42d0500811002e02024 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 273594901 1250 273593651 273593653
    0x30717040f03030c080d05010b0301090507050301120201030b0f130e01050901060605070b0901020d0f0501240e010f050403080c070810020901021c031d100c0c051c0207030818040b03 80
    0x24090850440074000960b5414207203140012024100040540a000b606500d500c2c00c090002c203017814004c0140d4100d80006009100c1c3e1f03158280c0c103640d0340c0024003030003030a010781d41000c00c003542c882e420059a81c01c02400c1400352402600105145a400e0344484045649400c20103098170000d2040d2917020b40810001c100c0642800706c014124420100090410b0486c03801240f6000c100f03504403485055000300c100170922000e041c980145c00c0034428003207540d151031340d00b690400f83c00301242c1d243c3c9066501c44e1010070305003005441d6200168032640c00c000007800701100041048000b000c56aa041008105881c0b03449922490140740035103441c10540144552240c47e40c0025043c210300e400c030ba00102c60030005800490041440c40c82c020100d0441c5818a1903901e80400e1515407000f14000502c49100181f4003038480c0f45841000400e1980038030b6018210f829601402c00035001c603031060f035400c0c990341e80310718489130001c008404666202c290140c80610b060f00c85c1c3c0c44500000d0b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 273596151 1250 273594901 273594907
    0x90915030f0c030d180e070203040b07050106060909020a171003320a0b010e061c03080a0b06040f170f060703060e06090f1303140c0309041a061606020714030717 71
    0x215598414030045e1040e146d500340c219011070301b810300a006442c050302c1420301031038540009050450103004079100f500040f6010716004904100035008a442d0b12005032075519886e0f0400343c500c0c1d801c80c002040e00c0c107034030000c0001000055188810301c054000d901604c03990540000700000060b060300a031445164000782a0000003040d0502450459280d41c100a004ac0e0b580004070341900b941d10034800402010f0103040c420182c1090001c2e0003040e031400304012080c0040207004082c1720341e000e11081080440d000b001202821103400a00d00c030340c802502c41041441c101076192100540350000869280c08003030004070660504958840c400b1141c2890301d051802942c1d03542c10f006030051811081200210007458090102d80d5104828200d0980e0703160b80310b030400d81d226008060a2441641400100564035103215005480108000c20107440d168582450300760300c0114050468481c0d40910100011405444030300d40d00460040145585041e0303850000888000d003070035203894180c24 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 273597401 1250 273596151 273596177
    0x14010b0903151302100c030206064203090a11031606031505090c040501140f031303090801090804090e07080714010203040e010b190311090915030f0c030d 68
    0x14003a144028030000c11069032074401040054440300f01d8040c0d040036400c098039640e42e5100c0300c84000a40664241e81c450740707c0f54100f1240c4036600100006c0d1510814840320340e414079a02015000c1011900070458203030300e040c100219041241d0324038450f00000804410301c1204100c160741d4071001c0700038040c14084050300c00d5088030380c3d0044904241e070700e200b49003c820902d5090005010018180d65851500803068402944680500d60000780c940f803111a03242500c1c0c080d51a0104100c0c0d280e030843d40c1d40041400a03644214050b030420040c90f000069200b420300c141d0740f43c0c90040e8031b85ca6a550a25401200303840e10304101084c0c40c2d12606041080c084046202029a680c40e41044003c014220040740b85005e107800c140079413003141c80001034146044000700000a001c9502d080044d10451040e0308481e0f650740d0111407141c1c02c00c800e1078a0724110360340301c2c1e01040142964131300e68048070202c0e10f44481c1ca1114030307082e401038440c90200d20301044a6949590586000d0b4549461 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 273598651 1250 273597401 273597403
    0x30306060403060c031e0515010206040c06210c030f05060108060a03140102092805061306030213030f0c180605010e04090f050f030d0f021204020d0201050405031014010b0903 77
    0x18521010b0443c994980e00480c0d914460b4025080c006400708010700315890f0045030354010003081e682240302049110f180d101d50b50000c90f100c0d10903600084421102490100c1c02d031000c410074104148001d41800d2880504102c034407891040000d1a9800144000d1100c15201142d00150400381808a039104020f11540c40240313500549e584070800280c000002010310f40a4000d1141c140d41c8003a00b16200d9410605d082c1c0912030075000e0420140c851942c40307050201c03c0c07107500c00d4501c001800b41c000f442524000e80042240c000250186000c0c0c80da00d032a0a0904d015102e0200d5520131040010070044c0901001001e410391040303c2080034030f01e01340003c0c0002466401c00f900031503e0744864018003110750802558103800009668500c1d10007504244c4aa004154664055240404207400c0c001d0714802d4070014404e10980d81c03042c1d2500e03001c00486560340401241046010032010030f0a480c103120700c10544101d440d0208640c2c0c0841004004950160000400003405000c03090040e64 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 273599901 1250 273598651 273598657
    0x90603020c0309010e030118050309090106030e0d03050405031308030d0b0105090109090906060803070323130e040c0f0603060603060503010506240d140f06010207080c130212010308070b010803030606 88
    0x100034203060170240142c4010034050035058a007601c2c0310604580c50000d0240c08002807800d844103c5102440c1ea890715000d404480100b02c0340304142d4041c07460403441c40d009a100d6600280904104c03800d20001417540329088803d60494002c1d0b4101050389035403c41640a00b441e007160908100382042c988400007080c07084039110b5400100d0f11207603075806009c5103034040030203000110287c075030322081820050249141131350b0707003a009400c02d80415102031034171050380c194111078444032200c4c034900110f0000c098009002928002503ea03000504580000907180082690303481c01b20b07040e841e142c80030341210400c5e88400d009905203401c0203c20394902c80540961007085d44103204544422450450358001d003020608402d107004040c00c80440c40301010380c4641103000308405183d907400012612212a4820f03040c1503403044c0f200108a01e0412b051512101c243c64005080c40238100102e6180701c0c1c20390003901c00400c001448014400035903500c0d40503001c2d080045103141010b00c003060040c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 273601151 1250 273599901 273599917
    0x6050a062405030a0b0d050a060b15090904240f1b080f0615070b040b04150207030801090c0201150f0501140a08060618090a0510090b0f0d030903020a0e07090603020c03 74
    0x594801d04e045980c6da1b078640180103075070010f045541100003850504010407800040d2031282c0e08100d0280300c400e9840003218403151000d880080103407036a5948041d409186209600894804207100d100071070b0300d04c248265550340c510081182e0900a090266880d5400381070410426400f04000c2c505090000382070b0004c5007540e80c400e80706450440c1082da0702901d0801820104107505100c1400200c1401e0350056009200002d604000884480103d00c00d1046c01004110803100400c241c407203c1d4011900c09615000208045510001c00c04100e42160420002c81c04250002d201c41c1d607214400c50b4041c29800c09851600920b007a000e0060400240030506c030f200c0000e2100751107802d03440d68046008001c2c102d2480d5040c04001400600350480c0c840e1500c000031240021003009d240a1008060000f0b0a030031000003158003800007030f148064099052151032030000006032140e8008000034100504080c10340d040030880200b200c040c03a4024820107005200b0408124008000c0707580d20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 273602401 1250 273601151 273601171
    0x2a2f09040f0f0b1e1303210204050607080c0f0102040602070b091f0e030c090c181908030a0905010c03120e0f03040801020408062a03040f06050a06240503 68
    0x441090301d0510001c02e160100104001d040c0c0c0c0a0208409541d4403c5604100c0808181c031560744043d40002968400e03040075000441c0180c504140c480d90329140c901c0f20741c1849025140c00c2d1207d0100e0a07030f9004400482c1d00640c002001d50b41c0030020300c00000341001078030080d85090703d04000250b6603255401880011000020500416a9008074242032100c0e02d102e44500841040400744c10b01000e104070600a0040240121181c584908800e2054500c0b65503141404843c400314400b060200c011030350072103c031031040c034080d40c07242c3e03400001000050010341d6a15120364004140324140c0d030000341800103840031040020b40001601d206813034450000140d4054040d10740d841e00c03030780e80081e5000e4000003030040780010064000780700303440c070880c129211600c071003044000a00f2003a1950480d072000c3d04006084201440c004c1d500280514a400f5034000f89444250403140240d50b000d04083c2c2c0c2c1c202c20000301007040c000209208803200740e0001c1c032005030405401c620000340180c441d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 273603651 1250 273602401 273602423
    0x1050904081b28030f03140a09060b190302130603020f0402180907050d1d0d050f1306090f0602010e0a1103121201030c0e010807062a2f0904 62
    0x50422420f4000c0e40740c042003241d0203403801448107260b56940800d50010391024026002d50380039018441f10031409004103641541c41620f500c0c002d04d072014040740e2842e1910015811540e070380030480da03000200020300381e4051962041007840200320140f2503a6a040940400240c0c3c0d4900e41090071034025103002d40d035407880494004803500038100803544422544140b003180c55018000d07002c00791101c1410854240180c00d40d81c1d10480340700d04158543c0c05050540c011303a1041d00600f180d4030501c0030190500d1480200c2444043c2c2d107410100010f50085002c00c054400384910034001e0145000030401d141620240a844041a410107040700740c007000c9880316501c04201c1129002220310041c1e480d0f4181110f0100854420320094459417030801020550310301c4a00c40c0707070484903080300420003e81f600b04151000c84a0400c162101c808080600c13009007842c0c0410725010780f1a100400e0b40460b051169226580b0b0740045060880d800e9403c4880d075110b034803505400036040030448070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 273604901 1250 273603651 273603697
    0x140f0d141b01020c060f1509160903050f031e07030c0209040212010207200f0a15051306020d090b090f040213030602070b0403090e06010503070e04060305011a090105090408 76
    0x26150012100c41d070041d61000845075075020000c01c46a004485450381ca00c602d88a19190016104020880c1030340310100101080b00e0a41c003420124075032000d41088031415649445042c00c041c4040700d0300c100d84c3c200150446800c1c0b040100341d0741c5901e903001c940c0d041902c940c42c010403000087c1e00003801030742a00045019542d84203500d50400054100940d9a42028a4034a5a140e00c0c0385605c4545c115128190100c4c1ca05440e04840c01040507207103a80140c03801d021104c841004007040030a0150401c0000341280614440a000d8185500181200050070f030b001410707100c090340403600034003082c05081c1c2c4075640c00c8401008c8080442e40542c440c02009600e0b0001d144540c0700800f210310000c0c40c00104031074000003074406d9010784c0711f24080c95603c0240c041025000c598442c00a1010000202498002c3c0c1190780340380c0c2c003e072000510a4982d0790321400c4582020046603032070180400b42105141160f04107001d0714081e24801001e0816a44150180c081c41690b4222101c0d0072940c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 273606151 1250 273604901 273604927
    0xc060c0c05092e050f06070f020d081c05010b0301060311040b0417101e050403180620031804090203031e03100902120a0b030a050307140f0d14 63
    0x4005090001c042c1505424a4021240d008254010400c544040c2d00d0345000d8916490340c81204031040917044072100d1014504110707841e4803201d422147c0c0680c80c41000d0158403486803541085209a03111580c81041c80e9001d1295603c45480501880c1003000601442804e0780c2070301e04544080c140856074402ca03a50100c45800703690050b400b0000c0c0441c00051144090903c101144201025a128640c2040c0e600c81074078451325042c8212407445000052072680c84d4441940240207162104c00c119100c00d0b4880104103030b43c0b200000440c0c00034a100f0001120554801704488400110310f000307110514040009403101c02c4611403680c41c0003c0c415524140201c0f00446001d19007030b00b0301240c55004c1c038240c0c0c000f81c481100030b075007405003c1a074000d24421600c84102c10801e2500c00c0d5074010312400034010302030415805000303620361840010300030405013079210b10816a20301d1f4804150a241d181002080c15104240e10011208041e103420034020590046201c5140385c0e00c51419003070b9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 273607401 1250 273606151 273606173
    0xa02060f0c060903040510110613081b0a030306060f08040204270812060105310b0c07081b01120c020a08041404050c03060310180803041407080a0c060c 67
    0xc4079142c041e030b10402030400000320080043c1c4100b202e030000300844210f8111070615081448407410790102c0f003c100c0c60194944111091403180019618009124401002103413410900303095690212440200301600f50042c0c402400031842c0c01d0100540f10702c2c0c01070a1510207071000c4d008540d00d0b061112080c04000000071022400d802d80e00d0315480e00e1a00098030ba101001000c2d240341304c180400c10541c481d20031605c0e544171022001d0b06007c040c030b41c0b009600b4540600c840204280ca0070000324a19240c000d84403041c420406012480e207030254040c1400d001200321048204140c60320360703c50781c00010311103802007410030020703001c140d0010aa280c0785a000c0b020700400d40101d0300241c101e0910301d1340e4003c8030b41650107200585800f2000c002d90f000648075a40e040e0031121200d031003a64994130044c540800c80840b400b000c5095102c00e416a03005030b40c00c0c0c5440d0241001a02c043d032082080c0c100502022004092020705034449510030303c9580100380801c61889a07807424001001c540c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 273608651 1250 273607401 273607417
    0x50c07060507020604030206070201150504020d0e060c0702090c0702010f0807180321030c0f0f0e0d050102090306010b090105091c020310022505060109180c0b0301030b0f0403020a02060f 82
    0x1040101e8204200b0203076035800c3c101c0b011801841110000b5002e28410f005412011007042c11480d8000d08020410001c0c0d00303c00742c216200b136900c040500072a0010840c0d00d02078064140e03159a540024014000f0700d01c40100b0815050701c4c1003010304010303640204459000285884c1105164030b8081e82140c00c07001e0044046c808114207440402804003c00d050b125038204d0b45c50700040d04420311001e4040c0e804466031480411080e2108d410300d280a00840c28522069161000348080c1080c00600c0190384100c1c15110b0740e5020508200e41e040c10401d039070240507024201c0c1d041460b0000000e000b8844c21401c24003e040408444440d208400d400c0611103500a06503188000b005000d14020340129841034442200b81d075108800701c8140840030b44c19034229029240030ba01303103c42800a4030600062880c40c1003811580c4010404a89481020303103840f0803030503aa940b46041400c000400907104508082000b070500001a800091034554a907058402a4640300081c08a000d50b0144001b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 273609901 1250 273608651 273608663
    0x11a19090504060506090f06030a12020708030f04080105010f0e01030807081908060108060d0312050619060c050705270711010f09050618031b030405120a020406050f13050c07 77
    0xc20b1208000160708030600c5040c3c2555040001e50300d1001c00c4122030000e44126070903800c4038807075401080c0d44003c500c1e028101d500481304103594680342d29241d584590320000640a01007801e00c8450428050351303006003604000c008d00e142c2004080b9004800612000300307810030000b105820010303248107942403c18896050b5a000300c490f20081c0c88139404803081400600400c00040d568900401000d00c0039405a5561301c0c060301e0a20507070300a28025041036840801c2c030304030b001d20310f4410078500040e0049a43c0c0e0100c1240c58a0b0103850303c2d04a4006911503004442d075040075140341101a001900c002c200308900e600c41703078010380e50780c46201e8095285e07500348002000b22a01a4126402c201d20a03011540c081e910074090070a40d82e821200d08400b50030401801c0c0446c50b0394985c14140780300c800309881c1b500e40d65400295403051800000f0000382c00001c03a40d4150f20f441e11031900142400c1c1d4210480c0e2502c0800960191042e00c005100e01d40c1d200d0200d4003c080000c2640c40c445d600c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 273611151 1250 273609901 273609911
    0x62303010608060a060206130b1003080c1b0913030f17100311120a02010f021507030b010e011106010b0a03060e090a140309010206070e0402070c17070503011a1909 72
    0x1400204080000c5401c1402441c0c3c00c013001495501c005005440b401000c41c031036800350a6903507152240c0c0302c0a410001408101e41010011035022b100409604da00c10000f80003821031170414010448070000c40d03d00c13810021041115030780000c4030700e6009a2b40f61400c80174100501070207a460116052000700d40c0c4c0b04010401c581d01e410003100c0e209807401030103650300070005c100411401141d24680005650010303070308000154002e5034426203441060058412500000320b46480412085444400098584036000a2540c10100250f030040082c42c1000c00d010700c1e403103116551007062058030b40c00f00c800222842441d10a60000e000b50007881c584c4070320760416240300d642e40c41001d1000c5c1e40541d61034500e00040000001250100c00040e0040c210030ba1709c8480030b035264800482c0c0240c000303408020711000184000d80110140c509104003170020040c00d41c210340703091155089240039a2402900305d005401d20b0000d02c030781d20303070884082c04105000d0100d8a0034603215404180e00c2401c0c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 273612401 1250 273611151 273611159
    0x121505091e090d0306080304050619021c0810060c02090c0c0304050406030809090f13021314091606030606051206040917180f0108040605070908070e01030204060b120106230301 78
    0x450068000140f42d40c062081a03225180640c9070b1040388101a03011004102604500ca088c1685481e074005a0040d0707400c80015010702e020100f850004070002135a41d00800c0222140542e080b0302500d80b51038082e5020b42d040d03000c15610f010241180000040108800110100c10011140941400391003806080d0b524942454580c000308000d030320071180000000c4603401d500070f1252090700ca8401c0d42101c83c00325001d106203010b15451143d030316900c2d90464410080e021200314041c181620082404800a084401c030500240d00080d0805091003020407005a0200a440841004602d06101501c4a8000a004104005004040c1e150814040405081c81400742c88540032a034400c081c0903400300b08204940c9403215032180458119000b28010a0140e44095800f0301541040080c5c6600c0b56400c0740741417903c4c1c0c015648030307040f08014011800c06002d6000108034a090050a081d100a109081c02005028035400c1100701d070480d2055850b000f02548001070b080005d00c0daa543c42d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 273613651 1250 273612401 273612403
    0x509010e0a050604050f03070c0312180b03070807080907060e03030910050d05150114033103021902010c02010c03091d060f1f1412070807121505091e09 67
    0x2080b5425581405070505088503c6e2011045400d001c2d481f550080d00582941e40300d8080540c200351582c00c000700c107041510a401101900d002030040180c0543c0c03240340c198002044084001c05480800089006014003c240080c0c01000da0704103080c00341480320094046499030044120591b0300c010380454180025420000034114102221028015907507801b01610648c2d00185441d0300081c00072903003003221414607010b1500724030310b400da40c1001200e007140325480c002c1c1d440c5a40013448a415030401055010090303c1c0001e0708020a00c1032242d005e80003c1d11910f210729029040c02040f104000802d4410710394138001c1d03d078800f010840c035181d6004c60360f1070b00d10483d0400d0040b400c8904152051500c0d0708980d4240034138244440304040c0703448044410b00c0d040340740316040c01e1040c4100c80050382a400e58600c51160b9030790f01d482c00d21f48964018905c50380409103001082c90a800d02003850b048280010540340e055628142c0c03500c50550340d410b0010a05841200c501c0c50744144100010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 273614901 1250 273613651 273613663
    0x140307080105100203430308010f0603051302011407060905010506150705120a170109090314031603050c040801151502010e030301090902030c1005130e06130509010e0a05 75
    0x340549003020f20094a95080c0da40303200fa4240b04c0002c0c00405600a007583c043c1c40e012505c138000101d504490186441e4110744240001c100300c02140e0488014802e8047c040c00410040485203404c0c801c60030010740d21420b64800c60006410000c0c113620720804210001c0864001c294030102c00c106200460400900920b0155905846075075a400003051071282c8070150390b401a08080170701091404101c3c03512a5a100117004400d108000c000c42c1a80e4842d280f20700d0003081c00007000b003825450741c80c00810420403550011000c03071050041c07069032241c090060610701510b040c0040c2d9501d5000003030b0514000c42c1d00c88040d542c24502400b840c24040f21580040300c035481a0745017580c0603104207030f00341d4074442d081c41c2050b80140010000c00e100e40e0403a00200380007030103868191142d800410040960920f16501256000880712011030303903503ca040041054200d40c45c49410017000265991000c10303100c8400d070303881c0d0300444d0040ea0213510003c1016442403c440d10000e95180c1380b602d41c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 273616151 1250 273614901 273614909
    0xc0d080c010c080c03060103150b0a030204050306010602010c050f09130204150f030c32030708011406040e042307080f01060e150634020f010e090a0207031403070801 73
    0x5400d042da6000101d004199003406034030b0007001c0038256030760900110f00400e8032401c1440310409035500090040720b91401000c12001640c1c1c00750381e8a080c1003e2501c2c054041c2d0010046a00d00300c008a01542d20a082d283c0c4140e03180c2d6490fa9840ca200006100c090103441001001440010005030a045d481c0310101d0078070300707a168440d00481005007627003110103082c03e40e4081104504a400e41c8810303440c00040400d130b003000d203102e20b000181048400e42c00c200c030703100c0105001c04010712024818001c0f003003402004031026407030705040034081401da1501404c010510030001d021000401c3c0801d02d004a1044c9402c2212410391b40c0d5a030081c1c0d02c500003d042030036540381035404035091050714040ba20401100555194500501c0300703124441c0d0000030704081d426006a803c800345071407030000c075100018103103444078007198600400c20192201c0b180b0f141440a604001c14454881c10290b1390f0005c000540142c842481d803e080c0e88601c1d0115164045040020801c1005600300851074161 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 273617401 1250 273616151 273616153
    0xa0f30080a21050f010603090515040311120705120702130c05030a0e0f030f1b060103230c0a090f14040f0b0f0c09040c1b050105070810031e02030c0d080c 68
    0x400906614102c0f4003d58905440260910060100d18025049461068480d1003202c48143c00b08203048010321040d10100c0011385440156110799908100400072910468007503843c0c03024555a07695192003494010f140d0580104040d402d40da03c400a1038040003160400380410010300c0d000400c0c1e544210b9501108500d05000701010030030000c0c0040801c17100100461a010801110360560b070003542c101801d242044242503810300c001e02549000714400d180350035a032200d55510300410820442c1d080c0080c1d1219600003521341e50010f0203011078100460000380c45019164201c00780440181c7da012048281080c0f0080000d803843c00c030030701c500400c0f01800d0b54965040260000030140c03940b1341c290405220440075894039070320405640100c1d00700030590482d04425480d1294141c1c80c04d562995481003001401500400e03400e90158903404480104c604540c0c82100a201c1c0d07525208503042c01d56942c1c811518208a8402c040070020500c1148080300c2c9008102c650103041d0190b19 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 273618651 1250 273617401 273617447
    0x30903062c01060305280203030d050106021e0d08071806081501050301030201020a1106040302091303030b0a080a030507060e0f030c0d0e0603010e0a060e0903090a0f30080a 76
    0x2072041807140c00300380c0382d0201c058490307080122400716808000c920142100a802d00c58100103070ba080008000600d540340740850030790300d40b00000c0d043c042e80340c07668007640140090050000c00e01050310507240d40503051800c400c0d02e90200883d00400004061241034010040100d034043e0016100e910441d049101e210551000b02d0045a82c1e00080c40020701503400100301400054248000c000c024101174010b43c107081d07480c0c00042d182201600d543d2071074007041081344149541809800c0d09500151140c56040703103051a410380d10b100c0008007400700031010a1040c1000640c2d000740c032a4042e00021661170300b0f6a405802d49035400102039440c180f00b1400c00c2d84003140928103d4103031041c000d101c2c90940c2c0c6444d050103da0b0000800310038002c0d40c0c0325000301d203240f0100102d50007000404015900c1c4d450f042309011301189250842c285000c00004104114114104540844503200300c2d400c6610020f26403594040c810039000030850780c030200780d00303582c01c0c0c0c050954012040341e424080c03c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 273619901 1250 273618651 273618731
    0x6090b12070305060112050c090a140f0405030d090614010f0510020705010203030703020d140a061806081c0903150f05070e01141c0207080306031c1b03090306 70
    0xd91000103102c002c0064114200400c00176022105131070380c0b28060740684640125490000e008071400b21814013001d42e94945010220241d0844180d025609201203003060400752a0140d50340648000d40ca921505c54400c1f01c10480d00350041020074207080d05140d86940c4941161007070715044d01556010300008035a205c3c085100081e410202c40042c0c01a51854850035402c80c0a54007481c080000300741c03901d260528080c80a039905225050320f0b1000601c060814285090019492100941d21410803c00b4048440042001614496414400c00590360503c000351260002036102074a05030109107070380036120181d00007881c02c9450742c408200070342d540c1005851000c00c44035058000b0314505055030a030b4504000500c900b000c07140d503182c0145480104070017641d10546c0122529a0003200b03001d52400c040104040403101080c148408203002c81d0010302140700c0340302070716560308848001c00c18140a09822805103400003818002001074040340d0071000c10400c9518030608425800744 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 273621151 1250 273619901 273619903
    0x40b030c1b19030e011e0c020f0307080318120a1406010e1306050a06081f06141507020f06030c070c061e030b030c0a15030b1e130b0406090b12 63
    0x489a010b0000c540c100b0348605071012a042441d040807541442249403100c00d000710b00307000001c43c01e100d607071b0780c1d800f0103041740f0510000d2144101110302944c4a01000e10030310310040103440207000e01c08160059000f004000420344844200101074070300030101030300180300740d00d00d003020824040001c45075142d0745c1d0091014682c2c42211020301000c034200240d00011f209401443d00300d1780b00d4401069803501c4048003800d02c2d80c03a90000841c40181114101019164099074004040084501c01030704020700215806281e0b262011a1341000024410210f590b01c54800344e03400c1c4c000d40079a03180d1600c00301c0c0000907405481c05486a213040e0340300268151042074100d48240c5805131412001d40d4844098000c0c0482c121502e61601542903010a107485039100780000302000428404c0c4000712401c0502198942c3c180d10b80581100940c2c0b01c0c40c159640085204202c0c16140390081d8545003035030800900c000440039a2290418000280c2c40380c040d0010703000c03c403007101c122040c0031043c2a65 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 273622401 1250 273621151 273621163
    0x506071a1311010c060f1e1b090b07150f061403060702031605010905060907030c060f1e0c0614060f01110606040b011101061e140109031502040b030c1b 67
    0x24200b2404014008503540300303650b40d02d419445114007140400240d10302c0c40603284044030f504205a0070b030084000d41e80c00b901444000741ca05107030f0680c23004900c0900801516844c0a00c02c071448002840714200310344074400c0e6031901c418002c2040306a10411003440a4000c40c442c01c2d1050580b2940783c0800d00c0c001c100300b402031106270011483c00d90540101420111142010340c0c5656a03011500c011550620555202d422020060101281103207007900c01c01009401072400c101562010174519600306504c2e2a085018644418500c0d01744c02084070000d5840e0740081c141c0c0d0500b80d0481401c01203050b201d0180c881203542445109004004440c0b5400070b41d5030540c180d02020100c0c40600b0140e0046207050010700d0030020a9041c08181405e50300f10740d01841601000144094804200c2d00e04030009e8500d41c00061002c0d803424000038600380c2c1e03c1c00040e203059410800041d558245a04440c0204405000c0075180d1a203000d11220540001070080d6410b41d01c10018290400702042c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 273623651 1250 273622401 273622403
    0x60c050f1b1f170a02090604030b04020103060f0b030a020325110606030102120c0705031207080108060124030c1812050d0801080a0311031c0b0a050a08030a030b0402040506071a13 79
    0x20f14030b00f0100d00c2d400c1004420081c040c20f1240d0742c01c006005498580c000140f0113140186440903083c1824400107080701c50070351104801452200c000d000e565040d00c00c80390060004200075032a40c503803021199003141884000083c0804100c00514041d8000c0c40c500b80040d0b1540039121950340700400c2c14241d01c00c080c0004040049040051052480702c2c0c06031105038045d4040b6400c0101080302e240e0561402c0d100b1002280303d00004116488042001502400300404240540800480400e80c6a202c12010070301f03150312010016003aa00c00c0014615000799107042d0b0080716501d0900c0d200c180103000c000c0c1d4007030180c42d030713450310240c01210721034100d602400c02480664880c1c3c42c12a0781b40c404208185160004200000355015500d2002c2c0414291040025040001c0c00070405448501d521031400340f8615501040001004000d4400c400e40354103002c10911820b6000034020711503a0046d030b81c400d401140800c18401c0c109085542c9902e40340e8280c0940e2a58510f140e84c01000141c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 273624901 1250 273623651 273623657
    0x42402061506270301090c0e06061c0504020f03030d0207060f020a140304050307021e010f0e06043b0906090304050a03061e0501080102190e0901060c050f1b1f 70
    0x7140c2000d111501948100803140d1910700c01c042d43c910010b0700395a003d020a0f0b490142c2c081e024440441a0783c655500440200c5c0e0341441c01041d01204850080c0143c1c0f070109540c2c1c5d540001d0107644602200840000c0001c040e2070765042c509a15000940100c0c0080e01d14600e084041d1001031000d208680e8122050385800c56441c0407092281a16400100102c03154041401924010f0b2030701c8510301040f55007049824290f410760300004040400c228241403c1010882d086052529014119000e0b944140b0b81d043d000c00c45480740e100600701340803103650862025052010450700030401d5a028003400d005540d641c0d1207400d01702c1d42c0d03800390b0b0007903a500941d900c004000180d07031540400c2402c07142c00768803450041e90900310000c940d8243e103d400c59940002d40d4003040340c512807030500b000f2070318140348a441d8104c1c00410002c2005014280174400183c5261080c08400c200102d5985040c000315080311880809603d00b0100361b0300002e0040e44202913440b88400070222020b0442420790b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 273626151 1250 273624901 273624907
    0x30303060918030d0209041b090b0c0705030f0c040c0504030302101508011404020103060f0f09020a03020f1b10050712090c120b040c0b03011a0f042402061506 70
    0x401080000580503203100142c01a12002c07110300402840900740000c4c14440050b254400c1c04140000d8940116140f40c9041c1800c42c040c00f201d07042056002642c8000705490b45400f42c0e4079000f440c001e100d400c0b9035811700c0b03843c2504220043c0010b50f1a542074083da002d0000c802d003103100380c5150003a1301004015030448081589446840e03400366040040644480603010354500e4080d08541c030198002d0100f450080411056503094010b4030002c240c010000348400b4542084030f1122400e501442011540000b00211138510940541d040c0d281c01c00140b03a95003240d2102d2150034070681c22102c00a0040c5491a42408841d00c1485c0c8141c5481d1112042003c20581e1000117045d0404215207401c1c0141d00403800c0d1442500510f080b034401c011b05070301ca04007401d059000301455031292410080810051094288a00d00c0f525000c405440c1584c03a04004404000503000703e8100c0054030110400e03110603e8443c0742220201da0f1160265500c40c0c880c08801b4000039803542086400500030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 273627401 1250 273626151 273626161
    0x80304060f0305151302030f010503060105060f0c030706061d010e040b040f0309030c0b090123040302060d020d15050907092301091508090f0c01020a140a050f030d060f05030303 78
    0x10750030283c0e010103e100c0040e050310300c44000414401780d40d500409080d5000c0100080c0010902105016003800c4009050545c54000000c2080c81441180910010302041c10100b0040401c00d4500c610340c4078409001203915010503000541203403d002496811010000032070005642005c0c0c0550380000c10445659181d848103c0700011209089080150352400040490841c03060324002d000403200c2c4596800054000400e05460f5503000729000c450030455440c5558050211000c5950560b4483d444414140e5224002e0103031010290490303040c000c0311084400c42050a8040e540116800c012645860008552501c010b01540300c010310341003401c00708103c545214444442c3c0500d04174590589503000a12894004241000801e4144062200c0c0000c184100348103038503018002e10020b4101070000350381e03000c40d0201034490b41c007461280007540002c2c0981401c0d150010111900944160b00d0503690340e02c001a4480081d1500401184104904100108580780140258103623102c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 273628651 1250 273627401 273627407
    0x14011b08032214030d0e1903030e030412050106030b15032a030f0109050705060f030705130e0721090302060406050c0403020306190f05012303010b0424080304060f 72
    0x80121420224914000950014034120f40303110340300da80c0d40061034036418011600740c00d81e502515011020303000041000b41e02045907850641c081c0d014500810381e0200c000c101d906502c29900080050b008950340c20307050100540228045a104040484807503030313182c880e00307241d1a00100c09545600260f035020503070703038032900600714050401c80508560340d0500c00081c500420201e80c4050f50751a90070070014400144a84002007200750707001480c182c0b070700311804424800100624140580464104454480c14410320007070103a190f441c002074145100054220204130100140001014071103d0300984a8081d1400ca294107400401142e1074540d111070251100606450184d0424007001000d691304125150040c0f0613030344195010003d4004c02c1c01a80d005466101046060500400c403106500c08440617801e200810080010408000240584001000e06502034203000f15400b00300719818030402c507050f907030300200e8071299180e02c1c1c1da48074061482804049030114100401980c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 273629901 1250 273628651 273628681
    0xc07030e010909020c1f020906030115053903040501020744010b01020105070c08090a0b13080c0f0612090c1c020906030727020408010614011b0803 65
    0x41414901c41441d21400b141c1d0882e001000e4103203683e8010707802c11a0100c0b02d2091b80c2c074840301c82e0100307600e0801110081084c070312042c450f00312a021004820682c0522078010703140341000241c60000c10520014030703262002d0300311004041e0030700040110642c02c2000421981114010303000b8003040c1e8a412404410803401c04031010800c02c1901035024189006244503044a02000f0000400030406440b0b50865120304070b600c0c150380c500000d008440e90481c44049006a03c10315980d070721030709140802c101085980c04101c0214000c41c9084d0700314042e5410342c0540c0c1a400480700751580300000c0040e01c074862810150065010000c0401c110480c40445510481a504030740e0400c0042001c0740402114003690b8651390b03d542d9180045140c4410f400b5040324040300202140da080c0000d00c40441180780280e106241121030428105815030103540c024011040208039059503420030721008004040c030a400543d80e61040302000080b91852203034907812008260541d80d6555400d44202d13 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 273631151 1250 273629901 273629927
    0x2030d0f03020906040b0307090f050d0f0501090c0f080f01020403080315120313031e030f0f0207120b0a0e06010b0a1d13061e030506160903080703050c0c0103050c0703 74
    0x2540030080d0f8038694540b04014802450012050390742c0f440c203044010700c0f0490300e0304810410340603000204090340d100d45c0b00b030510a420640c0306411945e18680b6a005041a0400500c441c50302c19000442c041040482d404503211441a6640d540c4122001401c03446a0302004040d85018008a00c540b4641560402c0000c0e0150500c220543c3d800e402c10710b150088148241c011800e01414400c00201c01403e4903400700c0c440010010354140d6a0142148244240c0e00c42005120108043c49034400c021b504010124012051184583c500b042d100b803a030120b959002c800d00f40f681d44a04d070400090118122203c1421140c01c1920045080381e0000006507001806190641c80300ba00d980c502558400c90036031000005038280c5800c02001140c0400c064008904103080e0041002c2000072644560204119010302002e03484920160380c5820150409444504003080ba0402c154200c1d0050001d84c1c4100100c82c5450396040044081c1d610803552030142010500c6841d000a00448145582c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 273632401 1250 273631151 273631157
    0x4271116140a150203070909020a1d01031d100b0a050a0e07120e0109050706050f040b030c0408060c21010b0d0906270c05030307020a170a0f03080a05070c02030d0f 72
    0x904003a1208245098043e040f06880c0e0340c00030502c1030f0b0030f03001402840106400c00003581807043c0003d002e480306d288031142c040c1300c1d24074451400090303200b50300c0080e24842803c41020718507140840c1c42c0d690148003150106c0301c1c0ca000480072281ca054411442102c0e001044994510b04049007406d00311405090f1005028840e40d500320789009500450458841c4400005202e1405052040c90211560701410902904000c0580c18541082c2140c055441c10000c03c1e9032912141040c4001c0d1140d0361241000b8060b01c020311291001c01001400a4001010f415000120152580e5403c18080c030030405000310070002d0001c0c3c0c58290f0884140e05000d21800590b124002d0180a101c00c4884a1a0984001440b0b44410005030716400030280a040e001117080146c91381c0410301100c80e500030240e01e9240c00280b0490000d04010181e031182d0301c420102c01c000d200d4a006480071405595501506003082c0000300d4181c4150f8140d008903400a0040000402d180c4007920810208402c1c1410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 273633651 1250 273632401 273632413
    0x11030106050c12070b2a03060f0609040903020606150a0807030507020a0b040c09060906210524040b06030c0904020f18010b0c12030c091003020427111614 68
    0x307070703c5944054030380341d40110b101014a140410107552400020300b11301c1020150100c600c5c070f0440c904400d595200d501502c4001070f104001c40001e510380204000658060700b0240c2120800d680480c0c1036004805c16206021403010225002d90a8004c00039000700285610000030904c0d44a5000250050038034015101e5500303407503e648429220494040d109658444810000d00c4c5003445a04001e140c250b034208001810162140024036444106501440d808659901403081c04d000c1911050720401d1074683d087d10045c41c7d00741d14082250295151074075130000070003504011814042d9400000d1102c0c01949d0f50b542040705200b46c1241541d08200f41042089280314804044d5000e0700416141e83c2c1c54910001415103820501106100c4298051003402903403030000b000c1d5542d081c00ac131900c0c01d5541620030101e00a0080c5da105e90700e00300d89010030603616101084c0d0303c10b0a08010400b88460300d200207000e04a84a00d02c0c080003914141c50100b800b20b0304003039541066034600015986 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 273634901 1250 273633651 273633673
    0x6010516030309020f0d0f0b18030408060411100e092205100506030a031b030509060403030c1130100e060a0e06130b0910020a020a060f11030106050c 66
    0x10340c1580c01001180400d50300c845101c203602d084007460b540d04400b21400c00303412885030b42d032a808040144004100004042c041440034003040c0410311410a203600712a283ea07900d40404c0d0703407103800361001e9544c18040103054a00e1b05041e003180e003000b600c2d900c0301c00001280b9414440908030040c1406c410460a6010389030104041c61000502c5008400402d1903405050f035005c101c1d4030250030079202e5070086600c9000680c000801c21111022842d03881a010300c03d0805562a102d00754140e980420001000310402d5080b0094001950040c80718141822940003032050601d41c510604c4521020242d0581c0f2140c0d014912204082e02308090b2200e0200c002c070700400792038262020340c943d90030941c10882c002e6000e2190418101201c80102802d040000110018080504d4080c1c0030110b40e01c00215410020090f403915940c031401d0841d035500111200035111580ca031411a111400c040c80d2a841d50f07050b01420141e00036070810702c1c0c41d6920b001702c19211940f00c41100c8441d0700030074041d04 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 273636151 1250 273634901 273634927
    0x308040509071713020a0b0909040803070924110d050405041806020d0914010605090a27120306090603050309061317010c0924081003020307150305090a030e0405060105 74
    0x140c059001801213403240100d03841004031b1a08176800c00d0031035072024005e02c40d0641d01d040394290404c0c0c00c169280c0d905c1d1160541141c03a002c4640000c810301c02c000c144180344105425840c451020184e45011107000e4200d0180d0f01d0740703140c0d000000003942c2448284000d1920b80e0102c01c00200440003d4170801c0c140d42c0d0b03107050f6004201d6255015607a545807006018402d46205ca40500c440d00810101c1d0606000030304003a170280401035895600d001075610441c450003460044d03480ca100302d10381e1344500c1c0380011202a00404c50b100103400c0c000001541c1350103021310030559038868065420100000c06103c03040e0000d0000100007001e40c8070003e55a413500b5128540c0068110000c10000b11445001d003d0f40c01e90350000d500301d0900020310901c2d45109150301d09461141c42c1c44100b5447c2c0c10004c54030b048180e00069410300806400042054010321b2140c031070a46074506115139622070300d1a5403646210300c000360200e610700c0100d407802d203002e52141e42c1c800814104503040c001c8100d210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 273637401 1250 273636151 273636197
    0x10e0a02063108120c0a081606090b2409040b100e010902041e0501050d0e03040504020a052a0d120906020c0a0501050f011208030615030f0403110106030804050907 72
    0x103a040c25081a4051240e41c10900c20140c143d00c107020070518080705d5001e40365031b4029501025154450105492030342d611107151100c12150401d03400c1c096010743d410b082c028204152030f800d100f1054441c05454083c0104000f00001c60018601c0803136a17a1500d40c0c84608900400d1058010384e50140451a41c07240e41006002c2c000b11000180c41ea0709141c00c0350010520b514903150b107a242d401082050707aa00c02c080700c1c0d540824500115030b444106a61320700e94051500416401800852040107541e408005806024110a019080000d4000202c2c03440c03041c03605c0000d00c1e90044180060484d0003201c0e07580c040180c101000482c8210f03500d45104030f0704801e02e0781c0b1083e0000200501400802d004080d000f410104c0282895491b00400034824050580020a80b110220015045d0b9681d4504490702100003504507a4a240c001001d6900000803102200800c044610226400805100b0300c2c0989030320006040c0b419052000300181c1c910024520410030280c052030700e0100900d0555 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 273638651 1250 273637401 273637477
    0x90f291908010806012106020a090906090b040f0207030e01050a020f03040902030108060601020601050a170a0c030b1803030c0304230d080702121e07021309050c01030c02010e0a0206 80
    0x3070721203254108080c035410030b54103a120605144806100c183c004903030704030401e40c880d40508010303070321a841740c8265113920560344040c68080c501240012041c4003504080c1000204036010089040030912102c120f0198490241c00200c80d080c8408007540a50010250b810450040b1912207641c407050603d16070082c0c02414070b694001c8010000b0110030414590000310900103001a5810100816410031180c0f180a184000540f9180d040071002c0c0024a12a5046862411a15101d080407041500283ea800420810380b05055256800201c29a40a06003591030b452440e156512442d4100e40c44054400c028014480320b1100c1e84030401c040c0040000607103c012551a10080103030070903042403c000c45c000301c200b0080d285200b4000010010080300c4911644440a50000c200c503080324583c01e40903285407a43d8403080c80b40000c0d101c000440e0984c3d080c8620449241e00324241c0c1c0c038482220500340e2084208500520304140034040144500040500011041c041112080c0b4113001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 273639901 1250 273638651 273638657
    0x5100e01140a06030b030c01050d020405040501080d0e090408120c090607060b09070203040503120d11040b0c010f110307080c0d020d06050907141801020307080d0c090f2919 76
    0x111416250800140d042c008050b20b003030800c83c001c4200080783c1c580c2d14100d030950400500180311032501640754181c4001d0040034000300010340c0c503281615a51074207001e01d6008117040398003078030300c03072511407419482540c0c0041b401d41015514072401d921140302500002c620581881449400c0d1280e42c041c0c01132501940022036000444014044242d10180480045400401c030a024a0300e002070115003182d45503800d0f070b6491001d1410f040041142841d503018501c03002900042c4107a0f218080c011034031403a00200103070318103004c80804441c2041c40b90448004140300150340d0703a00801000f907200d607807660aa40340142c0341d141c100c220b920403400999510f54440061100c0d04002282c1c80e40105241401c500007240365110301054054407984444401c02c0042250f41c59100784140d942280e0700110980d00ca03c0340d60b60704d1000d400106141c200059403c840000d4a11258201000310b0b072080c850480c0c0310561045441e0088602006107100f00c0c0c0c10807a401410814603488100c0080302e40d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 273641151 1250 273639901 273639929
    0x2040c0509090f3907050a0c150914042004060e092a070b07080901150605090607030c0203061608070c050601060e0103091a1902070f0605100e01 64
    0x740401200c882d0290203008004041c1041040c407000514103464030710543e2107800d4156403543d124070314900049900400529003c5040d90400c0fa002600c00c207002d104881d03003401117441c1d141031708000700142c944100103444001d08001081d070f0b800c40c1c011007100c00740c80420140c03e0701d440704000400b0500c0300b490a5070300090170050258407013845802120102ca04588a0170142454122891104007048407051120000c00288200f48200d800e07141d0b0101c42842c041c600008064810341040342c00e1a0f0950902c9102d1030014150040d82056410700d448041c200900b2a00b4001e00c0c1e00500300840c14002075000007409a6170401645204850802d410401445410002803441e08003038158003d01c0700d82200c03000081e50105165040d503581c1c2c41c101503d07100090048000d0241d460024084000d0941000b402c2030204030004e11450780000310130818001118000200d128a58000d8003000303008602d42c00090907508420f41104d52100000f41094483c080d040c1900801e9000701d050a010b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 273642401 1250 273641151 273641167
    0x503091009030e011706130c021c02010903030e06040f0803061306150207170712210306050a171504030c08030f0103021302090105070b090f07062001020307121802040c05 75
    0x10030300040d1002003426a4170091b040900100c0d40082d6145485042c2c15281c10541c03500034820054450541c2020b41d4030b000750000b040f4041e00071b00c000001607000900b40780fa800002800001c0807801183e2046038484000000d03122050a03800c040d184a60000900d100e840c90303d0218001c00d80a000a0083c0c0c203002152044040c1c81c101c0280d0148940c035240d4504908981c1c0d0208007103048030103038010061840601c2c9400d807030f080000744508140c0d44100e4042d041240d856800103066400170b0703440c0744406403620b03202c1c100c43c9414503903c407079903004001025075a0000040d0903080380c400c2c00c129201114555907401d1701d070001c40350f042c03c00e032402c401001507180800d10300006a01110046280105c0c1c00c000800b140b06400c0060304945402010401004080211901d01c01031314096031001912540d004041c1d0150100011007039841340040c801180042c03003101d000b151f00303071900300000a440d8003900280c0041600d00d44980082d40180c400341e00c4a0207901c040f03070619900c031a900d00c80 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 273643651 1250 273642401 273642407
    0x111903080d0c030b0a0e0712050a0b01030f0e030a18080d0210060911070602031306060b09040522140a12030915060e010501120204210203071403030a0503091009030e01 74
    0x550780c00c842c200360402441c031920780c903100440e00c10360700400e400f031030640e984c26010740d211116000d909017410324000410211103c0d5500030400801d00f6a010311001006e034845074151081c642c0c030020140c20400900ea011030046e584050f00b000c482c1c601c030940d00d6441e4100d40c24024040210800f6801031100c000c0c00351040c0c03050b10094070940b54104211703500d01032004c115004041c0020304d450350000c0424040e80003400740175400356120344c040c030101d6180d44003040e20b504681710b07450180d070400b404500041d0f0004241c101c56072070401020000c03001c80d01c49500c06004910340041034080d04941c00041034034401d001c1080c82d5107481c00b00e01c01d51140f030640c030301010079007481007142d19181080c084600411640f604540e0709103031202c03080c1c0c0640b030044000c1c4500c0e4005400750124144055000202035000d5020a00031015205403580d10900c0c40100b140c2d0140c500d030305800401025124a000b400516003140340c65080f135010300301d020302d02d008862032030f0000c0d40030486401c0034030895a4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 273644901 1250 273643651 273643661
    0xa082109060f0106030b1f020d0f051801050702062502010f0c030801090509010f06090b01091e060f051b0a050d030606050403060903050705030301090501150f0c111903080d 76
    0xc48003000740154a05400e03012410390040c0240b07010142c9034402c5a001e079891581e0035901241e003a0008421654001001c2d54411508003c0804198104d69400042d1b008206642c01001100948080c400381f0b81c0c011110741e48141c0e0300726400202441207405201e02040c03040601e10244602c9040c003483d40c0005000b48802c50500c1c8104001202c01c080000e43c029035480c11100e00030740c049525107603001ca0781e0140512405100d40c0510386007001600d500250400311541000381c03211480d0649510806a0240a80d4142c104c211a1040f040004a00c145406a4085060301e08181414100421426403030741e80040e08100d0340c044684035080c80410b1100e640300003800d0804000075840c0074800707002e6008500c4054500c5030340b04000300c10305006030200e44031181e108003071343e81c5c9684908110004080c280200090802074041c0b1203500350043c24a01441d042c161140b40700c0d00c0d42c5030f40311003003080d01c0007009410203c594010a1460103450244010314030a5600580b41c8803441c013036004482c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 273646151 1250 273644901 273644911
    0x4140f0f01270e0309060a050415030608060408070c030b0a0509010506010827010212100f0503190f1403040b0d140f160509090403030608060a0902060d0207050a0821 73
    0x100a2410060640c1400300d203844102000c074400306100101d03d80c003d096010b0301004c41d4000000103070080005a0010041c0191440001944107980070305e1001c40840d02c0e240542c84096100f200441d000c216080098014503100f203289440c0d1984030398408440c03a1054030f08101c01501d8105004420783e0a0107001c6d401402840e1203807607403800d0041010014642d424405100550364a041002c403c01c2d011101480f01505c1e81400600f849000c042129102d4458007502400101e80030609145c082620084c901d00016100400314260b180c0d4920354902030030440e028124141e201000315401d0014200070031520312001d07222080c00c0c001c2001c0d40c64101440a94401c503a0800c05040c040c0140c49420030010041c001c0c0c04d82c403a0209a83d540b00780120039601044000400c410103a0503040482900c20381e0b4199150358a8500c150025102c80550013540040140151031005c13803550b02400b46d250044e41104d44030046a00c03000c072194000034035020400c1c60300400c0261404903c0000f6040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 273647401 1250 273646151 273646169
    0x180a020d1401091d0c010c03140711010210020f09090601030f110d0605090108030f031e0408130e09062a0d141303051804060324110c030702040b04140f0f01 69
    0x94526200d60b145c442d040c40241c541440310801800040c540b181030640016480d0740c0c0829038409241c20058070314081c14141c0c030300500c1052090412500c8070b00a4886800050f41c03c1400e04038244d003040a0400c00418560406544071481004542640241501c10701a10b048540d10f0301c0101100c4181c03240da8115502a2001400400c80d50100200712922402d081d40804e45070b4a880000f40310720f8544100c140620840380e002e005c20f0144000090002504180b0340c2010309076201090043d0560450742040c03960840740c0013803081203584a00c0130201e02c3c01c202a014900c2910551100c0d5005030100c403001e180da40002c20f00000f0031507921600148811060034400030940c2c0c009203540b01d00340120b0201c0881007003024440d00c1d19005031010315488100006489440c4a0406900d003281e208034040038200250b1040100161046504030314a1401440c5000229020301019080071100c5a030065070b50180034011860020819008048800240c11142000f245040000c0b206800c03202d80 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 273648651 1250 273647401 273647441
    0x41415030d0e102c01021501140d05030c120d0f0e1e100f05040b1b0708030903040b190f02011109091005040507090504050c0306180a020d140109 64
    0x100d16005030740e6411150085401514410380c03071904582d444280180301803122160009440700034240e4601403540c0c1c00a86c01c581565155441e031549a04082c410fa4064201c1100fa0006c00d0070300e092501d40076030146089a1501e0310701c00c40d16241043e002d07064030701b03070002051902c104070180c011a04003d41d040824881003500340d1607580c980075040035074405c040d00c4122202c902041805240004024030004015001c07a1660b100050b0904503001c407810800040050102c07082e0b49209890101101a00c500f051003599612815a02c06081d041080c4014040085c404926400810fa10340949c0380501030480000c901a00b100007884000e02564100340c138895142c1101000c4c0d0700c20050490348003042e5180d00c4082202c20480e50440ca4006007007004000200d900820b9000440d502030b101000550341e9641044060b00040d25040d9104180003c050b00481c2e01c6a06a900800032880c01864100f1407402c2070215410040b80c90000d40a010040141d01103900c101c082500d02c02c0c50700d0350 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 273649901 1250 273648651 273648673
    0xf0e10020706081306050a020403032607030207020102010204031202070305060a06180b010c020a06030b0f0d0f060207020a0e010608100806040201020a060c0e060c010209150703020a02040902010e04141503 90
    0x740300c80030340c0070b60020041d0340301c0003494004218404800384d030782020b810820303800c0c003424032006548640819401b0030400f001d061a0302d000300340d030f03a90081e16117001140c3c0c60b22200d034110069840410113a046640078400480420b01c020f0605050f00d005070002c1c40b005266240503418210010110900c0d10f203854006c000040302d8118202c1c0180744104001030501510b00107891544100310040e40080303c1481c0451555059880701040c120200ca9031025544202d00300003aa8070030607801070000c0303005601c99000484940280c030b1010710040c6480101c903104d55406640540980c0000c0c0000d9152007403188104400504101614148019212078074003500040e646000b14040100321079070b111000c4070614805c045c807610801000300580d598061101625010750002c7c5074071b034858140e0f00c001c40c02140307010049441c0250715130090301800d82c4680800c0001c10312100282c1c10300400704000c614603903a510840541c240750040c0800d5074106581c20000401508603954001da0000c80020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 273651151 1250 273649901 273649903
    0x1502120618271c0219021c020301061809060606110303060910080708010209030f0c010917012706140c070809060409020f0d0b0604030b0a180203030a0f0e1002 70
    0x3a5101c0201ca00d00000200303030322111034015000740c00e03050082c0107915546880306035900c1100d1056101c0c4d404c80b44400c600000051600810701c100941c0301d002c1c034000d0f00710a14680400c0e5001c0740001e00008240b0b9540403d20300480c111001900c07160f0b514905901088528855540035204518103401000201c0f40d000e59a4070000c0c0482e4494042c05c2c001503029000d02c55180d0140040e0030540d00e03a03541e9400468040d42040992a10a00601002d07050290000840b541143d07416503800004502e40360140100c00750728204501e09540340c00446032805c0c08001032609410603c00316070f41400c1c2c1c0b402d05408884a501108042c1c0c01c6802c14030440d0380b44803059468582c0c0221240e69503d500300d000982c45c0c03040764010f12005002082c202544408507020b4044888868400d0003c40402810070041c4d20031404010164640c2c070780810b1881c6202e50005078888251419804104443d40000f071660304828a2800010b50b200a03000543c2e61002c00c00340201001d0700c4006211030003400203 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 273652401 1250 273651151 273651199
    0x4060305031b03070f03030b0f1e03060c0a141303051207020306160f1107180606170108070b0d0b040504110a0b1204020913060501090209100e09010905100315021206 73
    0x103000c00d615408e03c80344a0f47c0d801010301d6400750041c264401540d20300d904540700f600b0801c600e8824013a4030b00040894003c0070445414012560f20003420f0307044c01c0c0c4036840039000000e000c2e00000310074102000040e010811507800d0b01c68282c4030b58403a84d441c0304040c9007440042200d41c1144006250039001a00078440d1150030405040402d40d60741d000d040d05240c51090352100302448210241842524869803000060303c5082e600e003260030300d03103007640c510101c828404c018250703104074410010710b000100545081425403d010490b81c403c2c00001d425110141d806076441192606141d00603d44858084000c011680c861030401d40908142107131081c0c020f1000c1c1c0500e04030400203101144011200060607803240c02001696181e1441d40021b4211160641c011a4a40c124490a0b13001e41c11000203603c0080c50940107a08029220010b0100502820f501034403642c03010001586221000c7c1e40f4614401006881e04c03404200c1050010010740a103004403501c00c1d0b14840c0d2100607001c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 273653651 1250 273652401 273652403
    0x32303010312030e0a0611072901060f050403060c210f0b030a111003063308011824060201091104090f080915181f050904050402060904060305031b03070f 68
    0x35164887d014500742c7e0303104250b402048031492026030464030804240c10a1113a802522880075030b1788814040d11138881c5010300c1c40122740203000401c0041c1158002c1082c41a4074a40308001902010034840c407003034060907002c0c04030f46032040b4010703101c4030780300b49244454100c00402003500d55488280d0790003020394000d80145e088400400c0d0241c001c0e040140245442090110001a0841c400030300b00c0044012003480b101c8803240c030260900c03403100603040c1c502540c6041351580b000786c1c000c00280404c0740b9141122180610390103030102c1c003802e480c3c000c4c40c0c0d0303400204010746589041030850040d00c0c80c0b03500c60b6160a4180000c10320314508000c0d081d40c0940041d80d2540e1010006481e11087d00c601d1150140004044840141c0003010212a10381602c80c603c00c80402d542c210b100c01a0490070700c00049081c00082010f00d4180c01c0b540d00980064611498156908041400c0e030351140c0017030320554400101558180c0304007036946112080103000c0c41c100a800c0e565214a07900c0180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 273654901 1250 273653651 273653663
    0x603080f0a120c0f020d1e0e03034015050304020a1502030c120c03040611011107060e2406040b0a0305010204090c090807080d0c0305120f06030d020106050d0f032303010312030e0a 79
    0x41d90224580b8100107c0d81c03141c8e81d61201241d02c000e2070b08bc0e401c1030032980381c1c1e0010960300c81445027260320500e10043c0c10381d1041c40c031082528025413401c032044e4100810603640000301030400034000080052400340c00c01d940d405580c0c1c1e80780c001111b03482c0080000e6030407822201002900107142001c025201602d1061910303920030707560541800c0c017600c2c0d5018850f51107030001408400300040c0390307c40c800c0c01c01c25500f9903428201840d04820701c00c100317038180d02c0070040c5140041c6491515a12071174030038a00400090304241c5a440301403ca81040d0445051699241001500c13107400c05d68035802450441e000704045400c0bd4100c545840401da82c18080c04206c0921804046c003030750a85524281310400a801880e0115028040c0c0d40284e44640c041e0250908450b110f40c410701920094403400b0b8400f88540c4e490f990b500f0300d0040804000d40800003209210201c20040741010901e07080011401501c0c1c2d41942000c40c10210300048050034189821a5481e12980c046844000b041d000b41e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 273656151 1250 273654901 273654917
    0xa020d0e0f0d0c0309080d0215070f0905040f020d0e0c0910061d0a0315060e01050625021906030c080a050405190501021603081005040603080f0a120c0f020d1e 70
    0x45130690780c8689a0308800320728043c1c80009000d113640026401c904030001d00110009485030503050315803003040c540c607a0005544010510641c01c02e90000510303102964801403404030700901071411906031815100700342c1c1058038001c0d05072034034002e215002803112158400142c98250040c003582301c148d03541d8009400f8a42d0380b181650f034035005039000b1038214031200100000b031507400005108900819080c824010004291820850f09907040810007130704039090b1aa521844040010307004408991001c0602500094030300544404401001c0f41d0318045111481c0b500086d081c0c1c0d0004143d480f03540d280c0345c2000041240021028040f0300d01f142e004800c22200d0900d14064419251180c0d503002015900c00d0030560700c01c828901c1441000400c10040340c0b0340c404c0109a88042c4030146c01e51609020080802c141c0c44020003500b5a2810b02c80807c3e1000c440786401d496981208101007500c140300391240940621108408070114944020a803000d1000c1421403103400034500c0c1040070036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 273657401 1250 273656151 273656153
    0x50f0a15150b251a240a060e0301091725021c03110f030d050c070c061202040f06050702040c030b100e15030907151b110402120a020d0e0f0d0c 63
    0x2001c030102049400042c003540100d211994110011801e5528551108054100708018488610308074003003100102100725141c40c07c5000c0383c1c0c84e48400c0c1140c0d85550780703d8003070300001c880d401f000c0e20703200221005a4886500030052031001d13070302c0010350b074104110b41402401640c0b501d4106101c8110403641c400240b4140c1021683c1c840c0391031411405104200404034006000406094002250101440350399981a0b000d030700350145584c000c2180d0070b54141485040d002e01c10380700290b6001100142802e07614100d07a41d64841541c494000328100260320001d5040c603000d4002000386508040c4500440c20021581c105030030840b190400c0030202c6652016038a42d20440424003003242c4140e2207081015500d526152244603c01e42c070540301c00c2480c100c0c6e01800189116080290324440c1f40062901d940448400010303042c2d40c0f0681c2003280804140303401912901503424101d00503181d405044810302168038485050b4000d501c0724550b0841e66400140280f108450740c07030725140904031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 273658651 1250 273657401 273657457
    0x5070e0723211e0c04080d020c03030409110705030703080411010e0307030201140f070c0806130c0e070c0206030f18070b250b0702030d0c0806030309010c050f0a15150b 74
    0x407480420218030043e0520043c001c01001802c143c805510940b1010443c1c01e200740e96a4108001c4290181c0050004103d0b4280544c880c21122082c41201858500203a8403282164088041200415640402e00085c4034003008000c032200401c0c00d0458a22980c2c000095a905071840b0003030400095400d44051091003800303072404541807000f43c641761916482d0207918400070307024440b000e101e2040060f44820072100620720054100e104100800d08101d03040c402103d004020b070f000c0c0070311a2109801078440e000114824481e0942c03c840381c2c05e040440038248250a510a903480c0d001c0d42c010302030f088402084401084211821141c00c00c012030780d81c03000d03d01801c00548110100020040308907000700040002c0d42480764100f02034441042e0550315180b090703512a4240c0c0c000d1003421a55401001c0390b400c014001c0040301c20010303000c0c41d140c3c50801c00c10003ca82180d07504210300f2400d0064001c0280f414074560804440e1070503c4211a698000d511424039400c008604e44550080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 273659901 1250 273658651 273658681
    0xf0201020c0a0f1802030c070b061519090803090f0d060b04090b0703050f10050d05070b0d1a09040807020120070b0306100804110d05070e072321 64
    0x405098007042e1990b40c10411944180751141508042d0303059200c81d281c02c614801c4031320951103030b040c0504004103a125a0060b40b4000c0500303400c2066150352130700e10a501c0e4054201c25034810b01c4600c5010902c00020071907030309544080e109603c01c0c000c400542d550341212614260041daa0314584024038140070004c0c0c030100c0303803c0b07400c5807800c03006500f80030240c544140f060801d41c4003445151115140944944800c4030300240d41c1c5050030301408030345031802100e48004d00030b1080340c25450b00d410b00c41c0000d40c8071120b84528140d9441034004141c0c04038090904080c4202d93310300e2039107041d442ea1105072080342402410032040a40d4192400350317074903031000c0c00d407095000c5800302500e809100c6041c1d4016500c0310311030b0105030110007850f445000c58510503036000c03005a6088586000303000e00500c40103402c0344daa0081100102e504a0300c100924030030250355407041d008891030501c3c1014000050720f07650403803104016000c9000c1500c0320f405000d18504c088100f482d03a5408d050b0300010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 273661151 1250 273659901 273659923
    0x40b191e030f0c08161809051006080d090503061b1c02040b041809050c0103230f06093912150a0506040602060a090c051c05060c030408070f020102 65
    0x81402c40381c000e215811140301c055a44550031554189820b100c3e07040003c440d1300c40c03c0115141c0001140150003550000c2c8a154403a104850031682c2c41c074801001d4920076003040ca00340d0300144070300c560950b100304400300500c0282c02502e0103081000e90f0040303100481a89a01c0309500140440307401140003881164802c01c40030444d102e6450b940070041640c441c0c410035600e082c07400310b403c484510602c43c6c081510703400350007080c42c9a00040190060449020b030215030041e50f42200000003040807400307104d02068210120f803031034650b0801c9807901d00070f80410b0390302401c0c004000c0500071010b64983c1d0914916004034a03550f01c0b9106001c984180310a0540910040b4144003504404001c0803160380011a103543c011501c03072050003c0c50050381315400c0141e2142001c1054802c2540c000c03000c2a0040c8141c810305031302c54021030400204440143d5595186001410078043c052140c0303a0028180c040b080d24600301a29026400e0042940140400b44062200780c00c5a008004074842c0d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 273662401 1250 273661151 273661163
    0xb040b150d140a02190513140a0506190602010e06070c030903260c0102070c09050c04030809040b03060405060703060e1528061107080105040b130809060711040b191e03 74
    0x20300d20030107610801740c0881c41260700880780000051843c58450040558200080c000441e89a07034020200f400b0b0640a440c25030061450140c2c4000c502550070000041d00194002150b00f855400036589000070040c40d0804000d0002d000d0400250f01403000011281c001c030b40da4020070060410700d180c10291000b142890000041e429081900640281148500a050107803101d80c0d00d4074240269403040750305617620740d0204028070000d124231009e410b842d01c025200140068071603000c0391a105082d20300303031010f40c480d404000103240d02d4000d10b000f0b401c03c46032030340503410a80904810100e001c4041c500c5811081d0304200204403009100c60320082200c00104920b549800250402d0700790000a10303140603034580492204e405002d0b4900440d400851280c031561000c00107449048480300444906108104458240e80e81c10003821540d4050503c0e010440000d0b03082004035281021070380d02441107441e4072401612240b20b950100d0300d800602403242030500550096030310315034100a020f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 273663651 1250 273662401 273662419
    0x60b0303181002060708070f17070306050a080a0c23090c130b040f0605070203120a05031e041505101d071403090d2a0b040b150d140a02 60
    0x1d0041c103a58501c0c10345500799000c000c5101c0c10b41d41241c40b09811501040401c18090228550314421480d00c145181ca916200e4851382d0280740a4040410640b00c0c04000398644105001030702e00a91400b00400180b03000748500c407410b9036041200d000c14410a2491301d25035000403400c10b260300e204000040c0041c203c00c040d14210502c1000c5421400840c030511160303090201e0780b04144022241640d05258121002619200303045640341e100300001c907018000d2400c513229056400000d45070314011034450b07a07260b1800080e003513509449049412403000e070040900c00400e00100c4003002900c003801001c900c2e076562031407007200700c90581c5c4040010118000f240c0030802c0ca0300e00580c060651551550f5543c08052040b4450b804141c82c1440281c1140c00d0b403045447c02030460f03282c0c100c10005204286d4203c8101030304501500e6074166060580381080108110031800d0709603000c51558400c6aa0544c8a8085080844403020041c86540002c010f0b07402d81d03004000500e4070560040108803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 273664901 1250 273663651 273663667
    0xa05030f010c030e0703170a05040e090606011b0f03030b0402090a0b030f01080609070b13090e0307060b15090d06090506040305070c0806040803040303020a0918060302030705090105030a030804060b0303 89
    0x8001c060194070702d80001c0c0341140c041c01e0740f0f030089003d00840b904400303e40b01000c9103a001c08a44d03030001d03110380300780282040002005030140c07640030312561400300608501c1c54118005860f501c0008021952a1010024400040d10f8201c0b031403101c94251138000307458010100414000d208000340303075901216401001038003046140046101da81601c54071304103666560b00d2030390b50b2901551100c140c1d401c0356005006c96901480606103d04004000200c420354501c05401254040c1404a803075800008209090240a024000754901d0030f03241d541c03011182c0056000ca500410000030300c503290844502051000d103401c000c924607040070071340d80e2074201032030090f200f503000c80380841d640642c10b8800070310040f010039000c1c841c0b9007000c5801c2c6183d0352682e0440c0254032560186050002c08000444c413035083ea981064a403907400c10014100341140100342ca85441030b841180f142100d0340050005880210301e03da061589801e0800c0c00707031075034a048000b80c401500015014030020034115 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 273666151 1250 273664901 273664903
    0x4090b0d1e1205040b030a1a0a0b041d1b1c05011203110c010806101214160f05090103020901020115030c1a03060a090c090b0c0d03050108011b08070c051209010315120b060a05030f 79
    0x10444140c07601400440d41e53316021030700d4a00489000441c14804100c6520240c03248004006000300c5c00e900031800114000c0c0501200d1085e088070901c2544040c14000300b42e0880c105120517a00c2c54000c00e800c0540c040020704500e00184054020214600d850000b5030280880004010b840e28061003150710900b0120b030001d50455400020166005050b02789a00600e40d038070070701031503a1311680380c14044c10055000c1c1d448444034a0442d9a50703620380d290400700020b200061b51194007102903581c64400500d2000c0c0500c40701021180341041071112540e200c442d03104c122203200074041103c5180131000d540b0315416a00a060304480010407130304041c00130521504c0d1100c540c40410280e42c940c40742e6422505100808941c0e000300082c0c02000741d00880510750300505514140080c21070907950700341041d4018400344003418020404094035a09401382000196a9801c4001014909540c0300c03540c0c680d801c0041c00c100381c2500800c0e90354680850000203000c3c040d041f0749540e56940c00c09 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 273667401 1250 273666151 273666157
    0x42102030d020c010b010905010f050403061104080a050607031d0601051014030a0f0f0b06090d060b060f0711030f0a1202010b0406080a0606051504090b0d1e1205040b030a1a0a0b 78
    0x241c6c0c0040d40ca10008551036001e1a400c6200d04106c1d903510381050306595420b002401300c0900d03201c02c0c02c0d01344000605c16004101031000103114002500c03141c241410003406848105401550440c0b4000a6404103d000507219045444c111081c0da00090030b488282c40800f5406504003108074000104100c2c1134903500000c10901001800300503e1028021240846044081d5161b0091007004503101070711303060a0560845002d48000a40b140381480010050340c800d23009140700342c0340450786000303025801101d2240c0c00300030340103000e039030107650140e503200c904420008200c500e400030f03454086403013507000311042c03280900200441034807900b0566a0343c0810038229803140c2004000705031400c0c102100e0100030b140450b035504050900c04148054100300c40c00d50741100082d00d0400c00b04075951a400544425807801000c0c41a03142001d0700070710382e16010102444010001045078401080c1141d6020201c2e01c40042c50480c1c00c400600000c1744402c0580d4410404100441c4918210000b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 273668651 1250 273667401 273667421
    0x10521040803041a060604030f0627060e03280c1a09100c02100b01030f09060b010f0203070c0504090503090a080105071b0203070614040b070305120f042102030d020c01 74
    0x460040003002e13130314402a2041c210f40e130980000c1e00b84010000505411303681483c0600c2110b0114245506502c0402150742c0c2001080e50110313912640c009104991103000061190341000d589091040010803404041034240c1194407542d83c645140c0c540d215000c4201c440d40d10940c10050300f8598511100071300015550502a0700992049044001a503c100b000c0100705402410150140c1c130f854500405a0520fa07070305043e201c3e80c06140000861140a09407445004009140700e00d81d00014603806090851509541c000c102d000b02062901500000310360080300c011880c2000e501e441e038294041d031010380e604450606c0300883c1c3e2442c190000d0b0b2041040d60f64542d2986010311011822440486000e50150000300c03050001910138440c0741f08414070003121624103030f9200c0050400b5413044c0426000500081110000628900101e9030090071815003403415080c1904e5148100040d10365500c072201a14034883d2401d8001c1c020780300e4041c11054119102c1c2400ca0f8001d01908003080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 273669901 1250 273668651 273668663
    0x9070f081b040c0210150801050a1413080304020904020a0306090b04050c01020a150e01020f0c01020903070f08100b1203070b01030b010501090e010b030606040302060f0a08010806010b0901052104080304 89
    0x1c4018050502e840b0380d0036102c10a074000c0c0259504090918001c146a07140044881144c000200e144c060034002c0c0fa000d0003070080005114004540640e0005074041c0c41702645079081c881060203c0c0b0358100380e940054048900a5094a0301c4c4000744002003a68002040c13079052400a03824800d0790810140310342e010740282c56410b007180d0012611824010701c010909150203211400b0a04103900c11040109030380300043c0f030841840c0c40800030f500110600d404c12303900060707045040c0c1801c3c41154002e11101c00c8c6a07a1036402c086030540c94000126000f2041580c50104901a54641d4014800622001c040d0b90707880d0450304102242010901080e035007a44c0c030340700006642d4494030030b242c1160403001f06085164204100080240d001400142d444113083c0404000750b9500e00c01001c480d00d414007a20f41d103000141025040f40c00590240c041a00000010025514960203c1e458042c0c05d00e0040daa0340f040342d009a80002a038916008100181c6041100300140038001710f00441c0684 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 273671151 1250 273669901 273669943
    0x32906030c030a080c010902060c07090e0c150307030603080c150c0705030a0f1403010f08010c020706120c09090509070e0c031608060310051614040e0403050309070f08 74
    0x40149551400c140220981680c056001040401e0107080544140170903403001290a5820b07070006225a0418610559a80c0080b10100070000d240e00c0b58005141d03c40e00a0a18001c0050010703e00a00c000000f0013590800800510a58400d6212001665220301100d40700e4009038011640c030046003100c40301004094010900c103078285d078255a00d81e0341c410f0042d0b1030444417590865030030007010088014002c4500340d0081492215010f0741c082c065410000d1115890510518255541d81c10b000c0259049000f0078082c041d800380703000c0382408485c48045801070840380200c0e80d000e030320f61000700b20520780002d01165a20100300242220128054104c080d20b40602d0081e240c40203540700d002e501c681d04c001d9564a401960010340c00300e401000d82c1e00c4408200495800e0b598100d501003440c03819440f003100c1040d000160f4082041a80c01c06504050503c3c801c0c07c00d5004c00342016050040c0032002440c101030400010004d01129604e9100e4507a542c1481503441100130783c44911b020b661 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 273672401 1250 273671151 273671161
    0x5030a0f0507020a150903061802040605061c050c07050a060e0c190e0703020d050f0f1006021e1e071d060607031d031212070206062101060329 63
    0x20720181ea00041c1c00404102c41c13545059208424820518114800d220108600001044003403182e0401ca82c080144042c01c101c4a104201c211255034000c0d074031400e01400301480e182551a024011810001000a11030700c0383c0310b400b4120300505100400503c00c0c02c80308003c0100d1500880104007002c401c4401c28054002003000e10100401c01c070740d4480c54841c081050214800300036400203198240107241100d05500041601c0b001c6600d0b0320b404400c1c00604c40180e18904000b40e000e500310010316080c41c2013410007501c0da00c10320712071a0000c5403d211503003032880c1440b100c240144400050000741103544541500ea00c100c2c42010b54008800030307040c60700302c419118103115100c02001c003490070f81140c2c0c06031612600008550038410f040301d58080340c0d8400304601190004081103c54032001000024000792000410480440d0010400e000c80750311002e12840c1d01200c581005004c03104039141290050001e42d00240400c400f80004410b9001c880d000200c08000300c6881680e22707070358 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 273673651 1250 273672401 273672407
    0x6030606050a03120302030c0f12060909060c0412140a050708010b040603020d2a06120f0605030a120c3305012904050301050705130e0c04050d03051605030a0f 70
    0x907440007900c04208130b41103c1c40244640e00031544004450b103810f081201d1608080f0113900070070b0704070131250505424030800e80741a110703441d030111700c140c0103203118605165500348600685c4260301d0140001710300c400400460030810458030f003480c401c8030280706450400a6584400d03200b254015480c1c48003403010f40c1030074014141580d40240255210b00b1907640d51340d000000541903010300401c2c6110343c840c602503840110b002001290f40c0c602c0140b8000605200b00d4110881d081540343c0b802004000c01d4501003000800c3c141c04c1120644e1070000030300c0a83c7c8005c030000c8014010b0390120f00d52b4011820601c00703030780700860141d4403100284840105504480c2c0a0240c58201c1d01900d03504140c80f41004111003103411406042402c05075240e0100707080d0344095a000c1d012403004900d444040c003d014000006246581458542e070070301102820080c0300300c0c0115030141164107907400030f260041c411134080b1151801103100d100d00c5420a25129001b0800f1200015040300e44042030602c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 273674901 1250 273673651 273673669
    0x60810060c150b12010501090b18040803040203030c06040f15020c1b0415121703070806060702040209090709030302070609081213150c0606051c02010f1e030603060605 74
    0x300948070004550201d4803800703904840c501d8a80341141e1503605010460701e5103850803414000100c0082501d5040291600982d412114002c7c01145c10603610450208030621854000303402403071040c2e072900c890000c05e003107108410001d046031043d41d0500042110b4410000ca89134017500004c24080f8070281014141c2c851400781e8466607000c180048055400001e02c08000b1a0080c0f000481d0141720215066940140e4080f41201c012000d40c1d10901c04c0c000111020f800c4d007451114514903000b40003034103a81020300400c1c041c900104a080c01c42d01c0d26030454002020040943c6414030b48554003c012500c2030004500502901c03a0014100d40100e03042000c0d120700502420709105215401c800e04d800c00040384102419004000410344039900302c06996810301d5448440e001ca0310708124094807119440a405100701d01c40e41c0c0500d1828030803800c10b80d40d0910306003031f0071545510210b034817140545140c1c440c0769000c49074480554055101c6801c0340c0c0b1694060010031b40c1d500401400107 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 273676151 1250 273674901 273674909
    0x6030803100e010603021206210708060603061303080403122702010e010206131b030605070903200906091f120303050108070303080c0309031e040e0a200a0c02030115060810 76
    0x403803181f001c500545420b4010b428a10a00e6041c02c5455003140803852500d05541c0c40070400746c00600038807015090900a041e0b000348115130741c40702000b0543c0c00408200b00140003404200310101d0071a40a002c0390818808445d450084544d080b02d0740074068403481c0c0c42d01c2d04a0119a8090000a0301c2d400411070070300c20200350130a5124140c854841d08a1022003125042c05103018480220005003941300e114016645962545407903811458541c2c0c804150700d203054007001c049041c081069440d1b030800d03980800140c490001c20b17103814416208100c408007003d99400240d01e80458204000c00b10344010b240a59020300a50744c0e20401b55498180c036000160000e0b9982c2c00141001c10018001c680262030801100c0c075008001000c07442800c00030b000d001860f0b10001c0c0030010341045000f4640c00000d8203108000c4400e00c00d0f0340940140340500809092100806c07000d03921030044400301e0a264000d4000d00c030008000000700d480c0800d6001d0380c0041000702000c01e038004c900d108008266 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 273677401 1250 273676151 273676177
    0x1180c17010626061e1501050f07030906170f01050d050c0315070e12061807080604030e04290f06091507140318010e0d1415011707090203040606030803100e01060302 73
    0x3a181d554070303848003400080c06e1505100082040c0000300c0c00200080c00490f00940d20031003c41d042c004014118008000c80302d02035070008060211190458228a0458008a0306110300d4181c1d40341544c03d19417840d01c401c0e410b0080c015140e44400c0310003055841045169500100440701404115418021241030801c680c000d10002d201005e120100380010340e580000c41c1e030880d6880b1200d5103801001c0b01e0480008850900001150070540102c6d8900c19000091900b048240c132101e0b4022000c1184181c450040800240b0f501d40703c840444c0d010600190060b580d5218905c0c41441d075500c0282c080741c11140055102e0000a0003000303072295400122010f46816040500440b80f01c4504035052b42c0c040b100c44212030010f80c9112001150740480000f5280200808144641a00c03050740660107103100241001c203c48401b1030a1815203501c04001038507030322a414080c000340941e4100520380c03200001841400700f2040b03011070480724451203480c0d0a0b0b0300d403503084041c1d0040380380020326 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 273678651 1250 273677401 273677461
    0xb010e0d08070f02060f040914060103020412030807030608030c0c18091e16091b1112030a060803031009060603140f07030902060a050403020301180c1701062606 71
    0x2008040f4510034140020b080a080c0380c0b00b42ca5200056205070312444c940f60b624451a40710203041c9880d07591060342400d0450503d0b1603c445103d880c400c08100804010558001403982402540540003400c242002c480d10303025040781440d502c00c5108035030392282400d1a48090a00204104a44a0714142c0040c0204054040340044401c0f2900944045409511030034503007a6144c00041c80200005d001c0400c00b820094070030518004003425040c01c000c2009612200e00100251000e614415101015075070360301d403c480c1000f480950489071003030200009011180fa80711440c4025614280b808100ca55a130b4081681259490420b005250351540001200c02101403007060f8010003900740850024616400940b4980c0101c034040003040000c101802503003030034490443c00400d0043c0f04030f03488103a500c0e89a0780342414403540a8024264032401c0010200b0742082e40109480201e0300224070301d0359480190403004c5800e000380b41c81084000303442400d168100046002d104008051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 273679901 1250 273678651 273678653
    0x2403111903080708090f040c09060c1b080c01020d03020307200c0d0b15010305010302151e03010303030903030c1d09090a0803190b030f06060103090c050607060b010e0d0807 76
    0x488511801984500551040000001c100b622000b4107a80340310300441c9560f00c401c1000c200c2d25010075008140038524104032325a400d47c000e081c9500341c4078a400c14018410081ca004032145110014000c0501041c0c10000342d50750380041c25010300c1e0750903002d503204042101411004c030700084440e6400680b8401c4045942d208000e14524400850400e4881e17404400f808190016900401254491035100402040a60b4001b1031408d10a09190030b01541d45990005460820340065403e4401710009002100d40c211482e000d0488545ca2015922581d58ac00d015004245400703040d40824144010305100300c0c481d4001d03000e135000c8551109245640c20060001440c00145406054070405c04c8800c00b240812026604c43c101d80c1171441c0e0607002ea1080303201074070b0400d410700d070280e40102211568001c01040c041d078000301c203180018407840b007420401600400d5601c004c1d0800000a101414482950421100c81e002a21090300d140a200240450b00d03003a083c014007000340500c0094 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 273681151 1250 273679901 273679909
    0x501050304170a0903020f24180d0303020c190b16050c0304030c03060b04050f011a09040c0201020a021c0c390e01120809010f170901240311 62
    0x2541050082c1c034082040b220354207801e04103620246040c80468043c01c0c04000b14900311040704140441514501e0b0091030921204000040c013031644010700001050098102c4000c240c01d510035038004100000030740c0d07181405002540035010100960007842c07400e401e070842c0500850603190703005900110613a10b01c0d84412043d080000c603801088010400e8140000301000900051401200e015403001c1c591328148080b80c2141801034041c0d405d207000c0040315614172411034110f42c4824280e2050070524102000c00e489a070b400541d110740b4080b034404036940d056000e0105120303203801312180d001200c00408964111000e4000000d400c06030a0740002c0c04900e000e2902c82250b507009604a00200c10502c0107a000b075040c80a0003802c50010041c0c003030000c0c441e500601080144001160454642040606c00e843c1000d05022049a9012050384074100081d20018a51f41d01011707401d03c0310060b80641039000a03003042d000720b003905120b0140f0402e1034504032070340650380d0940e8451910070705c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 273682401 1250 273681151 273681157
    0x3110f01020109020a0f1e0501052a03030a05040629100e0603040b0910050105030a0609050a02040f0218150d0c02071706012c0103170c0109060218010810050105 71
    0x854115500ca41c100300058981280b2007000e03211100c2d0451202c4c0c201403600b18909020120310440201441041026980002c2142d0f002c21200140d8821000134444140429180d100b03014401d10002081144c4031313420b0750040d4007407403080900388080b10310f20680d080074280c60902c01d4031406490300c0ca00d1141c5440e0400403c4c8071868108802000030290014803d6002120b0035a91220940b04022100d8803c1c0403c49030003404801c1000103504110209a80e0302e1181d000801039039aa00101e41800000c00003050b125030b00034401e01c401704410311440f0207034101d010003844030780003c1c150091f14a024000c2007a620168480107050105a010040150080d0144071003940580080413500116031450701c0090001d0000910017545044144804552100c501400d01200f8002c04080100016800c604481d080f80b81210346134078500042085115007916a04c4a41c60203060b807042048a401522080c002051540641c404403001982d4401d01100e801d80e1888200308203002c550b01a01c06 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 273683651 1250 273682401 273682429
    0x30711010806190b0a090501020607020a060c27031502040501170c070807050f19050d230a080405010c080402060313030302070f030e120115170307020a0b030103110a0311 75
    0x1083c0c0007001e00703080c0d075124846150881300c0c1500000558190454200741010000c0400381700500302440c080400035101e9041d01e00083c600c644a5581e0000c042c884c00d401c80301d04030000d021401110300d00381c00c400308100ca888221200422121100c03001e40e900e01c00d0b20126a410384603003100003081d00504008100061514640d030000b0303c4500041817098000e4104140303e41d0080541d00907800545183c10300408000e072190391005503070300000d140814800c030601c0e41030402c08100806202c034450050b025003802050b841d03010608200700d9512030712190080b40100020412008100d0049640d02c004560203034008100300041140c11107400d08441c4041d02900d0018184007444d5038003501503280020680001c0e01012210000b4a4043c50317403c614240400200070b0f0130b0344010a04080b040710322840c01c0f40c075043d040c4a042d0b05418000c403845558018150001c503512500000c0564100380000d40c0c0e103100039002c0004908200d01c540701500c0c0c01100341c14a425a4030200b102c40054551 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 273684901 1250 273683651 273683659
    0x20f0709091703010308031b0403020d060e070512100501050609010c080a05091c03020105150f1903050109080309060c0a092c0705031609050f0d0215030108010203150102030711010806 81
    0x40d00c00700082d1030286010f1031148040d00c0ea03a050401d109489840c8014140c60f6880d01000100010b0381d8401e210076109074080b0002c01c0307020411076840d0400e83d070356000b01e4111900b10540b4015000210701c0040501e4018010000360f42c0318000e001040c028205510b001c10100c82d0b01c0008200e401c0003501d041602c0c1e103441407a01c1e800704041805d4040512400180b6000c40e0180350400d0340a000e01544400c00c4102009280105000141042a03455000e4080c0140104121380107282e00c070214040e5802a00901440c0c01d1840d00407003940c41180c5540d1039029040204030304d4100c94007154138424596888907001401c00702d04030284d400c0040100c0740700d0b01410510154603c003912141c41b4a40d90785680d03407649000511519064a800740d10010404442e000384610b80e0781c540420718002c029100281c0268052010480ca415410703228200c1642c041300008600740150002c51003501024012100b00b08010300590303481c06426401005004818144c01c45035200d4007056520034030040c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 273686151 1250 273684901 273684923
    0x161b050601121b15030c0503071409010e030a0803060415080303041b180509060114130c0225031104020414090408160507090b09070801120c051e040507020f070909 72
    0xc280b0401d60480c4c0c40360a04100042c690b088058242c482c001c072400c000d0801c00d140d1300d09075000400c1c0680612032800d400e400464104050f0b4401e11380744e06880380240440300c80d065141000c1c00349400c1290b829104a003084e00504c140403509190740201c54400f4001c604680300d95850180d60f4902003000303070b8407149003a80000e01c1c0051b070860000c15160301100080034185014814208a0141c001601f1081018211041c513168851307580800c81c86028002010a4058012814002c075400b010169450340d080748045500203648080403240301d440c0b40c80c4010005410710050f4000da21618190044094001802d420070b015041d0381705110b80500c81c40c0500039a010400c920303141c2c40a07a000e41c000c0070f003445800142c0c450f245000504490641e028542810010503804050040300c4450b40c9007101e080400c0200c00c190005000001c00544400e6140c000030a905601042060310940c182004a144d1600203d084102d1040490141400c0c505221125010300300c0e500048914848103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 273687401 1250 273686151 273686183
    0x708060a20030408070308010b040b070318030f140f010b0604052101020307030b04061406030402151911011407020c0f01090b0301080f0d02070b0409050a0902030105161b05060112 79
    0x80d0b00c0342c4d10840440b038494200b410001c0a8000507000540f1030b550810003030044100b24815207040c1541807522011000c4100c007614443d02665200809400c140341c0a1404c100220160346528a00c00086400c0d03415408005c9080e10070780b0040c1d84d00810100000c1c012414842408950315030300c44070500814211032002407c80c0c0c030480d080c500013551400103284c689420f02501e8010000865448034480ea40341c0011604c3c400a80700034810f13014400192100c07e12103091320b0030042c4c180019584502c48610142c800030300400c4a00d030702c2d413801c42840030490b407070f4205a000300d000d40c0c000e0005601e14414081c80d20400d050081c103001c90500006014442000103602a1000c100075101a2180c140105d1805000650a0042d50001300c0f007800f80c10b40100c01d0302c007140c4e407054010841d51030385030001c0001c00c00180040e4040d4240001c0201030305048080203100d840c0c40d039074028028440c106684400c001020024459000000104010342c5018a01c045503402905080e40003004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 273688651 1250 273687401 273687461
    0x203071b03031d0c03070e0c03012105120706050a0e0d033803060618190b030d0e0a080304030b0103110402040510020d02070f210503090301091110020708060a 70
    0x65204a58035540c40b1300c50080300e9040c240610f03c0103001041c13083c5128106464250b469000500881c202081d05005003000d03c01d03900e4030031034a6a0001c081e24036000d2444070500850340000320681da003909100c00304d0027000541c8100c1c010481080081e245850705110200c019100c440452001040400c0007001d410a61605860f2000c46040f08110400b6201d414507040240041c0342601c2200c0002c1c3c0440c0c114241103203c3e0340a176080c01042100c8001c100790000410b50f025030280c25100d240200789034507070040b200601210b0102d8034a40b10320764071080036640384114000280204000c2004000040e045030190314811002480035080980311b40105801520071304400c00142d010000024800da0103111a03001303000100c800c01441810301e522842205900c500014054481500c0401440700520681e848900e0007402401041c0342410808200103440e00d04c98070400380076800301c0005000007500c1c0704441e4008003074880795441201d018000d20100b205001103e60354500410540c0c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 273689901 1250 273688651 273688691
    0x80a020f0604050a080a1103010c120e0a170903100c0f1404030b0c040603050f01030c03150e1e0708030405240c121c0b06031303050f0a03060314010203071b0303 71
    0x420300c1c0003071011b80c6041c10807030030346e4003d80c61f03007402a4500a02d00d00d1060780704802c2402000358910211340e03054001300031864146440340191103015074880050104840760300516031054100d08030340c44543c1c00c01c01d040480f220400c00f8401704420403600c2c8039017405801240c2d2441c130032146250600d6601d480740400303080c082f500703400c2c88540000c0a2101035014071072075070000814001c120303541d819545c9108103203841d8003021700039403c0300c4440132010320780e900003100311400380c0705a81b03c4404140b00807900c400c6000c01d03043d15000d805c00100c0c203a030303001044d81d085440007010705c0c01c184a54036170840300c2c60f440303a0400800c071400c000d11842d0040800c6982038041c403444030b4640d500503802840c0c01d509441d000144d02c240c10140c0c01519a960303141525002900c401e20070b0303003034103a030b207010f480d5449483c010320700c59000410800c00e5650554028402c481c041d070f030300e2611380701101d0280f8201d10044901c0d2001c51008021b0100b421340351441402d0f280d100c0d0a000800360004202214a45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 273691151 1250 273689901 273689909
    0x1a060102301303110918030a051602130b0f03010905150c07060524100c02090a0207021c06050f01060203041406090301090606080d1d0d03020a12030203041a01080a020f0604050a 78
    0xb03040302c1540001d40c10485082c60340040ca41e01c0814040c00c0301303488243c03607106000811003048404100c51401c80842605881d4090f401800380d04058010a03311014100421300d40d0711841105455840c80d00b010f004100da80d03980b007006040480e4010905050f2154003408102a000061000c0c50006046128417030088030ba00e01e600340b000d200190b5100580c0d90741c0040c6070050000344000d500030343e006801445607540c1255801d80595481110748000d008190002c1d501100c12440d100313501c0744800f003c41030a4081c0000788141c7e41c541030003146581080c400c1400503441000204442030a0b5000c03504002c1c00240394078600f009040009007900d580c40f6040d2101a07a80800700300c2e00748100262681403417503040802000b80414407101840d0005130004d0b01900b05090040201071003800600380482d40002d20403000700f40403a009000750000c6404035190110100c500040004441070f881c1241e220030700411201c0d456034248100c04150a416030b402000601001c1079560b90203490720060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 273692401 1250 273691151 273691163
    0xc0f040f050406060912111c060608010c030c140906040e010b09240406030908040803040305060f07080f0c1e0c0c040b040b010e0d03020c04091a060102301303 70
    0x1604081c204011151075500150900c0b12046080000c682244001400c142e008140c61400311101c80100e42c151600381d0f030a569003c100d800603000c00001e68040340907912548020040c580903081d0580840b030304928905d003c241010718066042400e440100101074001d806e6601300f40c1d8a070350703803105481d00781c01a49402e80e0129145d01c150a004181603c0241025107084481c2c0c0610816411440365010301e00030952504000014004200125801008140c003100c0e030b119500e05242c0d845080586010f888607081101007905203225402490184800007008100c1b9201d4000c00c0c1c90715442901100d11540c41c445c0c8500c60508104090058000f0400c0540350f001007803000c11040b40c0300f103041c15216138904040b140701d503640201d1040c1e0800c002d0319580400d20703c1d41001d80c900380b89042d0903640541030184038020003144000c4101041406500801c560f00c0309401aa00c4250480307004c2c2d450304e032541d0304d204d030280350200500700d940d032401e5528500b00c034080b0240d2400405410984036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 273693651 1250 273692401 273692429
    0xa0e0312060907031109150f0a05070c090506010e040509010f0e06010501030c210b0a08011109040b1008041e0209010b07050c0306090c0d0305040b0c0109020103060902130306050c0f04 81
    0x2e0a10b0041c0590000d52480c041020b1400c6000c00000c40c0605030000c0d00560044401011050702c070012214402c006924440e112241d40700001c1807a807240e203040b20307410184000010200403600030640244016103880d58400005c0e8240802002b0050040ca4a50740f10040141c1400300d0340304552100750354034090540d0350b04001c005800d0b00c1c015141e103000c1241901c44400a440c40185100300d242c1c00030b0000c15000c010301e0010f1010034460f00030405952030710f5503850034130304148000c2c65042415a0280300b801c40900400040550100e490008a255a0006000a40404520862205c09440b11810390080d9004548080000d80010303c0d041c40000d514403c0c030000f0844140c0e50201180200079a00d032204030340740c40d0304c0c290300e9142c014100d0303520010030140118252009008407400c801d0b100c0108200c1c9034082c040d900300590100b40b41900100317140b55203001f110020b06003100503608103413071b642d00c0e40000e20008001602425051110305150306079100108001c22a0040c1000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 273694901 1250 273693651 273693661
    0x614010e0907030b0606131706011e06020c01111006090207050c1c060e010609180b0703180206030405120c0303101d011707030503042c1506030a0e0312 67
    0x421080c06005200e0030342c0034210410002e407403c0300c1e0725031060b001d850503502c540d4410100c001d0390740d041d0040c0c400c56080a40001c0580400900740d4102c0c0c0301c0d1440300911003c0150148a101031500034900183c0008400181a50058110504d0b22112000301d8044801c6003032140102c0d03080c1e030411070b1066000a170607000d00004204107281400304980c04800c2404148004241180c000c00080015856241a83c02c144080d44044010101228184400322902d84003c550344c1e0003090448114104070081002284248a0f065040642461080f078661203a020010b030340e00b004008031034610038a24207510f0304620b540a041c6469100000b582c8070f090040c404800c220040d00260301c1c2e1104103610024000d064440c46045401e1800002240f6195200c0241883c1c0e407608050094407000500050750b03036003c03d4901d520f641203111f042c001c0e2554240d40107402c4080d590585121144881a400c0d0300d0030310029508000c03100310021307850580c03201240c115081140060140091381080003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 273696151 1250 273694901 273694919
    0x140d14160902040b0415030207020a0b0703020d02070b0f0f13032306060d0f020f0d12030605010c02060a2a060207020f090f07140c030c0102090a082107030309061401 73
    0x2a01414108500b507003464107011554004e80550f22403a606800145034812041d4004e80c11102c00720780190800180681300c500c0c80301703254800f44040300107118503a000d485052011804000383c0d10005070051820314100b08420740d642100e0125a8404010080e240c01d1340d0700100b800004510070300c1404260f909524221200f42015075070446250000400c004155807040e00400b40154042e4000c2150300b0240040f6000900d0041c1e41600b10640064050501c5120071180400b4196a6410720195486500440d602544104000e41025040c4135a61505c0e008040841000b100c0e9041c44114182040905140403d503c0e03007590070f182c1c001111000d50524490745030030007405440c000a5410042d104000c4200000c3c00e00040040300350006200c4640501280d00c490403080c1200d4039010b0f42c1040314000d61105c036105d4071454400c0c10001d00380901290b91003400c5001c4585650f400350034202018a60712041d0202c00b01541c840180000900030705c02c603c3d01d10343e031401c42c903e1076040030280 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 273697401 1250 273696151 273696193
    0x302090a053705041404050a08070c090207050c030705030a11090c0c100e0c0d080d05041e2a03020607060b0301020d06030f030806120307020f0f18040309090507050301140d14 77
    0x80d401700c121000800000c04e00015101c0085540f00b00d280b540ea03c03190626241400d80c68225034402400001d002c4103200c40094602c1f203814044050741e5260340e03900101555044000c0c8010080404400e0030b0695150240716290300c2040c48013440d15040041e2040c07810f20200382250b00e400c5546090780c81005108020385465080c0c1a030703d010b244941c2d0348603140700e03005201703240b00c0e0607844100050070090f641c1c5003082001e0780c50310040d007444401e10b0308803000380d9019106441c00b56481e49502d08081c288402404030f0381c024086502d8243c090f00c50390040d06200003603542640d020004104d00d0380403407003540b0040d4024140605001443c0c980180303107510140c0542e10506061020340102035010007140c407143d030304844030451305000d4804907802e80e011210803640450315105100e0350313021a410340d80c4158441e03640c5040682d242c003184d13800c5650658038203000810500042c003406c1d0052039a9040046d00400880c0490001c1e0b507400141030034140070720342da9040b16800d034245864165417 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 273698651 1250 273697401 273697421
    0x20712180b0a0e0d050f030a0504051201200a0c0c060306080606041a040f0b04060308030403081303020703060e030c010f02191b060914010e0304150302090a05370504 73
    0x10451a041404800400c0401c00f1000d051081a40c09000c90401c20104155031000701040207030307a00d440403102c0103402c030b8005114285c040d44082c0b590003800f10040c404d400103103c0c104c40e03000981c1c104043c020340940012916009002040d1901404130300180102c10040c4083d5401084d00c0b41040c0c0c00506018000e040c1c98000e600700301301e08596550342c8042000301482940d000840c13919010314040940301460b00550072070f180c90808400d11000c1380c0203602c07840c000d841d002490f4a410098207480e6421090250050b0000b501c02c0c400511250008000451020304403030400b06188491421200817030171594081d5800a0000c00b58194610400316420741404c08104aa0354080d540c40c1400f040c242c002c020030741d80e02c2c0c035804000d09a0740721440d010f1400000c101c2100d010785010350b2076025005109000f9120302c047c900103480380c021203401000c0170b041071100d2850300c0c0500982c0c0c803400c0e551041c0780b22802a491807581506547c5a02101e10002c1c3e0351940c0d01c0e08052004030340741500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 273699901 1250 273698651 273698669
    0x1a0a0c0e010c02090a0e01111315081b0d0f020324060c0304030b06040912090608010905150d2d0b060909030f0703030b04020f03150a0810050a02071218 67
    0x10160001d40c4d103905001d580481d09403070124030854004491030042c03d0501c900ca44044000c55441c42c0d1001c09903640e4151030941e090700c10045002201910041801c41380d540d8880c0800310348101e2401c420000e0030050606100100d940700d11825120240c0c0c00443e00c40d80d54102018200341c464030b8008140d034400b00c056400d940762031681c4082c65280d100d41d00001c1c020807030400102d40d064603654406884503410000f1107003403040407031000b00384104a206201c00509200000314006440e8171032580501480910310210071110301c10311815180508042e01e030a400c082d905002031514800c14035101c000590504141d2045140400750b03008098050790040d04000c040104500b00041112480e851030740040341c0b10002440c0c2100900075541e251900a8000301d404080078407010013460143d803643c00011030004901c0d00b4459103410030301c24aa00340e480030328103007641ca025a1103641c2181c0f46210141c900030302c80d106d8020748403659566800190000c1500a41330150003100070141000740 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 273701151 1250 273699901 273699917
    0x60a090513020409021206010303090905071b0311070905091f020307020601052404030c08100e0c040f060503070b0c120a020a080a031d010f061205030409091a0a0c0e01 74
    0x121410707071140350411000f030003180d4605103a000c1d940d800304100c03118054081101c1040da102c4c64004e2086ca02441200246070038040030441d090701803012000701e410003905070b001561003928111240080318010798940d00500e40d001c1006076150207050f110314481d40040149d81d103441c401861170780b0203603101d00c4205c1c414802d0000442e404200141100c00403585040d520400d29136004420003450781c4200d0104000a0010030040c40541d00004c4039120385c04d8a441d04541141c24003a51081d02d044652600300c070300b02000a1400d5840184400c181c843d00243c0c094481c0d012900c0c1001c10b802c11800800b0205a801156404001d40c903110b00c00c2096490501091740006980c819030044000c00207280400c004018501c00c1e40300b030000d14a42c0250407613200396000c00e030b40200051103251444e1070410801040381c0503c0c4000551190f4050011840c1c249007490310b000a0200b400200c0701c0750329002031b0888000d2a41c4015006044403140081d01c5e203c5034001601940702c400500e07040c40914 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 273702401 1250 273701151 273701161
    0xe030d030222030230030a0807080c091008070509060f0c061305030d05070c0f0309081c0e091e07020c042003070e040e010903020303010302180108071203030603020a0b03060a0905 79
    0x21900a0941d0486008441c0c448040d1701481e0128032100c80540640c0b00110f110b511441e03000d4245402450152640741c3c05884200344181a44034503800c0343e41241c244154003040a01c501102d50344004103280c09804d10103041d0001c1e58a40c0a509984035240002c100c0740714a56042c0a45a0410122040500b5141480c3d40700b0b03450340a80d5514184099594002070031081c01642c20300701c02276001c030000491888a02c0d029080440500072a081882450021011040c41c203101c0d8415007020b0f191420300701c044404012035200c008120041603854001048141c06c850004135010b8120383c2c01821840303040c9030503c400c5403114100140124404010b0a03042e4600c0c2c421240c010140d803401180f0b11151030003180280c03030a841b100175558a8003c2da1424982c2c044082c0d4141c1e40300b01d4030454034440600b18483e1320700082c001c04071280c11960b410404040c00758216a0428402d0601017802907a039000165039480039804120100f40010812801d4508410100c0c050004c46004001c28249 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 273703651 1250 273702401 273702409
    0x181a04060810020d02040e01180b01050c0304050904020f06070503120c040b070201030903030e190204150e01210b0112020f0409080a05070c050d03111c02030a0507030e030d0302220302 81
    0x2c2c014a0b8038455400249070086150383d8046801402000352002c442e540d40b80b0401d40b0074000a800b0014a0b80741042d0311003107600c140c044503003401108000350f0a00e0b09200810502c0c0c0350140040741c3c4018003040b44540c0b500c031040a0624a400340025540314020811400503424009243c0820b400c2c08010901111242c1c0050b81e0f500d40e02072070005090810707890160010311000381d802d1484e00c5200c24910107040144440009680309803800d01030380d0f044a205640390341007030154021402154005201c0503041c142d1000f420481080c11050354802030b110704200031401c0e04040ca14038911001d1009500b00002e55691071041aa4204503403160703901c0301d8030b00380075801300d07001002030019080c0140004115240c001c1c1c50020400c401180c3e803482d0140058002030030740080e500500719103000000002340b03a50202c03e001d0b005940b41400b1a0b03412220799003c010110207010071808503510a886c02c11600e90307000401e480059442c10640e044507005d01400c0b804c0700324188546824030040c1c071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 273704901 1250 273703651 273703663
    0x903060506030a020307090b040f0501030c05060705120a02010606270e18010e01150e040507030816060e0d021c140d0e060c030609011203080412020106181a040608 72
    0x14000a0016940c0c4a400002e42452840740d4080d515100719600480c0c0c5802c582d114000203481203400b0440c00c1c0418034600b06561003440080d003a20316500c0100864113101e00180381c528414002d40c0d0748055450065000d0b50448082d49006030b640d40028070080d90048800349a00705148042d03020b51030035400404c603503e02c5c1e00500310070242d002c001c04c580111941102ca400355441009201080000c50428001c0624640c40c0f05e00040204000035009840440d940c041c07604039001e0404e250071070316540c0d4a903001b40d450b0301d00c01011010002c0414514410740030042d050001901c481d25103840000c5c41c0c403040064089200410b40003e9900c2c68102c2042065841514240c3d81c075a40d040c6030010080520401040b0301d40903040400110038a02402144101001c4506182d20390701c0740c1c100c602100806900801140c0c4007170208000c215030b40401814290248008140203444000703180300b20100d94442c0c0889900c9208501800700070810840320b482094808100041c5400b00d503503600d070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 273706151 1250 273704901 273704903
    0xe0103150e210c0106081501150804030e0f09090c01032403020108092401031b06051204050a14030a120c0806090907050604031a100608011a120a05010f060f0903 71
    0x4a821001841c850881d2030543d0221042103008219540d82c410030143c442c00c0000e0040207000403200080b8610341e881c2c040d101610001d035114120b55446d540d096542828a0f45c286a100309520700301c8031aa520362003032510442002001d4002400d84100240076a00d0718658214600400c41c000c2252044913000f000440b40c0900c0c19000e01d4441e0313401c0354140b550590808117004490202d000c0541c2902d1b810034101c030f00c952114020003a07507240e200b00200c0d1a01034080000d008205c000d00c050b950550a81c0c0060040342500c140302007070303901d009011078103017410600341d0004100e900d0429005141d4440200320008207205030b2103540401040240000c0104e48604010030200b46078071400c02120300030b004060201036480e40c49007000690440d4142460111a001e40001490b1502c0d0300c56034000c0b40c015407105e0b08140d080c508800c071141580841403041d0007040c46000c1c82e4000014100d4050316120000040c130354103080000300480090b401c0310341401003006c424050a80c0c410102804c80b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 273707401 1250 273706151 273706183
    0x11b02060901030c03020c0109060501031a090309130e100501060908062e0e130b0711060c090d0f081207080702030703120902030a1b1403120d02040f0e0103150e 71
    0x4d000880d0103038001c1c060252509200e40c60400c1403001c12155501c41d078141e0b40a40100c0c0000101000c0402805d94102c0b1940c3e5150400c1c46590b0341803c00300b200c03203185441c0010103e00060501511032806444594802c626a11a0010000c894100c85050060440d51003d01403174030300201c41e220700c6440078a641e6507600500040a0250030700c990000043e2440c54510354090828450802c142020140c003a66400422001700d2040f6000d02402074000901001400c41e030f5031011400c02d02c40c0c001c45011034118188960780d00002cac0480d20500d1150b44145911910b03000c0704001e09003000b100500130410f00c2000e9042c4040d0360780000036074500075410b03e45259001e0801d0741b444042c0007240f4009400d8850ba03d4000200700c20918600e06001c004540c0c07018656603041c1076884c6219100070a81c25801c18000310056003c105c0051241114042001d0310346581d440d403144807502c45600c2160780100e540018400c00070303400448002c0c0040c20200740901d60b8500c069070f07102da00f02a985110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 273708651 1250 273707401 273707411
    0x503010b0f040b07080901080604050f04120324080709061211131416090506090904060b0a12060608010b010801050405040c0308030c0a090807080718090818011b0206090103 76
    0x40892108590103802d00f90302198903281c0510b040310641d04050303e46800f184a10700003c0d11403c061103034070720601d2052030180341030b2965151401e89040003c0e18004064550b4002801440d03409031024115222040d1085150700d40602c160401040303400c5100742c00d080c84000c000409217459404000c60300b141500701c0f120310000018402041c00e80310950041d041c045100704030484418035900c560581f01e200a002d00d1440c4040383c070034000b40265507100d03000f403104420314140080c0c850f501034460140000c0214219002902d8160b541e07001e281111540c510302c1c0704005140c02124014400c0c4070003449009103100018002c41414045c65003d82d03030350400541400b01482840d4000c640000e6070998078180381001c00700079440103aa05000c5440c0da50300003808640026580200d0f0b00c032303c026203c19818655030a008185000010034019140d00240010800c000010160030f03500c00d104103040303102100090f00318241c00000da90160810112840503842d85000c40e400041c3c00d00c0d000503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 273709901 1250 273708651 273708667
    0x705060a020106080a0f030e150409090c0905040c030c0f05010c08090d0b01030320030f030c030403140d020d06121109090304090501140301051f06030b0a030b090d0809030a0503010b 80
    0x4010501c07581318403920f100faa544a01409084007981400a00035690700c0c0780b5004000a201c02c0c0d04501006495a1404200c01c00480c40d899001e4040c184c0b250000000c42981c41802c2c400f034500c00d07281903820007071a6a0801c00c10180e40c2007440100f000c00d04551200d840d00c80041e1184614401c0508039100014920340c107682c504040c99400b41d4401c4800300e85503143d05006142e0f49041440c0c01003010800310355401c0c4030300042034030703483c903441030009103185e0340c54103190466000548200d051000b2041c9042003089401d000c2c11440b683c444006840702516401c1d0b1042c0d40d0b155202030860450514504e000c61095030f152564500150f0701020680c13204410207246100b241e00035282c2c4c500c0c110011485025408045820b1002200288801d8407008181c018003c4403a195603884912001d0404c55203019801a40003594003d1002c80d045960761500c20b21000304072002c21031500107034142803007070303411050b13481d0401e50940040d42807444511016000344010b01640390ba203600810300d28 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 273711151 1250 273709901 273709903
    0x108160c06020712020c040b0409110f040207151a090108061305031b011401150503040b0403031413140303100308180301020a0906032d05040311031b120c0705060a02 73
    0x1030107144d022000010600070548000e40781c0c0001c0d55010301c201c0c180b40340c40b0b20601d0117004a001c41c03900403004078a03074040c19041007807075488800215049502400980c0100c1d04540d640b44490301100d4021802e8220381d9a82007000d50b00306c524907c1840200014010356000098066003c40b200c14500000140790500354034500480c25203074500960010050301102042d04040c90380c1030504011481a44c881006140c54850000c1c0140041c9080c00001d0115502121441d007282c041e00380080c058025200c51620f82030110340d10410030907681d010b2810810092502d05001d4005d0b0003950030b50810804010040e0312910001c1d1400e400031a5901c804144100c0e1000c10b420010b0085590305000c0c1e2000e00b041100e48512000b03c1d20702007002c821001038200883c820045d030300391041c110b40c10155a50007050064401da0403c406000000c012003420401421008121455a0040d800402c2510320f4603142510a1030002c0c410f02c43c0199850300042e0241c2039130400c0b250292901c403d15012 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 273712401 1250 273711151 273711157
    0x307121b020a06110105010f0510120e01020f04050909011e020a0215010e0405160b0a1214040b160e0603151203041409090c010903120c050304230108160c0602 70
    0x658841c0102c540014060303000002c0c580c002c8580340081c00142c0e03a40041c50040c4403e4403e45400c0500110060a04d511440d00300320050104000010a0301d01ca060890890b00b043c4c03140b03412400005014081880d14000140c0e00074030311002130005518000d60040300500100841094a40100750843c00790b000b0f00a81d0000100d84103031000075030f5103004001020300203403010340790340c002c010543c2580c03030201d040d040607200c0f03c02c1100e14010b425001103074880700320410854090b1746d881c2c807505c52130070800040e8003031405001387c45141d0422003404a80307102c0c485004018001011080d000d207072210820340341d015105840000702168060045144c05828440303068142c040010003150b41032890301724040420707064038a0b00e010b58414003856520810262907034041140150b0810004207111201752039002907140081101195907540c910b1900241c00c0841d1143c10382d150800402800c4c8401c4481c4102440c003515a400c10750b191b034421000400404040100840240e01070015940403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 273713651 1250 273712401 273712403
    0x6030705030312040218150d060e190303060b0a0c020d0203010b060a02060702070f080a0b0601050d15050301110913020702151204151b0509030f01060308030a05090307121b 76
    0xd6940d40e01c0f502409080a100486049114001440c2e9201c03c0010060501c0e1060840c0c034a4880c55818036020001d41c114025401c560068540702d41280e81d1000703108000c07595104507141901c1e02c0b024039002c0c00f50ba40a800c000304450041c8030b4004500e80c86030081c00150b405071024100d0390300c85c2c00440d02601c0d103038074031035004180000d4502d030f12940000d040d4400d20480d17003640c0000f51609001d4030410818030030b1f10200e51111401c82c1c081169030010f9904030700141420b0745007450381031a040507940b80f000d52548491180ba403c02890034280162030300c2e0b43c413a541451500c1803200005154041c8020300641c0658081081811500c5d48610030340c10102240206444221f0708460004e16001110119068100c18603601c00c00174140c045c20403184201150944c1c4840060303070031241c5404c100b1400c4c2d410b00c1407003002c8075020002e104100c05980150020360b564074000d80c0328030603507202070406040d076441000a10082103016201c00000f15680c5882e018228808851108110741420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 273714901 1250 273713651 273713653
    0xf1305090c030a0b0f090a0203150a06110f0708030f03040302031204060506180601020309100c02040c200d09030b06180c04081501050906100903140a02040b0303031b030603070503 79
    0x401d0004052031000558840c0c200d015043c4000009a0203015050780401c030003d0704040c070700b400b09040010940140da031200d0f0100d4203208404900300007444456660340880041a40c000600c0d061a0f0140180c0c2e681c4890a001845060710b08460f0690b40d00c1560040481d041b00400031404062081c0216004100c40e0180c035a454105402c2100c010031003522114802d075000c0071148011060a0340081c450340d4160081c50400f80e603034007030000141e01038000500700004501e5150042c0d07074501c02c0d800e41d81183d03507650030114140501400750b81d2140700c10003d50340c003461007070520591054408090740d601954031b13803031500c1d03860128270001070300301d410044003110340e0070402600005000b070011103c038071003118a0f1032008403000c05212828040c2c240c0001c0d8a900007400350404100e00007880303402780f038859411030f5680c135249001c100d4250b80e14541d8200d590018158509800b402000e00c90450240d0718500b020340713200d4030411240450508a0202200041e10390743c0c01d000140060170094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 273716151 1250 273714901 273714919
    0x60b070f0c12080d1b1211091221130605091f0f08010504060b0702091e0702070807060503010e071220040e0906070503042d03020c010906030e030f1305 67
    0x4a03002000703400061032807200758a001c100880c00d10121200341710b8850591102a400c2c21803a8500016242c202c080a104c000208441c55003520707000c082c00944480840903205400520040600300c140c1d00300300c0075145c1403d0006078105880281c42d1011140c0b070f801d016598601d40800304901400600d0b00c60b01d0040951f071469903c0350407074000541c48085035a0b00a0a80c0c89000f000201d0791311340101c05d080c800600c0180014204110000e400541c298441c041106080340c104008100c00c45103000160010f10040088460800048020f8005414014155810260140d2076004001c00c10020041d0038040c581d500c0a50383d0150085210111038084044414448003507242d02521072142649d1200c000114041800700310280981c010390350f2180342d074070b0366100c840264255141091070140c2c80c000048a05400328036000006d4801e8002d49421076003540090082c0c0d480d540709030305240c01d21952120012012017101c50740000140226103a0f030b007400c220710183c0003d410241e080303540c02e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 273717401 1250 273716151 273716153
    0x5090a0804061e05040b04030f05070521070e1905070e031b01020606030102070201020703030f180f210b070c08120c1309020703050406030b040902210f01060b070f0c12 74
    0x102620f420201030b240350400250b10340000850b8140325911494071400d000313000074400110a00c2403000b201c5d002e601160040b0740ca50740060651442107003047c40e061200c02c982810f101c0e0034400000140350b180080309013131801904411a42618680500c102030b912000560b03070a00428101810490160481d0402e40c18048031140454004880c070f40548103100000da2185414021902525410f03405004070070301d1542d0544404071404031030818000034521004600511301030200040220007840c04045161028884c0e0f005512003140a8441d0301c48000b4020541e000340140c0c02095034a0103a6101d071301fa0520030040d00401100c0a0030203008018020000102e5000d000490360501c0050034480d6a001d00c03408a2103100ac000b030109405004c1003100c1030082d0b21120000002400c0440c4644c416030000d04241c004031000d0150101c004075008130503030200419000001030a0080100b10300b05520501c0c40d006455004010303107040350700c110400040f1098280104101c2e040ca00041c615 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 273718651 1250 273717401 273717407
    0x17060f0126011814010605030303370903020705041802180903070c0e04020909060f1f0503010207150e070503030403060b040e1f0f050c0d0902010219030e04050a0b030d0305090a080406 81
    0x10440421142e1744c2040c101140a240202c12a4014030920201411003021b001581c180b10b183c804445c002c54081c0c0b5620a4105803d0140c0c4541c07502c40e5024140c045d0500003040122041044481005d0a4030f81d40d12b401030b1201140301020b400d06812640959070b50345501c91a41c03050820081c0301481c601000908541c002942c80e010302e108564071002541d80c0741c007103545c0384c0007240c500804001d19070100302c000720f04428038082120a14a0403000e680c8403004642079900c5000b0440710b220003040001c009074030600c40e02a14524260140c03189034900b0b00003030717600e009900001c0d20540e51500b0f032403410703a10fa07442141003107000c0080e240c0c89480c61034101203111a020540b11520b04080141c2e00204082c810948102130455a090801e946010342c600100350b409070403070640c402c0c11700490000c1a031020b0020114480e9035a00c0702c040c0840c00f4007041e1040584244041420802c0e40b00e1103990104803030001c801586000101580d54107040b0b454038068680280180c00c0000300818100d034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 273719901 1250 273718651 273718673
    0x1715150d0c0c0317041b060e01020c01050c1015090501180b2d0411161b06020a08070602190503150f240c010617060f01260118 56
    0x4a0303104010316400408156900075184900400241c0d120346450601c1944d852440c0d0842d01031311810311051007045610320021100e800c0304000c21240b003112010f9603410440001100028680142000003e070982d955505112510004c807903111650343da104000403108500030400140144029695924803500035020400b4085221707092209400660400c00815030002d482880c201c002d003070b01a140c81c0000b207494180940e00036203036025191002d11a030003404825a949149240848032464449048001e07580b080c20780d80018030b0308201141d000b16160401c03c0d0000310440c0e1750085460104000e204440003504401c80001d031b07031031296174001c0185104d042c1100380d90710391802210070015115170442c2c400d6800034030b10070b01c1098100440e2410010100c0386421a04110f110003150307003513514941000000e0a01c010195103070b031000308050b0740c204680e40840d008a506024187c03480e803c000002ca54034142070305a01c51054000d510940d4000800844480e0615076403801c501005 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 273721151 1250 273719901 273719917
    0x2030d180f0b07080a06080a0201030b060c0703060608210d0b03032104020111031602102f0d110d030b0a08010903030b03010e030a120504030e06120405010501090c171515 75
    0x43d40351000030101c441a115400c15070781d0710401840135a80c09d90045000d428201c000d2900b0210034042c00031894020086003010390b106480c08251349080900e40791406220306903038488078010000031040d040e1494106c8081078214400400c04e400c0070300202e40345125070f1402c45141c800300c40c040b01c607036410555554041da03c01d999201c189002a8a1a90b81e03000f03500c3c111303284d46040510607006107400301280300c07468aa424281010800d40d80048040105070344100307500d01e440c0f28001103280c0b003408211001403642c14040381d150703180c0e00310569588ca440000c0c0141581c5001c00701e200d544100d0100700400c2214024000400e903407130014090502d41c06034038040d60134907840100c00c20000c41a664a40c040380d903541003980c0c4448401f8081c20000d0015401d1020501001010380c90b840c004110607188100e02c500075003424a4070500311001680300007501850000300c180650341c0143c80604400482c0107140a6490311074503d04400901d03401d4070307032000000056010380d24941001e46080307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 273722401 1250 273721151 273721157
    0x5060a05100b070302030a210c021e0102030403090b03072115080606100305040f0204020c0f070906060f0f02150a0609060504060e190204080610090b01090602030d180f0b07 76
    0x1242d9580360986141c01151801809a0001c1c0419a031891152080c4103060307110346001c01d0303c005800405022150400b1001005800c508d00d44c883c0303144242089004901d80b900214503624040d28000c100400c1402145100707540040401c001a120b9a05082c0c001041d542003204030100003a944000c0804070021510080c0001c0e0004800d600825982c1c0304c1d400c003621000072603400780c000314000c9c140100201e0750400d0010b260130143e00c85e072000c3e040c004542c000600b88062064074452601400b90f0004060505110f000d010a41c0d02210451000d0742904001c28400b145003026401c0c240b03802501540051140100a82100540c00450485480a208000392030711801480243c4440303006540d50944954041034080c108515035864952889200608050300c820241d0f061100583d0781c444203d80005060026100c248103c00e4411002d080c0140b01a21303200c4065142e01a07480c0000b01160340341680b003d6a00112082c140c400c2e8400500c1c0d41200340e0703140800032048261091400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 273723651 1250 273722401 273722431
    0x4020d0c0e03160605090a0b0c03070201180311120f01050c09210601030201050c12030f040b060f151608031f06080112063201090b060f04050f010c05060a05 69
    0x1e1410085200e03101c3c0c0820b902d07210320003814150191210b50004280c282c010040280000d640520840a04500d10225001d5542c0e00b0b00b5000043c00382100d03204104540d000720200b040020002064035200c14020b41e141e60051842a403960300300000e11003401c0c015400d01d01040800b0400500800c52800c048035400d2a44e00c0000382080810144a514007607540b1000041c03000d5030140001d0112002000e00b00d6034041c10410203030803950070640e0310b00100303800c072410b10080080c03401c400d640c00b120139035401c1c20f8030703181000003661240700d88008400000b00117080e82c000801820404500368025901580c9c82c00e10407400380000005600164803004000004942240300c2c840e418101e450f0b54500ca01d40031103030303140d010003440120007d02c8600c119101014001649441c00341450b80401d060000640c0b402d40c0071415a040d03603620358402e4508100c00c0440d03002e034100365001d4403c181d650640c48142103005071131851100c1c1002e0018483d0204001141c2916000240300e00101150702079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 273724901 1250 273723651 273723677
    0xc17070501021918260a051f0f090807020d0204110711180609191803020109140d050403141009080703110a03050f1810050903010506060909010506071104020d0c 71
    0x1500d881c00e01030b00d98a41710500c45081d00c918524400d1309410100c0c820303180d80c0940c56641d0303460304079194a8003014050b06a00074080e41c3d03551246180c052102c1200380400c8a155560013002e00c40d800b40284103035007405405081d03468071b500910030a40c20070901560354025040c501103080300110424401e0101c00303200e92007019210309a034011136000d4081402c1e604d4051004401500204428014030340d00c4060021a03114590f009403018080c1e00002420561401c2142c858000081034800c1c9601c011003e031b0442d6402400c0360101c0c3d03002800030000101ca44031181c1040304940e1140310340c0d81841280d01c203120090004140c0c0c203120341c40303458458180c140c0300c50321104004000b0340070403402e10661900105020040891951760b000e008000b0310428001240c1c10911080700740022030100b45d2040740d0809200d140d401c40b104a0b01203050160480010310001814000c0500415000c00d141e010080c07c8010244040c1d0018015034a0b407905100c4600184040450800010301d4005051 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 273726151 1250 273724901 273724937
    0xb0f0406050906060d02070f030504093606110706020c070614030f070c050d1112030903040b2a1b0906031e07080a0803010609150c170705010219 64
    0x103411100c016014203181d80e541020031407241c0040c4031410134650208180d000080385003011000c505d210380c031120b40f00c9084c02e00500c1100c12fa940c0380030701401c17260bc00c040ca100d0441210032521000d003802c02585030a40c80c19802030000d401620f4a1802d0101c0c90f00d081004035000750025000740c00464400c1952440c049902d6100000c0c44903440c1c0007080851040010358407442e03400003050405000043d0a903030342910b07111961118000040c07075185a078030704810602918610a60510806065050410101d5220700c12840703162100f280000c0c800840c00850b400480c001005251400c202480e0a414641c0311001081d810700c0207802c035021a512460030104c40c5000700c2d0040c0041114088100c9501c640075001c00000f00288501040000e20810800c10415081d00c2014080d4495152080240482d81640c200d040c0456141d10005240755002c0e01d4001d1007030b00300780e1094100b01010810b140c02d00c224400600705500001d9440050a101c5114541c000d0345a91707910f4100c07141400755 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 273727401 1250 273726151 273726161
    0x3060b03070e131e0b060a05040605010509090721020414010503040f120905041503020906090903120c1b0a110a08070e0a0212042126180304090b0f04 66
    0x803100c00d0160101180000800940c0034030307044d1203440d00d8100310906407800002c03142c103140c00b104c1961810341040f03020b00703215441c0001400c007520203116150130300002030101d0290341042070144043d2400200c03850700c994814480e030055003040005050554010030080c0d4041d009101c00032203c0b42d542c2c40d065111305d04903442560080d4000c44949034a64801c00c901c89280b01c40300401c5421440800c01d43d0b2503200710411124001d100f24409480c0d1320500c8003410005020b40e1103100a0070420035540d101100703c41c1c0e003038581440785c80b10380e4415114440341c0c02240d84002070360440703100003c180c24000810b43d8000e0301620710b02c424000f18004200101a060080c0d480c139402150003004a105000b441c1c0f5007101d1482001350608180c0c5030280d128280454003071f00d4030a080034035904441d17110351040815000500d400e02e1040820240c042d51401d10245060a0745035600003d420203441c0c43c4900103810071082035076520f40d40c83d082c3e500a41000c58420348940008015210680740510903 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 273728651 1250 273727401 273727409
    0x81b030a0504050f0103060509070507170306100c06061e06180f052704110a17030301060c030509090a050a0e03090d02010e06070803040f0b0a02031513020d06090603060b0307 77
    0x6151820f4140010701c1540840007688606140c2c40e1403000c07903599510040b140c0300d09415550315886221608003880303940c0701a010320f440c02c0c40070001d11903239031600004010307035100c2820100315010f1640b07008001821380350f201b60038100078007148640e80c0c1c0b901c054280448065990701d168401d40c902c240042d17002140305140240800e51000c00036130030110f1146407101d2404580100da003044e0548004184002c40b000c440f084030328000c90b04a890140b4424025204d2080045071f202c1d90340303030003960f01d06c018025281848000031054042501c21802c44088030406000010791f41040304040001c1c00c0e06807294000c007400c0210465100a0000681d00040030044c4103c2c040300558006446400c9074080003034000100300100404030b0004001103014074828050920201c51758104003c4000c40502801c600c203004205100d2000001e941044400a0444d01e00c23440030f08500c49400288110988011005d00b8110001589442a84090100ca000303c0040c44100c814234101511003180d806 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 273729901 1250 273728651 273728657
    0x110f09040212070807080f160b04091d0a110312090a1e030804030b0f07030204080a060c030f320906010b0307030f2409050105011b110d081b030a 64
    0x40080c015150581d4100420820603043c1d980f11501e8802013800d200031034000b24981e900c2040c0c6c00c2c902c00b008003d5007881401c0c402d20341c00d1160900c058410944900d00c42c54000580f6030030640d107142c190f5004651041c01980449140000d40c1c07403c0952002c2c0c6c0c005040c820700945c0c04014503902c940b000c0324541c1070010a001105810800c40380c0c00d825480d110003100c40080080800001c0d00c0100a00c003460142e1401340803898254031008061900421035004c260040c0020840c04800041900b01140d100402264071140650308a00504482c80c2103841d40742451203c07415142e11081ca8080540d118140c8002d0f00103030341d07403548840801d4400c01f12607070100c0c0c01001509900f43c0030b5904044c052a0108461a050080030240d0303c1d4202102070202d020708880ba203000c00100001d005010002003030003e9803408001819400c5407a00381c50f540321000518008004440c2c0d084040c4000050a4010444250800c00a260440249130341090944129140e200200205561001500e0381d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 273731151 1250 273729901 273729919
    0xf01060e0112021803060f010e070e15181c031101050c03070f05160c240e01200f0c15030412050c1501090c0f0302040509151c03020604110f 62
    0x581c0b07200080d440090b4504158103100b9940f41c05940070700070180141c80c0110700000650402211040c400c902821030b4050103581d0108801984801e4129110400c44c848007989442404412a410460300e1080d20343c062003a140401c041c00380142c42c16803090280d6a808000300514034042c1c00c8960a4448240c100c0c3d0074030004a006104800041546138940350517400c2821417140c0c18000a556030044039202d5a400c8103111010905110ba4119032101c0e0054243c0c2000c0380010b01201c0c2c001d0f200c541001300e04d503a1208140360101046c51501c07021421503a26215114149440d01e0014500a100c0c6040c61b0000c0890f00740700e011340b4021794000c0c200315044070b0b182c00c00340c64550080844844601034101120344907420740768143d0081200d244040b07401320345040d0060107841100e0b42d00d0180b51050206200c00e4859004d0700b0ba00c4408400d1840a4030104030001c0c00680d1409401c0054207501003100e01015408a20b46010320310450644a51510040c10085240300704010700b03400170012 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 273732401 1250 273731151 273731177
    0x140105031302060a11010509060106082212020703080c01150b0f090418020d0506060a080a1104090303060f06020109020108010509061003090819020a1203020903070303030b03240f01060e01 83
    0x480c0103100064160174468565a8280030070303400c1d0340c001c446031081e0350444001049102e0300042c0c203e5000c0860013a00c81042c2002104000d084074034040506612050407100803414000c0103c00f02440c2c0180b4203036100d4000040140c0a05441083d101201100c10703800504901b1a10640c0c14840d8040e0310503040201d8002480300030051400500003192a103132019001d40c03a5400340e010b83c1d6000702c01920141c9400028081d40303c000d503105040b140d01107115040070807c080414543ca01040360082001d174030f1170034120060900780e0410100c0b0350f010751300001e4164055100003c0c5070701c00c0e02c4600b95aa0307500c04105d0380500c12548290040c040202c4034001e24030a6008047c0e161207000700034100200f4502849040d0091003410000d072780f1030366010081c0034503904c40301c0403040c00740340947c5085906400b01e9141c000300d120040505450700b18003810780d6800d0180034510030025221006998009141540084c400d031002180440c9030400800c15a1003941659500f07241a1501c01d0302c0094 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 273733651 1250 273732401 273732409
    0x1403090a17100515090105010806010207030f0c0e0f15060f040504020306150d0618050103170c0f0102031303030f0501081b060403120201021b011b0c1a040309140105031302 76
    0x1007101803030780324090415081500c20083c403e060045403400c071040003401c20341c010b1000f901411781000303042c020b09108105030ba81c1d001a00d1000e60382c2c00708940542c2d0350103241c1290000c00503004184110016400c00c0296640b00100611490b202030f400381600440805204262003807126008080d00104002c0c81b103070801c0e40045800c00b8000c0c1c00203a2100c0c0814500850f80c1025a10700409900c5840412050307610b0303140e602a8030340102c41002154915513403201807840302d6805860212000c00c4507189181c040c0400c0c80c28241c294000d566034500f15a03140901c0fa11650101c01092034842d1141c40d0418921030740e4141e070402e02c0100308104a212018005941c4010301581c460340070840880005e00546140168500940000d625500000c203000c401d40c5c44803c0308010340e850041142d8106268080d150300803103650a01e080640c9150a1503801038400c10b0142d90340c03e00d0752080c40101a80048050110741440072000d07000324001004495520040c0e44e046c0445c17000c900c0c0c450141c07078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 273734901 1250 273733651 273733679
    0x102121201060e031c030506030d0921080d02030f4204020c01020705030d06080a1106030a020903011a040e07080604110105070b04151b1d03011d0a1403090a 69
    0x40c00508030f9407171090401900c0b50140e00040c1c0c000002c0d0701c1f40d050260030b040c00c002c0a62111000d003401e6102c1414609040080b0007079080c1d411030b52003003000100a10041a04840c0b02140b070798825540d074a000028810003e50a448490800361a10f000a0b072903030f018440c403c82418192030b07240700004420b000710042c10860000d9544240c2c07c10948290010910041c8840c511039400b568031030300060030700c40407a80303503501195058101c522601d0000f6100d0350101c3d03002e5800c807000380d03c83d2607000c1094024040c11440030b0b05503107420282c1c2c20380c040344031496110740b90442c0d00388489090500455285c2641d8811094150302802c045000250700300500380c0800410300d4018149041138a544d038060000340c2e015610400803041d1403017121500e00440f03a888184040ca0007800d00c04210042c40305400d02041c2c0d0385203003c0805482e03503503000e4001c12114204501100e004064080b0090384410b000c000c1103640c0380f1a44403c40c80390b00d000c0107882e0700e0f40b0010102d1070210b02d030803105000c1c44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 273736151 1250 273734901 273734927
    0x1409011103041d0603010506030c0907080a0b1201020304060b0301020412020f0d0602190f02071202040518010c0e0f0a0f0302091504020409020711010215160c0b0a0902010212120106 80
    0x800180b001182d00c0c030075500400090b9075800708480050074504c0525084400c098181406504810028005a01d4202c00325400148520b04811035944410180e001031880304e0f007040d841580f91180408540381500514010740c0102030400c488a107003400c0500303e10642c800c000c0c0030103200d041c14015141258003201d8101024013132030304603140c5940e88000c0764006154001c100585000c8840e2450740f105c01182c4045050004150340c50600313401809441013490001c2c0f050382c0b160300291007000c2c84032110403511031040080c42408896007001d0500a031520b003441c082c0c490349020a0a030f160229540d4100d46a05164035506811902800000c0000500400c4000705807941845181c403188005c000502d0b044800503154a1185481281c5190203401d00d411176024000400c05503190102c41c5810400030b103514032083d000340b0b80a4070300500080000e4140d210280c100f0541a1003500240c0845c0d00c01d0b8241c42d00680100e1200c01580580000c690080b201400103000307090080c000007004d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 273737401 1250 273736151 273736153
    0x10509130203190f0506070c0b181006030b070e04060f0515130605030a06090e06240409111507051b0411030403020a1203020702180403050f1801090614090111 70
    0x1901000652842c240c00030074084032610b055a03441301c14002d080c803200707800840074504940c150420340c8441e82040001740014080c07030203927038002000a2081201c068104428030b824001155a8100b05114100456223000410700620444501d4075107489060b041d0303103021031841901800c01041c0500a0685548600440070070846e100380b419071183e0887c001c06030b41e0703030300b9640c1d1415070246802e0f111190300100b43d031424252103c00515020401c654421050a40c04c07440c003001000c0020500340c106440f0b034009180c450040140100007801c465011004e40f03a12070030400781d107103640151042100141c04d540102e1541041013109080305c1c810000000e00100c2c400040d448001c5695000307840840c00340e0310031103413a41080000da9102e141d0101d9824114104420380c0c0110b000c0c242d10304090581601c95800041c105400381c801e036100c12010712003190b102c14008045090b100d03c104800d90104025420001c0c416201c0d000c460b0101001c0400daa040001000041d9a0204c65458503a42 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 273738651 1250 273737401 273737413
    0x6120b01052508030a050105041107050d121b080603010e060405030d0f1b0e01030507091d0a240e010e01030c09020d0615020a02120d140a0210140a0b09010509130203 73
    0x103d07098601550040300070000020751545081c003008100d4a00701c00010b88100c080c48600c02145c000301d2190160120340c10070350401e0440d8000b140090a2080005803c001c42619007905581c0c4240c140e480340d0b00031b500810240741403040302591030130200c600500c0c0d030340204082005050150000000914548804a4410b81051140441c0d04c040503900000400280d80181c0355030307040c00340c82d42246690420402c01400d000304c03000c100f00015402c03000012400d020580300d01140c4d200350b0720741030158000040d1141000c0c485040d600c41340701d5200002040300001c00c55203603180c1c451341200c0e8041880d001407458001000060340181501040c055070321100080e00791800e0035140d0f420315056010300b403201041d2040201030301c00c0301c1d02503100c1d603c0074804401c02a0842100d02c1900e90401c403c030349034041382c03c0481c40e00301080f000d0043c0d603080a007003a45d2410702c02a028018030034540140f0002d1001c3c803d1110b400d03424070560747d000d500d00002c44c40c103030010850341403ca0300113416244 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 273739901 1250 273738651 273738653
    0x10b04210609020d061e0908030c0708090306010e04020102060106020106080309010c020f0d0827030a02010e150408030a030612020d1202030906190e0909250306050702010606120b010525 82
    0x8182030b0312084c15100c4a0f01d5500003034083d00d101c00078100c1c01807410750403c9013940c9a1108940d84c080104030710703c88600000d4004c03e1110100542d50320341c8004049420030360311042a15201f0405036012030143c801d0800106020380180150310035258600011030403c08100011160088a00b90581c1c000389034074481500380d115400361602c0c3c54010b004075075441d813907200c0344240008032452006440400140308030703c81d50017244814055030240307800e41c4038030304840c0080d00407054040001a07501c0c0001e00040c00f9030000c0302900f860342141e00c0c1000030030b5444040861356450004001e510000c4c500c0c14200048a24180c60341c5180745204503803c00c100741000c06c3c7c02c0e5100d42c0903d243c180044001c8150729502000c400d4007080141c40c008454142250b51981d01c008541c010076807049458140102d41b402d181c1d8020045422020500080c10050b501a000341000d004450000e5290300b800410440315003d64021a43c040e034940389011010762030007100707403c04404203119080d448490b05c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 273741007 1106 273739901 273739909
    0x1002033430030c0c150b0a1211010903020303030f190c090e0a0b1e1302070809030601050906030706051305040914070f03080702060c010b09090a0b010b0421060902 72
    0x10403041c45a170403002821a2920560f00955a4480046c00c0c81c802103840c960203008041e0b0380c1d81000d5030001140c01400c00c0c04042d406600400105000c554400703d0281c0c81000300004541c011030b1914500140d401c2d451240c80007400d000c0062002300ca50004654109810a400304012090400070505007140740c0208200d0780d240350a0142c050316901c8880d0902001e0102c21036444d5a41d00d01820150404610305000788920230000c200c0c1c1c1000304002c7e000d07500081c001c000180c83c0210131281580900c0e200301c2402c0030010006965100c1c0e002d0b51100d11300c18030400c090001041441490640203510944082e52008000c00220704501d04407460326405981070f03a61030400c822002d014210b41c2c491207030421400ca0030081b0b81040416041c010078807500501000e6641c1d851056841c2c0140d00612040164101c00d805400b1229184681c88074404d24012030b1024550b0009 = true := by decide +kernel

theorem cover : BRFrame.Cov 273561151 273741007 := by
  have h0 := BRFrame.cov_init 273561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 273561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 273561151 ≤ n) (h2 : n < 273741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
