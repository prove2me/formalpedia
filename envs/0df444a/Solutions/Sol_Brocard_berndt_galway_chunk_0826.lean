-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0826
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:01:18.463843+00:00
-- url     : https://prove2.me/submissions/b58ff5d3-3a1b-4406-908d-daf65a4a3124

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 148381294 ≤ n < 148561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 148382544 1250 148381294 148381297
    0x2030a08090a0f0906090e0a020109050f01091703130f0f060c080d050703270f06050709050d11010e011b061109120a0c06020a03050a0e040b0411090406050105031506 73
    0x11070280c07001101d2591814000b00001c0e450708000c5003075841c0c400c144175521780c2e44100d000b0308030103500414106126400103403d0b100140a0140a0920141680d00690281700d040005000c0c19280c0175809203060006c0d51290085a4840c40301d25101c1c0b00008e006041081010039603185107850740040b0715184068810000c010001c407449c4d01d040c086203021804a11600b80700d55441d0314081581004a0704a503c07001210300d40d030038203040e403402e5a0003207400a18411402903011100250f241c64100050311145120307400b49071301294100d00c0404200c03405c030840032081c03001c2e00e98854100c2e4200064840c2e03103407e0b40b0701c25104445025180881c1d45508502c007051800c0342000d28240c5400c3c081102140940c014846c0e65116039444400c01030400b801e40000c1c005131000e040f030f010380c660b402000707449100c1989003000400441c2030340035550703544904118100144200455800c1e06401e40d1150042d03102c040c0304902d00080000c407075010f50700311b905c540c01c1d8210000c00c0105180c100f0425 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 148383794 1250 148382544 148382557
    0x4080706051614010506010e041b05030406090b1e010906050d0f020d020621090309090c0705010e030301090c1205330a03060213090e030313030e04050c0307020d02010902030a08 78
    0x40c580c2da86800020403c26103055110118003000480c00d440d0420001d094046100f440c80e0085203421825a00e00032a0701026407110303081e00c0d0450b0749880fa41403180107810411405001d4008900a000b49500f4003503401421068236008014203a03600c840900860701c0b41d09c6119003100d030388008540001e048040e04040c1d0b900c01056200c1d800c500381c0101e82d440c0c10013000822225540550705000c04581c001c4140c0c03040740e4600542c038014440d8040f41c000ea6028002c401d26050201d034860820500790040c031284101702c02120b44969543c10b100c4003600100f0720f164003103000b943d0215a03c00c070f107001d00d81c82001010b6203411003050075030041c0c1350310703902c400804e80030f5000d0080000e240d5203029040000398000c000140c2c03640a0f4070340c0c006030401103521010119103804201d41d40782d03001000f030f242c0c0074410b450703e0103241d0028201543c400120208041d445464501044030301d4111001450040243e507089407803801801506900f213501084001c2e50544c069070904d000502410001c04c4c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 148385044 1250 148383794 148383817
    0x30f0c030c130906060605030901060f0b0706022d0306090601020a030e060307020f01060801020705190f060506010917010f0b030d05030c03061f090603050c030f0703050a15080705030709020408070605 88
    0x2422016130701e43c401101e4254000c10001a0008148a140c5509001d01d2000e800c058440070482c1d4503003006020781703100e5954010855a008142c9a4401100100700101c4144450340900703a8101501c5140e400d50044460f20310131010240071550035440091450800399040c0c55840440010318204001d0b604010300641c1144181e1103040c810704400e014201c0184108000941c40710348620b0400d0802002e8400582c16242c0102d0300d1000c01d142d07005501d007154018100055903102c24004a030005c820b41c00c0031440742d0044420b00c7e800e80d01540000b4580103111010480400b00320101620f0700c268079101d6000a500b8404204440b48031402075403c65001402e0103400a020f540e07058980303d0001e501004a801e9000c20044c1301e40502a207a404808281074a103149041c504207018001c01038100000c05907103d00007030a9400aa008225510083c0b0030114031b50761310095140c0d02e03c014021140280145180022440403600170b4506560400c000346c1000ba0404e00211641d400a0010340c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 148386294 1250 148385044 148385051
    0x102091306080613060f090b04141c0e03070f0308090907020c130b040e060c03090d09050a030f02180c070501060506030f070f0203070204090602121602060a02130b0301090b030f0c030c13 82
    0x40b1032100e51f126082089116081114003850182040c178000b100001c101002d5402131407821401e4204000c00c5851001c60742402e00001451101080c41d07ca03868000b0081d0945568020061007441e0003d403001010843c1c62854503611140100d071203d021b000850b4008034490915130348130150f41c020000b2054081c01c006004224003800c2e625206040e9407580d4a4140041172080001d0140308600a403415400e102500618050114910200d1444050611003038a800901156200d150304a48800c103da81401b003414980401c51140d800b802c0200d17020340c81e082001825090040a80c0e2003400b0103000250580d4a54200390760a40200c00c0410840c0820050113005079100e01c039018a4034080c960050300c60b00c042c010101d00001c0503010610303002d20b85810703403c0c4581c0060b01544c001540e14016880c0c031281c1a107000a18917a81202819400c003000101303a40358194002c00503940110101d510300d013407808242d510703058180c2503c0c1c0c0640111040031914240b500205c60420b1a850001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 148387544 1250 148386294 148386311
    0x1051302070605150a14030304090203091009121b020a05060a050c10050a05180601092004030b060918030301060c03110604120806060f0306101808010209130608061306 74
    0x2c4110350080325480541e07000c3e10308402d4107040400a400291030001d00b44400403240000203079aa02079032140c7c0072025000800210740e94001d0044400720491a1014040c1d02c0051414003002c000241190001800c3c00110360641007070381d503402e10300b40e4016222180316801e010900074941e0006070706009101c1c042020103000b00c020031440403110712007640020503041c071300c1d8144141e500c0a03100581900b69841050b00b0140041031040c1141c16050303002802d1320503002880000d4040510030040118040340020500002c810054420303070085400340140d540304c071444900d038070944421621540c814001840138500400d2041207450280c00c001c4c3c0c1c120407e540c0f071460035904540882d01c4104090b5051945500030b000d20340c0104084a03000d0400d048076000340e4050200411503407046c1401000061010302030720581252428a40c41c0f0901d064840307410030b020354080c111141c0610706001a004450406100300d109441000c0007600b1076449018014520022182044c3d611603a00c0044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 148388794 1250 148387544 148387553
    0x528121107060209060f031306051806060907180306020c010c0c0807060b04020f190e0906030d0c020f09010b0a02061506040302040b01200705041407020703031b120c02130b03060105130207 83
    0x55440307230403184070b04c03c03c4441e90f250070426604054070084018a6130303801c0304000203022450a074003400907100c82d080c0c2d9564240c12140c81c20b04803032902011061903c04010700586800404451805c18002e000b26a00510300300c0700f450081c80d002c1c009a8003400036100084594010011150b40100054140014a030050480b54841040c1080f03480340c075150f905040d500020480c0c0000c1c07003100c902c03096241010100351070343c0200900204025400d2003a41c01c565412072210300358070300a0101004c541e152600c0445035071050410034050310030344001503d0b00e0b0703c21100071307040724005d0441804d0901d190b0078031014040400c0100d050200d01d07031101051544040107000101802b90041c4083ca142c0400d000481c0c407040d4003618000010390030084140c0e00015001d00703da80c1483d083c081c0f207c0d4044400a920241800140806450f0042d0000f02e6442414461458001c640303804d02c5000340b45100d0101d46036001c4164140d000417004104134540146032803510000044094034002e40b5585 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 148390044 1250 148388794 148388797
    0x18030601060e010e010305010302090a09050a0b0906010501170402010c170c0a1203060e2a0f0c0a0c0e04050c011b0203060c03010608090f07030807030528121107060209060f 76
    0x104000140b40d48140c1006503920142d1007801400c00c3c00c0401c999419500030441100c00104110103c0e07441d02408400c00c04104070101c40781d40c11002c50740c0f4500307200c0d000f50380300c500a1140e0380c001901d01c0b02d2481e0100e0984496401503034144c48801109078150384841c0c5005481080702c5140f0000d00c01844101c3c414088022001d2085020f05219514600702a040700e55075042862500b25480400529505900660801d1000c044d0a6810700003401ba0b0000144201074051013207040101d40c4401200c000958000d140c3d1203002d010720703502d840e1610040e03a0f85088502404a038400c100702c40455006651500d1014103c0c54010000354640c0c001c2442e090082ea12070088400010040210681c0400495080a1448058015400c1038221281d84103d1800050650140014008105400380c0c044a02001103078080404004042c185500703c6603401d0f8140d00890804171000d1003404440c03260b0011064000790650030400f04d915030328000e403c1300c01c03200d401501c1049400101013a940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 148391294 1250 148390044 148390049
    0x15170402210f060c131a16060501051c0803040b060307080106060503190b01021c050d0518010507030b030d051303061b09080118030810090e01020702190303021218030601 75
    0x802415010340c58003400d440e2070030050038040031442c14801c3c4440b034001405c0001c103e0b0704280e0356a000105003150b20038203214913891940f8400140e014501085019000141202c404440301c041c404150811580d040003100070041940b1070400000d000542c4a82203035800c00000740031100940d07225807005007128060703040030010450210800503482d207218000c8261103030245003440111410030010b5030f2403090710740c18082c20241008401c1c281c0d1142050303481c112682041880346081c4940c000c1c10f501d560480342c403400c0d4200740000e40424003e0044440100000d80203200f480c03001d040807a090780107a1100e07480a2210030000000c11a01d000754092070809401d18004450035040192001c00340e0b900951041c4d04000b20744032005541d00b040300c0020b40604202610703a94080c2042c1030301030150041035400d441c1039003444003943c0540c0a071203014400d941aa550b07860403006850280d603c2d1000800507807001520000143e54100074002035000c62031268018000c8900003801e041e400d8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 148392544 1250 148391294 148391359
    0xa020102040509060f060a110109080a09060e0d0206030115020a02060301030c06110a0c060806030102090d06060614180120060408070204050a05071e0210020414090115170402 77
    0x89000e2000d45080262203401c00350480e4051003205c1c5101c040f408a0103001301d44400c0c07060700d019003070058200390801c03812241d01c80003442ea200d000744009003c1950900454000135601c0105014500b490f4800d09080c580003050300b400c50b86803a424403100840441c40c00218050b410311540103803100d074080e40c06144a15602c00904c1d08081001f031180c5010307044900316610414021004c640026052410b842143c0f40c05402076480c41c1c080b038068420544ad0326085141804107000303101c00d5a0001c01941ca03156100000d0b209038030340312605402881f0300c2d90321250345a81d503400c01d9805542801100601210519551221543d45a0601c50125019540e504000900d141103150a120741640040c400c00c0400841c2446400140104402a14950711007481c107206041d60340200b1000141e07002c1040159520340e207a0070003007408183c0300d0081c0d0040e00c0140001c9401e82d03402c080748203100c00540d070700d220900403554207444050780940281e0308111100421804644600320014400254 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 148393794 1250 148392544 148392547
    0x17070f030f0b2d0c0903100b011e0203030f040f0b0403091d040302061f080f0106090f05090d03150f080a030f0f020a141002070309030302101104051909020a020102 72
    0x6424104980a80101149106000300c0088101c1c407200c501c0f00d080203070140c000c2e810380340e49100c0f90002c103100701503039980e16110340c05d565070121041d81c0003d41c918200380c0c1c88514401e17203100c84c11003034045280c500d405a0014800034a6011000c1c404030f038001d0107044c2c10480c140c0c0a88910051000a40d415000074010010030310215440e01c00c00a144807080e10105414a0036882c006d450350000751649880450300c8501c0c2c0b140c05102d400800c054040e010580305c2011250700c199000380141d108001c151828240d210b070003d22180318007485070300284040c20709a000341508800030248451200c40c0e50031710350380201d0810250243c04000c0c00c1160000c100710319036800c018001d0f0113042d490404001c400c1c542c08200c036502151030213815501c880a071480c2042845c2e150704104819416044030303440415054241036100340000120790103502511004a1030031044800d0b070341d601510b00c02f0b003c2c040208003c2410442d01c10180502c07920414a8426150380c01c14090760b020750302d4038006030340 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 148395044 1250 148393794 148393823
    0x19111f050705070b160803071206120b13030f0c08130e040209151509061b03031e100b0d020d0614040c03020418020903070e0a0f0507020604030917070f03 68
    0x803c0403c0203003982c440794904040259407002c05d00501c2c044001c003000070100114100e903020704036200f8400c03460101400030035242e0300405101c039a81d003000e90f260600d81000c51121142404020115074244d5100048607040724420780382944030180c12186400c040008484a0030f51204040c0a814501404121405c00c1d0040218000d0050322028403006001c0156a0359500c258260341150400c551460b01c0c2c0071480001012401192048120071070358550400e40d038100400211b100f85e4802c41c5031101000d050320b070240310541c102d0342d00403100e05240d4140204003c0b00003902040605074409403902410248174420740f0020741c4040c114840c50002c128072842e043c01a48601c0c3c0b601d00d02142003924004020168908010903900340d1540060804c1d07250700c052048074050b004216001c803a038140000c1d45e000410b03285210380d40413481c103404910030a1007c1521402560584e42d9010304600b44140d890440c02070203282c007031900c00e08200080b9a01d83d4840b0100842c000c0401d840520b4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 148396294 1250 148395044 148395053
    0x302042c010b040e1501090506010311030405011b05030708041506080f0606010f0e030604020d050a0206030f07030605090603030702090a0609090809030106080a02150d020702130e01060819111f0507 87
    0x40200d4281203c60708440c5d540800c042c6464500c50444280e810041131075100d860050380107000700520125950000005c210038844150401c0340741c0040c000881c0c1042424103801c440600094528200080102c6c01040200d08608a00074540d40a0075001801a42c1c85440c02e00e000010804112143c0101d81000301568203c0c81503203410ba082c0c2000074240881800103922440300510091150f0030841d00c4005204003007245140841d03014100c16505d05049058070305161040f01c0324400241071410124950a000c80001e010b51406001181000155420061902401484d4104a650319440007408071040d001d03581000c3c0c056403e203962401920281403c1d550250400c902561020a0000047c0c0340d518499009101c0303038070a01d0300c509800c1e102e00d003e40708a58010b50311401450f8000001d0700d4550000300070703841c40c0c0d008011269030b031880c0d56100c250081d1428000b4100c0110f00011421564410480680c01022025a658400c000d00c24802ca14540d10b4000b6201064107410003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 148397544 1250 148396294 148396301
    0x10e041e110a0602060907060c150204060206100f050904120324031403180d0501060308130e0a05040b070c11060301030819020106030c030201050a03140c0c070b0c070302042c010b04 80
    0xd211904c05130417949040001c0310355a015a100d108200044440c450f4103000318120075402c14900301000703540e40c0c0d41d141002540c500d002da03034000ba41d0454500014144012450600880b0b0018194401c15500c545074682103041c4d00740a0000c0c90f888012801500400c004521180740c07600c424001d0a0381181003000341411a100707030040a0303004204040941900810045508400b150a040b400e0307070398a031503805030034107600041060001150550340b0b400256444010b50354040307040080c42d90703038181140c103035142500c014040d00440f5001c5540346114204121400380a11125541030241801245150340240c2c0282e9140e403000c5206c04800840d02080c0f1456401440240140b40c215290300b00100068400241400300010b51120300718080d4000600040128481c10b0161401c41617541c0c0651140094401c140074211000c281b80c4000b030140d40e082d100407402040c020f419642880020300310030360420704030a00c0c10083c0d52018004003c02940c0034801002140707142810091000351b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 148398794 1250 148397544 148397549
    0x90403030501060e0301060e0408091203040b0306121b0402160b09010209030f0601030816111f0801050102070303080a02030601020106083a0507030f0509031005011401080609010e041e110a 83
    0x3c1e41407d200308851085420901d030000c0d0015159a0390b0b440c903000003410b00c0504418003600c0d00000c0f9002544554510256110f200190f520350140b004079155680c40d0b02038050307406aa00c0440580180b941004c1d4043c1800c00004501c000700fa803100c1c0c40ba030400070401c82e8841d005a40029402c0c1c0315040900400d03112940010050040713504641d12141039009403070701c0030002034402c007411003400300d106029001c200000d400c0b0107200300b400000000d504155032023000810340607000001c3c3d6510009180040344d8046da68043c06880d98400c0038060340c03010741440d045649a070380100340f0a1003400903024101030241d50910003501000d900caa080f202d60202d103200e900080192400c280c0000c203c9000c298545031003014100941e0082d82d4a0140c500b07100d82510811400d09100303a141c0c0e12990680390007072032200c00300f03410038011a100c40b4110748982e0080c50300c80040051000e00c10500350400d101e8108075142c080e00b102511049100341400355030b065540256001503051284042d0301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 148400044 1250 148398794 148398799
    0x9110a080307030e040204030b040b0601180b04030206130305030f18040b010f03020306030708031605010f09020307050d050c130501150e012f010603140607110d08040809090403030501060e 83
    0x88040c500528181c503800744540c058140640074060700b030b050340e42c0d50440b40503591060b040c80c01410641481c0a00d20012180385020840d02c4121190880202d0841021140c00f4642141303894255401d0000c9900480c0e90841101c501020100000301c040c40070b0103424149407019074a074451440c0d034284500226610900540c41d01001c501d050741e0003002c09000503001e0601580da525000e01003440e00800c0c1d8011596400045605180e500c42c0143c01002d19000d02c00900401d200c90b0700c3c0804036080000c000b5411b0b4404a81049982059219008110b00410613184031107075180100c0c60859041c040305114a5444005000000c1483c0c1074020404045c945551540300040028003904145090800ca52000b240c0120100741202185904e41040100038007000707581c0e03d070039450f000f600c4003210028000d171000100f586118a807810200b44c02500100109207080409491980c4042d01c15292000b013003010b980980c0325120a40e000724403c0c0d034006403542c0361060045c10203211038401d51 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 148401294 1250 148400044 148400059
    0x25141612050307081b090307080102220803040302240d09141f0209061c020a020106060503040308270a0309030b01290a03090218060f0a0b160311030d0911 68
    0x115007607110204941c00f11720700380c00b80c0c40c402101504644900940c5510380d03140c400c0740341c042004070b41034000c0d2032001c103009018192013044607140b030929525406142110b9000b44070405c05894400b01c00148035004200c00403810101c0c2907410106d5015000c034200d001c1c0c40740c1c440c10800a000d2748501825440c400500307580c030b01c110480e204036600c0e01e102e0f5000f0358001c01c00469903600d400482d0300b0641d202004040c00f02804032900c010b5048100b6060155217041400504035000d070044a02c603d500d995a6200360392800450710102c1440644c00030344904c140c0f90003040803410400542d80f40d00917110f40c000c5925503d0442d83c3e0365416000401224001507000b03100ba0300101117405040c1645001c1501c0e4241c10004600800038880c010358407007095500c4030250440284058001d00c001c2c0c41d207400d20300000c4240f040c816002e210300030b0f00c12001c00c125444000030341100300041c2c0c461303c1c1110441100d210070516642003c1c1810480c0b42c0d0300c80085080014101d44203403400c0007954800d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 148402544 1250 148401294 148401301
    0x20306180d2712020316050907110111070503031605190e06070b0414010c0201020703050a08090a020901060201060503100c08010315140705041508251416120503 71
    0x20361038004240c0e01800b031200440e501d11072400140c80702080d0310541c2c00115216980c8002c444100a10442c0603802030080008903280c00503d0034000e400e41d81e002d0107181c03243d213038200c0846840d418504458903555a0354080032175591114001c0042e80e0090004540720300300580c800341d003c90f00703214038018800100f014400325449002403400c111b1103800e01c0c00c030701c45241010580d240b0412070010300c0c42441804000c2000720011007102003041e03001c001c201d43d10412005908034850500c01601044042c00b00c90341032403050b803c081d480503040c020f841c0c0c2018681d001c02c540c0d4400703820490140c1d445000521481c142040759048108511609110400c50800d01504100e030600000c0c1c9480c100c20004038200c1d1103600180300c08103030901a80313103620f44810004c006400074000c40b45098401c602c0c80040b18803503418603000f4000c0507002d000382c02d200f12282c2e02a1207008429803c0c070128401d1070700403001c0400944110b0800a0528041c0031a518000c1c00301e10110800c0800e128042c000e1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 148403794 1250 148402544 148402591
    0x60e0414010b01120f061802040f0605090d11011b05060714030c0f03090a080a091503021e0a1403100509060d0507060509010c060216030909020a020a02040b01090806070903020306 79
    0x2210380b1045078500084172900303011207401805480d00002021a1004004035000c0c02d113500a10481d00303904900d2101c0e07604d0700801c48651180161075035020703410040600c081500380e518058500d10504206141c004034580551040003940d00644898005034100401c40e40c000c03844880140701d404500b451403510384d50b5204640203141400e0300000b4084001071a50004001211b2a00e8020021603140d0070205402020030885c0d003e02d0618040c40c3c0d0880d14100d0190003a40c01c9038003029442c00c64103c001000031302c11341120300103c0070031110782e02030341c0d1565080c00210f0240070b900342c0348000c083c1000e050050314003004e0f00f0103015407411001c2c100441c2000c1802400c0e6100303803800e90713510700d45100103c1c0d502c828520060885840092010119107941050542c058441d0702c400708050358940200c2d0490194201141c05038001c094220010318140c6c0c001c0e0401d00050405507681521500b00614100084404001145e5003030001d005502e4100009988a0003402c2c001c01611b200900 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 148405044 1250 148403794 148403807
    0x506040f020f0d0213050403020c030708011a0a080a02150d0e010f0c14070f0201020705090708060a06410a080712050402011e17100f08060408071401020c01060e0414010b01 76
    0x1100070305c1651031001c201094402c6c0080e40818a0040c11540065103945095000740b0049039009852040c0c0e00709800b031418803d5100b0101c0300c500d03014112641d6a5024010715040c41c0414546201c4104514190200c00c0d00c02c402210449100010754140a04582c1c41182c08090030a0188841c1880c1110b2a5140900311390405610242c0200d2142c02440180c2c603242e102d8102a40c0081c0784010030000540c029003080c401c1070300b107030400310b56592001b06895243d9080c40504101da03e140c8280300c5201040d48001ca90303a1151000c94808010b18046009078008120b00d9000134242d406010341e143d0301815000001190b0b5008105134241756002814109241d00c00130901108000110b002500982e0183e10741c1a0f400d00c1c0c0713011440e081c030000088451038090035011000c1c00c800415200400140d262007154040306c0c1c0ca20740280780d00c5a045960207001c8228441d9000c010425001b002030003460020000e01890707810034181490400583d200400305800c09030300d003007240761460707030f2201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 148406294 1250 148405044 148405069
    0x6010f031202011112090115031203110712080718140112090212010b010f03090b0f0910060312030b09040b150d0204110a080108030429070506040f020f0d02 69
    0x414800c0c10310030030041640501303a10160494403000106108402074229500f40703104030b11070380080100d20a01d0315014a10b08032400064803a4006444035144d5034002e500c5200000c21030300070365040001c0c5e6562a24209401401c54000072010301c280110a034011040600c20038141c20700402960070800030449001c0700710401410030580905403505251140c0c400320f60140c018195454003001502d005002e4007200000a0000b01004002c0c02c0c242c5c1b0901c59444d0055014046401d55290700640710165a4080c0c00b40e5544d010715001140554014445d1000851044d20304040001d00e0b410080c0807100c0c146111070003080301c0010040010300c9190055031201390104c0e03001c0600c0d28003011404022942d24000e4105103001680b43c1c0690b0b100000c0c142c0403890307560b1007010343e80f1001101d40382e000e9441114288100b5200380104d01200c02221121114586c4440b0f051041c0c980740c039460080c4c15501512510003c020340070960510f01801c40043c0c0c0e05681c1706c001404640d010820400b00c45 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 148407544 1250 148406294 148406303
    0xc18060304120813081207080105040c020703021002070f061101061205060609150607060b040f02090d030c0213021603030614031002091512070806041107023c030f06010f03 76
    0xd03c006a401e98440c0c00480b6116003000744644c030b9034402034801c144988290368481c040345440d400080c551805020340404044603134041c083c100e14507401e0000c070070b5005080c40300758042e4034400700b0b80301c2041368104000c20260b0f89505007402c80a908908540d400c0e0404010307104d40e0000440811030005109030002e400340c80010390b541e43c1c0c94201000004034045a80d100a001401e041400f1035a009120300607012502004000c2800d90040d04070700c44c018803140c020010460800109014041e03480340d450010307247d048009004c61485040b40c0c0140301c242c4514003103000340010f05925201c0c00000e480381ca8400400b0481440020b651007920702d07040e441d200c3e00013648a6050320390301ca400102d86022400103891302e00300c4190b1001610f044803210006440030000805134900743c01252a000841c1e5091441d0488940034001e82110310b007450300200708400c0a050001c0c540c240141c94000480e256134550411100c101410004117600030030050b8858001031100003900c22249044a912 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 148408794 1250 148407544 148407557
    0x603040308101e0501081021030c151e092105040f0e0f0901020306060405090402180720070f1202010c060c08011410021c020c090c1806030412 63
    0xd400030700d8441c2c0c1c9903400800215094464810660800d10f0a8000741c81e42625120000e0790340d9a83c1500c865124803542620321802440115188101d401c12400c0c94082c4c505218400c1c4580c0310480a01c0701c6018018040756594418081c40f12401e40b5803a82c11129030040c8045066600c4580b1180c8140e0344410400c4070b08074184000d607020b841141c004020031404a6081c40d42c0b482d141c0c41d540f5089840b44403000002c0001005120184200c030b205000041040f4206810501441814500104104d81103100590540c0025981c8920984260340e941d4a807581c40015819040348100b280c00b404985c1e80c000c01003071007461201e158140aa60407115220f030300b441d007400100c520b280b030b6103405004c452506019400555210000f241a500c1200450a803080c0c00018004d80e803030a503d0345801a0009441041c542920304804502d1820310b03c11a403200c012800001d9040b081620140c036141c0002408040900b010111b00301000300484c0d00c07a007189425110740e48498105140070b01040305 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 148410044 1250 148408794 148408801
    0xe041203023907030602090a05060f0a05030403030f020c060106020c010f09031104110301080a020103060e0c0304030e060f0c010b09010e040b0403050705150702010e010b0301020f0f03060f0907090e070903020603040308 96
    0x10341ca10b40d40320610b081200ea609549080140080d408000681c1c010810100b0100c0c240c180401103801006a41c0340840c644440b00f8000c80703058001500c101e04168a03040f0040320410a40060402c049015010345904d524021380a454001803202c0e440c1400100040540c12680040d442000c99400a0904217545140300020340207100341c103480d600c18100031002080c2500d00160200100740300f0380b0104401e64441440b0f171111001207841200d0f4840c10000100003074030900900314003840241c400e90500d02d001d15042131035000119201640e030340d01c0394400e1262410031440e42c01084a20751514072420302d501d4100711558000c2016080c04000510712003040340821034600d0f072148030f44d00300030340f400c001400034040d00c005481c0720b41941c2010400354080c0307018800c075aa807141084240c1c0c03901010b84403119503900010701e05503028411b4881d1405075211210020721440855490300105410310001e4a4016800303401d1104000311248148016141c2c90102c2e0703041601402c02c03032038a64 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 148411294 1250 148410044 148410127
    0x90c04050c07020a2c1501031802040f02210405030a0f02030c01060f090f05010b0a140903011401080628050402120f0106150201020f0a050309070f0e04120302 70
    0x2c00c1c03000080d0002d0241c0d0000a481c4c00342e00d440b2041e420b0400700c21650100c0d0120043c4080819118480c19031800c01d840482c541c060740c0701182c0525030b078149a03540481c0c1e400190445044010b661802500041d5051039030000a5500c81590100c43d00d0501d141450744489a80f400341400041c184104900010356650003002581d40703a5810100900c0b00c5519260400f40e0a51940b182405031403e1802d446c801903554010141a6003030192100e06045014400701c500a01940c008102e0300b800300140380044c2c400b0b01403400403291860b1810200d52600c050503142000040520011034042c0620001c090380700103032500710f20600c85003c1800d0300d80c0d00014006c0c4880c3c40861145106d40b50107440301c060190010000c0710401000c4000c4240748540c207074240c0c480e1180d90b41166801300109580b09000d0702c041c581103403164044a40041d2540c180d40150703107031900b10041418440c400c100030000c13204508119001145819424094203445c0015442e01d4403004003140c0c1c4808d15039501a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 148412544 1250 148411294 148411297
    0x22a07140607080d0911030c1e04060906080c030c0a0803030a050a060509090604120f0e06031503101e02121302120312060913020306010b0901050d0608060702010b0405090c04050c 79
    0x8607005030b502d40c2d48910410180000345181e5174201d03041c905c5e20892026916011502007101072015041100e07880c1d40c0c02c0c544060080820165520560320140414409035903c1540094154040200315039070f240300806107010280034410384144ca03a04420703c44042c1c04025290006a042170100e940d07100c1c8680c14018291b243c002d00d402401071002c1203029800015954021030140180c0401e081d1121411030320b807141c03c400d01d40801c1c80c0603071040c140e04110f8000c1d0340c401641820a88034801100001c5d0030041603031120105191958000307400c40c012112481660108190114038142803000700106c22030008024491140005007200e040d920703015802d84550261800342c1341d0752000a2000b650109050360001d0203110500002850124071000c4500d0f40c2c2d80050083c68542c0c41d0020307004240d03007d42c200c2410800e0510440030751030114010b400c050305160001d00380c00c3c034104900a00b12061001818415030070001440028200850104240d400544001c00d140d80d6810308004c65 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 148413794 1250 148412544 148412557
    0x17060411070302010b0909060603070314010921110705010c141c0314090304050d0b0405010e03040b030108010e0c24071a060111060919030c1401022a071406 69
    0x30110001003010800d0303410f5001c5c0c44140c00c00c035040000d640b5110440d903034602e81100d1940c2c08d644403103014000705010340046590f8000c0140081100b101a548020402941d4110729003d0503204402101c550b030000001c0c0c41c01640b502c0108211481c00c0002442410b10340c0c4061301070f40020007e10038030503041c052010070112010801101c0352030010000c3c000c282c9a0740b25105c910b0394001050444a01004603000c89000800e040c1511420f07480c0d607403801601800c101c031159a00c1548603152202407001c2d000038460b00130f02c1d13501c941c500407109003516589681c0300041e412040080c10785591b0b00ba100000312303400080089d4096261001030906100754200941484170305194104041000050385200319020f0b600c482650140000982e0b4902d001e0b070b0301181c160000c517006022100c00041d240c5503180245010030f00042c042d26103903541d4080045902c096500000c141d200c00d10341b0050407000c0020503864642501c0e2012000761141654064451043e043e80710448482d03803070320706603a070307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 148415044 1250 148413794 148413821
    0x110105131203023603010902030706031d010903021b0909100c090b0409060306110703081f0e09060109050c091e06040b0d090c0603020702031e16120c080607170604 72
    0x40d80070741448050032204201c024504401300e107108001d41402d06000307402601c1d5010f0002c01465040060a40240443e0180280784081c00300c0200d4420900b401030303c00aa010750003900c414080c803892035500e000204101d0740144c4110082c04a0800005038600036602504000180344030f80e80b80450310120301c0e5105002000000c24089081961780d44000b080324410401004110040c29082c03855024105004e40450f01d4a80041d071a8450450704141c001040c42c0405c45684d140c0921051216090f16418130f294131280040c800345601d44205078100c2034003601a030908103a0000508615440700d01d0710720110200e0b152002e19101d45040d54003900b41d812400c0c1d00e6128585403134000f0004040300340c03407690340c2000000d0628001c0c07080b00c12083d00039001e0042c41071607440e0503042009024502042c0c0c4240c80000100704081c850b400302a001d0280700d8120301c1002e0810380c0203000290001c00c61a0022800d104407550884d10414249808284d100c0725a990301002500070000c4210170311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 148416294 1250 148415044 148415077
    0x81b16030515090106060207091a040c03020d0e0316020f0a120b100501081027020d090b16020705091902040e0109050709060207120204230711010513120302 69
    0x104100700818039003011046600d80d03180582e96603c0785401e0303070384a208480c096081440300f8801d240c4540c10904400315100c50007001190341d10082011551a10ba50400195011805400c5282e544c0940050485900019400d124610840945542c0c0c030520080c807420700c1d100411038a8603074440c108010304000c0103150300e200e080c2c20300c4020807400f00c0703030307025048104200400d541d170148100ba406080e01c000360255071070400b940c07510b010345c814441134480c40c03808242c0c1c40035400d940020a900003c89201081300c8a0340c0c60600781400000d00100031701c007180034000b40056030010304441191300441d2003c605132035809138050322600c4440c540342e03030f540000b0300441c0610b6041400c9040f0350080720100056030b6005001c580c00025409401c005800c1352900b004501c4143e10039545990005100040e419256002c5071a01c4162101c0420481108010040307040c1e0044007001e41c00d8034410003448549000c2017080c02051860700004c3c0804001d032b10312984180700b170381500c401d07001c1c0ea680076 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 148417544 1250 148416294 148416299
    0x708010c0c020306090d0804141606020c010e011b08160803041b17070b030702010608031204020406060908101109060a03140604020421020f03100504170403081b16 72
    0x41001201000c160f02900c551004603440700300024038981c022940356100d4581d07032215500c0c2d01a0742c03c3c0003c002c40600c07917041100d03041c1601048110007812179400400c00141600e0005d003e0f01046042203050082c40c15101030b04114441600a02590043e007183c2d403400c0c8505e070801904c0402501a11a001c040f040001b0000321604a034401c0f9410090700d05074650b61136414902e0700350207103010805d80003d0005c01941000a000d1504850319000100c4c110752140c02003850b60f0881a80940104074210600007981054850030001d060340d4039041038443e0400360f98030380d901341c0d041100e400b195a6114200d80b01c030312a0141c40100c10010180b0b030741c3d840d84200c01800313460444010507107165403d0128010307140600c00ca8041b104400c5070080002c0c2c0149015000110b2402d0070f80e0460031280101d2541d40c0e081c42100d600111408002802c0e050900340000300c01c40c0780b1416030051104102c20b10205210100340c0c2c6160f100d001e8071001f046e014210b818207110503040e141030700741c000d100003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 148418794 1250 148417544 148417547
    0xb070515010e0405010f0b010c0f020a0b1c0e0109121d060f072d0b040f020303040b0a0f020c010e130b130207031206050a051203071a040213110d0902030708010c 71
    0x440d400345000d00000c1c000c08150150706d208641d40485010f02040680901c000090040c0c0991006c190000300503075601941c1d821411410781c000303202e814000800100d4020080c00c1c5e80304a90024800e40300030406842c81d59070b0200a00499161502403211600b0300d4148000e4003000c010714007001a040320f031600c841c0d0014a500d9000000110307050300c204034006a40b1103000240d400c2c4c1d0709200c000e04210100940b90b42c154058068001e480c03407110700700c0d0031001d80c600b000200014500e90180f1907039180c0e80e950080c1154a20500c034821900f0180032452140c0c2d002003010810032003190400e0342555074218100c0200310b03181010750091900315904070b044115902a0003c107003c2d4603603050a442800112040710210b0013800d500010164090009040241c0042c10100450046903c0c0c08213680305e48600301003507840c5904d000010307020031045042c404c00b0a600810b850380301340041c000384d0301d01c104030340033b20b030311400005950b0300745c410a540e420824040100303c610020442c03842190340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 148420044 1250 148418794 148418819
    0x90a030f1101020a031b030e180603120309030f160204090507140a0803030411030a1a16030e06011503060314030d0605180105010f1e18080f06010b07051501 69
    0x7039800c444140059403080d4000f16074201a00d0381540c0e032000130702ca2858189800301051000780d0400c0340400d440c00d559202e0703006410420a084906c02580d1412000301440c0c10002d15083c19501424024885c0000e400000e8a24005110100a84444001000340014a0843c0e03010794010304105908046c043c010030302e034007523030301c4040c0e0300c0e80c0d2801c004180b060500440c820040c841e40100000780c0807414034007685204450007000e0b10a580f003152140f03409448040040c0e184464081c0900c681207444c0340c0300e8402d40e46181014055842c0789116280c8541d0140321702d0403244010451440b10502c00c0c0d020101075580851070042d8100301266480d41d0f5001100f06604c20b41c9407240c041842c2c904141a410f01c6425110040c02caa802c09004413956040044040248010241528140e8031240c00758080700f0002c0d07035240755404180081100344030160307220500e80e410181c16203d2250010580506440c2001070403560740c4124a0301c6860320344450512016103284600100e41501e40e0790 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 148421294 1250 148420044 148420073
    0x15050315012a0618020a0b071b090605040b011416081b060a06061b030c0201030605041e050f22080c07081b0306070c030e0f03060a0c021c080606030a02090a03 70
    0x10041003028413003500300780c2c0410300b00340195011486203c100070340c1d004040207105407881429540c100e4000780c001625400305607080110b4072521200e00340b01604180c41580b0986209217801700b5214000d000d404000d104400c0800d001d4610420300c0f00c10310041c039003103402c40790201c41c00504682c3c1002003a62580015568003110381d04085000403c6441034103040c8810383d1980c2d007443c035480300e035030180c98102103044101d0515446840003c0c5a940da40300c0d09007a1070a06003d40c264030668140c1c0340450360000d0a402c0700341c3d007180c00d004201c801200344540d0341d01c43d91400300f100c081504102c0300c0c600500600c0a210701ca80c0030080750701003011880303014401d5601a90070111482c0c60402d83c0303c18003116524002080b0140400c0480d20801303005e03480f82005085d0348060f404140110341441d000701e8009400548605a03113003110381c10446400f0f1802c03c14a44d100d0325000d114010000240501620b1103044003002141e900f010a504613588100018000303c03200c0d81e01d180005001141c50f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 148422544 1250 148421294 148421303
    0xd0606081e0f0c1f03090501110904050a05041115090405010f03031e0e1e04060806100e04080304020d020109121a070e0904150605040f020d050115050315012a 70
    0x124140340a01030010740441540c5000700f0740d03c440c010300c0c3c55610b134810718010508100340d241c10a00020640a1098480307180d082440f0581d2407103c2418401036aa0103030142000303519110400020a0346880480d503a2102281c04091070b40615442d1001c80c0502c04025a00c14070f46400001c4100e0401d10000c00c4911944540b04a09225000700c81119860700142e004609011621101031500d81d4150609401010000013062100310100e802c6426a2700040c036154494014801d10072480c400e204018500a240316249140c2996a0783ca40e00000d4402801034000320902800c580c040d070320700000b03010404102400351160b8204806c401c4900a803900c070000c0d5540205405034400e16039902c01c88000b81092225440310740d01c1581407500001c10094680e61110081401da46030b02514074072106242d805600e03103420550440031501c0680c0100d0340600a10f84074040c0c40c3e00f250960341c1c00041c1c3c0c49844550407e090059642d40c40ca9240e4140c500d0141d2010700c2d5549003080c1e42003505025 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 148423794 1250 148422544 148422553
    0x6030611031302190b070308010e01150c060207020a03050a05030a18030f0f0507150306090f020c060109150308040308030f0f010b07062313050c060f04050d0606081e 73
    0x8034003202911040e40c2104000107014100405820801d640700f1606850125580030035650390200b0606400c40c2c00e0880c00580d004004108603605035000a02420700125031101103500041d0151059100510081400782c0104285040d562079217002c070300031500b00d03040d02c07202e111910b001d40c5c6961012400d0b03008180c281c880f02009110f00751803041501d0f40a03c0405041c82a603c0c0e18428100c007005c03c039900d201302800843c20714862030106001c1c0c00f40d81c034080b82041c20400704c2c0e816103405402100d40544144028845000c0014400c2c2c11142c062400007102446041440500140e5800262040a0010b00003040000d4403008510500b11400c2076456511816000c207602d402c04e10808140c0c002c20300810002c6485940070200101c5090082c0c54180401c541c002c418010032164004195103034203907002803080900c00303030243c680f044400a10b04151302e00518801c1c05070b4010789001d102c1e00802001085195406a000740488804072450b441c0500680c0d580c9014603221001340303014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 148425044 1250 148423794 148423811
    0x501060902030408030a0506040e010e010c091d0c0304051501030c0501080603060705040b0d0b10080f07030524030c090f06040b0105071106130b03010803190503040201091a09090109060306 83
    0x5031090343e0150764482c13402c914540311000c444019010242440c1e502541d02c10410b14822800d00c1010150404000007045041088a000d41b0300345095101080e0401160000024069454a100d50203102042029101d407100e04090380381c100b2400780482000c0b00703c030000c014403100e01c0c2c10700e0850740d0903070b10a401c503903d8005250300d4460544441020600600003445070b055140090101c1e58a140e0000601c0d000510025841074080086400810031000030f001e01c0d0808814469841081d6050600a600b80801d8a181d0ba644100140e80b440d40e0020b07280320669024440202100300003072508110741030030f000c4200d1503a019140c00b0b1007203251400b49412540101c0a40c2e00c4035410403200320328202c1070024411325900010b40b600c5030700c5007a28041102c8403d2800f81d0f019003412001581c0303c501e019509034a901e0341101e00b2090003000d104000050307138400c840200f542c414103058040c82e6000400703d11180202c0001c598407804179000440c600c038072076002600322070140318148610300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 148426294 1250 148425044 148425059
    0x8010b09043002100c0c0c030209060105090a0326041d10030b070e0a0801111614030d020a0e0a0503061305280204060b04120b07050904020c150108070803071b030816050106 76
    0x1400078000406031000c0745010802740c641054044d60010040c14403920f05038200c0b0004094075802d8004540d03803c00410510902c03c0d8516402e502d5060f151001403400d41840e420050f0042c1e401111501a54214001500d021144810400a40d03002d145401941884440a4064420001c0c80e80c001c607108200007600400502402041101c010316240c9400800e407500c0c90080c0200c1026106100340020070000c4401c10001405074001d940001a29542c01d04801048440809290341c0f103100141c000307006035030300400c400790842c88942104d03803008400d16295040c11000300c07440140700741c103181c250340b9102801720611829200300c2c0c08200694035042c1d801298025030260024030000303c00d1031b00c0040d1602040701d80094a9040540c01c2c501e05600080c2a030340444150205900b000751900b100c140640c0c0c0c80c4c1e024100800280c448541008413541e52030045480c080c02c0301001c441124042c5c0440841c110280d070308403080642e202c1440e003850070305101d9802c088a49610b40310300029402d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 148427544 1250 148426294 148426307
    0x5070305042f040f02120c04090e2803020a0501060602030d05010905070f0f0203091c060b0301060b270603090a14070302030304181e0b010908010b09043002100c 71
    0x4100a00d650035800c1d40502c01c1c48010803e00b0140c5980039400c204034512445841030707040c400d00410081603507841c00c102082041d101c0004c008220ba0740075080100607046000c103042c000341200280110007000c103043c1245418640c140241070780d468034201092156010000300a8100c00350000d00007644d0b51040c0c00100c03a0304480810025240c00c140354505131051040506151413481201e04000c10324000400801031600540e05a001e1070f0711060030024940a070428450088001300101403603e90321101d00d2140385220a00c1204110041c00b40791101b13001d400808001070070194603841e280e0010790360b80107192819101004121010058003100041d4030082d00d5018015508240c90000075003001c01c032000304882c3c426200c032020070036800380700038204800c1115200410b4414180001610ba182550000a5070f030741003403409112074982d4130205822640c01442024881542506e100301c80c0240c4904540c00510f02c0e01d00e04031903038000b9640c0703158ad0003031004120b083c0f184102640c0b04d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 148428794 1250 148427544 148427603
    0x30b0102151302011202130f0902160308091504050a0b01170a30030606030c02030f120406060302031006030c0b1204060506010e04020406120b0604081903120507030504 74
    0x2030701d0700c50002424088070042500d558030710605280c07a46010203040d0307001381c0e088115000525951014104400e1841c98880c41c020080000110301e001c034110802c604200700e03040c02900340610f00011801c00141040500300074240403003224014100303403420b1501d90b46034980503920301c00d0440010459400f21304918020112000083c01001e2640d03444d0244059140c01500b1103807030034002c4505c1244903800c136aa4281c400e0345c0008080c1e0816002038100d0305420750070411035205000ca40200c0c118501110408000614090700546e6a13107071400c00303440103410094140c0980c211040c400750b1260040c1040d00c0c410149034002d1030f1210030010150103030300a052042030096002c1780c040b07401c0341d01c036039000401850030b203281504003c0810142c2c0c0c09940044000380c00059000c10044451144c080001c1040b18418681072620302503c0c2d6400d000503684046110414116080601420044060001941040c0200e24100c1400380042c2021a0151100202c2c480c0c847c12108902d0842c006 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 148430044 1250 148428794 148428823
    0x1207050901150e15070c060302160201031802040204060801150f0c1b05060a2105010b09090a02090d0c180b0603180c19050102070803041a07080d0516030b0102 70
    0x140342c2c0780c5650304003051031008a410622038202000203030380d212110003011400d24080d42e1076407600245031420040010b54800402c062040c40301e016820084416801c2c51364092034023280001e80324400010710b20310798600030b5000d880000c0004100d0b8011078030754101c410064805c0c0c00f15803444410b5402042040d402000038200c40316038030000e609010800341c2c882c00d640303948410a8803000480c1e2030354071000d042000324110030300c3da000001c4803c880d0b242d61102204180060f514010038021540600001a44500c8444000820b96905541900c00501d4000d00c80c1c202042c1604140f48900168055607512611811b40c0d0044801c0c54002c80280e140003615080c0b0316640d0519204022440c124064841d024204881c2c11650b100c03041c540b1405880c02e00440703020700d0f0000282c9058450780c00010181c0043c8400c00c040c403550717012201c007401e00e03c54242d0794601e07a1400e40780d0345c030071a814104001c0c0380205001200c04c040b0020620307441c240e141008a10986401681e1f5003890b0602440c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 148431294 1250 148430044 148430059
    0x6180f050a27060306021803150a0221010306020a11150a020c0f010f0b040b0a0b0406050a11010e101a03071404020f07030309020109060f0e0103050903040b04030809120705 76
    0x8001650000e00b801d44142c0724804032100008241500b040d205194400d03900d03103030045403100d1030742e681403000011400d0880041080d0035a140000148160003040d04020a034041400c14040808003110211458010641c440c2c175a142d00d005002500661041400624041110210300400040c210104c11078003500d6080c9a541101c0749010f075100008005260040e24150780700304c8800d015000307030b80d09c110304041401c480b2030081c0700c1110304070300c14684603001d5100304004140940301100c042e07804c14039003244d40700300c00c02e4151102581e040341800c45602c0e1a1484c0941c40022500d400000020007040c403002380000e85a5004820a0b0b01103030f45034010100402c451902c06600f1700c50104090030140c100f0107208079050482d040b42e8405d5011a880e0000704086607488007404000d81000e003490494290212001000040c10040b0076060540d1031005c030702c0e001d00820a540007412448201a0340ea922031410303001f2500464501e41c06920360050307060329034501081c0c4000313a03003020f00401c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 148432544 1250 148431294 148431299
    0x603110a0c0f0204020f0711041a06250816110102010b0612100b0f19021b0d0c0b0408010e1b1c142a0d0201080106120609050106180f050a 61
    0x399090360b0741540480c3e0003607003001805184400c500103495107500070f2080003619003052061209894400490b1950526456a48603195460380103940c00c42510340702c03050084d0350944050003a040521000b80007240081080b4120000030110000f940784200381c8410410500001a8240c0b1284000320394041400d00280c030300000d00c8611507a22070702e640320a0f02201c2da00c1c03821244e40e40c01040038203681907000402014500707009030b88250141841c1f000305a00042040324944407052400f040384200f45440180b01803010100900300505504400190340d40c2d0ba90240c0c0340200f0310407003025594050a000420020003c1c95248001e100140c003441c200c81d0500015002134041c117500310f9044407801140e140540d000c000c00081c0512015048149100004e050398078442e40704215803040700046d01e410300503688240240c0c1110380d51304040011180d51a800000f90406401c4040401d2601000240d500c0c0d02445540510355045500070002d0344030302c2001e12001c8980a240d4001410340c508 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 148433794 1250 148432544 148432553
    0x315061017010308090a0e0106050d0b0414190c0e0315060d0f081e13180905100b0906030708071e0806070207060909140c030405030405190603110a0c 66
    0x30303000e414445103001d0805003020303203049800c4242030700207071000d0001040310300e4a81404881d8201912981c08410311941c909500180715228822290f40f200351992003407005500d40742c100c0720710322520200c0d2481914001d0712020481007003086054045040c035140e014040e004e1500401c100344040c002c0c0800c103040c1d00a100031644050000d81d040310003a002000856040c0030b00d4030009100703500c0c403544c44c211401c0038031071519400c09004c502c540c00c00035400d00004581c000707411070b0a404d800d0b0845004011b2140d00510707507840060a42e0041c68152030b20400c080c1d000c0a800301c1e085545074a01d488101c1803580d902d83d1401030081c2d03948140e81c1844000904146000910200394a250503181c80e801014106801070b00c1800159218640522581e600a0841d002034100d200040011800e0102644032001e0058050b00e40441d000002c90f00707000080c070840307010340030142940080e110800c44a4490900d1881500700081c9404058891903454904407481031a0640e00c0301003c20b62500c0313 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 148435044 1250 148433794 148433809
    0x302070b060f0a0b03011503050a05060607030f0e0409050102090306281109210f030f040e1902070c06080f041109100906082104030203330112030e031506 68
    0x150fa441100001c0014054031940021406428a14030030800c2c2c0461000290945038003400598141d41440b041111584810701510318003034141c17402d1140e4020709442a115002c45644441d00a402c108c2580305202054000f00340214064084138025a280070500c551040981518002c1e41c0c1d00070300c0c1c0d401c03080844d00f000e130b9003008585040303150658482c0007940b688940d0780516141c0482d400401c40507a000d002d82d00000c41403130003542c0303010045401c10403e03114900a258018600d100070450000200c0080041100000307811541e1b821123050488201075140f00d6180000c500e080021031200300c0e00c9889014560115901c00c0c84e100c80c070108100520000c00d85004031840d07902c00100c2c00c00e6809540000c0208901902c2d01c04920800c038030384c7c95000741000301d580d07004110130001610001003400201080090030104540b501e11700441c00e104420344040d03440001c0d000490201a40c01c80c0c0c4040a01c01d031038a100d00504642859240c03104004468035800c102c0d0005000c5041c000c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 148436294 1250 148435044 148435069
    0x1802030714031503060709030b07080f07140706060b071e02030307020f180106031e05160c03021e0601061b0209190e0613030306170304090b010521090d0302070b06 72
    0x5030a52241d5038110100345812170031982d03d4002036070701c002001849000c548540e0450160b2801c2c58861600000d04171201d40d000c0d20420130003440c400740c01e64035100d00d0155404650302840a100e46591a0303c8200f6a4000380815562030100000b8400c840811010003271625902802443c2007002e035400300403808601c401e0710360f00070001600c080155880c884070517020b051261400180120041c1c0c0c0c116405021080c0081154644014450303c4800b915400013880307003610344601c1c074038042d280880c284071000c2c0b0940c071003110030110080107140c00b10f0600d040e031380b4035a94100304800790300808844045820307010b900040c0d1035011808008608a070001d0f02d0310000c00100b0b40c1c1c07610300b0889182c040304450a480100514944034100759044c000c060051075881652050304020383c070a0f9840340310303504c10b5000c01680d03a02a181035034007550903580d0103250380d1803030219001d1400c1d424000600840d1044114052418414a41d90103803007030f00c410540000807241d1590300c10050000307000050 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 148437544 1250 148436294 148436311
    0x90602040905040606150302070c03060c0c0b010b030f0a0b010c0209101d010503010b09100b1309020a0e011106070507030c0f080307020d090501020703030804020d17040807180203071403 82
    0xc00020451008500075140503500c981ca0020300d180c901440c1c082c049014060110401d03004200e20808a10010754000580c0d4008500094558504a040d01e00d2103042000810101c1c000307000068100580c0059486008076064224940c0d4950b1601411980051481800700311f0301c3c0340c80c00160a207100c4155010b403405440b002910b0721008243d0610b080082c1d00d010444107003005210604084c05014110f0500369103c041c6410030f00321407500d0140d240212074012501240110701440329041000003441100811580c1d100d4240d0014513034504c0428460100711945010100d071035000a42c2da110740001c0d03990504001c4c0603641114a090601815100040030041d84030104917604000c5005d012150010191b02e00300e02800750101600d94001e03410740d0005401007001c01c1d04500d000d503202e94103c4039103c802c48540380500b540460b0441d2076032902e50208008c600c0c000000350358816030710448010100e0031075481d9050141d11044a40b180025403036002c0340c40941e41e010256800c180e14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 148438794 1250 148437544 148437547
    0x150907030c200c0310020702031c0302091c021f020d1206080304090504020108100e010302010806040f060f0503010f0b0a060f02070317120903071718090a1406060c0a06090602 77
    0x544010304000d401c0b40e4030040e10340d0002000344070309140400c254446034a9921055050000070340000c5c0c1c403141c039003034007284940082c130103021421300caa41240c0c4062401020000c042c0a10002d00403200b0390040c0403402001d40702c0f8070051604204103800d0303004d26079600500d00014110f508443c04e860a5000346801e503110003002c610540c080c0040d0000e4030141a00042920b81400010000c42001e424074161140d107040070700c050700014180d607054030740a081c01283c685920b4041001400e44580c441400c9180c2140486c0c0d10748410103000840700c3c00c80090002030441e00200c0200c403502e005040c0d00001021042010b28059941e001c8010395074019a0303201d0781c0c0e80d22084a6101030270f030342c2c3d2604100000c0740300303189078101149a00a81400700560802100c3d549200f100368000c0c844a50031000414030345080641004111201540900a03116030304080b000d050182c21246a940111110100042c1442c10110152048608508000c1258641030b031540e40040c00e40440c2561050340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 148440044 1250 148438794 148438817
    0x6060c100b15030a050901111903020f070204090f170a0206060d0203120c0a12030504030e01032a1d01020c031905010b040c1e05031005040b0406050411040806150907030c 75
    0x83c1d03108004c1e4410114283c64400060b608503030896294000e14401884582c04c1105012095810145103090044e690924018201018028900000d5200e4100095003081140050030342c0200340c800c288200d9030310701c080202d40c224000c664078400143d0203040020081d1802e900c80b131441c180064140d52038901e40d404084111313480044000010350102d841501002a8041c4028131014140740400180c109960020413010102c041d05040546422541c0c401c0d020740031081c107540321410071324159a0f204180140070240d46649592007041400001c040d95400414000d0f041c103001005001a80c0310a000c12088207002801170300c196589481072551900c80388100a100b50164071803140d00c160b40e42901e00c0551070b1406050411105004ac482a8000e99090038140d0b10126004100032200c070000c1001044203078032040e445401c100c09541c240d44028018420b452250302901e5070340d0f03541a082200103c0308000b641d000013440c030025500522a03070084021241d1032030400810728 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 148441294 1250 148440044 148440079
    0xc010507140a1b06050f150a060e0d11091501080c0c06010e070201140c19030c0f0302160b0f010f0603060602190201031508030301081b0a032a180506060c100b 70
    0x17401282e481503a21549424410041c01d100709080a140e0111000d05105082500040c640d071032072400a8001d90f00800c2c000100300280b050503403d0030000d095020070346041c00460403407035151820140440c03109004203001889981c116201040031400400c03042c0d203801e0103590f1f0018024038010455603078100f552030b0300e00b0004070700f0701840e071901c2c0003a100c81040e00d004020480036005401454503004a030150680c000038506120006407c00580301d0f45d00740903100c2c50f00300300b00300103241303030142c0040040e401440001d0383e0695080613884030031039031520420b4049038202e00961f030140c1e00c240300c0703004130101603116240c1841c8180342c0403c141d10310441402d159025078000c0c03055074001100510803060108400c00c0e442e19035540030171120350b4080101c1d413100d0081c040900031805442e40703131050660f9040c5503002600040307128406c0715941d51290503000300c090354900b00d0301e0400010803807628202080e01c21a100f20000780c00c1109803815280000c1a4010781d19402200050080401c00d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 148442544 1250 148441294 148441301
    0x110301062f010218030f0d0e040603140a0c060c0503030619091404060506010c0c05060c070509150103060b070209190b0402070f050c0d08070818060f0c010507140a1b06 74
    0x90200d480090303201c142c4028000c080b013000f208228041e6024a248100340e40000450180f4140e044c14040d103640030082c04613019112540000c1c0c041003840d000110341c0172000561143c11070040a0007070709181c40716001c5920019241001d41203510a1010030300c14a08880000c0c0e400a04c803510055069490101400b80e84210340207400c140c019004000034400b0b00d0190a07172140003440c1c58460f042c880da80780e201103004e9001c3c041c0180d802003103001c000401000420050440100a2269441c0540c030071400c4000340e0050a000904002c800a1041006001e0ba920341ea03005241504640d01d8660880c410215080b160079425150305449041340c8680c03000703080c0540a0200c000701442d032401e2451900b00007075003581c09860720020504c0800c0d8844140c503040c950004803195507030392113005030142c80700e04030038a5800704001600401c000e56800080038042107a900a1005a035074030429180560b1004186801c41810400865058031540000d030201c6410105028021001c1d1142e508a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 148443794 1250 148442544 148442627
    0xb04060203180d090e04022103030405010c050301050616150c12050c0702062218140601020c1003150306051003170c1504050f120409060911030106 65
    0x698000180003001ca0819000c100e1115000c0003414043c00709400141a01054824480c1940210010404540c0c071000104000c00348003524103501d03680d019840d0b0b01d030f81c8143d8046445602e0640c88030410350180096074101c410007030800c0c0c103008042070030b4031200801002c00c4400700c95141d4401c1e504901403040300c902050a58550034016609200d02080b61005044034117071030310034400c080040c0c2d111b008590305c258506011003001c00b000c2d040b50102c001d0540003803456003005030b180c2c0700e403115a03403004040c90444013140c41152140801a6155130769500002e40007001c40000c0380989001e90081ca0341800c840e041c8504041d0740341c0307401040f04c106681984010f000800d0800c1404800716840002014410601e40382208a21a0640d40c10304401d01c1c0c5a0060301c2400241803007c01d00019500d081078005640c407166400d4010303000e0340d10070b0040180740c130301d000300105420103544568041002e425070082d15503402c241061312150b80030f6031040e40c00d00c05a41143c3d51a410107180c1001b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 148445044 1250 148443794 148443803
    0x151506110f01060305060703021b060109020a1b020112051b0315030c0613050906011209050f06102304020708070c0305010b060f0703140c250602210306010c0b04 71
    0x26038080086a5050038410200803295a0514800384085031000c24010380100150030f005960b590803890092941500c01d44900050180400014101c0501e8006113540e0741590b0340c011030080c031040841d0940091600c040d00199105d88140101016503100b942c1002d2140761501750700340030500300f1405a2080301c10454402c0001c2c1180d0603810304000080500408890280c01c4c503480340c4a10b0807800c503510640d84207460000200e03035664000c0598038020404218103105064040c20031340e03901e400010422605108110000d406401c1c480031640036110600b60440400c00194500e00d841038003142c040d6849a07080124074002500e031402001d00300c0c800d400c8032509615505046e4211f9048868850103100308105581d0000c200904032804141d040c1811000b035100a07400d031115008032a040711040c41191800ca00c941e10031080c5652210003c2400142c2a40384c0000b2601c880685031014500ca00040d4100390088500e4060340d443341041c0342104204200740c8413100c01c61400d590a54 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 148446294 1250 148445044 148445057
    0xc04050601030b0d29060d2402030a0207020f010207061209110306070c0c15050a03090302012c0f030711091e070f0305090c01020c100309020a08031b06040f151506 72
    0xc58100340c241840d284030060341c0300e84a2440d06c0004185c0c6000d05990060648808841c100038003081c0a00901c01d4480b000001c540b82d02d8261003500c020744c801d2200380c0c418a00100003000e15880001c042082e00d54a0780c59290144285803070758064032145808a641503001222400183c404101f0307544180d5072940d5900781c42542c2c4c1403803990303494560403200460124184004105400c2412102000f0300c0c1c6c60b000400d50103a040480c0105036504868107048000c5000e0014101040c032407a800c41051401d0b0b90090100160030b56407880743c2c54005084d221110181803151410320403855102d02200180046110480039042038510100c8441010550050500038507990510880d03a02c00401e6004050700041c94001035941e034464560140f1880301c140065000c00e210f40c21860380240d000e404800740d80d481d0481161260001c448003a00c40074403802054120100040c01c0e4011354108624a0251404e0b440b154a60b0724000903210690b51503403c0c03a00c0d10214101d05500420b100d03a10308 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 148447544 1250 148446294 148446323
    0x929040914240112050c060d0f091101020d02070e0c0a050d02070308010f0602060603070e07030906090c060e15030403081b070b040212030a020c0d02030c120604030e040903020c04050601030b0d 85
    0x10b408015041c0c00003030280115501d0180014800a02e01041c3c035800c890304c1c0e40300d02e400340503600900104003607117078042c2c103200c855410826503200c50176100304244c081d030b41041c40201040343d64280c0c1d84508130601e6151400700d051545007070000e105904031384c9006890b000b058501c2c00241d0380100e100300c000401d400010010b500c20102c0c50310240070a48060801030030400300003541e480590003012010f4440c000441c000c2402541b010301c00f580d004100740400c0401b41080c000b20000c5228140100b500c2301d080030854600510310740d0410f010790820600719100e40d10b080f1003801b401081d84500302c80100344000101844405860704500c5030511401d54541403045c4801000307143c00d000d40e070354824810000596004502000344140035214411030402c9400041d01d423903403072244a0f81129a0740280d0210000109072244200d010391a03041740c40c800724050000729042d181014005030410b010140310762815800150b04101d0500d804698140c80c640024034000348540d0840e5a01c1c01220380c5d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 148448794 1250 148447544 148447603
    0x9100e0112030c06151701090b010603020a09061103070b0a02030405010c180e1b0c1005070216030201050d1e06060206130b010302060304030203040f0608010929040914 74
    0x105001d41005040200d920500340e070042c1c46008248001013849450710040306009407041c40800050180d20074181e84414000c038038500820020794183c9159014100108000e4043d0081310701d03a00f900ea41c1c1c152464541001100c8400b034034284211b16002c10041c031000708208880b0303903005804a440c010303a80e04051408508480c02501c2c3d28040c42503201000220500d46500c0100b2200780c0383c080c0c0d0b4295101d40c000da078070b200040450303041403c0c0803d05c0e10360900000b5454012041d40c120401117a12915010f03a82c441351070391201d085d110005410f10040d4820700242004000704e20000c20074480c1c154412404250852140c68110ba480c04100240ca9040208d1a00314560444074950203065854441031072805010207401200000045402c140c803c10483e40108034610130b40e40c0c10380c2c07181c800804440f070038410710041c41d003000c1c0c0700c115404c002d00451004c0d460b41c01c486419194084240000703441000c600b030740c102030790082d10131030742d5010301078014860a40c0c9418100c0c54407000c0d5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 148450044 1250 148448794 148448819
    0x601051b012307020a080316020708010f050403140f0f090d02031b010e0a05060d05062b030e030d080621010204290c15040606172a0d1403090910 64
    0x1400071940a80117040c003040c5020101c03908050b80d03000d03030080398450780000e0303281030f103164172500b203561906400c5e00040c1c061b84d2009008912a5861f21403208070000c83e0b41c0d4501442410303010b01c01c020815003489403d568024100b44001070060000c5840c55000203017010784c480c0c0750040305400b41d0503840381e941e400040101222001c4440300312460510340490014040e2800b45980c140e5514082445a52543d181c980c1d010104102c0f400d407240d1321030100d00042c0d5121300480c00b10303116054130402840c02041c200a01106580c030319203203070b40710000c00c501c00036034101d43c1d02d45034200110100d5601003800207102400b840300002e4012403d4a186140b010306d00000200b204c64240010101000f020803100308070411910302441d55120750400c1c100800442e4842d0f1a05200c0c00d601c2410100c011448406854110003c0800481d170a2440324907801c4004000d94000c0c00401540c002541042044007103500000c22203007001140c030041402250107603800400c0c004c0b022420010546d0410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 148451294 1250 148450044 148450051
    0xf030b06043c110c0703060504020613031a010b030405060f061c03170c2104080d020313050c0901210501020c010519060503010209090c07021305130c1205060601051b0123 75
    0x9800c04d00c1c00341004c0000c1d4070b54000740001072001d5120004a4103540c0c440c01980c0607824075171a1343d611507a5078a4500c0750681c04d8000d00390680303442e50001446046e6401905c0c40349401201402140c0d039805803256007004020704a5602210f030000b4801454011240010300700e1180d01d0f40500248078259403000d9010082c1440c1c101c4008101120544a484055030003503422034150031456141d5180c6000180500d1240346507007803010081000030361410641c4480300d40682c09540c3c0c20a994410b1100e00a82402803404609010200c0b420241c140665000a140074200060a000b114a4094250703903094030b0307036580002200d41075401000c6500c940070050100720021483c0546190105140540061041d0383c10400070030000255103034940c00014070804494200003a1928440c06c01c40b211032103000b070303d81226409002c1044641c43c003c144500e83c00c24004d2219a540c000111401d51040c0301034080780c484070f841144d07148024060390419209910b00b0001c1c2e007000780000014050002d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 148452544 1250 148451294 148451321
    0x80105030601030c0b03090a02030d210908040b0a020a0f0b0403020d020a0b0601080403020f01110417070807030215130803040303032703030c030e03030a09020a0f030b06043c 77
    0x700400000d640903c2600c00c40704904215500ca80c0c903083c030281005040c010294250142d6009045408d0340051441403200c0351902c40b076440c0300800402c200729501140c004040d210200300512160302020058000c61382c13680b0445110031004e070360703910394100c00d25011615130324a07405000c201901030203280d503160803134802010400c0854403800c4601002600321414041d04401040030b241c405d1000c45400b00c6100002d0140d05852540448154450300c030302c0030140c0115141d800101c80204a01c81102c4043c0014a902800c40d000c0003492070500220200440c010043c41346141c88410401b40144400805191141d146080c0070302602d001c456403000d004500700749942e0b503410700a080c8045a815183c0080c001c100b0480581c01069078200e403110510002c0100702e4191042d0308a900313040d2007035030401002c07981d914503400d48141d1800001c02e0040f9103000580142000d40c00845035082c07060440c0da011300c00940040c1070305c1500c1c654030b030140100040d04c80300035018011181c4001c2d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 148453794 1250 148452544 148452553
    0xb090f010c03081303110f0609060610051c021b070501030c0905030604110301020f04091a0301050930040303020a05150606090402030907080102040f0303350a140703090308010503 79
    0x1039903000308400c00013000b40c400b48000b5201003080c0741c8184a00300381c1090a07012181000091001c13140da0b07003003c0b2480c940e244600c01c0007070424103001c2e032900d071310801e43e4803400d003041a4061103003c150442890024500c0e42400074620b07100f4905811040c0005210107800900c0c00c1c0740c0011b064034800554603090001c0301c4410402c5031400120715a0164000700c5449005800c080028068420764824a1180801240c04112030a095104e420a40d041e11000b0180d45004424075090b2282200e4060154003c00800d14103551410486000800c244026080002c00c0c151030455942058100b07800681c001c00c4000c00300032007040601604520b0780d4600e0f410f858501c0c00030314207205158085000b9134010012a107010000c202e9000905440c1c4020340d212602d4030070110030000c0e503100c2900004d0103804e40000c071100034105165000f28044a181d407000711544070042488003e00b80303d03c003a540d003080381100d400d61018030340584080e65010420300303c14280108130300b0040c0c010600c40d810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 148455044 1250 148453794 148453817
    0x16030513020103020a11030a09140d031b031103070605070809070b04120213050711060a020a020309060a1704080306030f0615190b07080a030e0f0c040209030703020a0b090f01 77
    0x100310415034421542407030050b03610300c8100402c41d80301d000c04000351403a20010a502d484c09170490807800551b0f0800c41c2440710b80040c8820410112407880b800b40c081481c6005400f030913245d00010b162034501074103008500152080481d4610342c01a801501ca05030789405010b4100e0b8840713480340d0480c00050007000070341e09201c0100003a01c5244510303200c5603445c516090454941020401c1d651391000c070b040150b4a48400b019003d0500c110050b0094054078001500141ca584280c9980460a60045052501039401e200866001c03041c41020300903039280c5541d5800181403028070a1b407240502030b840c0d041000c00c1c035207007941240a0180c160130440c10018040d100c03081490007544210380b0100515800c0703d800e1243c2c0e07500d07007200010441c0040d13004107010504009140325100f03681c0c10407100001410803a01c17015000300d000701a8000c46081c0c4d210340342070740140c028448004e00b519a455607a0780094103040c0782c0d520100740d45401259605031840d051507201d408440c2030034440072490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 148456294 1250 148455044 148455061
    0x204150c11091e010e0601030b090106020d050a1419030b0a050108040b0402040b10020c03150c07060c09081f0513030c0b0a020f0304210212070809030f0106030803160305 75
    0x514092007a4000e5610400040003501c00c100c580e000c0300c40003042d4140e03958545d2041032000e00111412404030303090010198803428810000c07030489900780d0140c150200d101e40111001e51100740300c001000094442000000310f900700404904640d02c100044030307803100d4405801c6da0103030300c00350348910b00c040da0401441e604a620a5441903201d00e20340190350b00c910000b401444a101c40d6600002c501c00f0101c0f0b0513400094400500c407044048071602e82d00c17202d4140218501301c0380308002c0f0b14103028010004415401c100310702e8070700d818410049900c80c42020325212500c1400410003800d5056100c01181500c2000c1e080000040501040209500d01402035081004014980c1c6944030004080505917415503a08079204072800e5940e0525082030007040c0c081080f1102c0c0d2640c081526401c080c00020b036400c030190840401c500b0f290250b2240720aa800144a168141c0910001122200402e1040c103015520926501d03442c1d051249180d080003000d400820140b6107418140191340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 148457544 1250 148456294 148456313
    0xc0c05070b0f0d09020d0c0b0d050c07020a0302102709060b0f04060f020a150b100c02030c04020703020c03030a020d0f020705010c080d090c080601050f01180e0702030f07060204150c 80
    0x43c1c10b4081c08034429502e0300c08951600d15000000e03148012148002c204081c5040042c95001c42c8410140140e071180c00040d03505106e00d0b41d000394814103242007003005050203400d0590605841c2000e010b14400c1e000002c00d01014802c0c140d01000004006021900c0706108040151030301c900c02c6400c001c4491680c401900c154003403001480300002104480342e10810010681a601c00c4018004040320403c2a0207406c041e0540c0d4828106084502c2e041303807159060f03007500c40d001802802180681e405000095010301d0f001d400314098003006c0c0c2c1441d1800c0005080401c2c0540c0140020003c0072030041c2032059010665086420420081205a9000c14007000c40e580102401d680e8040d03070315101e070003081c04100042809d80140c0d40001e0304600820041e040b10000c1c3d03840c50140541c5401124003010380080740c10322840740074044c4202c40d0344480c0c03564002841d004891600d6041c0c007580103a600300c04000c4a40b1500000d041c004d00c501e0608592061460342042443c0340030031756031940710 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 148458794 1250 148457544 148457557
    0x50d0305090a08030d0c17060904150b0301110c010507140a05030a0f09050c0405090a0f0b07021906020d15030b0a0c03060f14030d0c0c09021602040c0c05070b0f 71
    0x4110010a0000c1c1e41d03a10100c80c40c0081c030041c41201c2c0e40e90f201c03010030302c094110b003a10380003c903420003c1400d40c0d5802130102031290300018000145507035030b540c405107022200d030200d444695483d211045c0f281c500f4031411808604080050b030302c0b0701c8401c5010b429560001c00c0c1004004881a80a81c4942440c013550011501805d100f41c582d40c45d44120030040648041d220000b60900810100f03201001c2100e01c0744160944080c0b0440c0c4e10058941e42c1e42000c00c80080c0415946610740c00800c060140032604000c0c2c07031040c6c4501a007114a41c2240c042d0010381039545950005911500e00d40901c1a141040074102480b40d60a1458860003171081c17008201c1e9056640760350f800c002c9244a80c2c024809032a802c01004c1c8000c1c0c41c1c121a440120710764090a0103842020110089140602a03803410740d0b501901c41c01c81141030401d0400607400c03100d041610550030751007070001a5924000c01042d41c0c0c0e81e541c0d08107848a142401450400107510034111020b00b04049441c0f4000302c6c04a826 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 148460044 1250 148458794 148458797
    0x13050709050c07170a1805060904240303050d060e1918021009030b0112083f0421120b01230405100e01080403030906180b06010f0504050d03 62
    0x140d075a00c030050103400d44a450b0004000440c0303a401410601300000c0501454029682c54a4022403018140d80706170445011f800d0f80100b0500c0308090900c0c4c181c00c01c20301c401c01c00c050401106048008880410426002180400c0d00403840310b80341c603c54411034008020701c20f2507510a040c03115454030b074042d4045000c2481c0380c907400e042034982c10001d02c12220550241c04000c1d912064a00241038210a00040713400f12911800002c03141100b080c02155a504202c01620708900b031003d541f0210b0b00350224400c88c2100f80341e28554041981611505014a80554a910b107040c0c6412079a400e18032048003000e0f40400701918000e1390260340b4021500c90070b103000483c01da441d40162444d040080785528890f0345098680581500b8101510468005580b0044c407105011000c0e074154000c1c0450f2400950303100700140220b0710035003042407054000d003000038010a98000d10030080601003019945441040c1c148802c41d42e201064250f10303043c910303040341010300b8000040c0c40804804400740 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 148461294 1250 148460044 148460051
    0x31b17010504050414070605031f0315091403160605070815060d0b120304060306050a06050715020f070f1527030201020c060403021c03050c1c023013050709 69
    0x3d0400024890811040c0d00380300446e00115600c04d0005c0031a03204032501920300100240200b90703410762200304401d0720361200609078008aa04071610043c000000d059a68800100d036541c820340d81030009007010010715088a0300c0c450702e0300301403041e00e03406003072030f41007121800400860303e404078010706010100300e6510b07903140c0319501001d01805c0004001507002407103488203030280e600080240100c030b005880c20320096550b141080589440c500c22500440c2041000d80001a00200b00720f510282801c0d005041410704185c05000740c0103001c04550345800f840c2040e0a0000135584031015048080041c407000c21078601c403516248125508221503c1e00051a00415000f90103070303407a0040c1903003203400714039003402c0003075840e000220070380c80a40110f841400118407074080c2078820f41001100390701d401c140e18112080301000c4003c03e0400e5a090005035040e5421a80c6518520070450a50640042c10110100c50420240c00c2c0c00508020f44401000a08085076100c01c4440c03020001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 148462544 1250 148461294 148461301
    0x3201e030d12062d080307021003021e030c0a2a110402040e040b0a0b0618010e03070321090b16030807090506070803090c090108190f080a031b1701050405 68
    0xb54081c0003150007214400d141d0741e00d00040c0f80342d90840004000c0d99001441001d0f9a22615175460b0302c504900079401070440101004468000d400410400c0008139500c01d2082c00a80c2c0680b080d0420b0328604e4130154002400c0701210743c040c02c7d04101c0110042c0c190044004401890140340c1c4140e0f005040b940c9a0000c5280c035500c1c0e5041c0c03002400002060680c914141c03030f101c1c203048400c65030051002e1030002c045480b0b041c48400d4031451482d0040310a002a007040040d10454404003281ea41485000000300015440c02e0103061200081002d50380924030090000c0c0103031103c4d400501655000740583c1218024200351a030303400341c060610b00fa2a0b103510728121000c0110740c125581001c00040c8404c1042001d00045204030240d0044d00c5220842c3c02c100b00c00301000384100c0c3e030168800c0146001c011000c150717942c1211b100d00380b85401d9518554a060711074001190210200b943e030266820700418410101c610103050f480c14495019070b0704203c3c4d04800c2d041c0034580c01140d0340d0703001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 148463794 1250 148462544 148462577
    0xc021510170c030313150206070c020f04180804050a0b0903070b030601090f0303050d0542120607081e070f050408100f0f090c0b03070903201e030d 65
    0x548904103019044d203582e0320362040c400f0940d10403849403c0c82d8101c807000c000d004c2440858418080d40165039400d80c00c015580805c4090700701c0c002f407103030720969402d0040d172100d03003000b1052000c0d0f00c2104081c0e180c0d842e048c00c01c055040141e0244803400c9080007801540d50340450f451080c0c85105e04142d440741c80d0b8000480d065801030b0049050340f42c3d038007408014144c0110140c042084100014000c1d40e64110108528820512100000b07401142c0042c0410708007038031039640c80318941e08401e080381039840003848130741e00e00d4401c80c10707a00b00d00f09024155a00c990071a6104070120855003107146005204110f100c0010419070821110030000b40300d031072188080b200140840b504a403001400400d0107030081c00c140c00c0046c000d52400e030701441a5a01030144000c10f03508002000022440c1044101144c4e000801c50000c020101001000081e90450000402d4903107500c5041881854018408103904180e001e0000c80502100c6188d03981c0d00040003078050340e00d4038243c00c1881c280c158 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 148465044 1250 148463794 148463803
    0x20a2003160b07090e0109060807060e0f010309030302091e040501060206160c0807020a0b0a03050105030d0e01051602040608030403120504032001030603080307020c041823030d0c030c02151017 85
    0x5c00380c0e0805031400001201348a540002c4103546890080d40d400c140d0711502030361019480c4c1e02881d0072000f2402506501e60180c2c3c49100d1003402414090320b00403c20f03001507020000c0e020310070000c598401046083e410148100ca02501c0140010040c40c100850018140004400d01500704403c440c41c5408001881068640a503400741c550520192500206031864100d901c8600001e8644000080c943c0b400241c8180d41c0c40840d1a6400d81255100044605900c0301c010380c800c09013095850320058a0343c2c81307140f000348401e101543c3c070741d811071400504690b42c014206082140502080c40820050814650707080901180c17007008401140050740074080c503602c080d204a00100402c04596001b1401441d101c00407075080100c0c001c2d00120360025008500e02801c074040c40b103203243c000c981c0c0031030700c110289032401140d060541001d8490b05540c5400b42031800a0340700d948000384a60104020503480c0044200100b5500d0720481d00762108032130f440b83d48400f400000386505000c00c10700 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 148466294 1250 148465044 148465049
    0x100f03110a05270d03050903010e07060f050d090f050a0201080a06080d030c030f0504030206180109170306010909051003020a0b090108060f0d1b0e010b0f180f04020a2003160b0709 79
    0x202001200b00782800e0243c1b10740c00102e00c0c28029407c140407918440c00105008003524119110a4210080210101c42c21340207554020703102079440c4003150215400c91106040c0da48078100605100d41148001046c055000e0103107001542001030030b1082c00c0001c5804294200075160001c1c0c4035a00a800f20007510481c4a00b2910358900750130302c01450790101c0c50b43d1040340035480c144000703121525118200c840851300609115840c0c500ba0304041121002160000c0051509511f490f4503408460200c0da401d0302d000c4120f034450601001103050000f203075802020041a0326003001241d800192040c0c81c001c1c65244903c0c50b20301d01d8142c90755554100d81103117800644034041c0d607040b03c1549843d4a2140104100102d04030000201107254408541c60307550501c05846c144842446030026503002c804095620003012000d442042d180c51003c0e0000340c485554180034003034145800e2100080d44030003400310790020001c040c1ca01800c0c20f03014030310540c011b21106142d5500ea5040707451038000e4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 148467544 1250 148466294 148466299
    0x90418050c01020d0509061213051501050310090519060f061d060d0201020a12021507080703060b03010503190f0f080d06050d12050711100f03110a0527 67
    0x14088814088002241c490780d14080e0222180c0c415007482c10389140c015144070301e80c41074080003103200e0b40c14001180da8001e18008141c140c1d00210b980c0740b074101491002088541402040100180d01d0704020304510500c020a04020f1035076542c036450f88801c0e03e07807039036154045118195001c01201e0f0f40803202c00700d5030702c10800c02d10340c4941c0800c01c0c4d031100c00552241450801c011070345038684a9514013080c0d505030001c2c20481d80e01e98ce00c1151500340c2c07000070290b0050900c0c4031100081402e403188900e180c1d540b00d24943ca04003002404890107a0056030911405100522654a00048220a511804001c5c90070050306241134404646900c0300184034694000d0340b00c0402c018800600440020b010051140545940034000602d03031170000548001401b0f011200140d010f54018403505000b485101502c1c0a21782c0811070095021200200060070712600200c0c040d403510600f03a0045580103482d103048172080000700513000e03040610390240000152204240f00030a03901c0c5622001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 148468794 1250 148467544 148467581
    0x70809100204090c18052b020901170f07030803130c1208070b09010b13020313020a151805030a080a020304031205070c05030d0210050711060f01080c03031309020904 73
    0x84149002c0904840d01668004c2986005040014105040a10156800600881d4542c0c0310400c7e002220400d02d00461540c2048085010168446610603030107408010021100100c0c058101850102940c0b20301019130400301e400d0000852050032250094400d020201580d6141d040002500f04a540411288949103088408001403807018024a50089103408065959140c2441c2030705c0c410300160703502624154241c241034201e03501071600301c01d507080184401401035004c5140709210340c000300310700402148a180070581c80710b0100c6030810900f40200c02c0e50718000110f076130340b000f204d4010b103241c50214108011030700c20001d032401581c000d0400700750309120b03d1000d00182d000403401e984043d114030010809040018200110450650041401c01c0d07011b00c0003070081802410150400402441c1304031200340400c0280c0c001d03a44041c0e2030400e035150a00c020300d000a4101c0e464000e410a0083d910074010200d89041190704a080c0980d81d550080c1c000b0b40201912154555103519 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 148470044 1250 148468794 148468799
    0xb030c0a1e0f03030203030a02070807060c0309110301150315150603020304020112020702010512060402040803070305090a0f03080a0809031309140703050121050a0210050c150c03070809100204 85
    0x4000e29200151000340503041079441c1c50740e00d60500c0c18200d002c0a40540e00802c00301d0072882165000f04005c500800a603407c00c1c22640d5503400341e5454120780c5000030f895031601000c0c0440007007203881da41411402004040300182c000c4504040e0380c131028020101c42c9070748000c0c13045180c00040d4400303c804402400d051721200041c0c02034105a80c140d00007540b03200c001d1900e0a031842181c0ca100c0d016120103040548418030018030303107001002c440e0016003d210000700544104082d1403c0351080d00e6883c0c460a00b0401c0c450380e2030b155840b44030014041c4a0030404184e0340011982c0c04085450030041030742c3c48480b010310b1440340e08403440340000740e10000964540756170710074003400b240b0700c042103c540c44021048058810a0140340c0c1c0b441000380c00000001e040440c00782400303120b8019221407640e1600041c2034041c8100d015808550b0002e000c2d40d8102d01442100c0c03034101c160165402e1400e080d10307c0381e40c80c04028203010900c0f0b005c1d0b0104151280c02c00603202080324214040d981c464 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 148471294 1250 148470044 148470059
    0x703050105030705130f02160302070603061802030403031508010b0103050a0204121b080a0b060102010507030e060a0c020c030a06020403050609030f09040c03140103140c010503041502070222050f090318040b030c0a 94
    0xa0023100246c005014084002c0348280c42800b03000203da18000d240c00c404008141c01c00300075440a04210181341c1e41e4080309203003030b1a060440c40109200b400001c1e500100c00005070030398400070000c40003144108000d20003210002905d5640a4011950412128050b554140ca840b021741001c0311340c2c030596a14800708a03410244522a075400c0e8001c0c01b00342c5034140141d0544201c0c0c5000b1070942c004100060005c00681d119880e14a031510440d11a1032100020a041120084081e641d19130001802c3c002c0c044100403a5801811150045142c83d464001d200c00c14002c1448607440303561204000e141852180c2c0100c00208076410401c80d42e560744e0f2a016040c0c220480300c1d0308560140700344505c07196000304180d0b442603402070190100c0c05500709a070f030025402414101c0c0d02c03188050f000a00c0c2760501200b01d5078007202e602c1c000781c82e0038601198211810300030b11913001c47e0700401030b204412601d4880c403003400d5410788010581780d48500c00282004c900da000c4a400810341c8000140d4038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 148472544 1250 148471294 148471327
    0xd0e01050601030e06090d0f0c320607021b06040b0313020112090507090903020f1e06060604050d3e04140124030605150a080703050105030705130f02 66
    0x181e000362801c112513070314003003d076464890880e9084010340140c80110a07480c000c40c1800300c00d004e41e10b0f014901900c190b86008160280342c40d0307542045403034910390361100070070031180e045151030f00003e0035240707000d100003580c0f07401401c41a094007501c1c9441d450540c5480054901170861041c8070390700d91402412200d034413500d0705000ea00265110800c9613070300e40c5a00c00d0080460300300d0041e012250800c007207070000d400250380031011071080b000c1c008080c180034403c0c407203445801c142e000c0c400409210002e15107040501000e02c80ca02c10003082000da5550700201031b82c01c4e8031030110346080c4c01e800c444c07038504605c0300308091411110000960f0380d110409456a610032045408000340003040b01c888546c44001d0061649280d140e8400d20b00d0345130f51314030100410401d0301d00896069121004a8010601500032010040c00130a030401019040b1504a038003000c035141c00c0040d580741000003a69221240300b000d00810341c0b8010366080a4450b0414050611030500965880d240804a1a02c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 148473794 1250 148472544 148472551
    0x6062719060305241c05030c01150e010602010c0c030309050a05010501090e0105241c0807032a0c06140f030405030a090603090b0601031a0406090e01150305030d020f0d0e0105 77
    0x81d03008071480d0728114507112044484824005c2d1407034000350000650085d808401010aa840388418071451440080034000d41c482884940112802d0525048660000d40c0c4107030024005c2da418101c10b82d007429484234001103d15050319021070100d466040c03150800d509448094269400c00300080741c1c0c00c0841e00f200c020b4040071002001155905213011240a64480040c0301c0c014122040b0015071400d594000100e22100c1c03548030203806d13140d441001540c403a081c110302040710704105042c240e264215000012007118194603484040da9100c880401c894012381082c05540c1d00f40003d91100310007602c9103200c00d04506543d03800c02d4182541d8a8002c8041500003880700301c00440d20305d1082c040d00c2001507100020580c02d8641c400150040c5c14040da18080c030315a012150b001995440c040c1e80c0c02032091400001d45900541c140c0c41c00c1d100d4003a1122822942c10408000089000045030707400c41c1074002c01070320b595035450242658400d84510045031803c04e0440ea000c84d9041d07101500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 148475044 1250 148473794 148473811
    0x203090c03030301050d030c020312070f0b090610060807021005010f0306060506042702160b0a06120c15090518190e0a0201030509030c1e0606062719060305 69
    0xc85299102003698a11090003903e400501208100c1e0009002d19202c0b2503141c0b008046c2c0d6840c1c010000100d045402034002a91844030180050042c001260a03094205c2a4003000d4041450038010b0f0300c41e010024070400041150007400604040c0c801e1204034015406140280015651742145115011140c00140c6680b0b00d0184002412f19000084501300c1d411840b01010761f078160f07a0310301e1448a05212201e01660200f05d641c0301101e68240a80003e445100c40e448070b070501c851240708403100794001070f4003c01d20000320008a03036860544404c42e008914046000000c9840403207549003694816a0000542c0c0542001c81a54824081c41001109504038003201c00502d030714107075a510003414030039800001c1c0e01c4001d54480d8000662050b0200708a0380f034500e651150900c0c023041d0114140301040c000c6030810b55207005000c3c1680041c1b0464200d4108980095034215880d905007040c00307961003030000c0c90515181c0030b034086c0705800d4061500c4190780d80c03481c0180150804446245 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 148476294 1250 148475044 148475053
    0x606020c040c030524010302040b0307030e060c030112141608030a0810060c0b06010c0209010801021c050f06011b050313061b150207060e03030c12070306080c060706020d0e01020309 80
    0x4801c1c5200c0d1103414441c5c2240c0d21580028881c0c02200a50400c40c1c0c5036541c10181c00b00400b09450003054011070107400076031b400103114426103098600b08200a0100d248090f002c000411421041d0058140120b407c102d28913120804070070954a400b4280d0030b06814058680d20000d01c0003030100140040c240692185001c0d59034101b094810b40110f40501400300f0950300040010480010504d50b1008041c100104071140340d8000032844e510036480a83c05a40011300209406040b4400494041c40808244000c0c108061151011a001020b8604100001c805001c0300880303803056202043c1c21009a0b80e1303c0c0400c0c1d13100040f803100760044d00302258003034a1000c0030201a80a000d10181c000e603600d4040041101d902c00070b90310203241610681c0d00c030500480002d0702800210300406c90615400c0e81ca11120300c1e80301c14100018601000c1c5490140100107010340800e1010314110200c414507038a80c2d441c50305e00020f01860703c055a420703142c0911981a039405600941c0904034200c00c54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 148477544 1250 148476294 148476311
    0x1206050d111e0904060f021b07050307091109040b011407080426060a020307020717060906060a1802090424051f0210050a09120302030609060907080612100606020c04 73
    0x404141d054003000f07811080031000540071403155802540c02c2c50344143c0140c40c00e290341c0b002d2560003070b00d1710150301c80350000c4800308845e107810001d510080006907402c0c004070010f15184603450148020300c501a80e10f030500760046a10600f80d000070100034115440d2503201c0c038200343c122a04280618820045040b00003110035141e0800c1e0f2074220b91840040c11190344650010020707400140101d003d601ca0241c010a803140e018403900e28845600000f44068a401c1c1c5030b031803526401402260060a85050030721001000800d1014004039404002da41c50721884d0215008144030320008400c121507100d441516622464810201e0350100c40c5182c103200c50ba1121810258090b04170000760f40f00e03192101d440710864019682c49401028005070001c141c0d110800e07000b10300c911440001390300000700446031400c002c0d01500140240d84003c46413510030f80251480c20041c04503071052200c2d0070281a0503004228070558a20620024400306030703101c0c0c1c080d40c1c1d68441d00c0e24501c200d0901c0d050 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 148478794 1250 148477544 148477579
    0x60301030809041109130b031e01020319020304050a110a051807030b06090a210c0612200421020a0f180902010f0503090327030c010f0509011206050d11 67
    0x80e9031117850014040745403800d08800d120000d0800a40032601802030500200c01080d6908040581402c00000540d4030700d411030a07000502c3e0010103000300d9901c10f2041c0300109100240c031041440e0b00c000d0310b1a01c1c10564000a401003074980c13040b98420000350001b1001500c0e0341d0b91500440650b18184455180d50302000a18003175044607681244a1440400102611000b00382c103009002c501c03500c0c50141074a41c5121817101c0c0e007002c0c0110310b944e8400f0b04010254814000b4400204914105140d40c07210400010710543c403a045480b0100030391183c512980000300b466155000b00380712000341d43c0b40240f14205e0224480c1d110004080008000381203000d014059080b50705035a10f54488641b0f190996103030300080d209032010300c02800740304002c500070b58140d0122043e800c1c10040c240c0303414040501c3c29aa684806040200028001c0c0401d80c0081c142c944c0c0b20703402d0a02e040c84104a0503a18000e1485034403c96102d40c1085944d01802141303d0070f00e80e040340c03d4880c2c4140c01041c400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 148480044 1250 148478794 148478797
    0x13050f01050c0306151e13120203060109020309010e07030606150e090103020d1e050c090a0c021b0112090b06010e0907021c0509030a0309050406081b1c020603010308090411 76
    0x34000710b000c0b001c00c009031581c0b80030454542e0b115121281d031402c0400b6920f5180c440f00d009800600e1101e4002010407991001c0411513005010520f0300e805400b0265002ca0740b08c030010702c11003224640220201e00404008c1d0001c3c030043d5070b1601210985c1d942d904241c0007400c1a032181c4891104402c0030350184d50f100b2014644081e001412540c00c0d41d10703540c03d0110031001240150f0f65210820f81c4503000517420040c0c990384600440c010001d2400d210100702c03201038080e010203c41854440c21104590700450400b409100001850384492894001609c149111020034141c481c41c018880003041643d6611a010340e0b000c0c0d03192502c8014400a1203590741054a001d00942c1c8070300401800d811b100b0b10421140d580600d010f6040a0707106002ca0b02d0460070f101d00303c011039050318043c0104e08161060318010700400e07008100020702d00400e8050886c000421902170300e2420100b08103000030320b044521065000d0040340e641d41e0f5906140d501038000c00b81c124880c90070020a03001c0c8201c920f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 148481294 1250 148480044 148480051
    0x30227010b0c03120603011404050a0c060e01081614130e011d0c090118090905060601022d030415020a060c0306060801050105031b0d0209040f09081b0102040e13050f0105 75
    0x20003d520308210030300b42c0040c1060040241d5810740d01c42e8901200d001c41c61040360700544c400c1005005000301d034944046a842e19402500c10011300b02d0482e00240c1e44680140c1d08040c0032443c0c2124075130722004c1200c00018107216429030990000301246c140480c0c9002e001184c0c08030a40c001540d80b41c00b0847c000c3d288100c0802c640d102c000d004281d43c05500c100410008105050140800682620700c2c1c0c490000b070b034000b502040d40c80c801e140502c21705001c03d03a40802d00344050424001c01440140740030101014020b4500740030048906488010000c6070080d2514a42d82045060105002980c49148042c02c0f15040d08140040107824001d00404080d91043c1d02c036a0f03200d0303003010011102c64100a101301c20300c0a0032040c000059114800908040005e640d015070b850038680c1c144001d480c003c44040445038500301da001c012440702000d54030fa04800c0d81c0740d840d03c032013410903030360180c002c64000041800a40d41404411007001626541143c4110141c423010030201f16110b01700c0c0c0d003c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 148482544 1250 148481294 148481317
    0x11030306010c1203020d060e01090b1503011a07050f0616090608010504050705090904050d03060503030403020f0409150507180801051b0915070c050307080613030c0606030227010b 79
    0x82d60b1950000340c182c501d4081500d120300e401410a6040c2400400341e0b601c0d6803060810000882c010310404541c0d024040703041e2010355039859110003198031100240b00510840c6126507420f00801c481243c4001124011508141110300ba2010000d0050b1122025100400566580f00d003440c0941d020704150750883d4042c2d110740710943e1a020a02c4040c000042c51a01002004c000400c81c980d07610001a0086004600400100b43c00d441e016041318400e400c40ca11035032050008200607642c83d001d00311503074001c0d107000c1940800b51400340e0f460302103030050340b00c4a4100001c03c50401e40c01034401982d25070a154000c040b0390f40700100e83c2203480c1503071054079005011f000c8a000021010061000c5039000d00303071300b01307019007a84e0b0500d1b00e4014010445141c50358410405c42d0b0704c4d080100401914604000c5c15640c1801605894002e00c000d02c0181482203d030586414032020303074842ea00a540140804814035140b00b421480c1400d511481441c00f50080008903a5401003002d031500040103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 148483794 1250 148482544 148482557
    0x7020a05030d0506060c0f0105090f0705031c11061305060a0902091b0f040b030610081e09010f0603050f100507023004031b0503060c04151106070905011103030601 72
    0x82d00c802018140040c1680e0f04190b0070070507844010b404001344010080d03d8400000e25040840d007444c102800501c00c08115440081d0610031641c01140c88249003400c0c000e8210b408000d06d07800d030345001c1800003900581c0111700030004022158010b00c00c1d801c1c420020354180341d071401503483c1100d4030305038043d41103506940014404500700700000d0501125203083d0703040c40b82d0305110b10980d601076000300207a07090101c00e0048074104255907000700d07810350400c0c08551a00110100c801d0588002c004800c03c9144d0200e00740100a501c2031003c009103040500041da1203040181c4c1d925805204465648108100d0744a000070610800d80240e0b10303980030704680c40b410345c4c0507840c04080c1d4200207900c10015002e0344040c01c00c00d0040008600c6801d0a4400500f070303070000075001001e0707481140030380c101d10108155503040d1000c070307804c1c1c80c0d05050107440304003165400c032180c5080b102042c0442c072410041c00f401c1500a00344c502103802c00d9840343c058241006030107869000c00c0d202d90b40031488 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 148485044 1250 148483794 148483807
    0xf1b0b01060804060e0d0903020909061b070c05040213170c030c010f030f05010608010501110319200109080d06060507150509150f0a0c0507020f0609040204050d12030507020a0503 79
    0x200b1120203401038010003010031103813003c250290400c64903005150208804401c2082141000e400003680f006c520f001074501858029003d4507001d03a24003440004a000046040412416002c1800035100292045443d41c60500719040004028090710b200101c0d0718504510380400020300009000018015011668202005403082080455030609058507059204c03265500c9104a5000b003144d0340d1480402e500d040c0000d440e451440e501059035030030410042600790085504000c90b0701452030318081c02000e0800703c0300075410414022441e5402d140d000c3d418010650083c00c1583c0040008003c99650382000740c4081c443d44200410b00f46030640c90841d0241c840e8021079000300d080040d1f800d60106405910f8200d0401c40740d400c80710301c1b5401440f4048000d8866480c0890080c2003440c80d0800f25000107040c0064004090301c1450001040d01c425103031034050310002c02c000f825409080f445498010300100280080900092030200090030b50b5100148102d455500300000c2d500c5e013507 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 148486294 1250 148485044 148485047
    0x30f150316051009080313030b07020609151e130c060302042706031203020a03140601052a010e0106150207120602031302100215070801081b1f0f1b0b0106 68
    0x24460400f0028008000380c0060006400e00c010048428446036021a060031340c5440e08072800050045007c543c0f04804120924400156001b440c200450818415544038541000310a0702070490020000080b000c0c8045038050a00100d5010b1140030748950058807014100c0c02c0b40103070b02c0786640c04031020001c00c1a0f81d505400c0040c103a540041c020510035200d49410120318541c01d280070000703a001840e2204140c0c1403052850000d040078000c0c54904010000800b280030345441c5017441100c8145002d1006003c54403001c24000240c0240702e10451580224000c4c8450312a65205400440b80c0440d200e1001c24007100351031540704505401c0115465003c002c2d0001016945141c01014400c005a03035180c1c0d18214101030b03507009194482042c05c11440718a00640300038144041c11005001d100004039036680710f41122025040704600f964000b42c920b0019101e56066010440c2c07081d05610b610480e03100302034405132504140b1502001d201d11307104000107409080c0403d0f4600511006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 148487544 1250 148486294 148486309
    0x1c0906030e0c060316031a0604171e0a0c0f0f0b0f0f0d0f140f07050903010b10030c021204030507030b090c090114040608031c090314030f15031605 65
    0x340103803000c4071444041074003c0b4806a0003941c0081c2080c0a10805c0c2c107291740e05026031100c2c4400780e0071318a0f0081e030031400700702d850049003c1c802d101048461015a0b0359020494150182c554034003549948030014245511800c1e00c020a031013020441101051600d05c4040247c1256590345140100300d15200c0003c1c0c031038122203c000c030108002c021169500d211880030348242810700da0002403080c24403070b681084507207901040da20a486001000800c8030071110496112581d4103000da611080b100000b401062703529412607001c1c191182900790b4903490381c04000150038640031035000301a03101c1d0545840c0034910000b403144c0d010500510010f01e45078141d603080065141103a107401000307000900100d4003600104080c00ca50076a46d82c4d83d123407600800006000e208044c0d458040a1120056113002c28046e08410a407580d040c00c081600c41c44100702c80055807103205442e1f00701a1201c80480e2816a002400841c42c44407007a03040c0382c0840d4608141c01501e81e0410803a18160611a00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 148488794 1250 148487544 148487561
    0x12030f0903050601090c0e030606180901060b0301031515030f080703050405100c110a050d110105120405070321050d051009180506010b0f03070c021c03020c01021c090603 75
    0x8100c600000000000c104015840c007a0141917030114046803030840040c1554290040a44203a008070248019604e404000140d980c502c4c10411110340d542049032405044103502015000c90000000824015602011a008541c1d207905100d102c040c6000054030b07115600000c5c0002000401220001c0d03c0c14000f000240d10a040c114201b0b81d94034001119050b1085190f00400e20030520b220400880855601030700c2c004444180b80b00e03041c0f6000c14041c611507000140760f44113010388041c5d141c2c004d1701501c0e10291440b581402c3e5103801d15018ad202c2045210803620003c42040b000b24005041c16907000100040d034803241001c29240050010300700c05003805400c4081001cac00304a0101ca40102803c03203003d81281c0d41d072440f040c9481c07490b21105a001c4465600148809015410138000b2650080c210385807114144e8018000524107a0000c1000780908a0754020178081603004504c1e010b405409800350f034040e13110075010100d6080e40d0411b90300050806181408244d010740c3c4072201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 148490044 1250 148488794 148488797
    0x30a1802091807091b030f021207110d020607050a0309060b0a0f0e0a020f0702060c070e1303020d1107060f02031b01020301050a090207020603070c06020720040b06030112030f 77
    0x40040c0e00429401d1105a92403556034980c20720303003101c408080003d1001449410404c000020150140030440488404002c00700350302e9140a000d5030250f0307010342c5e1040d44441805421420503c1e0060090b40c0d16081c1c1c0c008a00a03c464040c0c603600110304144a89000e40311035240a2018008070028900440115245541e45140d03c0103171712000c64000241494020100c84503040180c100304a07040180038140b03050042100f2483c0c8401e8100307540c103407581640c500d03840740c80342c003881824000607401c000c40d000c801004100942c1d070440c540c8001c09010b41c0944a00c0001d449080759158101c3c1e104040d0b69204039410451588520002c181070080d900c10b59040504025a810502098010f85050b5070340120050280d032810326008001049810801c41c680040356003c18031502000300b4400a00c214500600b0030720881c1d4040b42d940c154800c0300c405104c013003e00802c640381140c1c48034500861400d00c91042e2030034454201c0c0e041e0f075010024280300803e1980c00300c41510015940d0310 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 148491294 1250 148490044 148490081
    0x305010b2514030d0b0301050103050a0209090304150201020d0615230c01020304060e06070206040302070b090d02060a020601030b010b040302130e16030b0105011211030f041110080a0e010504030203030a 89
    0x2258851510b1181110030101a603a541c80400056080d518050101c0b0702c2a45040010070001d90001110198140e0551b00200c80f43e0302c00740f106046002e00c1d44070401c403002c0c01403822030ba140c2c194010007044402c09400c204481c1c0325103040c841d62044039407134800f1a42002d440d010752512214288810001c2d401e42514120740c0740451402c0e038100b0358040b5191034890b9844956404103010340350f4005c24070310080c071052501ea10f00075503d00c1e091080920200e80029400c03003a403564171011449940140840755561107070000296608030074030003036582c030514000100d40405454222030403a90000d100407149504c00104a00030311201031704107103508c41c44440b421588640d8502200079030040e800d440c91589000f0015001000b47d500032040341789441080700808a6034400d0325005044400c0001c26a070340c900c2c202e0342e00b10006d40c41e117904c121140740c007201d401d034003410b064440c0201c1c0c0821301c05024404415403d84e602981c0007009608180b0001e02c415000358041c0101807080340468 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 148492544 1250 148491294 148491367
    0x9060e090a020d060b040c18150203070b100510020616020d0203040603020c0a0606030c06080604050705220801050a020408070b09030705060f13030609212f031602030d0305010b 78
    0x241200e00320340c80480800c840d00d00e110390381d00080c00040010180691009d84205455100075100d01c078402d0000e041e18130500114010620000c1910007900010b003078501c0e444c1304010301039a1800100c2c1d00b0300f408400040d4074111130b880840c1010b807018250b002541814100942a0065000f4040c1e02c841da100302550800032a885024000080d40108140c1182d03900301040103142c9a0010070107130180342800107120b451980201103c1d407003064102110304001421000b11000007060384104615800d0400b0301142500e00c3e401802102c0c5407008442c800e41e600c00c0f00103654042d000035968107400c400010171007814447c0052410b1300440002610703012028010801d828015041030740c500f40c1d1400000700304041800c9006403407812480340340104800c020011b04e01d1100b44c1c1000b03482010343c40010201418160b00e00e0b02c4058840a40391a031003d03032802040309800d00d109922034072131007005400c0359002e48241030607510740114903450070240700c417a01d02445d03252101394000034406242 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 148493794 1250 148492544 148492549
    0x507110706120b040516020f0303010e0c160204091209050f03120f07062901030207050a0303180b040f020f090702030307050f040302060d0507080a020c0c150417060109060e090a020d060b 82
    0x20700b0b21a10380040780006d99030942200900d0301480003151015507000b04014451240c0000b6802e81c006108406c1c56941d401e101841e20440303d214100940090428440004100c2c04018038a03100d0440d076104200d05569004201d840101c2c20081601900002035042c1514400c1f1700600002020926907890000c1076a2a00200e5640202d03081070b280301c3e4584000400e40319495082c17285c00174a000d500b44161501c80c0307030b1515890500201815554030b0f001104984041c07000402641000310025185442c2c202200d4a1415880072841480702e02e080520503e01001c1c4a0301a440581c000c40c11035581d41800d0710143d004042110030340c0414032001005965180050500484110003c289410b04010240460340050100e000140c0144801007041c0c1000800d030f076500c13108031040b0000c51880400000144100e4002c1aa42c01e41c04616092820780003600504a132050802040005c2c1e0360b00e82148043d40a8034925016044100d401d0050700d0715104640d5600d02410f030004040350305400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 148495044 1250 148493794 148493801
    0x603070b0408030301080d03020c19020310140412050322240b040501050406060c060b041103010609031208040b060d0311031c060902030103020d15020c010f050603010507110706120b04 81
    0x281d070f84004014020702406201185800f202401e00713500f05400d01c92801d03184ea102442c2582c2c0100500500000c0d036404009041140b803000e03404000014807041c5c5040070481c2254140e40039005120f01007409440b86003101e20546040e40d03104803548043c0352000c01c0b80d005203c144c0c0c0110581d440200aa1518008400028448100014011040410b00064560507030015204924144c800c111198000000c111000da000400040210003400090010841d07141c03440c4824201000202e2010707041968002524081d003448107444c01c0f90304003214000000c41d8020824080d0402050843c2082220110031522034100507480d4410301d03071150f14640040d41e500e50000300e01da540c40c4400e5503e01c9140040d00d494001075103150b040d40c020900c8041103c10060038121030a02c46000703007480d0390645003450450320017030200c0754100c101c0300042c003002c1c0c5805210b5444e05001c41c42c0d2034003072030341312900000000140852070700d801c8040d01c28400100103522113985600306456160f60314407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 148496294 1250 148495044 148495049
    0x1c020907021c030603050607110d050d06080d0207061701050618120a061505011107050f0a090204150e0621060406080a0b01081c0e0d021507030e0906030c0904020402030603070b04 79
    0x641c00a1350714034604115140550150109046c004a084040040d00b800700b0313000c03600c982c0d50078620350b1307108141100b40003055070794022000d5000b0030301c00c1100391f0b40c085442400c568983c0c1d83c104210401c02201d144108084c4117090303020030100200c0c455002c09071514070010f0401040c170154081a07802503410098004000c8440c1669002603401e8203400708803481c0940020318001c0012081405070554a840c0c5000b01e5201e084100e480094680d15182400f024003080b02d810b6490325500d481c1d1003420460505030002007420300c110b4800c24206078007a610481070040d0020b0b08003001c1d400340c03550310381c010f082d040d013064444401203280d040420150014910400c4001d1066151805041c100514900c50b0000c40c02c1c1c0b0444014400d90100700000340e20001c5440918008030303440011918050b400702c2e0380100202042070301c1419048098070701d01d500d060309c4030391036070b81c03514201519800b001d4281640300c1a100301050250505070f000d13643c805000703012074a01ea0f80300c5202e11a0b40e0400d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 148497544 1250 148496294 148496297
    0x30309020603041b080a1119050a03060f0b1203090f150a020a020f01050703080f070314070e0307060e030d030207021203030c07061b0806010c06060905010609030507051c020907021c 80
    0x35031240d010218810300c0000104280c1d000303818003508a543d44c050007031f480c0306803d201c0d040d14500d2030800c9101c6465074000b0300c0014480d1181740d035070b8502540038060382c04080d02da803403811041940301c2c281080401c0410b401c0d000a140f51402c5a020447c10b9024000a950403100112402481c079004c1c400601764030105400802c01110188100080c81c0202c140c0141042018002e14001030f800000a64205030300080381d0805a0f00c814084000380b402c840c2605a1004210900c920a6000314090f82c940c8401c1c0c065071801a20b8001c262107060030740d03010715015406004c00c030440d98800d9001e0401c282c80180100000016094200d1458106a07011401200001008010007119108034180c10aa030601c100e40c800d146c07480500150001010039051100105a12003001545da004070050811240108603950310707504001c03c51010760204840a00c0b0310400450f440c60074201001c0400c6034111920801d0001e0713030a12000b2080a0314000962240d80000c03944100801680d5039415a907 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 148498794 1250 148497544 148497563
    0xc1e0e0307050402091008192d0e030a05090f030d032f070602031e0f01060f030e0a0222060e060925050903070302030a0803040515010605070f03030902060304 70
    0xa90415003400602c1d0b01c414403440c410018601c141d241c60150300da0030a400c0c10405c03002d0b994413090302210600d41c0380c3c80300da203480c2002c000e4904850244800109010610403426800d49180c0d10703044460180b400081a4028410182c03854481c01c0200f40407c40030749043d20a0b035001000c01d140039640340090700400e031a01402c0110900c4252401a5004000040700c0070007803440194080384103e51002d00600d80000c005080940d00c03021201403011300c01ca5000c064038001c0c182912846003801801c0000704123086041c0b501c0d100c0c0c040c0301304109801c80900311130551070f82001000a04680503080b0300c0740c0122203032a160110702c2081d00403d6282c08a0070603242c1482040701048001b4600495441c443d080b1880e50600020070013a034240500f040c0d580d074580c050000b4a480c0107a0300080d450720074840b4440401142002540c0506d01c12402c81385007540c100b2001d000c03036409000308000104180404404541c25100002c0303011700a04000800d40080d402244417540100d130140e450910 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 148500044 1250 148498794 148498817
    0x13031103032b0b060403111309021003050a0b0d0b0c070318060906201e07080307050c18040f06020703090905071e080601090302060f090d03020f0f16090c1e 69
    0x81e40c01280e28030281180c13407a00c0c041c103640c0c9001c201030802d003000303014882d00403140707088000c0c650108041a800070421024000d031160010060481180c13400021810121500014100b21004400440e8090348001c010f80d9213503c1519980c01c0090240d04010032444400c0d2030703000e4142188041c100503900d00f1029800d0680c05841100074009000139246807860030000548041002640b010b0300700c00180c510740a604507546040c91907003040c00103000c00508007041100003d0100c01c41e40c4141c400140e8480e50042d9031050410464000d064001020b0040c00000e81302d5004181c107520030b040c10120b05407aa2110700450b501110383d0000f240d00b074454500406000142250815141d02d010300262600c240000d1400d0b040303101c000d00405001c01d40b01008034158042e03c2a0310740261200c0714107403283c24004e60b00c1d0f80142851455000e80c440c68540b0311808903003241c0348242c0d0301070980380d5440d1a1110009091841c08601080310a014000450118035014841d240039555160180c0c0b2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 148501294 1250 148500044 148500127
    0x20c160602070e0f0c0405040b01020c062a0601030507050603130b04141509070b07020a080d08061305040803070507030309140d030b0102010218010e01051605010614061303110303 79
    0x70005480f0500f0404221304005a00865108441c1174500544010810200c0c8000603440d0801c480300550b4400301c00325060b42400c5044001e400c1e0783e000009080ca8003450442c01035290715007808084c00640110409111600b0300000858024100d00b500b0100071105482d1940071100c141c1d4121240c0e810801341d16400941003001d07038001c0c084820102c14504010200c107076552124401ea003403d04002c105007096555191800000788407401c2a1421884643c02c02400400c00312030b0248140000c100400c0303540c0440c416907200d507603c001c455107561903d0505030381ca908402c0040b000c040c0c8136082c1c1d60018040e5241d804240380c1c44402001d5110701c03a180641614400110705045a20500c01d69401010345c02980d201c0c481c080c02c01e5132548130940700480d1107200300d4090300402c110506e090b804201c1c0c1503000008a84840200104102190f000c20845100c0c0c01d030481807180d4400c90a10100340340b02c0010180440040449280c0300c01d00c549e42c040c0040d0107640c49800e419101407125440c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 148502544 1250 148501294 148501319
    0x370909050a020f060a0e013002130806040309090b0d0212010e010f140a022505030901080c0708030615090409050606030613020108010b0313060e03030403021b030c04020c16060207 79
    0x4400480b202d500301170010340000c10f01c40312030100d18100008126020703240d180200c0428071001d120a401140d0107900c00750900a9802490340d210035155217200050211000720701c036070255a040e0380701c409992a089103040981084c14203c0c0d03200040d50070420050b0f5498907881600516000082900d03010005124219000f4140821700340e4181003440c0380d03514031903030481d5111a54060040e240c107944a05288004c00d01640601614420f068080500000102808854a090781c0e10b5030313180e850b190801c225014018008140d10410300c04074401d4500f00d0000191034a0004000342000510070018056070840380713055825030840401d00c41c0f982010b101c11584200d0b0320409040060a960000b404150148a94490404040045020f9602d951000341615400c0700c01800400d40b0007030440e407a0340c401d54088026200d5052110101c044070b02c00d60580c52402006000d0790308100c1d05000103544642e00303281b45c6016599801706440290342013440502043c1e80140089800d003000485d41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 148503794 1250 148502544 148502569
    0x5010f0e070f03030507060204170304081b0a06111203100e060a080307140109050d0f0f0801062c0a0e090d0203090a090b12010507030203070905370909050a02 70
    0x40d81c101200a0007004412161102120b80c540f400720750f0380d50b480c01c0000082c0961707001030401085690f0080741c0e01c5000800342c41035907128000d0b01d10181684c41c0e8441c0c0d44043d20303c0702d90003d41a8404020f8280070305a0020074030000c0c1d046e107095601c22603ca40b000d610840344c8010101603007805120300e4604100942e401581a14441c480038141840559640540e0340c004151309005400314103012800c0d003040140c0342d804002c85400307800c10b080292a9910125451001a080307502e1261418400e210f1203040b00e2080d2908214026071050710b40c0521110007440d15003241c4e000c07941074240c5030700043d44000e2441180110080c10082c02ca141441c0d0707600d03404421584107018001842d0345001c900022202c91a400080c0c40040c84003146981c45184003103081075182c4810800d070715400d90000e510441c0030b0340d194580d543d108d03010850401e041c1d42c801105681c50040c0c000d00c1c21085000540c800d00c0d080480318442c0e40d212008019a0020241160b160b000762201d8811030a000218644 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 148505044 1250 148503794 148503821
    0x9021c06030c03230706030b04050a05040c05090a0605030708010209010306061403060607060b04021207020d1404140f030a0609230c10050f04081f06150302030702010f020705010f 79
    0x651851a161804005002c0c00b02a0003803e007141c404510f0604201e80441c542d101c10240c2d042c01b42d5894001e8011b10004011601443c201400603903c1e201c1d501c200c5200e00c0d07100e40151003450824091008031440108680110b07a910300d80032900d035074200511002082d0040025070f07035a10017030005040d0350342c1c0d5103d04180f0248680c0e0980800801c130a80f60700200a0701c0302c2c0c1c1c0703071806424600068040040c06030b810610002d1582ca0208000f0011071040c0025001c490620044060840c0c001032806e11010102000380024044c0b032009200520040344c0080c201c08418901000080c14002d0712181141d82c40d035210080c004014602e0151040303482840c031300241a200382140e403511400010a00fa1003160464100c882060040091703503911345140780384a40360b5850350100d682e04c1c44041c442c881050020056181d0000c582c7c0250420740380307882040d0001010300ca40c01d83c040c0d04007034544410742d500e901d85103400428030b1015101d514000d03000496034598200c541011107070426225072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 148506294 1250 148505044 148505051
    0x603080c0708010b10050706020d2406080702122a1501050a0b040608090a20030c03010c0f0804030c051203071806050301140604030b0103051c0519080606120109021c 73
    0x1081355544d9280408140480c0c01c3c0039603903c0040ca0000700030310a112810400a02e00680d618005c00709458070f10a00700c51040c905511500c8d0342003943c442800b00c98007001644904a905a5440c07690040c0000315000c81102e1070075110340802c40c4448501020a5019a0140300161a0001000e040074010300059a20909040c1061240c210b1441240100818403e0200200c0d2641e5020002d8031030b070a4000038604158811109048541c0d40b090a0141c403d205141000540d480c062090000c14000c640310001c07040c4030180d00b59400300c0c000f8019010301000400c2c1401045d020300c0140e20728141c44144559900c1c01c090050615408513031b544a0b1700c3c0c0441d00900016420034101c0c0e0550309400c3c0f510154041c5180040c2051080d500014420303002800000104800085d003071640c520380941c01c0118140060084410b4028502c0da161a01000030000c01c0e40b0b030042002503042a000342c4081c0c82c0c60307140604440340203000c0e8010f00c80190b00045d003000d81c4c12950800c1904409121060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 148507544 1250 148506294 148506311
    0x120501050d060c020c0910181503060902030f030c1c051204140f010908030114010c15020a05161a0703020408030f130302130501050a120f1101050d0603080c070801 72
    0x181c0c9250354800700800742c55a611681c0038650080040d81c2e0316102c0104100f03a40c0c81d00c4031030449031203581d100e2080700030100079601c400301049009420481c4c0840c85400304c01d030300d1612040701038400200241d800d0702907144558054102800203081020035440184101d041c001c41d01e841e01e01d46c5000d04000c0081c141302c8072a08900c1001c000e504036803c041d0640d082004113031154240340409100c2d00181d880c00d4800c204112030381c40a0b604030380c200203082030440080801942c5110001e1802040c9000d072104580444030291b010f40b401144c1840c001c0e05003c0d00300008048405955010345050349014180013900d08041c40c0d00d0f60003070f05840c00390b0800c0d01e0504981e90300d0284007a4411425170128080e8580d841152010000f142c0007014a035003c88106a42c40c0103100038020b0a0107151858004a02c2008000200080d41c0d80300010040b05100703521030812100c0c8660200317042140c200566003c999050181c5406140148100e40d6900d2402c0602c81c5400083d40c0600c000780d040c00c0b280e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 148508794 1250 148507544 148507549
    0x12080912041d060301060b1201080c1f050a0c0c030b0405010b0616021203070203011d01180218070e040617100b010206160309120309031106160309050f07080604020112050105 77
    0x1600c4601180212249443e080000303409070076030381c0140a00f140b020a0880140c00700c80200c604071030408065482e407085580a208900d402c218500a004801503009006948501d0013808214414034241ca9240303a00d54610f1001e090302d6009465072504c0c134040c0400c5c02020310802c00781101c21525189004c45070f08694403100b28900c0c020b0303c5580c00041d074804046080c41102c403200c2c0c0c014001c001520340e0102503e442c0074042200c0d051980790503031000009244c01050320711150001c04034449900d04000a01c0800002402201001240d410107101a1250b0046034040c01294098201c070400c1c860141d4600300c0748201054001341420502d0585903000304003182c01c26045140210042c40340c0701c080d009000a040010300a03c03590b4002c08025034581d1000305610310a079641a140103400300303140d6a0301400c3e600010750001807081c040c01613020b40d104c513034954418425120a400c0c0000c00c18140f081c1ca500032540c903084101000115a40140342e002070f5406200c0403c03465061001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 148510044 1250 148508794 148508819
    0xc0408190b09010c120f0209090c1902030a0915051c020903010b0f0a06031d06011e0b1e031003021906030518030d0902010e030a0c05100215040204090602071208091204 74
    0x880b174403c0f540c078094001c03c40d80a40480b0002000508074828078200000302c026103510141c4020f4104030194081c0517440e2021084450b80e2400d030366000c50310b904100300c1000c1d20141700c5425040c400d080000c00645a280d45464058540040740140c0b0354032001c003413500f901c0803005030300d00c6600c0b01040c40039183d4580d8101000d40b021443c00181c150200b0302a00c203241c2c070702d80c40e8020b28404c00d4000500ca032a49104050440703009842104210f0340c039800a0480d00648480522107003403a4054800200c8510286910050b03c0f08040c010541ea5004611284011600803011301c440704002e202070340d01802000e800000d03101031084043d0050010588a00079003845500d0707161603034001015a031080141c00b4501c540107059030f04542ca0751800c91a46c0c017851040b240200d1541c155000340c82e00110b051201d21110315503411090f030743d5600700030007031a8081040390750990a02c1014086203185110400010b003a807259a120705040034650300d0502c1c085145521030300204814401c8284000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 148511294 1250 148510044 148510067
    0x30905030f030a02040308040e060109060c0b1305070f03050c0f010e031209040f060611160807030f050703060e030301090e0115380703080a0b0a0e0c0408190b09010c 73
    0x5030540e0b00c0780c44482c8014060700c600e510203041c40c0d40220700401e0720320020140700e0181c0401d888410200c2d13030b500c000f80d43c0004107034000b400299071400012000811900c1403600e19110320256184280c48501142c20b40505420540309540600000c12287c00c0c80c1d00d0030b02c150682400c2090600a6080020f0b6582155505c0c074445c450300800c00b141261110b4100366000700d43d030042030103890344500e0f006003061843c000400c0c50748580503003080010804207200095618a4000c0d1400c18207640301c1d5500502d802c1001c0b2068420140d000020421922808449851703600241d552549080310b40300680c1d0a00000642c140d04d8402d01c003070b005070382d000f0020450760340540e0200140d9000c90b00003020100e4604820300c0712950070103400c0420740d820040c500d00707129403140600303512990114012100899411504600f04580500008190851181e404004141040d18113604c42e90214248200e0190301d11611855440c003104200d2080344042d441000600200710602c80894000c1c510030050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 148512544 1250 148511294 148511317
    0x50f04020d030528030b0108100b03070f020a0507060c051507020d080c07020307030c091d100504050a0c15030e0c032a0d2003070b0d0515090405010e0d03090503 71
    0x564a081841042c509107140b0b000c1442900c008131890350140140c4003603100c1d51300040003500000e40c01803124840009175180300d1407150449d90b8111065400c408054030403010341c45545400b500040c0100302d04000b40c2803640e1003210514091030f160b45000c05440e0440c800007451810000e80507400169003061407024a400d507441d841d4a8003d5040d4401e0704c001940502901d06c3c08001e2002e100e150508903000101c0030803403010441050a01c0301303c8961000c115400c061a10b81d9108441c0c4c0003140c00c9406942590300188003560b603d04010400d510000d42c00c191610080029a0076104001d641c400407009001c220060900080d00c9581050701100c0e548001040c0035104648058030303040c4180b010300b03c1060b07855a42041003503058609000542003a0004417051607050110b0241c0c01c0320000398409003043d061090000183c10014440000e0030a9481d031f05070b503076a840320b90a0042d4040c0700000707203c2ca2254401401c0400d444029414542407104e16400036100104581c21071406 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 148513794 1250 148512544 148512547
    0x203070b0a05030708450d0504030f08190c11010302030402030a0311160803040311030312070c0609020406060c110f0a060507060e030a02100b030114010b0306120d020102040801050f04020d0305 85
    0x1907130842c8020350014528454551401c0312104d170030024092481d5101403c41d204070500340311070a100e580c1e9403d41f0004d0400108140001c20003e201910759110242c8107081d410705101e081c84800c040c40038610040b800007400300090100340081c0700c418014095003883c0035451807400781c005ca41d03a1b903064070004003040b0b20a02004401d210030b0160301c040401c0900340202c4150349071115a52034010380801c0d16080810300ea041c80301e10b00001210301441040d61004001e90740c10005031628441a0344c15034807262a034188100683d41d510a980c0039084035128000c0c4040c1303500305114820044030259024054201132284140c0d1a100f5140c1121550310301650b8400032403428078050000b00c00e40c5e1900f81b002152401030581c010a80d070b9402c855602c82000a0070749030341010300345c541c00902c42240c03005c0e800041c045481c0001c010b56102402030580e186040285184030704e0b0000724440600142d41c0030409000e1030b0420f01440341c0146648507601101d0030290005100c0b13183e159001000c0c0b110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 148515044 1250 148513794 148513801
    0xb0408091306080f15070801060f050c0102160b06040501030510110c0106030b1803090904080c15070513050402120604050403110a030c0b0f1005090601030209040203040c030203070b0a05030708 85
    0x10703445030100300300010300710502c0200d940d88115540c0e110a040969014042d9444078801d45541000c0c0610a1110742c1d50344201e030346810410364107040310040c101c00300801009074001e000001d00007401c0005d25010b081512120500304071460f01030180480b03200724240f00040010500000c0c659036000c189500000b280d0920441d10240c6110b400708240d03241d420840c3c00028045010b6245100d81a0f41c0b0507003030000030f4407105079240d10840b00341ea9032140700f4002250215902d1005000f4181d403040481e0b56039036102c454100251000c5078090006100080e0004000c40d501c08880000c02040d24290b04116200e00c4040059600500b05406180d41e031001409140c455516640410200e4095130694001c1e410001c00110b03483e401a111b501e110341c0030030130340320443e007501e0312030b81200381c118145a05120400000c420040c0c4002d04240e02408144055074507480294005e80c41580c80d00700c0580386105260402000c0e07441040700b500180300f5034183c60703081002c99500c1000c03854002900d0381e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 148516294 1250 148515044 148515049
    0x4080a09090e100b031c052a1b010c0f02090a060f09050702060105010f02060406050903040513020d061a04030b04170d0b15310801020c0d090506070b040809 69
    0x3403199000c201010300304902d0540c9030a010940102280d20f001d07040c011141800241a500d40500400d09080c80d101045a601244544080c002040d0180448141440e044c2c0809036051591520080d55400140f03004400000301e48080700c0c21102801c0904611510381c48400c401050410060f01990703840000450018043c2e01202c082c1074415504658182c442d04142c00818080700d075140584a04000420151301407051042d03c45880c0e1b00030081d81c0d13150f0380c0d140d01512001d004140e69110912020400d50359000364202007804a81006803560302c4804400240e8101341d10410b030401d000092075044244101c122029246c001200440719107880c9070403a59803080300b00f00030642c2c902140941c0343c0c2c8191307000900b46100444410340c100c4c000c881100700741d1080c000d40c12811036480c00c581144002c11b001781300c0c01d00745881c52004403d0740c48000500b27907400041402004d070070a80c5507209441e0081c1419010380b60580d801e0b82040043c1c1e8404a80000c007a10162641c02e0104410026a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 148517544 1250 148516294 148516307
    0x904050c040305010c0216050f06030c0d06050a1202010314061c030c020d06050a140603031903110316020601060216120503130b03090c0d020d060504020a030807110108060d0b04080a 80
    0xc6078000c0082041c6409450021f490302640196540c0142101d10b0000352846e0441c106400b28900400ca5890b40c2c035038900c0000a580001c01c00f8502a0300e4000001e200d5441a070744400401c2001100d5024800034400141100c05000300c3c1203180d4811001d1083c1038031065206540001e81c1004215445124281a5805950002e0007548007110105620400000e0382005010740503110041c003418603050800800c602080f54440c0d050352007030140c880d01904803000307801d414103d4240007500001280c0e040045500494180101410034880c3d6040c2c0341d41003041f9401842d161010b800400c2440f001c0203002001c0340304000d00d094003202d040c400d00000f44120754080200010301c0080d6540c4019a8a45410891368450140599032840131b190803c140c038a40d10300d0380103141c0c001006041e50361030700500c0060401d1f40c100341d03821b41c040009000c0d40c0080ca540b0340101a500f6060180000051041800401090158448000c9200010703440c41c030081d08158410344050300e171800901c084a10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 148518794 1250 148517544 148517549
    0x30308190203010b0702130506010c060b06070503030c13081c0c060e19020f0d0f0602180603040605010f0b070f0303200f04080610081b0d0209150a0503120904050c04 73
    0x8441c4000000503150501c00010b019152003030f40d030060303510308015044003210300c2100e44902160030602c0000001c4c045074001035074004002c000c0f80c103140c01a00c650307246400071549441280c80005810841707480030407641c3e00820038030000304025000f1048181d414000504000103100c0d42c51005d00806c1016048202584204c80440b440000069a421580580c0b6001680240d159900d98000c90600c48203e240e49504410081c1d030b07900c42d40c0e482d00001d52044002c404007184910001ca0155a039400541c040d0b03018402c08603655050080340c40c010311983d4040f804d0840d0400c1081d001428030304c0d010b1034541d094240010034852003444900701008070070050400a00c005101806a406803000e042500c414104540e0203659042c9855032000d054098070905600c8110050100424408218240540901a400d00c102d03154045407406106071040043d10707002d80f5401d11180bc003405070760014101100201000b91000140500301c3c45544a400d00443c3c444001030301404070a002c5800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 148520044 1250 148518794 148518841
    0x1020304150c17040b18031501030b09010c0c11060c0c060c01020d0f02161203110d02040e06090601120c11030408070f0614030604020306040b040c08061201060807030308 75
    0x2211101c020020a01e12500504403142060a5207203825460344a041d101540e0b84503501c50b103811703a410802d84803040ca48107500d5040c03145044000001c240195003e001718400d601c44160340c105807090b1800d441d84101441d0400082c0b000440c081844030b03d10140145058489545e1680642081410300b0501c400c65500300d0000034603445400c2c815130003005d150508000c2040312402e03a04000080e03100f1041c0089143c0403411800010623010482d45441c003001c3c3c24000389880245000e62900c0e004016070704c0d161640450208002600814220360100e0201e4881c11149000000038100c0d0381002c0d810000e131036985052860031405030710f449100c0031506044907101d60760b40a4196032503c89001d0541e03100414140040c21600440c40c1078603030700d010041d49040d552a101804000d40000f07210950054031420160b05a8071607100301d01c0214429a20b9404900d080030501560038481c886000c102da16110003046200000309144040c0e95062801445c103440700308020042c0e50610403c1e84 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 148521294 1250 148520044 148520069
    0x9080712050d0c020a08030403031e0e030a03110913050a02070b16020c121c05091306090b1e120102120108060906060907170403030f090501060302090a0c050d0b01020304 75
    0x1000c8036045005000006a00501403101842c19042280c40382c241c10030040c0044014000701c0d0002e1300a400480416415010144181c1090185002641c07403007205504c2c940c20026040300d540c0e43c507011b14078a04444c8081c86140030320303040100e510880c40d00c0034a250f06a42c1c00c04210101171580490784540d402c040c0c8140d003030500249016841501d003c00c00c000d8450181c40ea0810300306100c0d0360b41020307010300c0a45240c80c01088018862040075a81404022042098200542e0703800354030079a10403e80c01c0010300d1418220460100c42d5880080c44c41203080480442c3c030407000031407072050010103940248240000e480e0403070190141801001d0380080250000c25000400a41103206143c08022130b8101d492b104140115140103a42c4000010b039070884e4401c180002c1d01030b03640c04c54400d10300001c50b01980102d01086030034400080340c00da515860104154501048d030982c00a401d02c03010444104c80301005401e6204d4200c0400285440d14101c0c01168000e10030b0700c004140b00056003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 148522544 1250 148521294 148521323
    0xf0a030503090709090f080d11040b19081909110406080a0312050c04090c020c060408030a090f051f0306030c090203040201170f010b0c07031208040c0801140703090807 74
    0x2520319001241c181c1c4043c41980700004102d1081d004407050b1030f800098619041000752540a110740c0514003072000591a03a0001c1038014034200188000d0404041a640310303070300d51a041c09074602c01c8004904005000c81403002da58455442c1e95000c0b04c40403c000742c6d41880b4900301550403840080940e00501d450b01c009500c040220700707103007201d00c281d603640000c000000158040315400d1300c1c16045c0600620083c85002001da000441804060048501c1e60b10040e000800310340c4950030078020764001144c440315507a08800700070040d01c4888806440c0c01d04050100c1d0ba500905807841c81100784a00207216010f00983c0000080c641000790045201d4580d80e0743c10180d03000303031002c0b03000030800038200100c0251026118040d51103810054016440e141440005400c1044907441501a508000002900901c0441c4246002c0e0300c81500c3d500d01810301440d0750045030302608103641840410103812161055441c2c2c04581814005001e40e902d085c510ba4601a100c1c00801404070b41c03010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 148523794 1250 148522544 148522547
    0x5060703120905010e0f030304030909090f20010207050a0806043503150607050a02060309150907031202030a021c11010e1f0c0212180306010308070204060b09010503180f0a03 77
    0x31045194828100c4841c6c0c0e4010340380513034030f210480703020300040e08407002804248030310b402448420f40220410200300c0456102c0000360107107070108003081c0ca100715211045580611201004100c111019000305141c103520903242d081c01403000f8042143e05c44003c802c02200818141a9038150340e00d021250307442c0181d603515602c01e89803001c100d8040466241146001022102d4155129000c0c20386518036909000c03460b0406002c4591500542004480c04000d80081038030a8090310000c0049030314604001241c403044135080c03811500100002c240c0140c00044a90340201c44d00582859610355000c2200c04e520b050300344800c1542440c0c9009441c410006090b02104a075101e10b03902500d519503030108491038000e2070b50140e0000023850f4000c103910340190070070020034004145107201c420000307424018240c1044440d090082460760070b604151040001602d01d07194510700d40580000082c106020040156800c1a0900b04035101601c080c44042a640d08290440308000c005150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 148525044 1250 148523794 148523801
    0x11150a0501210201030f0627060602010506060403030807020c041109030c01110d031116230607091206060e070e041b05070b150607120215010f0506070312090501 71
    0x8204000504090001c40c0541d555528086140040c0300510303400c041a60041d00a030244000c907146195482800003940182031010220044100b109442c60820000c0000308032000794200e102160314150800c4450b448541c00c8030305507501806e200030380e942c03213110807440c2038042030400340c00504000581d140021400c0c007605113103030100c0940740000500401100c0f42c900b0510100c0e055230100c64503480701c0e0b000e9800002070102c0c00080300e182940c0c2081070320780e07000d0342c040840d860345590350740c0055210031105480501324242e02070403490a10841c0207000c45128091180c507000e0044524041010780d5200320000c1440021282181c988003130054054442000c1d080d002d02d003045500d044050a00b2611403002e02c46072607003400c0041c4c50700c40c40348072680100420796200e2100718000d555a1014090710f800c40c41803070300c0c0482607109034009007000820007015441c0c61700c1e50010301c0104044500941603c13016901d40352140040d0600725031004920b8003c482c21860401c3c50000d0000640 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 148526294 1250 148525044 148525051
    0x60909060f050718140d050106030302060f0a020f030106110a0507090c090602010221060111060108100f020a0e010305070302091c0219080303070c0204090510060509060a05060711011115 82
    0x340c003080302d569039070310950b0f1440480a248031100c440d1642401011034003140706a1505000d000584681c445070740f1380742102c1b87c640094015a004600700000d200000100650002080d84154182a841e0b82960340c28001802420280a8403003c411002c240c1000349002c0c89401c4022504c070180c1d02d802070130040c0b0481506100080d10628045001c83c0140200d4500482600d4004000c0381051480c0d5034071000507011904011a50780501014481080b030741c0d019200310b101074100060701113441d8003101e0740b9281782104cc80c018001c0611240e003140050240c40d00a01300840e00c0d9544200450081c443c1c01c000940c0311180c0c0191f0308070b042c0c00c020200c4583d4802e444580419801c4a02210088000d10a624442d0700800010f0300c000e200b0100410a148007030700c0400d0800040da202410f0a000700e140b805000d03030f205001c201a01d45008083e42003001030350007002c2c05040101213019031103a40300103001e6110b95100c08031140d01c51460b0f0160640004207a031060322000400104007181503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 148527544 1250 148526294 148526321
    0xf060f020d06080111091e0d0b07031505041103060103151a03010e0609040b010b070c03060e0303061009050f010809150403080702010e0d1e1106130201080f040215070606090906 78
    0x241d48034441781044220b945811004202510010144081101484044900c07a03004001c01c9103040c0054201030840d4010500e0b524080b4140800c0e040000b01c40b4210307800248264102100c0305003060a900459800440c2072a02240b03003070080a59009042803030b40102054070000141c8443d8400041c00345069400d1544403945949402041024241081c1e41c09444080c5410042001d03004420003060803501c61220b10074090303030320780f50142124200114681190800410010b13180740404002c2003540003401c200820f60f09010225080d426440203003810b00c100a4041444003200300407401c01c07984825460040ca00d0079143c000c0586506844030301c050340c00c04c4180f40041c00045807401551040e50ba81c103242c0c0340942610410084100070030814081103140b13000c1070043c144072440c8039450b40a0700352501c00140c40010700c1190000c1042c961410701e80140401a91134000a400000c407640b00d150319462a41020f50080280b50b10174201580741090702c1c0108041d175044049121640b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 148528794 1250 148527544 148527551
    0xc0916110718050c132106062402060f0a0b03031605210408190f061a030d0e0a03030e011701030c030b13120f0c050307060203010f060c050a0f060f020d060801 70
    0x20086071448600034400c15012010004406104959290840b11b0070095500e00c190400405901c4540403951980c0021090100e40c00b200f141c3ca0054400b5007007550181d10080c1060b00c2c240005c2e04000e0340150039034507800c0d2201d85016a694017003054402c0d00b611040e403e8262506031030032513980c4030f4000345504543c5c2001100c1510410200035070781100c220b2405020503107800180603516a05040c0121286000800b4074400701e0b0481c81058202c03020307201b480c40319954803402c2510b1319182680600400010317800d508995201d100f8a00201c0794541008114460540d005075141c0d50148080882100241c000105001c000c4c0007010880b8060b0804000f01d40b18010f4006162110050180c020b032241c54842c41c200e072090100303070102030580c500700c030704001c05695203411540640002d60b0400d03000f01c0140400d0002d810401c000b450b4074100641504020ba45050f101d00d1000001b810b46100d002404052049035085256580501d24045640d200c3c101d40840062006000d240c21944c43c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 148530044 1250 148528794 148528801
    0xe06070903150507051c09061b0e090402040e0f0c040606030207020f010c022205041203150909060f050406020a020c0103060f0504050a0207080a0203030403030c020c091611071805 79
    0x80c0d4659815690412401520908003128541c041c02c0c018101004018080140500176240c0315034201801c1d16603600400c110300c050a00030155082c40341c1d81025168103e81000c41c1d140c01c23410005480e1001e5511549a41d01c0d4000034008004155103001c5901640c903030300410340340100b5458000c0f003049800b04040d5031510422400c0f0700600800a402c00e0b480d0100b00150341c020214122000e02c01001c15000c2003518003440300300e00280902060090f02d41c0d01340420010315010040490794903107010010141180b40207a441241c5224000a281d51000f2043c1403020b25000740540d210741940c00d0080c1d05280c036103407009500c40c40c0c3c4d2800500408c03c0d0f52040b0740c400d020304002c503840d00c40703955090360800f81000020000544441780d0590300b0840c400001d0350754809005694001d40180d030700c80c5047c0c28040c0540b442c2c80341101c1103400201e0307800750a549a500d0280c00c185119000740700707050f0400003074802c02c0c1806002290342c41007090003c0c03034403200301405158000d4804107100944 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 148531294 1250 148530044 148530047
    0x190c0f060e01081801060b18030615090c19080612010b2409040606030603020a08060717090a0f061e09020a09021309020409020a0e2d0d05010509010e0607 68
    0x11980c000d100c0000d081c00c0760003030298450720342c058002900e000c4601ca40e0040030001400c4401651080604030b60209940d1465894076200d81c170182d009601501881c644140c07060b9200b007404203d00d22442101000c502010303c000240c4a50180303030362041d901484c1710b100c041e05d4120101c4074148100d07880059806072a10602801044802c0508000703001a0404644170712015281d45625001006210a507c0c41d0b03620300540000740f0013a1070020380d250450040c0000c913010742d00011003a6000c0018849403e501000807451181c4400da0108142c6801c080b103410105407c1000d09101d82c104060342c140400c1d035000d820401c210300b0f0746014040c00034451400703a41c1030250103507100020000400410071590020034501c4101c440e210082b80e100c00700314003282c0107a01300820541e800300e0800905600084034040c4800116801c00800304070b658841c0a40d40714002410740720400440340c040c15161648000d030f607180d10200a02292421003641c40c020220f200c580c0920f48262008110a103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 148532544 1250 148531294 148531319
    0x3060405160215070201090b0c041e061d0607022701060f0c02101b0c081506061602030304170a050111040f0603021324020705010503060a091d190c 65
    0x15103003500508081e5443c5041244200002440001903540320100750f8005000100702a101d400c0688003e500c4d036091044403111050983c4181003c0c0d00e042400b40419034102403040220383d8400d40403000c1c084000c010505034015038100070f4000201980d070802248a040300784045038441c0c80100340503a038500048416800b510340c800e02080c2c03192044805400d080c651001d40e200745003445200449100e110750701c41118402c0075100c0c503412050500005806121252407105d0900c1800c0b12402d0440000310700303124640c0c5030050108014403c0c021074070180701f6180244260086440e00b10050041c0075102c1941c2d0400301d40725441c040d560486c100808041c0c500307880050307407078182ca2401c0c50b00c142c00035402404080503611000d8000500d00c400402c040712403002c1c0031040e9044560941000e4030300704c0305400540c14444103008102030358072032183d050111001d200340803640202c800e00c100220014450100318600400c5e81226900426074495124103200e18640124a540d400c000c81c2da4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 148533794 1250 148532544 148532581
    0x41104260d050915131508010e010e06010302070302010b0a0b1305150a0c06060b0f0d0c03050106020c27130308010905060102070312050c06040b0109060602010212010603052a03060405 81
    0x801d4081c8041000b505080103182c4082110340240351400c01060308500442003182d214003003d900a030301b0f545400c0c0e40011400d00502c040300d04d4141c41d504004007810428401030055042590200d80c104c1454401d401115017104090705aa03142912010324007903903400b00101c10754420076290002054240300720f0740c00a039210380c00b80c141000300aa0f81200c0408500e0b00c00d81b0000e03181c44020511076100307001040c403440d80b41092907540ba1020500746c1a00c1d2454462400c4c10700d0039004010503034010071406900ba4040b00c0d100101e03072042808039039402911042c0b0f141910076600300640b10400800114613076010751a07070b070b100741e80c1c4040460580b441141c2050050704044401c0001070103842c1c0c0001da4405600782a410034030350000240c40e0510440c0c098586070100d000400565010b0b00c5000302920492009603d481e181180c1c10180600c184141010155144005980010703880103000c208070f196900004403542c0c1085011079070704241d6000b03114525050109428401d104140c480 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 148535044 1250 148533794 148533797
    0x20c01020f0c09150d05031207030c0206070c12020f01021602010207080706090e0402010c0519020a050307240e1201060303080f190b010e03150103140a0302060c030402041104260d 79
    0xa0031354036001801c01c8080d080c8409a00034543d04402400500d061019001d0552040641540c40c60107003c020151000c40d8000019904684140002d203a071200c00c1074021a0491012101592015002c034030f4803003d40d403280e5480d48042560780d10383c500c51a0348440f040c001d90840701d0554031110703401e8903100540b041c6004174080c0320040110030796013050b483d4230070700504102e00305104a07243c0c1403c05007140c080c0d581a44140544004600e0402d40480142c841a8001e084282c1041e1740c4a0115415080d10500341c036000114002191044031488070826014000901840c1061307201806400c5130b00088003c5030724000000c1c10001070443d107521a0600c503429200160201e10076a004000031074002c3c0c100840d0340c9403540291010490324004c211107402c0b8030b1041d0700d141012107030380c40c00d254205860340165400c030010a030b00284d4990400c0340ea43d02c4517529151031000900505a4090754a090031003c1000105003104551a1316210a0129030b201c05031b0341d00030394586030400903e1200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 148536294 1250 148535044 148535059
    0x2411091203040e1617040b0a0f0b0d14070305031201180216030c03091707030605010803030603030406110c0d151d100207060e01020d060536060619020c01020f0c 71
    0x31064210101c4640d149050383c2801c0c05e2071a988515a000c1d2a011a0f00385c0d607004040b41032017940b000303a00c60f030b403842818a00301f001440f52060010319800d17400320025106031106440090898400d0049000455004007147e60758100111035540141091050781b521071108154141598903038000c40b640313900420b074401150030595500b61448031240009030100700c2414004940d0407103000c01e00740e020a03da00203200581c954603111041e150160088042ca400520030b201c0f140d01c000041d241038036030300c0c20100d801100341d0022501e801c1611000507440b0f010a003e640a03c0a4444401d02100c00d40c1014030001d0500c1003080030880e1029139410b13080d4400100210104815405007408a1048001141c0020000806800e9070400b07003104024641e90344c01000503141100c0031030040c00711420480b110a101c0d0250700721444108913840b00c00d00591000420b269101c0c030464080325000140107100605403080250384803c0105070501600c02e010501c1900c460000d0440c01c0c1180007005103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 148537544 1250 148536294 148536301
    0xd0305180601030804180b210f0a02060409050c0d0c030219081003030e060702030f100501060801030803070305070c021314180606060903010605090c0a090f080a2411091203040e 78
    0x80c0c0620036080c0100085036881800d241c4a544540700302c6c880c4001079401089100b08c82111034240348540c02c03c0007c50744400b043d10010f80b100f0064900701d031381c90880083c4075560030208008920aa0301204006450051298038098040d40030300407440048d6600c40d070b01202d6400958080c48285d03515001c4200982c4100002442000c1c1558440d02c05881135092401c5a03001c08d01e0407640914526107038002030450141d0604510a060051002c0d26040b04503503d11b845410580c880584014101600d410004400d280150070300728242e54080c040298505e00b28110302c00509040c0301405029582d071002c82c00c29030000c411440003080300e41c050b01745602c0c0c01040040325031210000c10b816540310701d000942c1e0b0340e0ba074419600c10001d401580b41d41c0c001844004080d5052038000d40070010900da03045c04100390001368000c1036544401c4001800c040b4184083c034161200303d28104050400c0b00c0c043e4a5100ca03405456820307000d85501110480c4140032940b070380900c3c014996208041e2001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 148538794 1250 148537544 148537559
    0x7050a0602100b040605030726030a0512061504030b18010e07090b030f070e010e160804080a030b0306010b041806050108270106090e0d090609260d0305180601030804 73
    0x148145040003440000d80c1e550b02d1001c28100912356000c00d08040e0301403151310114420441c42d8240302c1e4003002451038140300c940042c00328007036101d000f031042c0e442d1400100781d61160b1100040c0c0203281000151915a02e150207103154000300c03455407061629401036401c0340014020750580880f410060241c4a041100032030080a500c60841da05124540901200c42c00c01e20a0f9005014401510310b481d40c18442d001c0c25090019101c4d181d0801c2e030640d420030056012841e00d401030380c0140d0701c69030f60144e030504401928000008030b80c503009840001a61007860303002081141d074078281c9420f80b0001d211981084070035a203d42400300351403100281d011010016155244250790308034507071036030142e18081c3c21108a0f4003c0c400c069507603039000103041420001100142d0b62407815206440c1442801400030541d841580741e0302d100310340000400900c0c0d8400000c450710401c1250700b40008007400401400050b16030798a103000d08a00340645000128086050b6078016122074500b42c50f2000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 148540044 1250 148538794 148538801
    0x10b240f040302060d060518010612020d1b1101180803150d0f05010b0f101e03110309010911060a08040308040212010e0601050301051e0c0702060702060a030e07050a060210 76
    0x30361548411007040080b006035a294068910a41c80380e8000801034100001d0103020a0000c1d1540c1031410354100403c01c880d03001f0004c501c100d07801d000250f00ca24120420101404c0200003c007101d40c1c0c03d80070a00420743c003401801051840704028040c031000140e10a0344d08803e040007500801d400c00010f40441c60205440000500191002d410302c1e41c582c45003142a1001c4004aa241e5124039402da89840d041800d00c2040e0811a035100c01503400c00f401402c0c6661b242c1c04c40260583c0c58498000b03483c000e6101040d8040198000741e42c034a444900c141c0240a003040c101c90700008180b200306c0b2400c1c13003401c0d00ca500c4401d0715a94425141c9803800d170f0f12114000d20481e0f0040030301c06000c845131800e021b4035544000c120024074095050008250a4540081960440d11a0030040c14170960320002d42e90b41140c2e004a407156540e0322400850042d106030480a500110005240074400e07505902061185203e00240d6100c982c6030782c10000d414000e40b08110059112440000c8a80041da0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 148541294 1250 148540044 148540057
    0x50705041113080a02040f11030a05151305060901060e0901031b0b1602092202060d091b08010b0108070e01080a140108010e101b050c0f031b010b24 65
    0x40c80300e8108030300040d00800005090308030030f00c5600011840d07421820180182c01c20049004418400740c80242e501007040e020040aa640d0180c0310070200d90345022004540d0210700c805801400294103148031203014010076a0789901034158200009903043c464001e10658000040c040200340e481e58841644284030800d403524149045400040c4071441c12000b8410b802c0c0306500d00d603401150340108000c0c204001e241440e24001d03082540544002d08003440c10035541106c0d00c0341c41e0f43c9000880703001405095001003007194603c8070f4035840380c40c2c012000c0442c2c541c2d200900c0001c0c81c0d0001141e03030460a9807101c1c003003402c0e03280d10305c00f035070141130203a0f0701000005000406003140030326004c240c03400381c1c40143e9595491414041500041c00101c01d0040d034150140310302c05140700c0744a22040505401810031601042010981c4814090280d0b201840803c40b511106900c21202c5420351450440159601e4083e0500480c14003080c2c7c2408042e42c0c02425529040b406d0074015240d1082 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 148542544 1250 148541294 148541321
    0xe1c17090a06030905061503031b0c100305010e090f03030f0a0b0d03030522020a030305030916180606022d0102070b13060b030303010b160309080307030f020c010c05070504 76
    0xe000884603600e400010300010140390340d020840140604250f810500080c100c45211090840d0800307568500004460181c0340041d0341d20905000c0504040c10400e10100c1151300000c10840d10070300c507601d03400843c1a50200742d40907005844071520741e0ba90b074101d66000d0082c0d810510000f219007054540455201c0c02e20325010402c0021880020810480e01070200c0101c0e5554080c0b01100e13015031072100a40c4906038550460fa2f04980004031041d82600c002000c108c40000002e528800510805a81c1d8000c0740c103000c219a21440d44a100800340e00207800003518282c0c1c0008d0162000414030704a00d81049401c1ea0710300c20303d060080283c0f21481419481d9000c000c07a1001407083d40e0350750720407079012028181058251800005680725441307000e00c681c3c0144014441c07000e0309002c07a064201c0301c800042000c80249010b032000000c69229040c01d000c0030a442050681002101c0c45929103039003580c050940f02001511051a03581c00940340e6880340340d00b80468103040e0700680340740c10324 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 148543794 1250 148542544 148542547
    0x1b210c13051c0602120a05060a05010203040302040213030b0103060501060f1706090709080f060412050f03070c2f090610020705120313081e030405090402130603051c0e1c17 76
    0x10b0310703200f05076845100e042c8030002c20768007041070185c401d20a554010804540a154840c94100000d41c2d03400340303000c003a114540c0040c82000140042240600443e400b01c2046250341c0d50b42001c00080c1000d1040f8400306180c904a1444030740f1801e403a509014000302c00d40b5007500c40070b01740b141c0c0040c020100000e00c03402d8800403491640c20402020b541d200039000702041c3c1361924101402d41c41000105c0c045c4501031003019446402501030703136441600362a0042c481c41301800e007192202c3c201c05500240140300d080b1020503082e00a101c62154200b66000310080d2258420301000711840075403180180c11001c002e110300c0c5054261600d94150b003038100e0b03051207041c2c200c2c9031500401e90f20500c03450b0301220302d42c1189640221a0000c50030a04055401d041c48c00001c038543c004001d200a00c6680c14140025102203a81e010001541e0000201c504e40743c100d05414800d844004400313408502c200c29101e24500c2d00385c2c00d02c2d41800c0300341c80076034039000c035070380d8021690400c4039409089500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 148545044 1250 148543794 148543849
    0x20c04020c1f02040305070b0a0c1b050414010e060114091002030c1b06032d010609170601120f0201110303040605160807090e1b210c1305 61
    0x215800644840302000002c0c01c61804200381c40400316040c907005041c401c3c0140820804100040b0302582200c0740f2903071a5503520740c1a0703801c99403040002c1c8010724032582000182c03403642041106c0c0c010350b9001e482c100100903205428003081e0800344070f04040032400744000b414075480b50b90562480d9000b94026401c0c591200300080c0300aa01412081c010b8ac00031036510b10204003000406542e00b0030034042000e1074218004607000d40b000400c0d0400015100c0c070035003a140c9592400340310b03210a401c0748410359612050b00415008040c41040c2d00c00c0b0502601d070300081c4011503568121680540a4080b400060752030b0794003050001d405a051010031204046445d8040c8001d5202e20b100704000100c62402a00610520f814a00c0030010040b05508000c0825080030401041e0f0300ea500c0c034100c60740c0c0c40b0609040c009039594007100d00504045802c10a482c01920a00c0340140c81070340100079940d07200348410341800b445240e040783c1355000d002046242000c00c100d001c81c01c3d03891990b031580308 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 148546294 1250 148545044 148545049
    0xe0c0f01090515090f12120a09080609101b0507140c090f070305011d07080a06090f020c010605010305070c12020c04051602060108030a090611010e19150207020d060c020c 75
    0x10b030001190407540300058141c1c524940f20005e141040c004440100300180140700e031036a6000500b4005051480000c2c0680380c1d1800740034180020001c04003107500600e4803502c516112609541d0312462281084075581e800711240100c1c52050b1404d0762443c0c14518243c0395111012035016484046000e200c022001c961030360301c40c16200e5005414024154180600c1c000e04032401640015280201001070784822803480c0c23a03040c0c02803150310381150a0745908004500401c407540c0300c5a91b142c5850240303008110f0340e03005813444030560300003000356690b550010740c10390303904684440c0061141008003001414014107254080482c0c8111480400600c02080403a0000d071765a006d0810700d140724001c1d541e41040b00c1809802550003660920910310000b51220803140a50818030400400c03500c0c408809510440181e40241e08a440b400055070020122101d00402075401c0540d408004030511503d00850301c48a9020340a0000a07410f030311400002e15007583c1c20b1f070842c018102c2891181e0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 148547544 1250 148546294 148546309
    0x3040c12030206180601060c110f120a0302011b0203031f03120806130c08160c0807031107060801060c11060d0f060512010e0303070f02120a0302040e09010e0c0f010905 74
    0x50301c20340051149082403105211146540a80070300c0580c4114014810207512100200c142c1d42d100144200030440500000d540c0c0178441c8400d9000809040629940d4130001070b0080401c0c040d030020099020000b281044042d0b00111010260b44104042901d038100e0242052081d03c0c042c107007071031043c0c4079510300701401c10450b54000000c01c9102441268500b441c0d1b21284c01c40e00400c104280010340c4406403403510006d001d5019405075810081c4030030b0051801c0c501c1c032584540d42c542c0d180721624028000c58800d10f04c140352882030460200740c0c24050004141a101c0540b40c4400c80d02c0907503950840b24216981d01c0f80c02680c240241e040504041c001d40200b00b032007560120314103040505000e4404c0050444425a0303041400004a0310008421690019050700d4034002450242a00303a01d00040170300303411030f00744000418141d216070650241c800c1e45c8540400c50b100d0388409404c1400d0364899440d007030094000d140800600e207820101e5081c49a0107040c2814200d94441c00110380c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 148548794 1250 148547544 148547579
    0x70c0510020a03060506210a0b1c050601080601080a06091e110f010c08070f050c0904060f0b10051b16090516030504050303010b0706140106021c2303040c 68
    0x55000b09151240315003500500000c0d0805a0310386050585c94003038106c501d081400d000f000a4a0a80400d40452039134000481d03100c0c0141000b40c0c038441d20201007074031348408030050320b0354003c1c0400400c100c040410154100c8010400800c42d004c1755482d484001e01e4981c2046840c0c0580c000ca0072580018480324580c0305000e624007070001200b410600002801c0c5505141c104103800707800500164006054070003240e00804c5140041c3c07003528000d032505003010340390b41e800744048042000700314031764120003414580f0881c14410b407500c2205000072b0900d105401000300b8400c0c00300c00b0000e030b00c1d45c2c50345503003141800440c4c800b803015034840880140300b504902d210300e07290002c1058200c8500c1042c40d43c2c151030b107130801441c945929215100c2c001030041d20200d130800901c4e4400c1c0841504070901c40b0800c080300e98104e507580d0710080d50382e25101e05403030012401c001c044206103000d64030000c44503070380c0754030440360603c0525803c4499000800803102112414000700d000c0380000580b804 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 148550044 1250 148548794 148548823
    0xf050106081b04050a03140a0503070c1e0302060a03050405011b050a02160f030f2915030610060e12120405031204050d0b04020f0d0323040509040308070c05 69
    0x3032420008029002000c60004107115a00104001c00c115124005c011040720340003410380940703d11040815040c514480ba001d032040c440810500c040c4818800c1900444120701c80d031011030050504c4c00d1620301d5180c4000780d07001d034060000f06010360194116a502c60b00c0794000003808180003440c4100309000b000b50900080300820b1150200307404001c40390031140000400e0410303905c1c0c40540f40c4840080c0c00010403035248001d4940c100021104840c01c419100d9040d090b0181503401030381e807040411240034141000c81110101741e0306020039050f01400304e0500c881c0c40c10b03081030382c06d6608038000003145400c0f00b881e680704111003c0a100107203000225542c031940e1a40361074101450080007c00200a0702403c0000300810307601c1c3d80311012450340c84181e6003171594031400013a2014010b031040a4101d040716565101f01903100b042c140d520a9144010302d8080d01088071107001d030243c3d018098000140300b0102c0e01003401070341003643c800c00502d0940c030024100d80c1e640d030a00d0400c03000e510 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 148551294 1250 148550044 148550057
    0x13050702030306040f0e03030c070c08070b130b030402010914030c03030711010f08070c0b0c09040c0c020102100e061803190206040302120a2c04020429030403020d120f050106 77
    0x43da40762900480340c032404034810a1103220303c2403104544910014044100c01e08002075100e04000b5003101680040120409448480e992414403100a40c00710502c01c001d20380a010218804006205483c017641c0c041e5604400d00c2d0030003000c0280481050305442d81442103446442441e0b42c20030080070240e01c00e2030b808007080380301c9001604448079910048140f112010401a6195104030305410407508003411503c2522264801e0b5a584901401c0d16045810700170750000d41600000e9074a080392007070342250b04080100c0b20f00022155204010004c940080d0003103a1250400e080741c540030f0400702c0989140044030184030342c3ca103098100312400740c0c002030204030078180c0504c000c1b407422891007011460096011401400d00000c59488400301d40c074200055840071950020301481040900115555502c9a13600c0520f40c081d00341407203c074505501c03020300c12108142580d01440d8150000e00d000709407001c0927a40d0305942100001b01d141d03144944c582c00d03120340c0a000e000700b0f05512100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 148552544 1250 148551294 148551301
    0x30a0e030615030a110103110406032a050703050309011121010b070c0e180615090a1a0108041502040303030204091a0307050111010e01060f0f0905010602070e06130507020303 77
    0x9814240024011035003882c61011412240c0c6020442e0440c19621400b40100045020010f800401e2414001c207092080828086241d07a0980e10030303410601c00c03009131569150300c03c0240484109100021000031014060580000d00903000386402006200001ca04000b49030402280c5811891f800007101e10035a48203003c80c02e1685807030b405007540c0740400b4680b60b1161540d00d00c080c01c1d48140441001ca03000054070081c01c010411139580b20b080180d0b01c090900510202054204149140c070524aa201151007002c1c45d102c0c0c20381c0040350a81c1d031714005080200540d1403142c000d01c15510410040c11521011043340700402c0030314401e0f100180c48a04100d4210202d948900300c207500c3c00017420328040a40e030005900022103400740b070841e609041c840c8200d4050440040b076503180b9800d1020224401c0341c1800c5c0b071016281d40303410406c011580d4414100503500203209517030140e008804103100c8100c10101040d44404040c01305d183d01d082d04030849045840855001700181c06c041300b803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 148553794 1250 148552544 148552549
    0x10120213030c140616030507020301050c0310052e090b07050303100501032003090f010203090f211206060f0d05060108010b0a09050402030a18080403030206070801150e0f03030a0e 79
    0x1400645050f08001c5290341c42640810002c3c81020001080398014246034000c06200d80100e0300c2841e40600203214909050882c008140c109031180f0050094000c0003080c1803c0c14042104841b80155004143c43c0c0c07802e007034020703100143e601c1e0420007408543c0800c16040b45c8008040d550301c00c0c001159689001a0103265811850b08024101410030101030003060700d046110380c0d42a029200c0c039030399840b04000d851614844148000642d4004810812401c04c0491115455440355040d1903440c044c4a1001500d003486890340140e41106100720f000c14810810101d40c00790020f0701462611034074812000070b0340c0010554a00b4192198200f01040d6803244003140105042c85600e42041c25056000d40300a605000301ca000707540c0440000d011000b96001440110316070510b184050046042815440e40180000c0d0054814807001c61030701445520154121540001000c102d1306004008407131407c900008940d018844003491406035400340b004003080c1d14641c030794402d40c0924506 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 148555044 1250 148553794 148553813
    0xc17040807050406080a33020306030c060702010c17040509010e071103040501050a0503040f06020a02031b0303040309030f0201030609020a030915020703020303130c12030e01110a111012021303 85
    0x100c28007550034100200b00b80c81001401a0707801e82d1140105000356014411f40e0052800240382c40c40d0440c0c1d9801190619580d54000c40c0103400907001d6a0071203246105005d024814000c001b0b00003441a10140042220015180d94079113000c2443c03440c050341e4100180722900207030009500e9007200030a02c1801038000804005101420001d103040915103000a001c50040004450030300000000050800c001c420308400c20a500000c00c40d111320002800940c0d035084072800d1081001c0c0c004034004c08140c000306583c41254155034244415085075145102210030700022810b040d2103003c08500f160b6180090000040e1540d8005110300250a003140c12600308100165680e10400500d80425070200c12664071080784c48003400141281e15145040c01080d40c40740c020710300400e51080805074000145803403c1e000340c0c2ca80b024203000040d0302d9204c039105040200018011814940b1505143c10344150b40c110500304440001030707821240c01640d01920181042e2410030b035040c42004580d09 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 148556294 1250 148555044 148555049
    0x70909060506180903041503200306090c09030a0212030c0a11030c040911040e071203081e0f06010305070908060907051005040b04050607170a09090b010c1a070c17040807 75
    0x1281441e5400d00c40c01a82e01d0f441607000e40c440714480c07d400c00460741d000343c110004008800c13014000000340e00c05010240d801c250f842920500b00342010031503001d845816071b4108140140a01034107100c643c20012640c0c400c2c4400826800b0520144221100900000f03038171030b00401c1d014804040300c03820503003032110602e0100d20a9140400c10004036085101880550300269000540c001700380710254a4003020b54080c07490051808600c4082562140c5c2c3c0c24010440c8039101d43c1c0010100c0e142d410780e010101c84041d420000000040e070340758400e410658000d11281004811143c407030b800c403401c120301120a500c0c00da1024100308060f04004c240340784140c1003071a001741400d09010800201c2d200c0d07845194411000441c2c81d030305110b200450301c0e6441d0300c0d514050350f6801d80b090001c0d240780014400d0f00c6109203400310454055024119000c0e44542c040f03000a89461500412400e805015290704104800349166500160000780c10007a00401f2550381621645020903262819061b45c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 148557544 1250 148556294 148556329
    0x6030607030c0e09060a030807080a090b040803091e12010212060105040e01150302121609080303190504050118150506010306051804141006032d080309070909060506 73
    0x10b402800e01d0350701240c0c006181c60308982da103c0c0d035165600080d214900c10780005d041040c1c00220f100030403206034028500d20104c1e4480d038449540d1110030351020300440c401c68906800c00c1120741c3c850b14040280d501c03080e0050b270410b0640429000441c03154800d0007441c0303500380e50020325071148443c7c06e10204da10030b800b403030b00d103107000d090108008099006100c0d48500310380130280584c80d1402501a62210006050350900718034024070b00b42407254610901d100450800c16020403240c10100440b84101d441280c41c84429035000300b6a001803100401c00d48241d56207a078062600710564804000c128001c404042003017884000c140111040030304014107142c50079004011589400380d000105248413004601cec241e0311405c0010b1100c480b038054030b800340600b00c0f04003082240381d0f0041082d0390040c003004514005080b0304920811822003003800b40c80d40d040c880d80018890200850744401240165020341c0e03034130450442aa2001c10084030346070344500c1088010305081100c100110b04e032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 148558794 1250 148557544 148557551
    0x10150e0619030201080c0f0a0306050f0409080f18120102041d06090c091c120f02010b0d1e051005060411090108060402030a09170705010e0318360603060703 69
    0x8a05592102201d03911009040c04107407400192914410340a464800700c582401642e103545d01100207000700030500a240c480c0000c00443d03141410107101e0301074040e1740300354031034580001c1604821032031300144401d1075520804580d4a41c1c0f5140c1e10445415150b0780400580c5071801d00b103034603041182c10030344284502b100380104070bc82e6a42c084501c1c0c002407175244051780c40386034101241c0c00c03c2d0900703031002c0000c10341c0080c0800c000c2014094400c120301c9568511042c0e141a4041b400ea4485412540d80711503c0d62081000c0b504644131500b8210712024100c001c03400b641e0f10941013203114613500c400c55968400300401070070540039006000c446030725034903e0400c1c100000390100001034915070060343c0c0400000e941e070807554001c04001d90445c1c0f000401216600e00c010340b80e888500120b80075402c04007000e00c2900008180c1c0d0a81c0000142004080c2d03082043c0903450741c240b907800c41604c0e09060412081112040007000c00c1450307260070741c000d00d4010245403404001034140d104052a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 148560044 1250 148558794 148558819
    0x5030d020f0a0201120b060a08060112062d0e07020334060905031312140d0816030f020a03090b0f2a070611030f0c030103020105120910150e06 63
    0x4012a001d00d5803030342400d16115814045680100070146c501c8a0b98201d240051310071655a0800306a500c0303200260b0b1080e0210340c0a010b62004d68200c3d201b800c15851403a42c0e4101c840700c280f24107400c8400b460b00300950050b503444148100c800c05542d1600580c00018400c00e200c60b0000441310500344100010389906280c1c401c0d02241c203c25103010304990f55980c071310030802005000721a00503641c2d03611803074107a4680301c03500416043c0320002c950003604600d40c80840c44022451f68441003098903400e816170f84845400840c480301400503420190b403140803c44508561000d04090000f6640024100015283c0b10085d0f0001500c1420320340b20420801c40914410700000c01000c0080980301c090346038031950f409042c00b810400a00040c1050030210840320203001852054203030002038103007512050300c0341489100a000190014004002d52034561300242c414a400000c08000c55030108503445848003110201c5914140300314488500300125118640a15000102141c0604241c107 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 148561151 1107 148560044 148560073
    0x11407020d030501050405151c0209041104050a0b060405040f0e1203100902030402060a0804140d110d09121b0306020d020712080708150d0c090605030d02 68
    0x291810f0300000302c4d0700d454044d05000d14000d000501e40c1d41ea9044c10700100100d40c00c00d40140003110440500161140c130314462140c2e0140c00b4411045003c20200f006807040a0507041d016420042c074220315aa42c501224126202101c0000d03104405400300c4002d040948021161401070b240340d1602c0307401c0103005510824640e00c24403501529000e1600072404180c40194000c0340c02c2c840c4015a9014140721078106001e15601c0600703500e040310207480d0510480103000019907100d0800342403041041201609007480c02d03c008003600303020404d50800745d4028090649540d082d251928901e6414828000e5900404290350798034121345600c020794030403a001c580315032204d03410304041403152003518000c20241d42d8840e05074a8459030020b4101d10440010307031107040500440006042c6041e0072000300640d10020484a1810003014149102056035a080d900420420354071070 = true := by decide +kernel

theorem cover : BRFrame.Cov 148381294 148561151 := by
  have h0 := BRFrame.cov_init 148381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 148381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 148381294 ≤ n) (h2 : n < 148561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
