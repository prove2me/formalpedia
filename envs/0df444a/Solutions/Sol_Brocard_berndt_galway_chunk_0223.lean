-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0223
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:33:45.035002+00:00
-- url     : https://prove2.me/submissions/f5d85bb0-b65d-4087-b389-6368a932e313

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 39928062 ≤ n < 40107918 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 39929312 1250 39928062 39928079
    0x20403081605030d0501060305040c09110a0c0807080304121106010510030b030f010c0203041e2d0b0a032f090f011106010f0e010f030302030f030a021204200910 71
    0x242c401c03030035030707081580c010885000c6503400d902032000729456030100020460501d080310007a103409003040001c22188a00f0300e13140d004400c060014172540008450600041e04c056980b0981d10084040e07032480c00d490004400c0c4580f41000000c5500549148038075040802c025050381c80c0030f41410902e92800000720043c01140e0b111036018011411325640050080c0201c8030024403a07002107558625003480801c24407050250022485921481400b08013002078a00d811041d002e000c0d443c03070b500c520010900c01640c42d4442240b10000140e07002003550140c2001d06008400012641184a5010036101000060b5241c1240c0c0310108140102d41c0b8020003e10403005043c546020f041e2141c1d542c8610b440300c284c00c000400000040104505501108054054003e02070561451441c1d130342d01070340c2c81c0100e036503807400342002100040c104401541504c10258078680007074554202400c20000b00303008200b003050b115010414440341401c100544902811203c10b00f1000c3c0ea1030700508 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 39930562 1250 39929312 39929347
    0xe10180b0616030e03100506030c0904050a0f0813060e010306060503090601050108090c030a05150106090803090d030e09270102090f04050c040308070c05010f0c0209180f0118020f0402040308 84
    0x88081c03000c201004c0d225518100170f100b1560803500c0d4001220700304602010310302440f9200c0300340705d860642c1c10440018000b06034000c80d15801000104981214503116145000b041600b007100c428a01000030480d03444208074038000000c6e01c04004040e15900204c0e840d1100701c406d000180d00c0100100501d500c200035182e400700050040c1c035030300c403000c000290824044201c140d9559100300704190040742ca004800340103000c9801d040301319514102e149034480c02501d484510510b5035412513402d00d170050103082140c1e5002006220685405680c0e281c0c0845000005000c580c1d000e0891406100144202da041d0800180384006041d031003400c1001400000317000302ea0590307080c800080028000400341a040d442038110355081400d2000060101c1c820f101414100847c522060700561203042c04150050032059540701220300142c45980b4044920f2107400c842e43c0307010805911160307501005a803051080301c1220441d0708c820100f1091303010320700018140d50000c02c0961024500c190a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 39931812 1250 39930562 39930607
    0x40c12030f1d03030a050403020a0e060135090a0302060a0506012a06020a050301080105060102030f1206010c020a060f081317030405010b0901090203070e0409050d11070e10180b06 79
    0x307600c4402c100741c101180c11504004e0401000c607902090600c11450000a0440508a01c0110003610301c1d0680000300089400314200b408020315180c034828095641100b54503840c110340c898030352420140d81256407042036007001d90040c06031201003112801503011703031405410160740706d4981c015010000302c11241010010503427894269012400141d80740058080f2500d15100c0a0f141e614140c099401e45000a2980341150400c0102032140e40500c0701744e4030810155206026546d03680302c01690303007800490b0040c0d4085941200001ea03207600c04000340403e00c1c90391b58620980c507507800a0144027008038008120340392244044115010107800f4551160068002040038443d070070100e91890b00a03000341400c5a0000200f000581e000540032055007401d40d020400151240ca4070b648a6418828107410001d04450407509501c08100b450b010b0040480d0b12042c40c00c00160b94041603d45129082c1c03001071800807208080f182d4403902070703100400b41c94546002802202078401d81403481 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 39933062 1250 39931812 39931847
    0x304110909010e0606190e09010c090e041502090d02040501090c0207060c0206030f09120d060609060804170309031c0e060105010206070c081312030c03020c040e030403110312070b040c12030f 84
    0x40e00007e5180003003480600906400c8000581c5901824004000c115035802c5640e8410708401031200080055890010303000345441d005844006090000365500000d50000c4c0d0300504060001c50440801e901c403592200d8107800f2240d01a6644a080da109072207284081e510400071300c00a03c00e1070726400d0203580241d2030400e48050a8501002c02c249800c02d801c0c580e861651080306200c03442d00b00400c80098400d500341151240f030144d9481c403a42c4100001c00a4000000c00400c10385442001590707a01f80c0340c3d03c0d02c10204895200340000415101c4080d0000f0f2044030000112540041f900d61b00440c1e03540d55064030040d80fa200c0783d81c66800030280b003c121401c0c0400003403891a042d4000901c621039036030914245020f0070000c0c94007a111240a200d9860401c1c0a020740b0b000200b142d040700da126280360700e0031546000003810080c0d07605240880c0140000d5042c01c009a2643d0f00788914852180c2c47c8101d91170322070303440364001022802404036614030700140c4484d018001116503241d465 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 39934312 1250 39933062 39933109
    0x61e02070b0d06170c03150c0904090813091509020a1d010c02090103050d180b04050f030c0405090a0308090604031715150c070503010207080313080903030304110909010e0606 77
    0x452003107103c511100500120758000083c522001d15083c080c420b4034002c52039001f15030342820202e842c400d101d2207c105208a030780d10140300400c550241542e401d000709014410585603284401e2020b0001c11410903044411200041421986403007600c0c0b510f0501d656420920280b000b03c030703045100d85880c0d14107210394102184016a207600050f07004e9803081010f400440d40c3e0b5040a03080000722400845200b4800ca000d100070700c0c0790000e68040b034408a80301100c2810079004281800004000240c20fd03040004208d6044800140e0a1000f44039554070034070360381c54890780f5450340c0c82514020000365081ca40b05100d101300c0c3d51241d0300b024050754500005d40c25100080d1f1248031019880480f20008030b00c085c6004c1d0280001d0004000a80c025403078a04903039107a000e544030003070100d41034001034104070041c89816010794140c000058126541c81c20300e41805141c20040c40034540c441c561850000e040c41c0c406000c5d0780324040b00c01004040d030381c0751001002000844116150080c0109 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 39935562 1250 39934312 39934319
    0x7080405010b27060a05130f020d0603030203120f06010c02060901110109050d090e01030c0b0a090b040605030103150912050306010c150b030c0907050313020a05090a06061e02070b0d06 81
    0x10250140b4072040301c0f40445044020000a0034150440200064410100131504000c40c1d1036910100201c0203140a0000d201c50b83d001d00d98000340501404e06c580b040c5066800310400d81c0010042c002c00d085001c200c2250b50354514070061081085031094005503100d0143c000500b061000381540000506144900e100202c4944d400c40d45004001d0320640c1c046038202140f03a800c40d031000b01800c141d4140c2200da6040d901c0e1813641ca07000380303c0c0c0e41e0002800960401c00c1881000c0f070002800c1220a80c0ba0b0312903a618006046400c00c0c0401e90f43b000381044221240c40d040c0c0700707480b402d6521601402e40780200d00d009452641000307000034140010215040001149107414220180e010303400040d00c1500802030514104d06205500d0240000c1c00611214035009000d4940c40402d400c15004418030500c041510300e0000d07400700382c01184507401d11105541a0f001a001ea98160355000342c2845400c0004038074520108507180541c100704018003100c030401c402002820200400413841965 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 39936812 1250 39935562 39935569
    0x608010203150901090c0e060d060e010306140109090f170f040e040b0903091807050706020a020d030b150702130902100914030312070509030a081605010b03030c0607080405010b 78
    0x200c91003001100344441c20340b414940724024a0240c00100e100308802600e800014114a42070200288107070b81c089040281040c454001d800500341d4102907a565583d6450081d0180844085290880500d40c0020803440c0c0c072031003500300140c6c104000320403410386600c0e0783c07414032030441c28812802020049003040c4400407000300014001c01e10201080d183c282010008808080c006071441d400800903c0d40c1a61910705001c8491080c03241e900850b294600c3c02d640764400c41074010817031030000c20751915407500031a110300e4002c0140c40074400368101c0d908004001503001031201e144a001c0c4510809030415601c52000d5034901e403000512242c4580009100c0c00007500440300042c031219050010210a052086000b48250001c5d030401c8041d507641e00c07422100801d03070400c002d03002c18244a596410050005100c1d00311140665030b03032080040c400b1070001001c1c29141e5608119140b681810000101c840d5502c42c6800740046032a1070504659a10016101313613225900c4074407410b030554 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 39938062 1250 39936812 39936817
    0xd050c060c0304030311030a391109070e01080c130b0c030903070f12060f0b0a03060b011803081204021807020d170402030c040f0e0703150e280606080102 68
    0x80c001c20040d920b4524525000f412030201d150340ca6000e030401d2140c04440d90b000120181c124546000343c41b942c0c544a1f0342c21210f0f2007041240401d9100030800c02003400f4081c051003070003000903101d1081d10340d0f8210082d100c0b01c94902049000030481c80001c1d498065240142c02e003900e042c801740c10100e9440c140240e054000b06d14094264000003a0030700d09148c200700840c01440d0b40105162514640261059803c0c80c24002620560b1614a02008034425a0120300c5202c8010845001913450707007001c42c024600c0200c900d0200d1190100c0910081484a10030100c13075103c4031030f5140c550301504e080f0700c0300b001601c101c0e048600c0a4007001011200714600d0300c80c0f0101d44c003c0c2003404034450010f00b0f83d4040c2403001031a9291509000140c3c41c0230030100304d0711000b0b49010402c01c2c1100c400304020704003404442018040c1520100c104801c1c8046003105074510002030245001c2440b41c2911040c04005089120007052140c60503440144204030b002405060b00183d400d0f44d0300d10b00790036039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 39939312 1250 39938062 39938077
    0xf070509120304180501120c0e0411191809050a06091406070f140a021903050d0f0e0c031c0c05120a02010506120115050d08090d0308091902010e0d050c06 68
    0x207600741e54550085246910070301b401400004081c4040e000c0c40d403659028072240e80100c040400c00b01340003900344080c080c0c0310710410b04083e0070b9840301d0411035808681d2440078000c0700d40318107050300c2d1902c0c1610315010700703040c06c0e0700800074100b03411131661510020154260121208801000c00b0000034005125642c0300350040d840b821803040e44044001c0031000c508540c20b1000e0424007070303124401d50005130b1051000c00302d02c458610700da45003410b580301d00500403c2e203007007801c0040300160741155070000c0500140b06000c84015181180070551160703600b111068021754003205500b10240b19050703040c1180c1c040d0040c1c039440c8000601507015644280b03200c0000d80e464105201c110306142619035040d030740020003004001c07610300c81c0b41003984551040702e22540c4c4100c040024016400f04442001c40f00400041e9000454503000c0c004060856141865014603410350041040082c007050507194140d5072000c1c01200c440402050200450b02603483c0d04c80d03098910402e1b26800d0091552 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 39940562 1250 39939312 39939329
    0xc0303010603061505041e03080c0a05060109020301030f031b0b0a0501030218100501030b130203010807061403010501020606040908070516150e030601050409170a0c060506090f070509120304 84
    0xa940c141140902036070711940c0061800c1c0300ea02d16940c1101d178031030b00307071004e0310300b4103c4a440c42400c520682d01c000440b604080d095210000754010101b01c0014140b107460300c180e0982e51280c0c0c0c0c603441ca6040f400244800b0309104e81d0384400000081c8260000c000348000e1045010341c042294950344040c44e4200e8598180c0c65880005105600e05455400007103040b028000000c1e20b4034402045200350301c0c0c82200d06140c0c0310008041655124100100d4825a0701400c5441e0342e5910b51503a41c41c40c251040601003840007090040e1907d14000726416108180c00400c542d0b100d01c0244402032014803810360341504140700c0400019020310200307004004801d05030781c2441c184003c0c42c46c01e20425028000f8450381c2600c125a585002c6011070454400b160000307400d0312241007030000514040c040c1a001200080c003410220f81140403200780c03e0181e81c041000d40c2c1c500c01444205803003a07440c41501022175000070100e520620050125003000b8104003100c0b8401c4015501d942c0194228091 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 39941812 1250 39940562 39940567
    0x120c10090809040b1c02011b0204020c0c0f0109120b0604060b0307020114150109031e08030906011a040b0d0504170a080a0e0105010b1c0b120109030314070e04050a0b060c03 76
    0x1035629160050030490f06017210010441560ba207007008520b00c5280c0001c1c180001403480c0c45020714110003d10195401030000c4d503403804100d4803551900c0c070038440a0b100d4980e0b0940d500302540708458038000d450541d24148846425606e0b00059548024079040d070040d12084003080c1004401c0c0a903000d01c00d2034001041044e410030003404c05400083c81c40d101031412041828160307031b015001364102d03900a0410204000c20440f10a007507481060040d00400001040c8510300c480002d186040b501150025044240c1002212409100c0da10410403070341c05c140841d40c4400210b522403500305114100914800101c280003e50940140301c000001c200003004200282004d0700031070543c0741540d402001b00c0d40c10b060b07003007406005250002802c0c0c000941807840144c01c0c2d5100a0051100500ba0315041c1030702c803e001e0203414050000c07000a410702404c144100445240c05005501c1c40c1ca610410f2294841800002d080c000d00b901c107042e4460640980d40e03111440100000b0403000060765 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 39943062 1250 39941812 39941827
    0x1031e2001080105040519180203030a08040309060f080f070c02030d1706120d12061a03061e09071215032a1202060702030c0a0b040603060501050c120c100908 70
    0x1000503405134026070041e414401000101682407410f00019101050001428500d6507402100c03203141c004c0094040c440003941c81d000c9a007004070035225901c40d944800040ea1103030710072101840300107002000718848a000c9554003044680709a4041500c0c0f8081980d0811500000c0c944400090312502040c55022041c060401c2104003e50081d001c0e10070300544004040080d036100000c41e4090200711341506841d840003901c0d04400f00400014800d003001425802111a40d58402d0b41c42d248a074008561030311040090448450300c5100040804c400355962400c2074984144264010707081030390f580d400a1440d405030616401860181d40c8441240b01500804614940801d1160258059002c020406c50500d044070118255050b9002502c9054901c0800e1401c607000ca034203540003000800101e01016084040c0044038882d81d818800f41e6529001510a445400d41150351500400000e50b01541c0100007082c112460034204c85034a24402040822144039600449180300c0004200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 39944312 1250 39943062 39943067
    0xb06040b0109120b0709080601060f03140708010b0a0c3221070213180201030605040c0203040314070503100903030b0604121202120c1e0c030601031e2001 68
    0x40c0e184510a0800110460401460000202c82c0e41e40c010400c8038400300007081e5030300c9000020000d182e510111081540c40c0c4001400030700b900c82c00d0350300081c03500c01c600d402080e080c81d18500510844c1c49a030308507424061403144a510141503001482400c40f1072800180e98400580841801d004145407801d650050078072036401d00249030b4030705074080303040a88007000c2c03401c2c400e8601d40580401640c0d00101e102041010030010100d1801d280b9010720106041c941001220100740300366030400c180c03a15181040100c41104440b2801644140002d00024070194a04082c6403810380c03c9070760040d0b80c2c0c0002441d210740704059004054861120804040e0140500c45a40c4070494003182070504005d054030206440c0c03500900340002080d41402c41600900c01c001040d040b5446107565901005169030343d81100e0300c1d4000540c500c03201428503520300400e4040e5101401070280c2000d0346103031185200c2111045000582400401803903000521294440c412025040001041100b940c03001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 39945562 1250 39944312 39944321
    0x30a0c051002041503180611180301020307020307020904020414040f1b0e06060a0c05060a0605130501050607020603100509010e0103050d1d010c031704060203060901061107031101020a0b040b0604 86
    0x41c0029005120030300154460b040d20340c0ea12001031400007614001503400126103c81c0c1e90014100500c0d1202c0004840c24a0008200d0300240d14541c0301030844d5501890700702c1c401210b40e1401a0000d1116000525001401a40140c001400807403841204040c5c1140110152000c48407803041c15003010401c240031440b011404090386000661710b00d8013400c07a294040050010b8420f503000164108124080c401b9034901d150403904071100c40c07414104620050003a802071520680c408070f141d20340c5c0e05442c0241816950003070001400c12000d603007484070680000d005403491020202c0f0102d4a920f0b100d421500030f0082d00320802295140d420400d08010072501c0d09010000c0401c450550554040ba0030b10076201e0030700c0e103003040b4101c60804482001188009400882c00002800309110300c0303402440c0101c90403516640141d982d407009445018001c0400744182c0c004400410100c1c241c150030100c030305018015980300c81394585c0c50304035200044a044038129044028416142024400c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 39946812 1250 39945562 39945583
    0xa08010323060411030a0611041d130303090507080a0303140702150402060f0906030a14100f050d15020712030e0307030212030603010b030d02010b031209060306010f0e03030a0c05 79
    0xc00c0741502400400558607040d00910107402a00c1c0841c1c0c4101e0b5440400c82c4210258102c0c0d81000078500b058031550303855001e40b10b003412009512501018500001900600855005074182c032425103941c0c040e009807100321000c2e035040c0100600060f400a05110032560b82d03100ea9030008600c03203618003061018401070854001c56000c8a0000303800380d000702200c3e0300140c04860441e1503002e000c901a0440c8501500a0381160011040c4904403140e90400701e450b1990034001403040e500c1c0e900590f0040d02600c40e40740c01150010f01049107007032a1101e60041805001d1322201b9541c5c00070b07040c0c180c1c1d100d0704080343c41a0344000c2d203d0403f5814460480e003102c40700041c602d80082600e00070750321030781c6110485c060348000011803610b0350f09600503511000301600b030718021005100701034000e0004015550180c02000880c0300600700f00d000f1100d50305801000507040d5102e50004581843d08031440d42c1c180729010415a1307082d54104007521081c190380e6512121880e86140c80307824401180c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 39948062 1250 39946812 39946853
    0x190f02070302030a18080717010516020a120306051e0a05011d0909150f150a030f0f020102070b030903130905070203031b091f02012307120902060a080103 68
    0x3000364002603022044641c00d8240e450840782c0301d41610028130b12400b096000210a101c2c01d400040e01000b41c00c9800c0d450100720000708055a551002c1d612400c0109601d00011b0b044103584c600003480c404024241c8a10324500080e0441d2500301003a508000c4509803022880124600112032501c101008098203080ca4000d1a0300071000403158903c03a134451040c030030f08241000440320705081012a10044162480c900c01c7d00b8107000310403480c0802d0f9031b1100c0d049541e442002d228100078060380201c03a804030748a15005ca030381d114105032009110049046004458000071405034120140d402481594051680c2d414400003083d4454420350101d4080da08040810892700d4010042da5400340c1141d28491065a1030036400206104080441381e00c000a080724a4489640e41c0e00d105044085800070001c0700c404844001c903142c2600b00e0310160680c0c0d10700103a14540b00b1100755078071230070004000c10178241780d500040d040c2d045038512000080e54400108123000f02004594030041040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 39949312 1250 39948062 39948067
    0x20403060f0605100e0d05030a0f080108070308030a020c03091002010209030d0206040c0b090a0b0a03020301031101020c091501090f0b0304030207230105030c0c01090308040c051207170c0306190f02 87
    0x4010652030b026541340d100501c240c200116086071210300c00140529480030039299203540c0c80030050201d045081c2c084001170142000800d1702180040c1d480c081e660801003190566540c15200700c084c0d44802c45c10201404148001c0100343ca42450602c4132246c181c002603118101e81c024585045501d05031402154004400d00003c40c0c10884c040c000c0c2c030b04003c802a541d00c0d074074003c11f5070002c0c02d030301c02c00841d980040c03455005035040e8044d605aa02c41e0711190400040c1c00012030782c91880820351b80c1d018900344046403017001c0085074440d000d034048c10314141441c0e0300d10044014001c1641704d012151400010442015414040314025108200040c4248005041d441d41302d210420b007200d05009000000c90304008004081d92a41e05070032009000540007032500421180c0181c2d0304440c40c000c40354000c5103500e092135280c5041103194008103601032900050030900840340c140d8240d20702955826070482e4a090100511031400e42c0b40c0602141d082050490803505240705c00190f1500c103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 39950562 1250 39949312 39949319
    0xf060e060409080906070803060a05010c0b151f11010501060203030c070308060613030f02031b03030904242d0501050d09060f18021206070c0b0405030c03040603020403060f06 77
    0x2142080d8000038259800140d5514a25040185200b03040b001e40d031041020406504112440d002144202030580318401140d0340d0320010755400c0403100c40180708000f00e5000440541e180d150305251070000a20460309030034070004110400c03084600041c0041d10100c21680e002a09000700c900501c428402036207545030072040d6907024081c1c203400504010038a00401d2103580c606003a1143c0300808500c42e0151507487c6001011046141001ca010b802003111034159200303d89014a05010040e01a519003007556041100900040c40010b02c0111403982100e0001b05500c1d00c080a401d04180d80484181500d00401c20740c0d20b40030030300c0780a0111001c144500e9a010003a0350f0810031609003c20604c02a15001d0080d102da0b0550058403071600012181540c11b00c01560130907402034580000000c4413001d5944c658000b101c0380700c00314440522040000307607a649045c5d441801082a02d0030582062101401c5a00071b911100000c0e4011074144103001c400d1246107441198400c040104030714 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 39951812 1250 39950562 39950579
    0xb0d05010e06220e030d0605131512031202031e010b070317060d05010c0e1e09130510150e070c051507030b040207120905060c0303010b28080a0f06 65
    0x4600000344a030300d036800041c07103403102c250801d002c4910390303201740c03a101c290561120004040d24840c451095168030300c1d080c80003410707110b005600a4081e07414003016041030b2080d4145444500b04400304940031180c0454078100f4405940500100054002d00c044105080ca58125041e040403080010401c0400c00298000c1180401010303000440c0d02541e5504c000260750740f403d250090815424a8440500c080c7d1240c00e614030618221001c6020100d00440112080c0c2c40350300349504860064003007021001050104420b4a101d9011250302c075800718010760565180072084002c002605030140480340100000550220403460a41802a0b80341c035a10f9483c81e4942c80711001044200206030010f11039080034130340c0503003d80b095680b2003152520003200420340c41c030003000030f003544c500bc0303560b141c2002220580f00100c4011400c5908000350000703130380e02c82c40c001c15110000c1040441c001540c01c10000801480381c030743c5000c616180710034000f65100031000e042e80c00e181a906028444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 39953062 1250 39951812 39951829
    0x4030b090706020c0904061b12061211130605060c0303060109061103071209090e060609070c050706080a020403020a090515040c09030b0901020c01020301121a060d02040b0315010b0d05010e06 84
    0x81c0803a03008038180c845081100023812a102e050100760200451a84450b4109542070441c5803803000810450740d64030309103005031062250087c0b11011040c078640304c03031400c0c81000c0756540d0b40c030000149040c0e40380c001440c1d99002c00c44103000c036000482000460341c0c1056810b80145070600304841da881d100c0c001f4a03124840d0303900c0200405003606a07080b4061141c0c0701c11000c0c02c10410f040000008940e541640c540044410b03d2003925540700184107140706005048549602500404825050420a95610034000c0202c4507069081c800040981c0e0f0729485000200100840011141070000003210760071400d08040d402141085050700c00740da407043c1c120017100d40100420700c10b9101c0120190183c4a0042c6210440d0b00100002c140c40c1d04012041c80094450f010320b0f0305003d015074008280510450302c082c1d11100200b81400075080039005030244030801000c0d52038446650b66406030105c1c081c1c0254624200100d2800c582d010117110f42800b5000704c029240c400e00d04140000d0180 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 39954312 1250 39953062 39953083
    0x10b03060904080714030a03020c070b0f0703140f0d020403030f09030803070507060207020d1101120507050313050102070b010305010c090801020f03130212071202041a0307030314160804030b09070602 88
    0x860000d21101805030700445e4003102e03c1040250382e80ca4411040041c080d4100d080d0f2001140500719001560b0350703451040b80c058201c03091240d41030403103e031010344103840d4448104500b410104200218054030b01c0050040e02041c003401a110350550600802040c1071080b10301c18014001828004104541c3c1920381c458030303074513069075240c207640b400c000079008184000707400000c41d8640c20104000b5920300030b00d4403001c4c0c1e510050542900b07110800d440090b03c1484c0410f40420116401a44628020140900800c005485c1090950701d0f082c89a070240e10582e00e9940d942da100d403091b0341c0701c1c00c4c413402010603400a600b44418800001c00520019101d50030171500b0303800c0d12045488040583c1c1c0036509800685051a544071343c402018560000100d100f40c0c82c051003041c108251844003240c050000c0d0007043c0c02c0b400d40d50203880c03621f40000c140b11101c1091003000102d000200200020610901c0e144d03072198a10300c0c007002c1e03150303019080003900c3c0c00c003001c240b2201e41c1c00107030b81090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 39955562 1250 39954312 39954323
    0xb180c0307031401060b030405070509130b0609060a0e0405060f01090605060f1b0d080a15032004020408011a031005070f03150905010b03060901050901080a080c0106081f05010b03060904 82
    0x1020300c3c40d02d0941c01000580d0103071000354404000c0000788640841c041c400c4890558028050799105809010702c481c00040080c440e9050303101090342ca0400401041e0b000f50301174a218055600c54000000d40882101c0841d181e034022000c01551503840c0c90002d0040000101c10300c01c003030a2800060b443d000c0d4444504291002103040e07101080101c00c4016090700500507190030301040c0134001c0034000c0840d4040a40da0520544a100b010251141011250040c010402651b1140d4401c42c1011150100580c1b064080c000460811003e1041c0900d80b101d4520b1803012440c100d01f41810000000107200100b454441000543c5400203901100742c1024070303000030343c8030300c0c1841c81275840e01542107120410f00e00030010440b20003400007103004941c1107a03122400d0303a84004024544074240142c4070f00f508002001c80004071741002804a54440b01e00110f400c0f0b494042d124078211207600c240360401c480c110074011500381846254050100c01001ea03140d8640b5002050041c0fa015000030030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 39956812 1250 39955562 39955583
    0x7060c1d03070b0309330f0118020304050a0804060f180f0b0307030207060c0924050405220911010f030e0c0d060207170309010b060c0c01050a020a050a0b180c030703 73
    0xd6102441642c1b21400f1514101c42c100803980d140c55028080c5000350f1501080200220b2a5011440601030480d03c029000c84c1ca0803011045000107508050011180c9109481320030000403180c0c0041c001134842c56070341070002000001c0013000d00f04104010b00c0103010245050201f61251500b00042d2109408e82c10790329111100700b10000c5c8600c1c1405048985081d1740801c85580c400485411100040c600d0889074003000b159102000c9000e204202281041004105904001c0607503c114500314040d541c0004180e02d6441c00e40d003180d041103c0340d40c0550708244003980c001161240d00140d5140c00c20034842c5000038240d8440207804028030400d0700903001010450355030101d580095018060756011b01c2513512404240d00107030360301ca00d55424241d4100081c18460280c5902001840090210b151200b0040d1840c2d482800c803d021400340a0516011400030481010241d01c2800401020b2429a1800c080a001c0d200540c2d40b580003001da02006517400a1468244d070f401100118 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 39958062 1250 39956812 39956821
    0xb070503090f0a09050a02090405070f0801060315030506161103070c14150a02010509210d0209040912050901021005070c060e0c030f010f0e061e040f0807060c1d03070b03 75
    0x11441e43e002e030320481c401401c00c8104210f000710f0b60094207a2143c16141880f80d80c4981001340e6500b00444661000142810b0041140c603200e5013003840c1c02c801c0b600000074044d45a80b942400e00d50102c6605180300c8882a071a01016407080c44c45071417142150203141408504c0da03c1322442c040394403030154551802c2110f5001c5641c0c1760b0312201046020310840d03558400000b00a80038200440d1144081e0059444e424801d80c00d001c0c0300b0481d0400034925526200134400010001d4110721440c0e90000ea4920f000c0d03002940c104500c415805041e2201600c0701842e4000a113040100c80c0c0c0e03c620b450401050100d038030303044002e0885880d070290001c84d54000308054280750001144405515104030800181741c80c4040d4400c01000d00e0028050151140d0121301965424060703c1012449015185004c41d0201c0b81e00400d41040c8070340d01c034801d0550b40d40c450040301d412220003621220344c1d61002d0060645c0010750b00d00044905035041c0c0141131000c00003512003046100e680c81c11040000000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 39959312 1250 39958062 39958069
    0x30304030303020904270201092709050106090903080f0105041e0b1f0e011d01080705070f02060f03060f03060405100902010e0310020703020d02010b0310020d0209150d060b070503090f 81
    0x24180c90f56940301100c188821b02e1002c030f201d00c80750300281d005c1101c1c0d10000c20201e10003124543c01311040e94050076003c0c415590000109085002074070f05541c0c8480214007041e481c0142c820a038000e0390740b40000d0800d00b680d02046201a4021880b40f440c043d040c401018103020507490803141d0000c0022910b41c00c1000c6034000500810b504002080071581c6507031036400c0184080c00c100c080c1e0b2035802e11007600710884238042040c046240411800c600045800b84070301c0091070322a204840300303050952181d0100e9100c1c0c0080a540450520100402c8158100318801003ca004120f008003080e0429845140d00d980310340c1074070147c140d01c0d4030f411415a4040d1103000340000d4054112440800c07480880b800941014504a0060280d039071050075082c41401015801d21004014007624101040300030000d40c0320209003050b241d028841401a99a01e0034100403643c00303035a801e0365611107450300504032401034001c2004804144140c0b00400d4000040d1060003030155102d100c403402100c0007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 39960562 1250 39959312 39959321
    0x103020906070c0b0301080c0103180b04080408030301060201061502030304021003050c120108061503060f060108180a0302010906061508062b030c020f010f0c0303200c03040503071202030304030303020904 90
    0x2e400260a4140001d401d03131107070001d60490300d07520705440035146a0f00045094031019124040c4400c580c00c21080466031a801c1d060304503201c0d0140d946855034404c05541503810903401080540d5460780208404003411007071149242c1103101851540c40d040e400500728241d00d171800c030f080669400004903c00350f590100c40f08440440c1c2d200440d90303500d50300340d550f0307010455882d48500500d000355042800e0020340d140c024040c12228000554943c2d00440c1c90740001007000c6c15000b440800d441d000d80e81484002c2c1c0d0707a40a9400415070907401c1c04c25100707407500ca80c0940301c820858120907032025030220380d007608408101e0b4542c203032100c2c0304003100800d221030307503906d800048007403001080541000c1b0307440e9058400d480345100d1801d03820054035030f0101422002c0100320261800390000e442a400444062040c06580c20780d2003c110b03280080380c1001340a44155440060240001e20781000068000c0030181d011801c0e035940340c2c1c04603440b40980d110007014541c011071280c560307070343d035811 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 39961812 1250 39960562 39960577
    0x110d031517100b0a050607060b010203040f0b070209150102070303110703020a12060b060a08130f0b090a030305011403070e07050403080d090b090114070f02070f060e0a0909030e0103020906 83
    0x100301e440c52144221685a4a4100b00c144042d403408860020a003800d61504003103e000501c0c2c2400c091aa80301c1070064411800d01ca411400104004038482c03220800d40005030000c09411034407a000c500c144040c01d80b0150400030602c50068440066a0b4005016800d5951518088489040800700c12f40341c501150130095011040c41008242e0048034610300d24158081c0c05d09005500c0050248480d030f11660240500144024000903a55450041002202442000e403842003420945a44000010554402065800c02250fa13800d1550500815014011100c4c11304845070342e00000955512045c03042c0707400c2d00c03901c03400251200e0091041c2c8000f103070404140c41d91130b00c0f2034022030002c01400c101220010012030100ba4201c005104030b22030300100d181d90200f240c5940500359818074292a42908606c14484d001c071b00300c00c4500b034400080c001078403441404902c032070402a00d090b042e0413103981c0c1b03894210100003281d0b22026121084d070080c2001642d03207a910000c41d003a80728990 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 39963062 1250 39961812 39961829
    0x501080c1203072118050a0501112b17010503060a09030203120a0212010b07030801050415050d0804080f0d020d230a0807080a06050f040f091e0210110d0315 69
    0x81c288030a95125030313007404806445039603103002c9050610791062034443d00e00800b50401d001030030a00141d40201c9203019201c0c4d070308040344c0c001100300d250b820711181c601d0036032104e03203808040f41ca6005400032040700f010003a282d21443e5640c10600407030340c0e4801c0148036165651705e0302501d0701814020300441d01d1a203198007542c01246050742d1500003942c0b00e07110a0b09404043c10001541d12142410baa00065056844c51b00a0b4a04800c10010382190441400000c200103c006965a1541401c240b0148540341c0300f6212803410403d281031001200704064290005541c45c0d01d41a80815001c94240320740c100400451b9203402c800c48818a001c2024030b0298000580c0c9882582150800344910801d5035404000d42e101d003006415070740d1600c1401d03040b98801525030480c1c0742a4200c0c41411500c4540000d4990983e224556608840307901c2c403c0203024030031a0019420305032002d90000125040c0142c86a2000304110360300d0310680c9065040666076031a40120030710074240303000201003e8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 39964312 1250 39963062 39963083
    0xa0b0c1b060714070e07050306100e040b040f091703010602030a0c061407030218030d02070303030b030a0606030803012c06040506030c04110a090504061508070504080106031101030c030501080c120307 88
    0x1001c840e5941e80c140c050420703917101c00800500e50707900c9442201d20501c00608040b110a403428416524800500c0d100c5510030b440c0c3c0141000d5440303030710580c01c000280183c04103410603981440c5294041c100b0805841c481e04000500086400000b180c040810702c0c540b007900c000b0242071520040554850100e80701c3d1609091140140e815005440c0c1c0810181c07c5905941d0002c00b0155240060327211a4096003090701d04001007806a0701480124030b014059403e0a840341c1d0390b54046901a8004076510380d804401071000c11107203021541041c0c003180b844100040ca00b41c2c08400000001c0034640f145489000180003a1000d2201c0300384140007520522251140c2403500059800c00180c2c48000b884400e000984c070301d06030241c81d0494004074590070f0b20407031202c8103c4000c0741c01044201400742c1000001800c480910441004500416640040045113000181580c1e44909202c007050300f04001481809404100d6a181c0360b4200c41c000c003d4540e003042281035014030080034010700f101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 39965562 1250 39964312 39964343
    0x20909040b04080d0f2301031e06020409020703020d0206070503010303050306090606090312040911030c0a0f180f0e060609090a050702010e0334051b13020a02010b0a0b0c1b0607 78
    0x51b801100024000c09819044220754211810b0210000d01c0050b1011000e8071440c1d125800d00814101803a0044002500e043d841e079245030103990004404400581c00020342c103e038a58103200709500400c0e10b203085455545541c80007056800041d001071720803001200455078a0386c82e8030031138002e840c0c003030291016400c0c2c007100d159041d0080d1051044250a00c1001d0450b0b02c407010440f44140040c8421505008000300b08441c450f015282400601ca01440c0c03001e900d012945c840703002040203201c1a40907905100c0ea01210038030252040d401180240803070946039545141b055403013982c000000480c0e55807000100c0c0541004c07100540c2134000015a441c440103070301c1c144035607603922160b01a0720610302c1061195101c00c0800141068111320710416840421042c0c5000203e0010300074500c071406071102000301c0c1d01503204a80584c0d52224061120b060035103103030000300041403045080c0141850381b503444441e14001c40b0030311201d441d100d5446076604425203110503040b00c0401040e000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 39966812 1250 39965562 39965591
    0xa030309021005070b1503120c0a0c0b0c0a060b030102040b13030b0f0712051509010602010b09011505070605040c03050703051e010207032f0f0d0e04020909040b04080d 74
    0x1000c10007030b4010b00c204507032002d1003400764085909203580100101c034107588410281c803041142c880411b030b140c01400d180310f0224501002600c0c108119802070042030b500d52403d8030300342c42942c2c0080c0c0d500740c0c2400702e890300d0000469503410345500300c80701180303040360140060300905c615001860321600100d038207101c0600150185040e01e1191301000e200c0e031565910f41000030341c216040b00004420200030310b04078819130070031070b0408840e4800c01078941d0300000040f44136509800000040c0c4d5180c062405501d80040031900405200a405100e031206010040151051003c054005519040820108001040402c00131500003003568240794072490541e0b200c3c42c2d507808003c02d043c9038940380d013400001031080302c5d050340d490385490140f8060040d034100404050341c8201d81c0b0600c170300e40704500107009015010311140c4500c094a2481101080030f001e014200402d076000f0717032040c0052074107910740c014802d400581100e010301d83d07030303503030b407401d64031900c110000c2c406000d061800c1c10a1050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 39968062 1250 39966812 39966821
    0x902040909020405100509041203022109010b101e0207030203030a0e0102150c040311030c180115080103170c030c070e0402010311030712020a090f080c030d0f0206070e010e030a0303 80
    0x5200f1034040c041602c4468021004038a81d004090340400c80c60003140000c2c0002941c640052003605016043c41441601816202d08a90300510361604032ba08002c008002842040440d15040360000302020b03c80030300a04840e440600f4001e42c0000352900304189000b0044140110350040440303983c0c44c4031900007002c140c800c110f158058802d02e40c0f44002454004c200621039542011f19a041c02d2458445014500c0c041d600140c150294008140054851608640c22501c12004001c1d0951506180e0744030765184040c4c00081100c50001400002d0381d0410b0302c4800581204465140c080c030a05090035403041001c0d240745846100d1000400b109270912845c4624000d8900304855440b4861448183c070084448000041201c03820015280c0c3d035901410b11644c442c546620b01d9622045030084541e065005a1181c4d03100307803c801070500d4100485100703c40c691402001865040001070b55940026111800b40064004000c7d1107900c111500360961900404548011083d82001340040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 39969312 1250 39968062 39968081
    0x60c031f03200a03031b08070b040c0302130e03030f070219030206010806010603020405030d1202040506040e06040509070602190204020d05070c1401020a051b030408150901060e010b120a0609020409 87
    0x100341c000a4008510f0200c1d50030040744d8041e141c610740c0b02d40b40010a584281122000c0300c40c01c030180b1050000c035038961807040c4540d00ca010a0b9541c2425801007104550201c02ca005d155401c207242e803204280080152600102180e03590480340d00c48a071b040e810000d44008441ca03401e481c001034000d15070f0000d0502c0c100d801003c01d9900a2340c96007011016071040d8011150144e01c40a480d110580c801c0712141103903459208014100f82d181c00000340540c1c460360041d04100071150500c04c907460144240c0e074004d580706000301512450200081d40301c12480060705880c03268441c00c001076454680459148002003c0200005e1504180190900300c0282040d15412030791a08003403c44414422903010582903103919003003800c020007000441400350442d0b030050009003c0000c024200b0048041c41c0b5825182507861860403840701e90840d000f96000381410221000100090600d02c01180e0000488410240d0703c1d980e03500d00343c0080c2645500a007440c2d40b00080000d0600745507071150036007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 39970562 1250 39969312 39969353
    0x40f062906040b0a0e0102101a040b040b03060106050d09020409030906081308040b130306050c030105120a210e090124080118020915131703030702060c031f03 70
    0x400d011080c40018040c501030f64108100401c41251540e003d0b01c2c1500030034105204946208110303101580586044480c110900c2c0f040c42d0140311a46024007401461080c103680c03c01c00d0800381c1000039590141845001c090080000c0e40c0034561125410810040313030007410a10401c01c140ca4010849421449160005800314010035100d94600502d0003800e904684032904090400340c200d80706600400384c0c650302c214503000c0000000d06501510344109160b00080e0f40702d40c034220520981640325804510305e5003000880e0350000d441d151240d0b80550044460744105441c1410079610052000401544210090000514140540d185891110b00380b600710056a8442c501520041000e00500d01c10302c40481c0078441c04540c41d400b802d06144001e24240741c0c010f601481500603400141828901c0141d14070034841c4115030708400c020302d45008000c51075403411000080d15848040c002a8049000101180c50380c1011008400c1d0110700c1d1100105940d604d1a1002c1c070740141074900d001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 39971812 1250 39970562 39970631
    0x206070f050d14090a140f030618070f06020703080304140a0501060303030c0c0b04080a23040311010c020f190b0d020903010506030d0c0807211205010503010203011805040f06 77
    0x2e03050f58000650761501c2c009001108030b20304102035400c0005010b45001e4100076600c030740c00c1c0c0076034040100c14060002030b65a04045c0d0450300d0454203108254102500210311044104881a80062541c0882e500910701507180d44407494004080e40150300c0c2c4900350322480c1901010b04c007042d4462402c6030700c40e40b0104100030300701c01d080c1c0c1d8103244070101815500c0032400040100b281d031401400408024170340840000805100c0066025207503070300e0f00c440c0001003010b01c00c000e00c19030b400c40c11603400d0809810380c40c0c1d44e50024080ca00b04001e03080c040e0f8546405d03560180d11200404018002c0c1c514042c2d200e40540c0c0000c0c00a4101d108d5076882582010045200d6050100c0d903080401c00c1d5548200040784a80c54410141d8040003088500b00200b80b00d201c50030000907448a481030303270b5a84000b8510301443c1e40e1800d8601c1a00314074400d0344100010000600b0080603006030280c40c590201d0265190b040801640e200c049000e05905d0030a03a070040003505484402c41c0000c3e41c80d12200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 39973062 1250 39971812 39971837
    0x10305180a0305180d0f030e03010203040b06040902010c060204081b090405060c0304030e040606050c01050a0507020d0e06040509040b010515040602030f181206011712090d0206070f050d 82
    0x3600000182450310680c102041d1000070901c01c0b001000041041d482c8030304040c03080e40224403074001800055844460b600a924109a80124081c6032154120003d41c01d600f402d8840d40400c0301c3c0a0881e030f12495a40d1028000c690182c0d400c03461040c0c0010717007107440719601c40030300c0e80781c0c074060081c007069030036401140d04c0b82d20b041c0f540d0707601940c4c009c00141015070350b500892103282c0c000351094091110420344422507580d98044c20024080340e5460b59281c0113901c60701400e640000e4240b440c0750b0300341801c0010b400e9001401c091001502c0c540031108450410125410780b1568100039040140c4100700818804030740403850403650203941c1c1240c80814080b20005501a81c010302005030020041c6211405070351740540740401c401c2e06140030340d50b00c0100052406921051100c0b40740c10200042100d0b090f00482403410300d00e00d40140109401c814110401031051000d61441240c0c041c6040040d5150380e0103661010340d004107121081440d81c20160740d690204610319001442041c44203 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 39974312 1250 39973062 39973081
    0x51201020f04030b06060d0603050a06050c0a08040210181202010e0a030503040603050c1902010f0501050301090b0417040b030a1a01090302010c02040b040209030d030b040b010c0b070305060402090402040311010305 94
    0x310780900014212034105421907856211002e03024040a910a500b8041140e000b1018807e2400840c8100024a5001040c0c6400300c2540c0e0001c4c81b40c50303400320510001d010190040d110541c050b80c1210344480c2c40d407001c0c0c000c0e02c10a02e041c021030080205031002040070303100011581035060003601c8500096508004000300d10520f400000c0003904244003c11200c2e019401c0103812550400f078583c24076130049030120102c0c41500080c00182c1d120b0022000e0310709584141805031106800900514003151210000a400548000c01e0801542c15040c0c489650000b65001341c590101003680d2801d01c2a404005000c0d1200022a50400303241c0003002503009404050071a54181c495031710a001a800f0440104013500f10107420540030000e940c110380d0144290031102029860008400c00c411080c4421688426401c506010340000341c00e0200780040c0c15181e21064610b00400c40da511400490064010301c05600c2e005400401c0200811115030618840302d80d003030340d041110340d1302c0c40c069 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 39975562 1250 39974312 39974317
    0x30e0f0604050f0f28020d12030f051608040c030b09030c07060203130b0703020109020a060306080105010e061807030902060f0d0e0c060a03020702030c150a1103031005040902030c03070f05120102 86
    0x62411584204000017003c00e00c071011200091078203d072001c5004a0b034000c507024a051003000c13039264400700721400302e054051044440034030b1882d038108554034024034944a0682d1000001062041d0400054100400c5001076005140d00030086201070070300d180c00715540e4100e40d0312001c0c603014207200420006d1000041d2124200000d0711032404509c0d1070b01510b4141d0041c0800e60442d500c2c4d00b8090056242c02c6500300c003c19013a980022040d03c3c000c0280c2c21164180c00c002d00c00b05800050203a159a82c1c50803032512001031003101016100d5400c258000e020b4000c0081d0011f6020400700402400d40020301380c43c41100c00c007849881094408261500c0c0a80d03850f6034801c0d41403000301910307407183c0c2c0505509880601280d1b181440c0d000010060a0f003a90320784000b0748002482c81c4040c2c0e22a114000385d490040085045003090803e010f04641c1600801c0c3c01140d549120405555041056241210707000c0d00395124242c80b00c01c1700c4481046400345a0007010440315103460800140308 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 39976812 1250 39975562 39975583
    0x90705131a0a030f023d0c0b180d030b0d0209060d06090302030a0e01110723191703040b09060a031107050705030c0303040501140f07020a0906150503150d03030e0f0604050f 76
    0x80c0e01d02c01d42c817019420406a4003186c00c1401c01c10407403203000c0026444071040703000700e400d251403504500d074003a0480c0c03a01580d001400100b50604240c00c030551903070565088181e90440c0c01031942d035125000700d145885c080c0700180805007049000d13410705401100a0480c03000070f03580d014008050b980199034002694050117150780c400031003042207821803010003c0d01c01c105c03ca81001020200c00007110680f0450035955021b5841c1c000b0002824076400646840d007201c406036080c5803408036141c8140c001e042a2601035180000c0420172703680700b0344c040400390a001c200c1c2520f0340d01c42d08007541c1d074000c2402024080e21031000c01d400c40c1c4c6000010760f03003121707016500c0040030001e04481c0401034000b42c0380c020104074244000c60061f0355961700107018180c0d03000c001800b10715113152584284030300c18094060101c00c0040c40001c1c0c2d441d5041c50103e00050b1082d00ca140000d01d0201e000f81000c00c10700d54070b8003441c0c0c8a4802c1440100c0d42d00d015a004108440d001001d218007251288148103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 39978062 1250 39976812 39976879
    0xc0702030a020d031224091103070c02010909060b031e01180209030708070815070503040210030b151603020c031606081f06080609090705131a0a030f02 67
    0x18075034010b1601c0c0380c003201658440d261004040d4a252105416100195444021011840600040719003028400c0c402040c8442040c0301000c0842c40d074812511018001800f040300caa070880c4150790040807550300802d0b90801c1008810f6495103a001035030025030f800e05121b20180100e046040c1c0100c030090603158411902c03496561401e000304001d5001e941c01d10303014080c0130b0f00080c3c55071040c84024010241c0001520346400300c61501c0c00449002040c44052040500c00d003c056100c00645002200d000d040000d0514501000039140301041d0903c400590000183d541010b0045031110780c0c1c01c0e209400301c03101408108105501da62464802c0c2c9401c2d190b0000c100482442088829006142d68020700c4d20485040544105d00352541c10003001f05d040141400524104241e046900c6440700c400b402c0c20b10305000002300c88407044841140038645031400c009105560f1408081c1d164030052010998680d0707841c4c0800c007030584900c20b9211703004880f01e03103032902d410305000100c284440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 39979312 1250 39978062 39978073
    0x302030901030902030111030f090d02012705100c0315060309021f12150f0b03060d03030213120f0b01170303010320090a06050306010504090302190201030b0a030f020103050c070203 80
    0x90300440c014402c9110680e4107649a0340c0e4281c25100318002580900c60301820b181161812550301031401682030240421685891524024080b80c0300c40e10040414500d0750a001c2605814103915007115142561007082c5413411012501e5056031203c400708419980802c8115654401541260170b04103000c0e4006172410385000b0511079039860840c0c4c0c8242070070002800c1d51003900384021102d500d03032112041031100c10140072441f074203034803080103001001d0348501d186044804181d4522114400a0074150081071703c06a003401011542c0141c9031490341503020490b1401c121005040c003203401e542100f4400004604100285070214640c0041c000540c1346904c0e595829000d80841758020301400100f003442ca180b9a01c100005003d080301e200d011441c1c81c00c02c000c0500b0600b060b88010300c12403401071500002034020880c050782d040a0000c41a10307459500042c3d000e00b0b09000c0c51a401740ca524004420841e00b6001040c40900030b0303908028a60781c3c031445102c03500c201c500c06075043d8841c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 39980562 1250 39979312 39979327
    0xd0c1707020f192a051503130b07032004091b050a05030702070306020705010e0c010e03210409060602060916030803060603040c03170715020301150804060905030f0307031503030203 80
    0x940e8400f0300300d91180d14402003403140d44945800c0540b540d62000c00300c00004400f000301d4688610180c07000c681c506d8100d03296003400c0e0120007817019000e10080984054400064400e40a0703442000200341c04400d031001081c481d12040190741c4640103000e511840c1020ba5032252003144091010b4405684440345001aa400700b900c26420051524045100320000400000e0150000e40485881840041445062034a4260a0a00c981c4040d4100522500e004483d5034000031490048407100040070214181040c80000e14403445d0880101141481d0000911640c0050001e1007007800d21b00359090000b0880000c0d072042841e01c00a0078429040c004992035291600007180c0182c85450713038900995403581c854018034242c441c0705e0310040001c070701c100038480c0284250b4001000701e1021407031581001d8a1601c164048240c1c1010002e02d034001408021140d400354894681060880b80c031039020302e12030007060744122403a03800241030007420340509030842207010549030705070045d604180d030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 39981812 1250 39980562 39980593
    0x50d050304150906090201020c01020a15020a0302070615030203071a03010b0f0706060602010c140c0303070807020a060609091103160504051302120318030307080708030a020d0c1707020f 82
    0x80c0003980c1819038540d12500c202118826a10f003e0f11880e404200c0920354000607061000c04d180080c103540050802c070001544c800340000921482e46001a00c1d00d0651104400a0003542d40050040b4074102c01070301c504482c2008007041324400ca044403d0f050700d448403a0008400505200351190041c00144046403040019041501800b81d00c0c0707042c0465a291801030751420f87c00180580d45d900c8001400c103070300c410400b0404010300c410600d003510300c00d0119900e220040caa00204802074000c1200e02c1c0c82405481800c5400440500c01c898858824000400036100c00b222604041e00b4030f03207034a003004240100c500f1031700b40e03801280916010a0002412004040e05d008001e8401c900006035120051244051a68001944c403034401c02503007e80582d2921a01d403081d0310038800240054000b00446403480c0d404010395440ba129034150b0710103030288401c940121824025121290396000b5170411102d24420304040c0c10343c80c1d401083e41c072901c51030410807042c1c102034911001c080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 39983062 1250 39981812 39981817
    0x30a170429010f050a0f03150908030109050907050f060706200c0709050907030f08090105040909050d0806060306361801061508071101090503180103060f03050d05 72
    0x902440d440a1122000304045440340300c0301c0103480c1540a000014008a50a0001e45029040c02c3c2e40c028945030800500c00c841e900179100c02032440500419104411480d07030096501e01b82d0100002e40c0300d50b140c2d070091024041c2103844025030f00c0785050000f001c1ca071051003454041e070050070452a080c0319407145400303000c9103100301c02030001c50001000c0c400e4400b0010300d5080100005800120f060103401c00035544090450301590b4040e15041c400310380c242c22051005640700c041c1c3e903a96203481d03006850b1400b40ea072050080358a82031405042c84004508070b06c040c203256407210115903903c01000700d13500080c0e50880e04035109407581c44441c51f201d0a0008034120740305032180c0030f80c07070395100380b08401040b030700640194030f01d0410010b803140074018480580310810001002c0c5103000310003406100001c0043c820040d5141d400c468076002035022080712a004400d4a03a10104480440600d0098043c19030000381740c00d03170015031480c43c0307140c020640354000040c103c41c242d0480c4c01c407240d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 39984312 1250 39983062 39983071
    0x609030a0c1104090b090102040f0e01030804060f021207030306050f09010b030a020711060c070f06020604110d1b080d11031303111c05070f06030b010816020f0303010308040314030a17 81
    0xa64031001840031421782c220306031046520b54000b40e5101c0c203009002c4500941035018820a0440800510000b40f0f8001910180ca0a52070107041c00c00c100c2078101e14020386a013002041c0304000840505155150b04000240c07031007564105200c20100c001d004550b44240301c1c1e801300140074004234544003480d400520303c10707000300c2d4501403e0740f02c10005800795106c4081400717941d020388020490f00b020712428000030421030014040e140b81076100e45080c030f0081c50005102c0c1ca0510400070400145050700400d50350605c1540d68035a8403410501e41d10241861818003007428902c0d0003440b404000111100048040c04070383c1828610b51f102d1114007544100710307610028404608900710400e881c0014628000d00c0244510b030301c0e2400b00300c0840390070382003c402c0600300315008007140d0300404800e4101c1044000c210008250000c00c03405d0100307449200344140000000002403003401e02c05041a01c2c050703107a20881700000148030355240310f03500020000c6408020130101c101784c0884c0c0a51302 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 39985562 1250 39984312 39984319
    0x105071b020f01030e0a0606090203060108010503030307091a0f0a0306321509090c03011406041d09070b04140a0909050601060c02060405090106050712020106080a080c010f1b020609030a0c11 84
    0x8146d0f040da280d206403a8240c10081245d54040104140703580c0c0007100e00c2c014002a8042c1d483c60a0042d03004101c40918020080c20402e000c007804900c407046c2c01280c042207001c50030541c8460311010010b0150003a4440c1e04020100480c50160303100844600e4004144804a020181600002408000030751071840112500081c0840221500c540d1888d034800c400d0000303415540c0d03040c5004060184000c116490299005002c01d1100051038002c0b80c42c54546096080159a07540160500c1e003840c80d04111640140401c0c0010070314810340c3d20301c8203118102d4888a445460794071000c100da0414101411a50241004100d442d008140e02141c0c14000307801245071945075804618055400e0b4080340c005000000c44030144042409149074603e10b910081c02418034044050395940200c0601030000039000900c545020b40960000f4584040a10103001d41298180c1410300301602200c5000940210b0001400c0c0d41c201008951003522076440d401d85c000480e483c0c0d00b104400c0381d1082d640 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 39986812 1250 39985562 39985573
    0x30d020d18080304060c05010c0c150504050c042d110405120f06010e15040c020c040b04020909040308040203060906060d0305090612280b06190903140105071b020f01030e 75
    0x42c0400203000802c040d03d25611140c8408405140c52806c4464111154041000e1000604002243d400c44520155030400d0003082a03150340c206070342044c286502e046e9200b46000007140c284400c00e124949020310f0031814081c0540012100015070342282e01050918500300300a2005160061100340c03031401e5034044404691900d181546000000e8102280302180e0100b00818043c0c4021901d100400c141e400340b0a0380c801c408007a40d14a2a0305e04207110310740700c807030801c0c058032a5030540306141d03401000c1814504060401030b0000b00d00352403d9009008a40010310b40c42030000e8107030b00035130b400b408000c0b0322400354904591640160501a034000810410102c1083e00580e05901816181c03e40315054030001d0710700800d40f0950104485081d08051008190b5078945081d20404d081d100403940c180800410200d904038841d400045c2031586d140030940c10032905501030f80c813843c201d482c4c581c0510000e4454540341064484000d5109804130546521035200384c202d081803000b007038100c0c4c3d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 39988062 1250 39986812 39986819
    0x141315030308130f0629030c06030601050c01020d020703110f2805031803010b120c09040c15020c090117061305010e01020711090c0702010504090209060403200102010605030d020d18 80
    0x7419944c0c42c0041d201e40e9191224622005600e02c159218202c501c05800648610100480d880c0e481f4108454400d00f0f0210004405901440403a030b0030000a07070085583c0c001218000c0c00035007000c44140d0000e0f80441c48512250030010318181107404c41d00041400007292a2000705030202001c1c00c2d1941c0400080c518001001000034208000e000750464401001c00c600b8142100d8407129208c2c400d1082640c81140108040780c00c02207504140c0d41d100980e41d80d41010541440c06030300100d41040d44805000d0a6503020460760707800003085600c80b440340d0f40c0b5448440141d41111007070034a034010b600840c0d103075580028600f1a161165002241e80e146041d04282283c0000c20103a4034482100c402c1c5d10302d4501003000b142c0c000141040e030b03400c158803500000c01c6401607005440095600003007102d1250fa0750800e980c000c50380900840414024034a150380c003510070701010381c095800d00c240410685000b1a9228841f9103690003040e103958200740c100d407100b03144091500344640241011 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 39989312 1250 39988062 39988073
    0x60209040b090702010e0606100f03050603010e0a0305030a0509071d100503120409110301080c10050715020403020f09010501080c2212030f020109120f0509090114131503030813 78
    0x1240f1981c0c1c2c83d00001620544e500355181400d4009007101c1c85410302c12590303004076130000c06400c00d000c0e061400007803650314640464014101038600b40e00d00d10519000004142d4481c0003184150900c40040c0140e482c1c4002c41c990340c140a00400c41140d00080111503480d480304551395120041803c001c0e01c09a07103030007003400c1c808250300056110b0f40028007070040c00a1130050010b4203500c0f0944a24541c54690542e0300c0e8089804e1751480341c4042080202104d100e9816661341c690030144040810341d415100302c00035803051104a0040c009100030880c240b4000060604a0300180c480c02807070b9860801004459020b400c6140600700d484103401800d907a0801c500b406070001004131803480c001c43c2005041c41c1da281a0070350440e070602141100250303001c550001c0d41100d80c100041e9070905004151340314064414042e80086403a0f0002413114030385498070b411070005880c1c81405c1030b10b442c250416621880510300d40381102d19410400a0320801d43c1c0d81e440b11041da005000a90380b035480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 39990562 1250 39989312 39989329
    0x317070b0c030a110903190c1703030106090503031204030e150c0a02012c0103093014070317070306080a08030f0709051807090503010e0102130501051303060209040b 73
    0xe01c01c0344000481080700c0e43e0300030710945030f0b0600e044c2c00c01410854910002981c45085040011031912581d900c03c0802c0341e403902c01c1700034207108103110070144412005680e40760424421a00019a154400506410048200c4171048898141c581070783e0b80c0c50310b040d60b40800b00c1281c1500301d4230404440840609000c050030b40d00507004050080d484c11070000400d0027034104405c1038000001c0400201c440c1070b109050000b200d0030b007008500541d01d41000c14000c4581c41e40003266501d500c0c13040d54032000100c0b4507080c0d55035039210700e202241050810051801815001070110311041c0b00f11500ca0181507480d0307440a0640780200d0707002d85440da040e0600c170139440100c5030144040240944065101c1c90203502c202103180070441315240c80002007590050200081d903400b14840422003070b51181404074003030040035009020b00185134103081d00035400008002c102010b80203001c101980306c1d030101c2c1c064030881191029400c1c19500e40b0703c029804800016071060381c48603030f0481c030b44403402c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 39991812 1250 39990562 39990571
    0x10e120a051b030c0117061908030c0d0518041817030405101404021201060803030c04030c0504050402030a080c07050d12030507031b0c02030c0405040b0907060512010317070b 77
    0xa407001800b0301e102c100039007840c061558803e401c034020a00c90b07641d0110365503040d90b1321401304081646480c400f040898624201e070a1510f014418003099060002000b05141090001201c101c5400c00604540301d014444207400c00e00d02d00601c01300503240580011044407140042819940c5459440303113009402140703403055200c3d01000300030034030206200c904c0b00f460b088101440400401d68070b46050400c0140001d2051008100c03c0c020305800354400700103002844100c075030f64108045020060b801070311040b00d00c9400140c000c07031f40341018000d0600403030303000e03006100d920035a64408507942c001c1c0c0c1501d2030520030080c0020b416502c00d0300159209011300b03080a02200d9080000742900c2c8010540002d0605000110b0746611000c00700070003030800c038607116031102179a01c0068201080011120340c40384c18030082c03005202060000c18003071320b2004100c4400b41d9070341005641601420243c0301390703030420400410200b40500305103040b40b864015031074a4003019071b6409920300b10958 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 39993062 1250 39991812 39991823
    0x5041e03050c010204060e0a14010c14190308061c020f01030509030c0304060302120105030118110303040b0c03030604050105090f010605030604020f0706052e090c020a14060403020d0906050306010e120a 89
    0x24000e40b00e50234624001c002828114184841d0724600f0400a8840716581b100281005455141025402018041c0400e24070f2044c0080c1ca81940d10705004110003c10b88245110b0009414010400620410704800d015806001e1a4040300303180010b40c004c240050451000d03010800c50320341000420310050015140a450058071591021742040303805005801c5076029a14251403841b1646200d8964400d0741c1d84a440c0c0250301c03920001013400c500840e400500e07200804a1000e40f41100840550301c650400c0c0c0e8104020380e030310010040844420380d0b5074048018000700501a00d031080700150f5014001820240c03810b140120900e40d103902002041e42c003140d4400501c50306c4007000303441c131181d4828a2014041107a09071701c20a44908144075081e80d0710780da4082d0340a254009c0c0510030300700c0d4004a101500c000e24852a41c1c0301c00c0c04450441c014013071f411050300500d01a0364000c1c1507940b6a6512401e50790b6140c01510341000030105154440348030908150aa0020004840036621a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 39994312 1250 39993062 39993077
    0x15030b1f0311030c030a0911130e0d050403080a0302250f05010605060f160203070905040b10050102030a090312020703020901080f07090204081f0b03100b010206090105041e03050c01020406 83
    0x41009044802d890307800c0382814001c00520050040300415260421030541c000208181d240c680078440d100c40d50b2045800c0300d072620480040041980c8200c0c0307040c100f02d0945020a101c054116458425800020081803060010280107407203503010f0701d002130003040e0b280e104a0b1103002e40300c041d01c80c3c0707242101c00c6198250f815041000c2070146000030041a2140c41c28000e400381381d1a028050548403104041c8600d00c0941550b504100c11002481000c00c10026814036003425562003604841040300c1180080c8000ec10394400011211030340303426581c20081c02d04642d901c0302800d01c1101000c045214600300840540e07a4880038900803d42c05009195001240c58020306111142d44802c00d40d80c81884200488100070422200800c40e04c01103d20918181d1001c0c802003269806840c0c06201d100161850034100d5400007058440980845d40b0a540b42803515007602c1d411100109032506035014485400355407000c0d402500c0c46400c0082c1001d81031107400342242c010fa408040011100d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 39995562 1250 39994312 39994369
    0x50d080c010b0a0f06031e050411030d08010302061b15090601140a0806011403031b070f090b0d020405090c0306041b051005040b07140114190204060915030b 69
    0xd109001d0945000d9030000d03603072031902014503d146954802d000615440b40c600304412030401042403004041c07110b08002c0d508003400e11124102503e4415406032042054141c4cc25005200441c1200d42c014034681c5001030502000c0107444840c1c00c3c2c001907214441030a2000f10050304c2091240d580b020043c1303003543c5000e00c0000072480700d0040c20b005600c50390040c00026400315640c0d05441444440d085201911400b00b459841400382417014086204400c2c0e405045c04a4801c04484200c4109003409490342c0d101c400b10307944440030315400213400800c0401801c058000076803110075042035070000b0400001003820148200da088415540380002c081c902c041d407601c200c01501050f11644d0003d40004800341580c07180d4003070003089080c040703003100c1040030390400d001e000c050010080c00b018400399050b280205080c0c82041d8544102c00c2d101004a00718030981d400c0b105280d0307981c5001c52408030301e2000001590f40140401d40c4401e00007100d030700c030b54041308030007003060344502e203614903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 39996812 1250 39995562 39995587
    0x41e0b220614070b06030a0b010603020406020c01030507020a20130e010507020a050304170c060703080f01060201020a0e15040509041203050903030609040803090f0d02010603050f03130b0d0204050d08 88
    0x1907820110510982c100e01c900d501c0000c0058988040d403004081040751500c5002918083c20140010b0460500400101d84285c5c15005041110866000c881e02c410500005400f554412148a40160b0055038840c000c1902d01082c5841d00081e0307080c2c150421900c9001c102d41c1141d1031703100310b200c50f100c40c1200c0c00748109203d100d6000c0000d10207011685619600c0e00d8880c803031481541c2040e0408040d2030140b035000d0010a5151200521156035a0503a180181407003d04580030201526000000149680107008a038030100385907441e803910849010402c100304400d60000c00e511942400045210b0319079460450145018002c61441100170041c001d0503900018010b240580003401440841c2d203400c0d0041c1d03001548410304540b07a984880c00181340c60805000c2d0f0825108884078003610303a8065010505032070041059a8440d002c8484140e52841010f014196440031700804000b010000d0018000c1c0740080a000740c82c00746d40d000040c4800410030b005440084000403224000b61 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 39998062 1250 39996812 39996877
    0xe01020a031401091104121103031c180503031f03171c1104060507060f0603030929030a11040902030114010306050306040507050111010f06120b010b030c041e0b 71
    0x44407041c00840611740c003201440c041d5100c1c0f4100d07112000702c442c040040707038402e1094001c1e015085a441d80050b03010340c50551445c03500c0704c000e40d10306a5469038400b4506450030800360020021442c503112401d412541d0700c40200304242c81c11200300e010000840c903414107072041c0c003500f80c2e0944540c4603a40400d01804840914460107180c9161300c1c014580311020303901182d5643c04c01e10707128405403c0180283c00814108540245003e20100406401c048a41c0648141202503011100c1c41c03007140c09014088032030b60744c010000303000260225407181c0000e803801c0c1507810b100d41055a079100710380603a042a0005c01d0210003024890320596414800d0030014082107008000908060b2900d9413074000d140a0a4100018507034000f81c00f043c25008601400400c440030450655260400342e44910040c00403206407010710000070b540241c40c0306807805005003140080c42c0c40d14204681d94040060103c50308200300b280000203d481c1c80b02d001d4414203014109071800000c602460303103004e8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 39999312 1250 39998062 39998069
    0x30702011413110603010317070204090f050a0302070b180d0203160605040e0a14060103111303060e060703020702180702100c0206040201020c09130f0204020d0507050c10050403050f0a030e01020a031401 89
    0x1e01c1309200400208070b03040c1520445401400d485559446140007150140054050241c40c0c805881d820b50704001000500d2803030341c0d000e0b0b401e442005442c0c500c154800e1107001003254040e51106289082c03132500320100b03010307a44024201c0303190f80300380400c0f001d00072070a61101c40454404102000fa1108000220740c0c01030080d041085880c000c0d4030380149180340500124101580c0d500346012000003a000c448640c00d045094252003a0b8924000025001d13071042d0910070300400c00451110340c024000d541866600070314050280c498810b044400380c40007454030003144a50320300c04e0140c500a10900329020032960240c04a407410b80006450047c0107242c1d0b601072a041e404100c940e003c1c1110380d1024a40c80341340e03d0300c04401400010040e024485035480e60610b4002801070b0705400a00070b100f002010703000c2c1c0700915400300706501111130072280640807400822180344511001c0c0e004100400d141e09001030f04200301481182240c0268400034082070b0364060000c1003600c0218210b004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 40000562 1250 39999312 39999319
    0x60601020606010507030806010c060f02041404060e040b04060906050403030e0c121f0e06090a0212060603030301120201030e0105040b01081204051005090102240a0b0108060d030503070201141311 86
    0x1c0e0510340b0000380540b15900c00901001052004a00307280c1c840ca0710001e0301500302906015180c5181843c400a500600c2a10301e4040035882d840f599080c140601d01c03c54bc44507803403c80c0c0b0340d01c80d11410f07450300c00107108541d9180d442c044e000006000c4c2c0301b032600540c041e640000b003d03a4101d1490b4940968400031900c142c2004035110103000c1c0001b07075500800701d2980069200010109a00064a140e16042a00f401640c0401c220210300042c50b0350703068001c680d50190f200600f00c2e4903443c1d110030380e44103030560410401405280c1c200e0030b00403441071040c5400115440b4040ea000d0860304191401c40b5a00c003004010411080c0400810320481c05249200340780074078180005503220840302ca54000d00c4000701e41d200d10350b0b000380281d5200a85090f46000c8002c2e402c8150002d00384203c851000c1c0619000016041d0b503c2001e601d442003038060044225002561001c2d40d85800007421202159266000040a8411300d02c0e054016801c1c815020818206413421280c44100340044c03900 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 40001812 1250 40000562 40000573
    0x50417100f0212010501030e0c041b08070c0308060613050d0506040201021204060e1c080a02030409110c06190e0706080a0e010c0212030c0f0708130f050d0204020d0209090c0c06060102 81
    0x2110f000040c0d0300e41c1196401d081c001002082100d1441c10015802c2040381c0c441e160103001d0b104007141c41c0e6050040c48099a4a9911f070392506415a2041000800030700010083c00019429090000c024540c4150303501100490759520700000304440300041080359190001c000b4001107580400041c5000481c0701c00c407a0605080c010300074040700141780020301c034032003c03030f014002c9800a81104040c940c120b00107076580c5070b0041000e5034a0740288540001d86d8640340d01c16800e004400151024082c02101500c2e49403900c400825041010b030b8510b2400660380e400480c41036900b000301d074000f000a51120141d51911034600000c80c0c10402000c0410790402c854245015404944105091081c0070034546039165000c000d01940650340c855800c00701c001658800f03005840e806859903600040703443c0c0321992245201402c0120602c40c858200c403084804600605c2c00c3d0b005040c100304801c8006041c5100000010004c038010b941055040c0f40028038800d5030320b418000103500503400c0c001401c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 40003062 1250 40001812 40001827
    0xf01050d02060904090203030a0815060315010e01020718060e010f0303200304052205090d02061504020f040e010f06020102071101031d0f0607020f01090c06030507050417100f02 78
    0x100c84404514000b07105000000c1c0340b403410f0b0b0355036012408040d000317801c44c1d840362030b082d4000c0c00035007040d90201c10014901800e841c0750300e03101d011a403041c040d505160000c1802d0b1401550344603c1c42140c0c0741503002d842004500c0001028205006030303648400400e00307030302e00700b074011410034103070030420380103111102c00d002280c2c00c214130050702000e505800c2ca0505400c52118114016030700220b074840b81c441d407044401c241d0640825040c100b6510208540e0711a0319202d5a2500498001c00168022100190f201c03140045d41c00318a100140c005487e0440000c08100c041c0c0c4141c2110348880007500050120b10040415040901441c0c0021490041d8944400840088030056103041645400c1000000e20009001c004284116012602c4040074074646903120f580480351a80140b29400002c440140140110611a0b80096130355000c0ea007082002c9000c2e19008003100c0034004108400210000d14148902805503603001615502035802180e1099619100e0307000031460050040b034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 40004312 1250 40003062 40003069
    0x81b03040510030908040311010c060e0106090e0606010e010f020102040803030a09060b010c0f20040c110f070f0e0403140c070305010b04050c0d150902220f080d030b01020102040b0c0a0b0f0105 85
    0x550942c1c1e041011041130345142030040718013199203c8018600e81c03c0c0304130305481c070ce03054002d50103482246601381310000071010b10703d83d01c0c041203903081e001610280180701c855000b01c884005201941c4005840d26444070f02c003d00c0c40c0c6c004d072144640255901c040c0c02c207120032403092018105003464407100c4101d2544400160030988000900016140b00e18100003d05846503101230030005072007032281090400000e408c10b031260040200500a040c0300426072a00071640000743c40743c40d41c03041031040c10480a4906920f0040003182400040140d015100603008058225925508002c6c00d0350350035860b026003920a0500150f01403030a19092000c0c40348100306590300503a4802000440054035580840d00046039031107281840d10015684120b103500b20815903114400380405c0a4255541c01200c0302c8040520444c0f02c0c0350042d80904a1651103134004190130b031814400541003a0702c45030342006c5035000e002001501c3d0b02011001c41001100400e003a4024940c0688903100c0d8986400f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 40005562 1250 40004312 40004317
    0x6060310110a03051f060e0f06090102030a050309010f0501150f0f05070f02010e060409090605010b040b0f070314030c030412180510030204091401031a090a02010c081b03040510030908 81
    0x4082415102c84c001141002e415032050800d04600343d085c0303045990b84038003400d412681204a8020019030b000074429042c0700c82169008401a03005500c1c01404060440e80d540006d82451419500c804c070310302544c00c1c0342c0941406004441040ca02c1001c10781405007021020140b032505000c0c40c458000c03085034105080e5000d0355003103520200c01007080e200403234042c251202c2c41d0f0340c41a80402c0204080341036038416020305104100400c800e0343c88a640c070300c482c0680d10070001822001c1108042145001c0d0181c4a183d01c21b00b44240c03400c600d59954001500200c1d100c4e8200310703000c000c0109000c50201030203001c98003400c004203500300011810307902507220b019080c040c92841e040506c1032031007603044500805030144100200d05149031104c0d5484d50a2100b56264281c01003511003140a1280c0c140c007819001005042e4450036900540300b00c182408107a807220024441c00c0c0d404401e403003001c608030140718040e503a604c0c140420054025080790504003094039064040c4005042c2804 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 40006812 1250 40005562 40005577
    0x602100e07050d05010f05010b09011115070e150a05030a05130201140f090a03120201050718030f020609040507020a020102010e0a08040b0d090812010303020c010c2003031603020606031011 83
    0x30042c01120241c1002401341c86a83d000d86c0403645410000130b03160b03880d04081d00660400340c1e6030301d0218510000307466030788826035001c01c1c155040e140400d2007a806166045800d02b009002d403001d05030000340c6903001c0d400c1101d040002c554000108602240c85100b19980140004107400d148003290f000280b64058212005205a0340001c0e1003442d02056810b40c3c00051009001c0e103181500d91400e0465990b24444400240d070801c0b0114010900803081d6032480345e8103201e03402d00d191450702c0c1c2489075000800c05980241307040020303030050f40b40d5024242c415a540d400401007c0494800242181d072280c00001070341d04101c08020001d80744104032004c0f01c49403a01e15444409844071000103040340c100040000c180080c101c1c80c102c5500c0f509034101c038001c0d000ea4840b01440c030015101e41c035085800038400007400600d03501d001242401c1c0c40803204094100c900f8260340040184060603580310a80259205400304105446d0030000403003500b00c0540180281034240300c1a413641c1c0034604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 40008062 1250 40006812 40006819
    0x1060e0415080f0a1709010813030903062406050c0a0201030509150403080907060504050625060509100617030a08070507080a09080d020a020303030105060702040b04060603060602100e0705 83
    0x14290800784065012510141120364251101d21140000440e5544102d140c11a0784c4c0c20001c1c4107400d04030000082c3c600020b03040c0c480c641c40b9500c01d06d4285e895044518102c2c140610b90b42d022000c180184508000c500f010707031200d41802d5007040383c011503c6d030170303842035040100400c41c9900b0a4004a0600c50146d0b0a081c04100d0b0746460300741c103080103118072850011a180f0b000f00014194801451402800071800b51200e5030340350070f000c0320540304a0040540000e42003201013820b160240c614a110780005244e00b08051842e6540d50a661090310f4240d810ba0120b0f00f164000c80040c480d95000f00702441740c16112102e81c400b40342e220301696540d1001d10640c240015401c5001d481244d00c980c0e4420301041d0303141c980d000c010f8908000c40c082c05460b88103044291f606140002241001241c00400460850780303000e040000030380c1b040700700701e80086d2a2109040c80d521240501c43c00f0380b8440d1000b042c080e04102c2e0007858118448001803083c0e08040c1041032407d00407031008140c031802d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 40009312 1250 40008062 40008071
    0x50111120105130b030d110106030506041a100506031605120c0d11040302090103020909070b07050105100b0c12090f03030412021008130609060209060705211305061b030705160e01060e04 82
    0x58082401480e065002409078010502040200600d100f055032020714101c141003415120340b84204850303f0607000341c5812800402c0801c1c403020b200c00580c0740184151900717910f0f011500485440da00c00907202d00f2004100070501881c40c500b40d00503180f0401c01c485900342043e1564000810000040c0720203809981913002042e0700c400e0030b00c90000904414421203035200c81c146069070080208031085184c4000200c07010420409c00b030111100014240e00409403034002c40c2410340740382d01c1007444039400820342d88190441e0314280040d0004110141002505030114010b00000e01414481d0101b0003e2000400040c2e001031131060786401e401800c00124a801c0e450030000034032400203020b030302030000b1804902b00100040c00202c107038842908442c40076007010409680340902e00c51601d0125510380f050040781868409081d408442d8488252110a03c000c40c1e405d60340030690903500c6420007220505090f440b0140788005100c1c5141d96000c641c502003001700300c0150142594895600c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 40010562 1250 40009312 40009337
    0x3080a02070305190203010f1803030b03160906080c010804050a060b010c0b01030807061406010905010804230f010b031212040f0b010801020a1202070309030f050111120105130b030d 80
    0x208050070245900c141107803504a400c0d00544950b5810388400c81c440c1d800c0c4100d9201140584c0600048607040c5200c0ca000c0c40c5490f030f01900604454401a9010310800450028a110012400c07000340703640040000d8060074404480e05001207101da41c0e040c41074420030f120000b400051100c2c640d03600500c0000301c0c41d42120049902c1c0070110740c06084101c0560000c02803085030001403104610408080020400081d6900c44812040f039a15011401d0a00c04101c5035000f810b0140d8418414040140300841c980c4000301804007440c000c590344e610100320110207090912071542c0300e1908500801140c2518003040907184655074600d0306540c95140401c08000900071541046c560001d040c43c2250703142d400c918000c0d00800410400140795580c031481502e4188219001c50340c0641e1070707542942c159140c00341c244480920480c2c2d00e658a90b070741d25600f01c0527400b0305590003040040342c03125490301c81001030329040c400a569041c1e26101541c56a65000150310851070550b0174010362100e039 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 40011812 1250 40010562 40010567
    0xf021b03031902150c04080c150f070c0302030102030a060f0609051003020a031b03050a060603180b07050c0105070215010602031206090603100204290c1207020d120909050c0a02060103080a 83
    0x71403210b10760904c1c07a64014440041580c00142044d65000e20481d000168290104009030500c80b0074100e03070700c208212640f4a0400507000f082003500418250f4401031703a0742d000c03c1c00c9a104540c86a51903544d207400303021a150400c04080201810301c1c1031410242060001441c4800f0020140700b41540051104880350080c0c1004d110417000f0b48801d006040201c1025024000465400d034080d8980200898428064410b0078040e03186009451040c40d86035407855001800030f48090248501800304000540d4240900c038403070a2980e0142c0100c4c1141841100d81c1041a0410300c2990414840700c81c03007005006d1466446002110618150303221140402c0c04c100d240f17060380b000a0300002c1d000c280815a10004060240104c80310b010020008200116500403e02d8441154001c038110f100a00e1100b40a007148074001003928101000321758075540150740382162403001c566001e10800041090707110f2280d210108a80d12403901045d030b48029120070f81408010003000c1c000c2201a900c61 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 40013062 1250 40011812 40011823
    0x3071203090614091b01020d0c080d06031e030207050d020d0308060609030d020601081b011202030601050f030106080a14011505070c090509060405070501090617180105070f021b03031902 82
    0x1210f804101860800c0c03140302e40c94898180d011a4000207807410a40594400a45203e83c44456520f00d490030321290341d5811154003602608040c55101c000210103e0791200c001805415507440e0f04100d0307e01450003070b003407402541c0502c1c4941061140e41d030140e158880310080c59030341454200b00d181d59600009101c0d000c0c075044160103100350301c10303030001640000c1c15034140c031400c0e030890b0542c502180030100d51120031a003da00080c3c540c0d4040142c4d8074035801964000a050400038100300d08051460084d0704240d1000001480d04401d208d8080e0440c410080c1c200c4e08a2000e6880c0e60520b0300c0001d2400740e4139514402c0103000100c45060000c1d442041010300304141c800c0c00b040c20401070580d91400207440603101070048003000680c941c050003805080324042c2c0c40d03030141d03400e042c030304130072468001012061005c4e240c01c2ca420b4598070a2103172610a02da15141c010380c030685018000d10740341004080301080f0100300d2400c0c4041e0340000c260303510140c031b800120500c184c201070f0072821300c0d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 40014312 1250 40013062 40013081
    0x801090b0a080f070807120215030c0c01090305041e050a06050f1b0a14030c070e0405010f050106050a1115160c12080402180f0402010e0303130b0d0e030712030906 72
    0x900800420001200c00414000101d406817070403101c4041c1c84110b0b100202c404010300a40c006083c4c240d1446220182d4041d5034054000c054031030a000c3c600280500b91091248218002900090144043d205502c5500d2520080310119204d10f401c04020520444d02070181c07001340280800e09a0901800108a481d4202102004c40d0410b03030410300159511844041200d03298822040c1c0480c140001090702c04513404107006080399441d0106000d400d803c060001c5d00c0030b54882c041040f1041d0359000759402421035a0310541d80d0f45003000000d0104420000340c3c00e003500710000a0716140d05408405801082c0300d180114241e482440c19226051401001000000009200350a10340c1011321188154025110100f5400d1840d10404840d40102c42e101d0750446090041005035200f032004801840002d400c403842c0a10000d8901412281540b03e1064600b00040203500c00801d401400450700b01c5100450a1105580d01c5442c099044070207d8101070303032034403620240a8039400c00c5036072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 40015562 1250 40014312 40014329
    0x809040b0406080c0f03150604090f0203012901050405010e0411070f051005102402030408070e100902040303120509030403021302091809070e1005090c041d0105010801090b0a 77
    0x42c503507100101d40d2036407208070645204003101c590040d0f8500340460700f1004541030b42c82085581d51040300704001030a6a0600f81d685c641e001a05d1401610240703c1c0b9040601091180d00c020031403100010302d540460810581046010f010410099800c54641000d46600320790101d49500c080142070102e02413020041c0149100310440d000744403010070031910781100d64409224a0792200c4510040b000b07503109030b070304e02e802e81607045003510689034100f02440c0b500c0c4141d918107951400c0301d91401916400c26003104a4030401d012156007030310b80150060203406410760400c1d1171a100a44202680000109840e03180d4001400442c0148212000396034000c201c0d40ca085c1510328018025044013412078040c401030b130703c000c0f05510b4844000d881080c60100500c803c038140904070600f82800707001d00e0480d80a031074002c26190b40354203039980b0a0780010841500c482c0b511241c001c0703001214621a460700743c510018001a40d01006441c107480440350b020820140300b502207003500b1000c1c0c0c400c10b079 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 40016812 1250 40015562 40015571
    0xf0a06020c030c1c02060f0610121409010b031c05120a0612120e030105010e13030309140604021f02030d1a0a03061d0c030309190305060118060b03060109030809040b04 74
    0x2c08410300e0a05002c80c52645c0d085699543c0c440d0344040d01041c081d42c1d40361b4801102d940d0038500510900354110000580035011075141c0e6100d003071200b22001501d40c851141d4440a04c02c00900381003102d0040f4020200d40380c80200b00c00c10001d4035900c5040c64601d103540400d00020340c1440c80360440b030002d1030f1610612440b0b00e024109802684030420514000408014a1400328136050007030314166052280711641c1d82d19244128a08101180c40c1142032507141e0510031302190300da890b8000f2030068100507101916052040101031070840000c0a0360070f2a50b401101600c1d070000542d4003c0042082c0007a644107010502c1740b011010315140e61b401124088007204001803a041006030b045421181d485200054007029200c03e032407007085030180d1090111050602e0440300c0b1540c907521142c1960784d13054403500c8407030410340300343c10800502803e4241042e421007507100346001020252811419410301e480001c1c0b860116100140080c080860341c60a1035855031f200d08200c3d68028000c10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 40018062 1250 40016812 40016833
    0x20a0618080d030b01030f150618050607050705120a0b0f04060f05130201030e030a0c0b040c0e010e0402011e0f0804051c02010614040c080103062d021206030f0a06020c030c 76
    0x10084d10800071410b0001e8100024295101e119001d0703030f0902c505080c421902c40b402c1400844168000f0110000c01b645c1c01c3c0340c000750766151305006048940c098030207030105509010500604080d44402a81c45500c11107400000c224028140717608852044400d08190b147d506102c0003403d034085060180f5450202030281d9501400d1074a40514800e8805115925007401030586030f016a0010001080030140c80c000028032034448154058483d1f5006035056131240d49110300d0300c00036001421b90303910307041c1400706540e04194042070314042d200c81100100c4414030010410a07030000c0038014001090085420400103000001008130340001054020000c0070009010b002180f0400341000b040c80d03030b58103160404d80140c2400011644809030942d00c1c40c0d0341c1d42d0052040c5030303030001d8901c0210207801240c1c1000c2102d51042c1c40703005026841c0d000c40b00780e580030548003030700d21032080c4e0261091900342e002c04038100701103039000031005845500c000744c0c1e01d04611940c130400c0c03a540200043c06 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 40019312 1250 40018062 40018067
    0x705180907020a020a0905010b0414130504290c0d02030a09060c183303060302040207060605040b0906010f050c0c0303041502060109050103050a0611160b010501020c01020109020a0618080d 83
    0x400f2150b000300d0310000001d544c2c421086c2110702c280944014044104400e1040d80d040714009000d0000292400484071019081002140c1e015101280c9500085807403e410381c192404c1c09038003c50201800043d81051300411400d803040003070f107040d290780110000d094418545e209a19064120030300b44140308400c04000c04003110450032076051801c040d0086040b0303a641c240d0740e03441d4181c01c06400001250003420300b510800030750014105a00c1e0000030005840d940060305189101300d4011034050b040070104429210f4080300d0f00d002e407201c0b908004581ea13006813401a20490350910a5503003020540755814a007150452130341520002070001011800c81c080080400d5065098500590701d6100180c1034860a1002030071710f074400500d4101141640d844000d040d0150b40c1c015150850141d86082e014400b45401d80d941300d00c01c00100701a580500603400700d540244000c121001056002600c4c10101c2e00807401088460b030410542122802c00b11409461210202c0c1d000b448c5101c0300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 40020562 1250 40019312 40019323
    0x108011b0e060d06240201090b0c03040516091b051207120f02030408030a06080703080d020a030f0c0207030b07030b0901090506040e03070516050108060d060f060b0a0503060a0b0c06070518090702 86
    0xa045010308030000484a062041c42103048c1652302c2040e524443d1507402d000001c07178102070814ac400740100000307941c1c40d00082d07400b07500a000c3c1c00c2020810a041410030383c0c82901c030a21980500804100c40240c9101400c80594080e55030f00f46000148014841c110050804031a4590709078030000502050018007800f0b140b2440c4541810300c1055250151540c84070164440245140400e0040150200e000e4000c0d0400c003907686400998142c41c85228001d0f5591140d015004da00991802e01c1885941240359a2040003402d0378003c2034900300100300c2e01501440340182d115680c0d00407079115900c0780c00c00f11508240340226030303d8200e035040c6a510340045208114a95000c0c40001507254050145140700e04402801e20079448590703124500585124059601c45540e90500425124074400283c80d0030f80081d0b54041c0c8919041043c001d07140100d400c4085050004d101c1084240030000c0e01c185c0c00855490001e40f5120119070904101120000d1340307074481020400c100180c1c2c0c2c0005c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 40021812 1250 40020562 40020599
    0x120c010b0f0d02060a0c1511070302060906070f050903010204030210090e06040b010c1401060503060a060905010504020c031c140a02030a0b121e0a0503040b0903060108011b0e060d06 80
    0x4240704000c81e000e0401403400d0100d03100940040c070038440c20040174007542d140c1841d240510704040c4080c2c2c40c1c2050004481c218012011000d0740403d5280601d0b6041142540c0840c5050007488513080c18031010301103110b5606101d00b04480007504524648007901510f0080d0344c007802c3c048130410000006084690300b801041a80e4108100261039842d1500030440d17403203c1a15014040099901c0d0351801500c0c91100314069900c680e000213080c1c4080164510500340403900141c11400d1003002e0083d40c10681c40f00b1310841c018401d91030601c0c0084100d03910445000c10060429207001150005071081100e040038a40c2d51508004041030350760000d500c20400003070300704a051503200402103074020300101103200c0c1d44524404202100d06004803890300401c94216101000341d40c1c5c0c0c1c01c0c5140d006030090702c03100001080c20062820101310044c09420214000e0003400039000300086051206030a9008000c0039410514103510341d070088501c00701100390140300d903d0716400c41200c134819165 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 40023062 1250 40021812 40021819
    0x30503040b04181104030809040e0a080306040b0102060121150207110112051b0a0e030109080406030608120a05090a05060c06102102060f0c060108060f070c050607030905120c010b 79
    0x99503c034500b40a21800c0c46404100d00c800b410141180c071240302c190001040a50025510074035800d0600d0204601861248107e60701d0b5524585071040c407040d180c1c0654017070b0642d88481c0043c029541c1d19030341040341e20950212000000c01ca81484051142e821001d403903294400241c4005011000c40d000036100001c0e00c4400700480c8001d082c2c0300b224011140c0d200364401d25894454003004040c014000d500107850500c00c1403902c2000a801c4500301070048880c0300c8001007c2200b942c01d4050a802403200c90080c2c51040c100c3c400080541c403515404c40c1c10800c002a02e0322080d80c40307140d01c40c0504000f5080d2900e0b440c1c080b42c4181d81e400d054450f0401e592922800003078130107500d0a40700b0402c030340c980e000325403a8096091069a8200c1c1d1000c00e04c001007030115022800b400c0242600038400900103100c0781c10014100d0110146c0503240c4402c0012140008000c40c0000519581020341031030002486916810a1420f0901d4484440404000020b0403400c2c00d805420071100700d80c044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 40024312 1250 40023062 40023089
    0x50606150f0a20010f090c06030203010308180a1502010c03050f100e0901020702060c10061d0105010f09091a120d0207030305130306090629030712030504030503040b04 74
    0x100d0034003881c000c5101100301c1c08030400c0b141003201d20078111030a00e1464042c0041001081210840c00d44201000c081205071782c0d0380ca000107014013596040010441820210b10315411625900968418190071090350320403100028016181c40305014000d001449a1b01c410042040c002030103840c4d104001c4000a0601e808252420001118035015008417114032598a16020303c0c890400c030020508881958244544809a140c050041400c405d030305002d40301221119550034110f424075040310301342c20202c03000f100c03080a074103008070b05403002400c03e4007240c48065001c54100b0840d41045403020304202a014030601c0202484140b0402221015220280a088140e441c0c107580348080c01640146130030808a4010001451360103c001c21200074a5100e494001c255205104111921956070203c0035010000b2030149003001a842110b0202021510009a880d085070240180c01d0300181c0840003054044c0781254015a032000c1030b40e80300d0f550b680e40c902c0c90ba00248132322410038014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 40025562 1250 40024312 40024339
    0x2d0603090b07081012030905030d020106170114060909010b12010b040c0e0901060813050f060618090a03300504030e0d05120a03060806100501030b0a03020d080705010b0d050606 78
    0x3600780504c1403c40a2081114030724100303280840c4620200281d00b0f01000351004141601c09101e0314501203529000490038528002c140da00881402024140c184d142400c400040342c0e0b80444541c204108481c07440c0c0940750110194010403800c0e011a038010001018a284103c040d00800b0001d0b20440c0c04114814000509882c581c41c2280c1e0558082d80c1280140501c074098120743d6001300b032400d80205841c0b451ba9825141c018012000c81c0c103a030140080100b18038145140308000340d00e50340c2d1030155013850740aa980e2441c40c0300780181842030305190912050902c0f41c403800d081846003944404140f050105030000c0c402070780c040c0c00140da260a00c40c3e03e804c0c10321211400c10380c4640102031807001c03c407003002503030041d0071035004050301c90381d0001e2446020801d40d40109401d403480074101c1d00e48400501100c480a8003140611160802080980d0300c00b040001b03100d405c845200ea4070251480e000703005000010300a5403002074600c41304184607000400511580c030a6603c90603e840703 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 40026812 1250 40025562 40025567
    0x8060604060503060a091106040f08070f0617150a0e0907120b0112020a0b0c030a030c030c05090d060204081507120b09041103070305010e0d140a092d0603090b07 71
    0x600034180c03d41d000ba07001c100744064aa104c0109907001e5444403851400c18400120141c1c09513100041d4006180000d010440060013454000c0c82c69214403035003d4605400581011128440c8040c0702e410325000031a01104840d54071403080004108003c615100c81412401480994030741c070203482280b2022804606c142242e01c40140c200303207540c556a28210303441d4a41c42c88990200c2e00b015145c60001184049030001d440c540c001c80c5c01454a6412611f0014102d843e0315800030304041c01c140c0d034840f00300d82142c12503a503102c00b5180802e02d56284c3c142040a0312580d88000414821b0801c04244c04000c2c0c0c04280c000d007015900c8440e04042c450740d4000b0b45041c1c81d4002d03840030741400820000b400d18102049200809420f41c0c00345942ca40b2400e08440100c078880e1410380000c030715001180c1c7c0c40700141040076a44c0c24003600b08040c4000041c01c400540c050f16406021b030442a80c0c80d45440000f2030106c5104107490b1030309985500b00100501100003003142c4400311000460a800d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 40028062 1250 40026812 40026821
    0x6030105010e1002190b01080f0604080a120207150c080c070c09090302150708070e0915010c020315040c0303030513050c0105030a0905010908040815010b370908060604 74
    0x11816564465920ba00d5410807040c003419403e00e10a5116145110030000d03090400141c003180191100c181c50342c035080c811403d02204d494201c0307403a04141e04102c0054601801e503010305c2014a8402c102c880c003c20500020b01ca0b81c18090000b4007480380804905420360044c412100c016a107074440340c0ca0f058001c04d158000c00c00020a02001d0040a101c5a020765000d441e03030382e0003032040b1500380c240c0c00c03034a01d40064242d60382070001d44500b04205501d0340082c240300d6074140645540d0880c2c41c04507090344110034800f010758108440001007000b0355804200814203441d030b00b0b0359528035040900e01000510302c3c078401100400d0801300007500b0321600200c0c15186e260045c6c0544140500c4c031004540f0303a40001c0808400c5580d5028120105809100d148111440340004c0c990300e5060080d09440e010151303140c0c044505811005005200d81f500640c0e180c807850801000030005800c0c2f100100c0c0c81e4100ca12034402d92101701000c0000c1e80289800111a4804c041d900d007519a4002d003c19503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 40029312 1250 40028062 40028069
    0xf0c150b0306010b18030f21121008070602030a02070e07110d0201020406080c0910030c051309021b0c1804020625020406050102010c020307020112020f07030c060b010327060f0e0a05010506060301 86
    0x12381000d0181e01180f800309803c4a4050108858945400000302d01d0014400041d210790081c582d40b10002c0c410078800300595400341095000650502c0c0349000b0096980c1114012000507440d03101c04914014056110700383d0440000c0d054400e500d8501d00d000f8000d400910946c0001000c05001c500f00e002c54030121940c80c040900700030000c00c5940800c0e00500b900c036150104201040020000b090b6a01124901802c1c101c0009030303860340e548041c10040207564098a80e1a0406d120400c1c3e2a590204bc0989040c04004203103503e079940c1c000600c441c058210490f01550190640c5100c0507078944026215902c210350030003200b41c803080128201e9054001000159000f0005403000d98043c8603c08510a00140003514000010205403000e8004010840c0800d079010440d10412403503005003080420280390811240c200708032051401840c0ca052030a4417170002203c41c00340600f90b0001c0b0030302c00c00070b00c00340140b4250b150216501c040c18a020b07103440d441c02012034258036000c2c0441c0d049 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 40030562 1250 40029312 40029343
    0x6110c0d1d01080f180a05010e0a02040b060306061605010f0c03050601080702010504030f0507110d081308061e19050906090d02010605060901030e0304090507050d0605010f0c150b0306010b1803 85
    0x451340d5a100b0066005c100c0102c101d40d0707101d20f10310400000d000b406580e0705450910b000e041c4461243c41444185e030b0500d508588200414800c00c1007075102d0798103490f059000171101022170342c41e42c14440e004010507803403c04401d0905120b8804150181c0010303004080a0f41d56034803135034800000300c0c200c903001d86008001850210f166840544910060f140741401081410502584800020340804049404603104100070880046051141c402c040041440344060002450246208410215084644449188524045440141001f45608a035034a2140401403401c0088840340e586000b1900b4846074030950156221661043c05540201c42d80a45128149802c000040d006080c0c0302c0c101c04020b1100388030010310380010340a41c1e8000c1015454180d0796040f0160510b094400740d401003414840da000e69140c15691000d91459520340007800b42292215501c549805080c0404102d94940b090500124609041d40c0040c8038251103030900a11508850302411384504014012054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 40031812 1250 40030562 40030591
    0x604120807050d06081c1706010f050c010e010501081b090f040203120f0403020f0d05060403031d150a0b04050105030a15020904020a02010218040b0d06110c0d1d0108 73
    0x19500d00840d00c00350040c075141007590906602d1280b800883e02a40c0c0b05001c0caa11000284004100303248188a6030078003841c00c00a2800c255404084010028102c5030401c5a4144407a913680c0c811005c1d550000b103080000d01c5100d40b0260b0701c5010380000e0040c1c1c0c1042c05220f441e64032070641204240d40c00d12000c1c08a01c1c03143e440c440d41c8440020020300690301401001c801403940741c0d14900800c922a0720308125910785082d401032041c403408684480d40101c000300702d001d001c2000005c045a02513418680480c00c0380180300100422414103901202501c07a155000c8200042c1d4801d5510030b9546100802003080d59a00300010303620203104070b83d0507070021a980d402050f080d00c0c0d031398401002018007605c0c001d28640030904a13031241c4903400042c5d501041d94442d61503203002c4850300c1901150180080162100081c10b80e10300c0c804001c00f600d596030305c2c1800481ca0b100a03160107a82c400107aa4000740e41c204040c0803100400c4140c1d216504e130b09580c4c402503000300c0ba5a80507240c1c500c541017 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 40033062 1250 40031812 40031843
    0x1050f0405150306041209050102060103030504210203030c011406090f071202070512090414010b0318010f020304080702090a050c0a0806030c10120b0d02060712090e010e04020f030604 81
    0x10000070340b4221141c2d50203401040c040e10200b110b180920b200d04100003201300c2482c4000c1c103008503070304014115003207940108082944281650b0603115580803558058405002c80700c1011490f220003034040c00007242d540012901036100030f05402c07000c0c8111401765102010401251002c80f142086440e0f1034002c03d042d60701c04c4882504a20f0402c1c0018070386030458803214a00103ca59035a20f00f5100050254003504290186c459615100240304506506001c2c0790480380c0801450780b0800c003480100d02040480940040e00d0303c03404c444ac00c6642c0d04103030400e0070031640f1521041e80500100404110742d1141c902c80d41f480340d05062815414102d800384110740b0400003400030381c2d15111f0000c884031541c2d6840d14123510240c003a101c840802c01030f01d0001c405c2e83c0ca000e00075440b80d03010007440320158445108880425074840079010994680ca5401e80d103402d966003000015900303010011030384424230311310140181c0c0202d03021100d080b0b0100c00c040e980d5030100c0e0014507110b034285624 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 40034312 1250 40033062 40033069
    0x605060409020f120901060302010e190e060d0c091b0503090a02060702040207050f010f05100305250e01060e041404150f06050303070c030c05030c030607110705100c0501060b0301050f 81
    0x3003c08042040d030b4a0b2521a0300c0c180c0c90080d01c0183c50480007650345000c10421503070011070307880b035041c41500c0b811020304d028480c8001000310741c862240c4190085001801507640c501c03042c2c2c011507000722040492070301d41c0c10310002040010511091085d59080c54425503005205807841200c10100408001703c041d400c1c40030580182a0498000b03800784400c000080f001e10401400000070400001c5013100000c81c00150341340a8018600142581010710200d400843e08801030700d0302c040080303003001c0015038299040900d50700c0100c0e01c0050741e00209905510181144071200200c90900150035110401c4491100507940101400c91040350500f12031181d8124106020221000050340c90b40e13000800d0075540803050840b14100202c00c00d03c00c00c075151495002034031042c3c0c020301c40c07840c2210102c2e649001c0070301108140301e000280e16410000c1042800b001e0f03d0048c012401541c0d00d520b001e0801e040d180350890300c40d42412000301d80741e940002642e04950b0b00406002a140482091 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 40035562 1250 40034312 40034317
    0x10b130b16020406030b0403030f02030106020706030506030f0d080a051e130204140114150a0c080c0c03030703030e06070206041e080d06120b0708070903060e1507050d060504060506040902 83
    0x5010038a4a506000c05640c41307114050041d809030303a0071141e6140501c0d004049502440c074031440e05206000602569500207103620aa510b141800283d6481d503000007440c00902e910300d0f180600c030781c07000448060740c0b05100c0fa015041802d801d11441d100d07000d50340b0710844002c000c40408024000018100b0094042d40319410740090000680501950140c0c1421003098108000c030b00f0503401524030703d042100c003801b00b9212900d020740c10940807080c000d2030707043c2c1e07d034000c0d002c05c001094001c02001c050101c43c905c08001001c9903036030f0703440d4170b0003801034607451911010901582001403031380341c00800c003241310765445040007400c11058107080750b10041e02441580ca901c401e000b01e4070a501d4512605d0058550840c08082d0400071f80b50440c0000801801070301088152028040d049030007581100940368089408982d80301506c8910b03184c02e10241c6101c41c01e4202e2801e03c2542500200104a1141030000902041343c9a500b40000c0d40c0a61040a8202600304410403038a50302e50301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 40036812 1250 40035562 40035577
    0x41a0309060c0d2903070501020a02090411061b0d0f0f080604020d02040b04080f07151d0103090b07030e01051f0e0a06050d050c03060a060803120703020c0d17010b130b 74
    0x126252015400c118001003044031111068119601da100d505d810420000201000d10003401c40c200710354040341c19414041e20042c205031540e071030282150f4030070f010344240d1440c44408040500344600e0a40c1d0b154184459500403510030018030354030740d10501e41304580c48410745554000351079842c00d0000035480700d219121241d03800c0c0b002007000c2c03690500400040a4080c0108807900e41c6428440c00e040c01036000c4004d08107038801e000c5080c0d402003074810054940800085c440c030790240040c2c02500052000405443d0742000700b000180c0c150b404111810070240080100c1c0d81d803142c1c100300c00501c00d000c14144411042c0f003048100b0350188180e40c010301c0c120001c1401556030340070445010001e0070840e220b4008201043d02801c2c1080317040e510000c082401c1c80f445203001b60040c1c903449031003d182c03081c0043c280001c0103180290125940d11041008440744401072441c010100c0c01c040300031800002e2010300024130080b0746401c0e249150b03440c10040d021f107850084500d03ca030b4401003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 40038062 1250 40036812 40036837
    0x90601020c0f0a0f0806011a0913020a02010f02040e0f0a061a0d090c062a0804050f0d0b090c01020f0c30060115030b040606020309130e06010b041a0309060c 69
    0x40c0041354084403024204000d09456000309550b50400310170052403100610411b041800500c4984190342d00c04070301d1401c00c41e24a60041e03948120040c22409010411012031525000140010b9800c1c502c055061184084070007a618035101d68814906642143c4620321454428000d418681c2c0d103000010100d00714240b40000e546000c0e130380c50a9920010b540010003180c1824a00205508e81d11810384240c40511a41c0300024400d590b24480380c00f5074000c0c02e000c0c8a5400110f85591941486040d216402c8207110b00946401c541840e5603131300300c04a2a005000e070700403480c0103d1000030441d4003294014030700703400c50005005c041c205048050200b0700e50701c00740c000c1040c21038090120f24081c00d040ca8186414060384040581521000c100b05401546086070070441180e0200a85000a204480d60300b6130300b00c1525004c0242c01c52460240c010701a110000402641c00300003401218611410242e028911058030003050101b1600d501d115045200003804040c46980180b00c02450903 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 40039312 1250 40038062 40038079
    0x30e010e0304140d20130b0102060c1b160503010e060103021c0305220f050306060a0e1504020f04031a01030c06050304031b060501031104020a02031b0304120602040501030b090601020c0f 82
    0x5840312102985c00c003034245084100c0001528490038890300342d2070600e441000174031950f0b184000003951400c00034007140600c5400308441d5440c1c070310001c881d1815590082200c2002484118103040f40403e803184611942c40c140259440710004901c1c01c4c1284e400401550000d00c411441c100719525a400031005c00c4000c1110340b410f101c41d1b80e04481c21813004e480f854001403c11541500c0c0540c0d40d00124401e910020801c881c550703500b252141a03136038080300007590340c450030040f209138200c04810540c4a40046140e0014120707a101030402c80f8007401000006803072180760150003050a00000e04440c031020014000280a5030046030010b01c2841c00b0f80d40e04200001c013403081004c9030401c5036100d032590010014454502c49000101070121400c5282822101c03000c0c1d500c3c8251481c00b6281c0c07825103142001c1c0d42003071055034014402d4103200d0b2140a0b441c0f5000c0000d500500882e40840d103003a140c08034034100004540e11807081a0000c04401103035004001c2e01d0494100b4240e4031000c070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 40040562 1250 40039312 40039339
    0x60b07020d1406070309020a091e09320c06040b0f0304030c06050109091a0601050904150503010203010608070f03090b01060c171902060c0309070e070203040905070c03030e010e030414 81
    0x10080f5604c10f000c15540010b18001034170410070000d1841d13104c0c1003c1810483c0340055680c0b5404080c240703091810780024412481e10701546100c1a0030844200d04140c00310520282e03001811b000301c4071851000b0b070b8160241d05d500b000305030b000700c0c00364040118080c4012208414030340c2c011034105000303040c040444982540c0b5001610001d03017002004d6900d4070b603076a04100d1100d49040010001c2c1800344113a14011000801c58060401d40a1103251509840f01c6507003541c140c080c02612000e4025540c940c1c59440140011600b540c1171400907009102c2091458482e11400c1c000a501c102c11401a07440e268040321030907010b04059410100300c0600000d8801084010000965800200d11030b07211544d00c06410480000d250040e44a41001017010b00080880c000081d114035552002194032480781c100d1950103070350071402002e0301d0581480041c90b000036001202c03910958090002c4140002124260f80214084044a0f0b1083c8814404400c2d032035543e4554800c0170380321100c5c500383c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 40041812 1250 40040562 40040603
    0x60507120908060114040c0903170904021603051902160303081f0e0114010305040c0306020304050a08040305150a020c210d02071109090a030903020d03090806040b070201050901060b07020d 83
    0x80e030100b900c11034030141a91715820036001d0464040d89904001d1030709451910b070200c5641041c1d4002642c414001420341d034a1b5100d5040c0e4401c1440d401030004440b0301894050202d500c4180803c10344c0c41e801407919070480c80080d0403960b1070104004181201d10303640d01510b071500c0141c105941204c00c0c5c42c60700c8030008010b807424024034040000503030651412070044041a80341d07000d9410541031104110100340d2240314901100c1d409030300107a0380d50719401c0c8903082c1180c11034024603010000900105022000544ac80403d5440030542d0f02903c070103218204911503031030b208001e5045400002070039038441c612922071850302c0700001d1800000c091480120f034001b01c401c03225040214400080c40c20410059640071270b0200041c4a494140d44000e00010341c0c0384002031080c43c039201007100301885055250002c1140e4000c8950a0034681b40015003d0b204a4616005620300000a040ca00e1f050181c00b0480341098501498070410381c09010105400740c80c1510010201402803512a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 40043062 1250 40041812 40041823
    0x30c0a14040b0103182312041505070f060b03070510080402040b0a09090602041404092a05040507020607080609060d03111501080d030e010504020a051c02060a05070b010e01060507120908 82
    0x248681c0c60964800400351b954015805c0900c80342480f80e1280e58066a0625080300319010381d940b010060401c01129242111140301c0d920004000b8002c21400c9410008d06030400740c10300c107046003554035068541e0188400c4000c420390040c0010003100105015040c25408029260405000e160805442c0c00d455815901e1201c07003102ca190f40020b04100b40b040300080d020b040071088505101e013110a80311a010882c0c40c105c4101c0780c560007240c1c001200300c01000b5100900018006000503d048007006e500c8041c101d074580d000c503144400080c0140b80c903155452050b80020310304800a6002d840803217407541004403410082c4111024a01c801c4400031030540285254401040150409072008060b21070030308071008103a042c2004d200041c0c0c1d554401106a450030344800711140804440c8510039000b615000c4c0d006200001c1c201c01595002008100b4035005110b4107100d030b6610000d01d03642c54424031076800083c4d014802e03040020030100c0382900400040c600780340b00710348070200c2a0410 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 40044312 1250 40043062 40043111
    0x204020c030705060903070309230406030c031e020310020f070f05060603120309030a03020a031410140303070b06060c03130b19080906070e030708010504080306030c0a14040b0103 79
    0x703500c0031464004201040200d954450f000102a6041c0301071964040d02c0000c0c917005807050a8810300c41c81c03140c0303a000103440c80304000040c814001d041c1d42c1d040c54081000030f4041074504070a00c1141e10b18140d0102c21800b005c82d0b0181c010008541c2c0c4500034002508502020050260100a1000429050b482a01c5114020f40140c00c240c10034004051500180b101007141180040c0308206624801000f5640010645c0c2400f582d81c14420104500802055140840902c0c1c40c00611040300f04441c1a441a240300d2000c82004925200816a8a0003140310017071410f00208001006070074803d010300301501070b2500320707400c2c40d0041186071114611600b00c0581c0d00b1001c607503004032460200a42080510601304802d507400c04003007040d10750200400142c28040240301c40c103415242041100c00900c00d00000700814103107441c00341c240364826030300c091113841606803420051410b040d5200840717403c9100c50b85840d8900c401d000141200e10841d5040c5560f400b0850340e8016101030900e0903 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 40045562 1250 40044312 40044337
    0x50a0315150f080403171008061e0603011806151a070302011503030f0e01021006090203060f010e130504080f0708030402101803030c11040c090f09050606091c020402 73
    0xa0000010010028242c11080760308029009080c00b0100e84c10660510b100e0040d0400c24505549500100e007401e4010b5000c48064882c003020070401c90540c3c045070000c207016030548852500c401081509a608100100d405172102d414003200084141c0e00128400b90b010041c1000d65507500050580f820303c800c000d5024a4000509200301030f4203218000400c802c001103078000a085481c002d140c08510069072040c01080311801d07070141e0003080580c190310011001840102c1c0c641095002039001512117600460380414891502e40c040c030303290304803210040c2c00140404951000d45015010181c0295a0344008000c0000e5281d101c40c01000028001c0c10215521700b0f00384107200200c0501c2d21428200304c65001c02904850b183c6003508201d81c1c141c40c00807280b20036400d141402c0b00d491040c140d1f02900e008070b50b0000c0e82d00321192004480724580301302101c0d942e8081703142c01d03180d003110071a900031000c100002440c90149034000120a81a200344c0e010049130303002c41c04903408202000708 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 40046812 1250 40045562 40045589
    0x60126010b06070804090c170406050604270201090b0309061b090d060c0e2d0406050301060f0e0f0603030703050d0e10021b070509060d020102211213030e01050a0315 73
    0x11506c0b031070040c1c2110410f0340c41c000c6541903c81c3c1454400840c041c100900481d10f0b98045921560303541c014542c004661544201c412100140a26004d052044104d02081e519080040d01c9103064042da845600061b01800281c0e8ad8007034801c2da4aa544507071a161514284003c111948400c02c0f03444046100d0300c0c0000d0f02c0c55104c0005840c460441d01820310840c50301d40401c1d000e003400b5443c5540c90440d030600e18000d040b1000040e01520403600250340645c6440d03000035803001e8200c41d03842220380c44000c24480703031580d40005840440842d072081d0958810048600040e00c00d800804914a0050000803100c1c3c0003001c40b8102151100300e480001d40100f80520703980d50b03810040700c101003100005d03c0110302d8031010400d1343d00e0040c04144180196100b440c190f90090001e0b001e8025001410f00d1050380880e581c903001d03080000046001180303040007818079185a14407440b040c0d05030b200c4400f1050907000465541d84458a013104150f1601440240c450100d150000900344150703c458 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 40048062 1250 40046812 40046819
    0x30909020f0d060b090a03020613030602070f02040c020706090e0a110d050a15030312020c070e040305030718080606090a060911041505030105060d0c0203071a04050609060126010b06070804 83
    0x1e03603002c4d07007002d18140f204000d03c120344e0343d4034021601101c0d4107941c001e40f111750140f078800e0340f403031070351704c0a0106400040c0840400000c45400560240700716001c0040000d0814102d80c0d030f803450f004100c04103c8000c024803165501c1550b0a81c8095100c001084520440d401d9040d250042d07100c00d43c0307079a1124244245860203014007000c0c001c04541650754140346440080c052a10150000c0b100c56001400c440d12400900040001d020860107052450030503290080c55944216690b130000341c06150090620b901405401d000c880703400b8010b202c1d03619184100401c64401601100c000c603691000001e0000c0940103034042402c1d040440c94481c2e02d040740b1411a40c0c803810305402007010400c0140084e03a1136606482c4103040c1000b00140c600c03c0010300b070307141d8450744101409042c0011040114000074032030440c415172007141518100d0b111016041c4d81d5a001b070207082d0341480d00c00c20314440140501052400e28070f80d1000400c040c8039450200d080342e0300c01c40342a50070002c0003c050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 40049312 1250 40048062 40048087
    0x10b040e1e0d050d050402060d0603150605030a030507030f0e12100e0601060f1412040f02030115030510020c01110307030608070e070203090105030901090b090105060a0b120112030909020f 83
    0x2010755070080c100e81c0700724070b9005082e849070048020016a960002c14190340303c41d01aa81e505c00b09500c00c1080395101d050100c40c0748100d03980b01201900740b90000c146e41c01d01292107980700d54140c50707913404d0083d90741d010399510501e9003140c02001980108904e140d51000c2c107601c0c0d101121030207000f1008908004c08191202080b44c000650b011400402c4515440002840c2c1c285141c070b00403101c02d40150b00c1a032544030752951080000a1303001072005001512221000c441c1c030890003000601c40c0710900c585524800e10000d4203d4004222054003285160000d10744140902c00001d00c010103505140129041651500c0c002503032000280b006410030409200580010030400c4840e00d000e080003552031080520f0320b0304210000c80440d40314882504540c60b0aa400050080c680c9401f80150f4001c0c80100c0d40c0c030384503140d503100004a00b24200700700d07a1504a0301c10b00040c02e0782042003200c5281280f00044003002129040001c1c008910300c0686948a069141180c1d50403264502 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 40050562 1250 40049312 40049353
    0x18010b03150303090a1202120f030a030f09150b121903020708190f06020c0f010e07090c0504050607140313050a06110d0e010509040e0c09070c0b0106050309010b040e 73
    0x107090181d0300410003401140e41c2c804031041154043d506182c030602c4c051001c9421040005c1c2180c2c510311903e0041051041c000c0080c0c481028213035400c003c0208103a683c001074843c05075000d84270651452018507491000c1d044102c42078030140a0340300e50307d00d038034580b4a02b05210400c0f40d1800c0040440d1020160706000090090500b41d000f030803141003a10a11858208422004007481c80b075040050070000e15030103603004070103003100b41d403013401c000d21520340a130801c0290b5401901a110001c03920a41c503100d41080d40d4000c0d603401d030500e424503050001c00d503c00d401c29a00d5503081c00c02d05024910420040000b403803010340d20b421230744c504002c0c090341540e290041414442c4005c422503903200000764a40d00a400c5240c0200a10120801030300c6512508032840d1300242031032404241c0c01030008800c5c01811050710b82c4080c40c0c0d18440b042741c900814000007032140c3c05c0c3c540100700703c5204e1009190007141c2c60000042920702400050704945094200c0900ca401410808080100120b01c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 40051812 1250 40050562 40050601
    0x90a0315140609010902031003020d03020d02011b020714040b100c050106080c0f0f0109030503130305100204050f090a0f140403120506010e120304050a08061008030403020307060e18010b03 83
    0x988100e07a0600700005103544205004101102d5404000030f01038020200b441d80003140c021b424050101c00c01e05000303489040300700703c0e40d000d58204a4005500240c109042d86040c1403940908043c50601c21003600b06085001c034183c1c059240da903c0042c0740c0e1200c0110101c84025100c005e0040c3d45444c2550964501d540032420a030051401c1c40000d444030800d090741e44000301c0307250a9070300c1c40b180140c82107007035504040e015100c0441c5c0c0c1460485040301c00010340340104222011781c3c1c4d8058078241a071042d8011950069036003082408135061140c2c1460b0464107905003c259102c1038003c0d80308039014110f031011000c00c18010700042c075801102000b00d00d0400750050106251010019100140440c0d9250160031501c2460f008518103005440150900900101100c1d949070120340d55000c007500e0003000c03124036400000c0c20401c000211000c0b25805800303800d80f245404c00903a10304084000381070300070f1117458254041004814400d8044c1903000703200c1d9103909000c5560182140c0040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 40053062 1250 40051812 40051841
    0xd0209100513050d14010606082208040b0c031603090f0506130308090a0e1008060f01030b070e04060b0705010e1213030215070b01080106030506060405011508090102090a0315 77
    0x842401801d0b030321500d2038183d40341030711442c6220040d4600403401c64a0034080384d0883d441e1042c0418800da000c50010b018541c690f11568201e0100c070400564404120401082c240c0b08010070407280000d00041c1444640c54029030742086900d401002c55030002c0181100000e054900504c00055031141c8000a02410780b0081d003001780d00090405c4140c0b10340005807001d02c000c2031408803a0b840d5911000078010018400942d4100820ba03030402031228001c4400318021000040c1030024088000da040303e030050740309074090725404000d803044015954181d800035192800812142c03c00801000030034402c10001a10f0030104040e00d081540405820f00d10b80d00c01c00c0244d01001d00600008103903034040340c00d03044100c01001c0f082c03210310440200070010070555000207001201944400308581c003071019990166103010800003107810900403404a4080742040304000da22a15100d40d0081e01c220005207484902d00024141c070040798012205924000e45103000346240780104254401070b132 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 40054312 1250 40053062 40053067
    0xb010b090d060e0106050301020a051e0702090f04020a170607080108010209060f0310030f0c0612020a0912020307030507090c030e03120606070303090602040603050103210e06090a09020d02091005 86
    0x8800245920070036003806044a6242c1c030f1140b25610080d8070940c001c0c00020021035565031250000362554006030034203896401140030720007000d0142c508442d02194000c0c044480d542c0d82c0805c01150b104040c8c8240d802c6064901c1c041000c01500340480d0341c141d4088010802842c22000040034002e050f04420416401804001e59948820041d5426540b07000c01a075181c1e520301c8204501000d25030300141000c911080d0b01e10a2001244510040c3c1c0c00659469981142011200c030903441903040b01d000140d044181000307400305190b80b48032614401415143d80aa50740c490600c2c0c00d290340c10244c0801e41d0742c044c210392181c0620a060702031107201d000e10704200c66040c68030b5034004001c0003d4050203000450008040c8aa80051407140d03104600310340710b50311014010300500003400211000d44124810000040c0491440c0c04000e03034542c2c400d50f80000c07020a010300ca0b0030980140303400010580c404290507459002801c40d51a058200584034801c21080140d584540d803414421310004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 40055562 1250 40054312 40054327
    0xc1209050f10030e0601030822050a0905060d02040912091202060f090112020f090f01030e06040602090d020d110117090712030e0306070f03050114180903071e0b010b 73
    0x71000e039050040703011120300100c03621181054024100f07070701c013142250041500110810050001030401d4151280364101c07034041100700101d01030442c0c000c0640c02098407100b0822060349070001036001c0006820750082204039404a07056501c0500101d5038051114a044850b130b0303020003854000e10491602250201103038000c60300910a01c200010366420014070290f60364010480c07000c40e003841c03101c00c55480d8002c544586990700700a0301d09101c2e0445c10010300030356120b80168210751200e42d0107000c00e81c556980d940b00a600211919801041c035070030700009030f0b5030818200d02c5903000c2d120f0b070382c0c103070308944001820841c00c1c000d00b000300c54800090141074480015880142c8140341c0c403010800119040c20780b4103410f440c001c95030601c21481000b02007a440031803401e00d0b52054030203101507602c43d0f2000a000520f82a26a080340c60f2520046005090302241508000d214054902e040c039281ca5100400d0002092805450781d882a82307020000345900c00d90042050740e4010303041841 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 40056812 1250 40055562 40055569
    0xf081c0516050721090503030301060503070201060f080c01030b04110c0105010305100513330e0c060f0a2f0312060301020a0e01180f090605040b0a05061209150103030c120905 77
    0x1c400212130300035130810300100c070b501e4042c50400c1c000d4000103040ba030700e0350381d60440244954000c84500005509003103000aa040d104a5605e05589140015050440000c030045005100d80704100d50700549649000c208020300710000d1580c08501000843c0c4c643c11418006e00d0071403621800c41d0807500e0501001050411050080d46103a84940a403180401c08480c544c0740c07408500381700b00440c81c24108803c2000c1035601c00320080c204030341980c950400c84410440076005500c0c0754180d02c4010170122245910442c000c1d040b003490703450400403002e50510b04850700442c00080244c01c1c0d00010303588480038119411507030b0121040300207529000700301e000100450300d2a4141410701c01150310300080b800c40030070040060482951f121a21a0b81c90010001400081c401d80740594503040b0a40300704d080240707241050320006000c95103030909088402d500400001c000356400c0c050303182c59803003c654404e245402103000717546141e103a00880c02c0c0300060940d0351030107005000b0200300410207900c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 40058062 1250 40056812 40056833
    0x50603060f04081602090c0a0314010b0a051c1407270e0a1b08190203010308030c0a090e070504141801140301090b01030f030807021203040f081c05160507 68
    0x16440501a500d134a03030031140410740401004003d40c4900b107034041040403150304002c3c22030f0300003d80c3c01344020a10100e80c0302480382d0230701840c41000070400858084502407801881e08290446403c812550340010100480381400041c0c14045894001d000c146c951000c017003602c404121410004904034a00311020061591107864002c6040c800000c0441c42990b101d841e0340304480c40000040000380740010503002045900c92003141c46244410962005882600d05903031388030340d0b0b00d8038544a91100240d0780c3c010007203041c00c210100501042c6000d015040501424030342d29143c0e1224108242c1c1204640003042d001c1c01190000340c40100340c42d034200000d0444030141114240e801103c00464054004420003810031114840000108040720f600c2442c1c1c68042c2d80c0740205600c40030000c036168610f00000b078031070342d0703007400840c0107c0c5514003001d032070707030700c2114200d280c41d0301050a48100048020b200130300d0f42c0e0f04c078100a42360070f002c4111403000189180032807810031150307101780042 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 40059312 1250 40058062 40058071
    0x501051006021b01080703060b3403020a140304120506011401031e0506010302040807030302030d0c020303040203060411030114070302071205030601170606130e04060b0d02060901030c090504020f0c01050603060f 93
    0x80d8008611b0050083d880b00000e0109050071559440780102d10012001d10102c050740300070100341200c4201d05683c250640e00319455409002410300c0c90b12950003940c0340b0301c0d5075545404100030020740f42c020b08070a08801c80c404c034041c2c5040d40c5004101d6403007610401080c2d0600d800c058401110b40f416070000e1209025503000001c04c3e03162400124000d00540c0c010044034450200080107054001010b86942a41890140055003140340105d0716404240e070000d4142e846000401c0016845480f00040924040c000103204421980d012011a4050b02c004021039400148034040c44250180744c0d203100303c2c44c20726600d1400d1110008112580030302d0743c2c001024100c40420950341c2e600b000c6400c20003090014050007925002c40c0801c0c2c28080e04c088481c030b03190081e05006410080890811260010601ca090180c1c4000660140408201240400000c40c00114040e96248041e1501500f00d180341500e034048500340508440c00078100d203200398410b000b04070100c0405692683d10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 40060562 1250 40059312 40059317
    0x80606070b25030b030610080c060705150a0903110f07290304110a090902010c02040b01020c0a08060a0c030204210206040801090b160c0b0a15030f0501051006021b01 73
    0x903541c0b07030b0180540c03021041d900000800240904284842d81c150050f4040d0201241a682c0300d882d1207080d440005810311400f142d5820404d10100380e4a0f05c107003d492124021020b4640c140410301c01400303240d5040340c141d86e509a96074800c0302499444480c50a00f441c0300c2c00240700c1c48244081c9503907501120701c00e406581004400081c035403140c03c00942e108441c444402c075164141031511800e0300901030011030150005820000e200c49040c02800015901a180c41403940d105409100c040d15054038041d040d407188080c44961903c541502070018481d0001802180c18100d0382a0281c580d40c0e6010020580140b0007446042645034851070601c00244880c55505503910103d072250103107a1042d20b02c1d510f002121030510804000c1d00384102c810301e18107505160f0400c0e06803200084194042c2840503c10001039001009170301000c268030451818075030942e44d03540e4840003c80300c000200c5443e5103a0091281820000100700c02406280c0041c00141c814045000d00400340300800504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 40061812 1250 40060562 40060583
    0x608010b010806040c020f010603080a0305090a03050a0c020d02030a0b0403030b01050a1421010e07091502060f0903090d050c090117030a030f0b09130309050105090604030602030408090d0b070f08060607 89
    0x4516008110802081c5031f20b90003406081c2e0b0306c4c1485485600320403c505c0c04030341070400040130081d01146528402c0d03030640710f80c3e00381a046001100c50100903001207030807040071040080541d800708502d5040e10b2086120803440d240c2498010145d88401420318107100091000010603a001803608800c1b00c1c05903d41912070006200c440c6110145071940c04410200b5000451450220342d40325110700c040e600d03840d58065072002030040600c814a03101c0b0068120f080404d4500c0c031007044041e0058140c40840741010083c500068000501d1842207500b45d00081200705242801425075005103511720000c1404012802d4060301e91140c00c6c1d80300c04143e910300b0001d00c10a800e5010030300317080028185c007409141100c5810050541107405601041680400040942c851021981620005011a420a482d40d51900d029410140003151041c40501c040742d030907199140442401405003824030110304052070058042c0e1500117000e402c1100b08020800c0c940c450f403040f01c1c0780c0ea500c05080d05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 40063062 1250 40061812 40061831
    0x319020418023009061014062206031406180402010804050102130b040305100c09060c110607081b0307030e012d18050301051302040203060105040306050f0a0608010b01080604 77
    0xe4500c41540c418403c0c10802000380c481030b8580b00e0300c80c2e204020081c203c03500b686850a2485c0b2145030303486031800700b0440e0b641c5d0084c81d09226010703000507445000305004c0a540d4041c100600d40d15074000c01c0001340d882401a800a10183d02c3c26046007064803c000d113036080000040790100c00a2010f810f114806012604101d001d5040310501c0c039070301030a6501180c5482c2038200307035441440140c601d881046000c00501c405449001401038540d1942d07140c041c9009010342d48404c105c1d07416519113600c5085101c040d00d40b02c0c0103106540c4940400c80e5601e04888030400078000c000c0d018080780c1e02c180482c10000381c108040748a680001d081044410400e04181168512203140c00303500d904460f10ba04940d1904202500c10311183c0700100c0c01c1c600d0302c1e072051500f00c0e501221520303420020005280c016082541c0150b8001350185016072400313413070b52180402da500c1525180d810840110400000c4205442000003411030315009101d0300000c4030009010fa0000b0700030702e101ea541e601c1c808 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 40064312 1250 40063062 40063087
    0x512190318060905040b0102031218070b16230703080d020405122a0306010504020a030b060c03131d1b04080a0303090c08030f04030318051302031902041802 69
    0x60741c4541c41101e1030780ca80d9455020051055034184207460040c0d0401d41254115070010007580d00d401d980d0b040d500d15564940511b00040500d00c800182203000d075860205001001b40002c04d40c200c6441070381d01a210542c80c04040d1600c14a1900762071400d4003081200c060740108045080325004013105840720107460804009106540c8a0b680c00003000c07a89404007000441c0103840300d034100810511081c6040c08c84011181d00d540101da060b0002d03801445a40703083da0180c010030905c1d240002d8106041c9000c654550301c0803002204590003c120003080c000c03200b01c0303613018041c1c80301005840900d004a00d240718601034500700243c0010703454a9040480e010a80b0014581c3c2d07811240b5000345818042e004060420007550000ca901c100450b814000000300d405c3d1a8090750010300e000e00e0754404036402c02c0305080ca8003003a181514000b5050351413817050300100700c024a0050352030a0080b42201500d124030901815940140020400404165904c092440700f50001503038405c1070380c0d180c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 40065562 1250 40064312 40064327
    0xe010e0703021213061a01050901140403060c1e0311070f020409050102040b07020a0e01060503040f060905120a0e030a08250803040506060102060106080c0306010309030c02091f05121903 82
    0x24090202c440404c000d0080e00103c80000410702565007003103034007050304c07000903501400910302d40824020804a620f030f5108255201100001e20304140c00c1070342325503540c1c060354500301e2514001103981d01441c05048809000091514090408120180003920241c030103010384034001d031015000340c1e01e00c0c0039500d940d00f014121550010085559545400b840c06140c1c0107a9400d90040c1d5106001040c840c034201d038050306039091904c0b61411543c481d620fa0511100401c41180d00649032032240c00000c00400481c078005120203000342d15a00071704001801041107031142842548000c0009000c60050801c648440400a1244003504000e00da034101e06888000028007800c0d0000811040c44008609640991001d90a0300e01d140d9072030078100c80811059401e880070a2080010440340d40c02075100200d1a071080c2440302c02d14206030000b40241000f2150381a88144404c185600d1100b03400c4000c3c040d00c0100e501d00400c207401402c0c00d5031007400301d01e800002d171420a403100525001d1842e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 40066812 1250 40065562 40065577
    0x1081509030d0e0f010b0103050603070b03060a0e010605090906010c02100f020304080304120209060d0c09020a1407061a180a0c03060b0d020c0105010905040209131103190507050a0e010e070302 85
    0x1051040401020035290344444c00408186070703520b4090700310040c0d8031a00aa03800b4440042c020181c080c14056007020350740c00907111590100604100140781d88948562a000300300c5030308c9298407030502400f4070189030b40081003141001030000300f101c010780d610b54220000c0003852030040c0000070507030000c2e40b0f5403189030014600e610011030300080d0351000c002d110703048038400e1302e02d09540d4454600703000311044040b500038040109003100344141d402030303400703052495064640003001c59100184c200c800e602c03100040c4c403469240e400b11a58002c3c00010449200425103d412000c51311007100048082c01500d00c81009841d120007050b01c45c4a81c0203000030340ba808035007541d508203001c02d0000951004043e81d509509107400001e182400e40302d49482243c01510403440d551f00c1c0e0001807803808406c1c804440c5801044844503070f54800300990b02a4440000c50000d141410b824414076021260740090300c0b4a0007918207000101ba690310103811106101045072036a25404001e50180c02800c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 40068062 1250 40066812 40066837
    0x812060402092806030e0a110312030a0e0d05090f0f04200703030c02060c0f070201090f0f0305070806060d031b0f08180a0303050a0e06040b0a080613050108150903 72
    0x2150041c0c00c1d0484580ca40c800e040403101c2c951003684d5a1040d4151816070310f4483c1e207500210b04440c08650040540a440302c402015180d003c00d10007040c00311600155801c440ca56074403003104504d0340e010400410703114000d08016050910320700c006a01030f480d12000e075009030310321400c02e4200d07120364005c06159445050b6801c45031103020003040a5422981c001c0c0d00203418010b03203452950001c02d00b036000d50b9401e140c0600e0204d048400d04c42d034ad88051412030401c00003100c001002800d0b44d5125001e400160300140c0d902d0f203141821072610a094102c0c1c0301c503400c444203003c5036980b00b03a88001d00a602d801d05000c45c0d003180074030b00c00c0e031a0f0342c503805800003070b10b44814410030000710006c0101c20807041602c07200c0d1310040103201c00031145001c01008a0010820020118041c1001540c420b00040016140640310301100c52150401d41c02c030404107070b0500c140001807400454040c0915460b2104112a41c0340c445032903621440d814104c5000c440c4d07071002c600040000e0044503e101e4620 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 40069312 1250 40068062 40068079
    0x11209060c03020a120507090e151201061701051510050c0a0506010509070c02010206041e080d0204090c0c0b060f1305070207170a0308220f0605060a050402030103081206040209 78
    0x10715010b800ba501c101c8030040005da802602c02c80400e1240300d100d00808556030b40c00c020604104a40d40c0c00c0d800600349a5a015855401e400d2541c0e5003070b81d014101c00140000710b4182c2c949062401d04204c07092001005034141403c0080c11140010240f8080794202c40b00c0300c55180d0200c2c156064841c4840680130f038018074095030180180050600e040b1b0780d0645040c062640c40c400212401502400c0090040c1c00140100340490740c0119290724546509640084402c91581c03007651aa1000ca210f0300a9600810200404c1842e0301c68500c00e8251070400d0481010255502200050000d100c2807161a000400f4081501c5940c2184500034000c14200003a09001c0c00181d42e032680c520805a03400255600f4000d04c56010880000495046e120640e43e81c550500c41a40d0000c9030018a513101481244403020525032041e281b0342e503000300740c00616820020180501440b09800c0706005034010001040050118000c4421020701800203e200380c44640c0010064401c100480da07012010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 40070562 1250 40069312 40069331
    0x40b060a090e160f0c050c0a030c0314010b0a0603091e0b090105010b0c0318120303040b1009060b0403060218030709020c01230606030a02070605010e070f030506090601120906 77
    0x100d0700141c2920840c0840c0c9085940d500341c1d003440c0d80094001d40d00080d281e1404011294003801c4003c1c0f4151080003500c42ca81c0540c008141f0001c450340c400d46000e0b450b01c00410521014180798022803071204028421160510082a034920452166004042d920901403042c0110320183c84900c41d462144c0c4075160403242040c20150a080c0c4400700c4551802d0000a0501074000403600918401c402460501444905c0c14040900004001c1c0c0c00c02502c0d15501080c01c03040c401148114030450305807a280c10a0b074020588013941c0d400005086242040500480310507005403001c51b42e102c080981d40b0b09420161350300850591032090782500c41e000c0c0105800c01d1540241001c55008030080000d15a4070403100b10900c01710b00320450805a040104100303041820040d984416426809494071407148e0b554021034100340c1c409074551508400340b0419a42c404d44003030b016100380c60706008906290000131100302028000c54144019006580109902604280f200320b810030401c0014101 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 40071812 1250 40070562 40070567
    0x70302030c100e06180f0901181e15030507080f03041502010b030a050706030c0305060a0501030e1203040b06090609150405060406080714040b0607050c04020304060905010c02150108032502040b060a 87
    0x1640001d240305a04030000f520f910b00781f43c02d0940c1260000c0d00034a50a0040c0242c80c1c1c0209080c0c1c500c94420200c0380c0a54040d282503002d01e545100400940000441c554107249003010301c281c1120b0501c0d00402d07544100f2038000010345058030032901012a440f43c240324180d0040079500f00140d05030041c100600240200400c80204542c240e460500000d90148011801c464040761540d51060490740d003440a540300b503001e6800c000154088a078058107084507603556400c00c8400302c0b8100078020070031025050195610784c0000042c1d5440980e810041e210304449000c0b15003403401559101b001034110354480c4c112900816160041d6010300751039680d40c08181c08c004000c0d03070080d810440207000c035040180403907001c50f130018041e002c1442c031901040040d600c0580300751903440d100c05151020460a01c100d61a59146070000c1c10400524010708036600e10581c4418215002880340104091070441e2200071080c069030340902141842c80060000c2c41e001c4a11038010b84003040390808a0b8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 40073062 1250 40071812 40071847
    0x2160b0a06081603030207030b04031b0f03030c0c0201050720060a020c040c090302030601210212060711010501120305090406030b0c070314040f0b07020301060503010c031a03070302030c100e06 85
    0xa9a0740103540505400c42c80440f51002507100c014010fa20840c801c1010070069985c0c19046072003440c00c0720f00091500300b8003d0b600030420b01950f03070b003803007014034010160148222a441c21050600d24807141c40358001030500c0c000c103d0050079101e5202034035202c030720501e6080000780300001c020588588070a040290348868030240240520301d007050000c082c074007400d40d43c011030764028000c00c26682448180405028448451003544000010036401070b51182e00500c9540c54a41c0180030b9840c00d124010324980556004500d41e9140038018460000f80b1081e4218694050130882e543d400c1c8070b000704000b1310032a80058112141d07142441020a10300004003442e42c06659000703440c4038030f4290b1101c84c1c4100d10402c806003050740070400520703108501030070009000800000300e00b591240440c1c00e440c01c55480c000003e5481d000b8264500c45404500c075140300c00c2c3d00500c540c0381180d000c05e83e100521110303180f141c2c241e04000e840051007001e06c10000e010140ca40340d00c4251340341c3d000d074105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 40074312 1250 40073062 40073069
    0x5060c09090c0313080a020f0706030902090708040b0105010c030c061517030a020304050405040615091d0102070503030604021c1b110606010c060c0c02041a03070e070e0402160b0a06 80
    0x1c00d01800842c440204110540b801000b042c01c48a11401056440341403940c0700d981007600354000d20aa007100080c05001d5400204019100829040d8641c8100802028024076210602c010101440041510040344505441c020300344959004803a05040c1e031082d403c030740000e00036410011002c00c20721122420300b08a0b03e034400186074100c03640e80d40e16100d00803071141341c00503841440200618034103074102c40d80090090b100003450f601d40307581e20f1080c442c05030004c1d002c060300e52a418401c004001d41501499660500850620f1100c1d5101c41e00c0744805400f59118a40102c0c2c04194003d00015000042001450410dd003008252000e82c6039010b1803140710204043c0b0502c0041c0348000714105204040503540c4c003110490f00d031760701070080034086021420403031001c01c81c200585541c130412602d00262003100740341d20544410140b600c01c0039004159035403440380034000031641180703074a010400122809a100c2c060100c00000e0420410400717808400c004007409004052580490182e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 40075562 1250 40074312 40074319
    0x106030308011203080604090c08030c07050f04060e0103020d061103150312160f03180e04060e0a08040306051911030603070501031a2707050408010c080403080406020c0a05060c09 79
    0x1143e0340e481e41c1040c01d800400c0c0281c00b00d40d20400081c11440c1c0759100821203440717441200d5080352900d0440c0d107540c004031568121a40443c50030b00c0f9501d0010349861200c0f404950500240d400c003400c0c0170403000c3c10303c0001d011390b002c0508a401c024958119038012500b244c0541e072245070030003120807214074039001c2c2070081c000d900403000d15900d244200c170031903031603220701d03600c0031076242d0781c0056200030485c05504205d84252000360020201c2d010000401c1c00280081c005d0034142041811169211070041c0c05600000c22400003070050310a42d130071a9001040083d4907a1078000000602c0349507100c909940f8507105c1030207000b0280201031401003205808489a45031240019001c07905254201e8800d840c070003c428140d40ba000406101c0007410790710009200e00b034403100d110b41d00ba042ea030340c0010500c089070900c56800f0034030525585e400503151091880c2090b84001d44442c101030f20250542e600040c4070f4048540400580c040664000704442d06842e004084400703e81190307865910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 40076812 1250 40075562 40075577
    0x60c150106030203041e2f010908010e0607050c1f1a0d0203120703051e04030210031a060d0b0306010608010906060804111002070803040305070303030c0507050d0f0c0206030901060303 81
    0x10001e10034829680b00f207900440441c03801b0310b0f001c0d03c0501e410b0143c2c8110f4003504054010b00e007100e0381002010084142c030366001500c81d414800901a0b10b83c94000140a0b8504a4250804400061110703009012420040c3d0f5807814001c1c05030500740709000b114122441e034420386000b8a003a92140140040752582912502001c80403c501a1540c04000c0d41c1030b8041440c080c0d054010300d009115191182c1003440c5003254400104c4030803201a000f01c03191134000b01d010802d60074132401c8440c6030315440c41c0400041c480e004510002c81d49019000d070180710007056400c2044000e03400301185160080031590780d503940d1500242441030034002e41002509080700091518011000c1d14044d0ba44a15011410080c07002030080e8025003680d05400c40c49001400a8480700900090000d1401600038210321811402d01409031134044400c1c80800008224000100b203010070400940e07481807800c0012426940d80071980c5025041c4080e512500004c140041141c0540c0020202d031701c252035090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 40078062 1250 40076812 40076819
    0x905010506090a060503130501050c09040e0303010609120c080f06010f05010f0203030a15170105070e010c020d240e0106050901060306120b060a0b070807030e0a0f03060506030309060c1501 83
    0x85010b4481807640050002206000d01c07030044d40959445040c40e0000d503100c00079602c555003554016a4041d01305540080c084d02136041034020940486441c00c001c610b15490544000c0c00503406202e030464159891850504224240615500800e02e100444401c0815010819103030784003842511001c1c1031125001480b54081c400c0075142000c1d6401a600350742d0784070030b50070203800030300e4040c42413018241c0c000c03031010300189070402d006104074000546880c00000c00b8100403c00c1070201c2c140200305c841c0000680d25a90b0100c2041d610001e454120f0344908880e96500242c40c4180d80c4803030511400b00c9400360305501800c00c40d0380450b0b10075a2640e907481e040c1c0c200c4499002c0e5010034002125840b001c10084200d0580081c3d0251020f4442c50f0340b8030443c0b00a03000315600300c07062030f00054080c4c107140d4041d00d89059240101c44a4950600e4041c500403034160900c0001d110548500c0054083d030f84c18025280e0b032500c00b412880d550031307503551a141c90314503078000000d044e5a40c60021 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 40079312 1250 40078062 40078069
    0x50102010e0705120705040e030703090e0402090115030e06090a0314180d050a02041a040b0102150a090c2607080105040302030a030203151302091507020303070224120109050105 78
    0xc0c20701d5032641002d403514604080520001101c41c1102070164400c604000035282c44a1060714030300600300c0c005c0c41e12079816242c01000030130381c1d51021405d80050070a01016030b80300e000650440b50818400d07000403024000a03400b8100c0204101c009026007010040c1d00303d07002ca8000390061099a8008201002210010340c038082c1507864200da04828850324803905000040110003405103003100c0c081c1050750300040a5800d1221407112031020007102c2129800c003401180c0c8080b500340041c00444a6040032503511000042c12040ca10b07859110030b01c14404140344c20405805e070a542080005511000b48241002070588c1e85514402c50071700003030300d48040c49001e02455050307010b9440d102c2c44800c100d01030b4101030710fa903007105140300310440d0990b40c00d01030240003540c4500141c2c40e8040401000949801602c0495002000704603460062f5004821902400d070704aa61920599548414001401241255143e400d000081c1c08400b1510145614101c4041940500482c0e0722030061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 40080562 1250 40079312 40079321
    0x3050102091c0b0c1e041404060501031802010503060a05041103060108091207030807030f0f0f05060607030c02040213120c031707030f080703020f04121a01030b1501020102211005010201 82
    0x9801c4440348001301e41880409002003207040c0d0340782c44004420480e8a1616002da01650051000485210142c81c0509250150000600c401d00b01000804542c1000c1c0300c0224031448000d04101000000034085d03074559010001625028000300013000142850b01b107581d00555006010404240010f01451000900b5a40f040f00c0080c000c2d0900b540d55405882c03e0402130160414541c8654038850441090321410350110490000812415080c62421040f0380020300114013601c3c0800200b40843c2d0042c00c0b66134001c1d8190380c010782d2880d4001600480d1042d54000e491445e61142118003804111803540080d240695840c00900b2044021140c0a10400b0320040c0801caa002c1100542401000352650003d2682070251401c02102da002c0744c40d90141d00301101e1010824224410720002d401103008070654040e8081f0b60354115102c001c003440c002040100034002d080003000c400c2e40300b0f40569210a60032110240c01100a50f020380c1c2c004011030b003460100c02021000203840d07205028 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 40081812 1250 40080562 40080619
    0x3061401081207020102150c07020901060509012f07031a0f06090403180506130303090b030417031509130308060d020603011403030f07080301060f0203090105040b0d090c0305010209 80
    0x1801e8520030b03100d403100ba540110406a040d8002d42021900d0f904000040e948030b010090b400c02d6032075005104101e85400180c0050040210070b202c941070b180d8015985e9205100102075260608032864200041c01041d403003240d003240035805000042041d2100015201010340c40f05040f0f030780c0c40600900404074105c5149600205000c04034012900500c0d180030103030641c1d58086003544e11000130034030395030288a5500010703642541c1001403642c802c4100340a000001e8010b803031402c0c117480e841c0c2030a09014101e180804000003150a00700031403654625800060840300f01032402c1104050030283c800030607000300300c0c1d007030010f0f03014940b440c01c030344081e64000c04ca24250b909005104000d00019189141c2500c030420159005a0001002c3c24085203d0030a03142d6070f40c1401001011920b011305084250751090102484680c0c101060b50151a00302c7c51080d00d0704031445420300500b100c888040c0c002c08010101005110040d0014000b1420a548580d4902d122003116803d003214440c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 40083062 1250 40081812 40081829
    0x903030304030c1401051603060909151d0f010c0305010b03070c11030a051002070c060c0f11130c020a0c14030604140312090d0905011706010807030e070f03061401 72
    0x9000240103010721079280e0f0142c85400c18007001c00c5001381c210303502540d1000c545e0135449540006d0640c18000d410242410324410702c001403640e030b00c05803e42e082c85550140191a2100205141c1c0f0f10300600c0f4901c82c01e4012500c0ca4112030301da9030b00a080c9230b5000706c0000d0420001240072030022089074000c001d1590b036003803503c01984910200600c09440d041d81402810f84a44c04100d04004a02010004d040010713a604043d1404001d0a44664040401e01841020450200320200e450035012900080b80030104c240580010301e039050304200310705c841441c0c0044807a1580e80028080c0407e40b14138481481c07140c803003800251030716450413a964580d010100182c0001e00c1e0300e490705044074410044038184010401c0c141c10002080b51300502d82d60000714103801456011440304010602805c4c00f06c2c03058007611103126800303c0200303024141f03c07980c4041503441c1c0c826445011104282000d40c1d851680f9141800c1503040c042c84161085428000c140f90a0380d964150340741290940b5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 40084312 1250 40083062 40083067
    0x609050619050d0603030302040f0f0e070f090513050411040b151c020c0f0d08070e010f180617340c020a03060209030f01050709051903081306090b090303 68
    0x1201c50000c41e4000c010504100001408060307100b07041d500414018520944001d038a80c4e0401d03442640991b0564044002041c1c80e5008100c400800841c041e006100c514258410f01101c40d019201c4c0c00466101c02c2d04030308440e84007044c0c3d810950005025034850b503000700c1d1011010042105442e51040d89a52107204400400901c040200080c0802100315807000120044001407108a0304003850329038840c0c20640c00c5004590042c44440500c1001d07040000355400c01200040410200725411414400420075101a260180810750000c12089140b82c100546421000b8140d91445602c1a001c5280c031000c69081c008100710341250300f10902c0142c0700181c2c1402502200405000c41c1c00901407010305400141e01c542c14490080c3d07004004c050380d03a2142505042c685072410450404613450041407000b1079034045a83d8003182c8044904c0c04540c18200072a5041c0d8050f54402406000d0014a06200e110300070052f10840b199600c6070314003940c0d038859004151107a12542513158004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 40085562 1250 40084312 40084327
    0x30117012a03150e01031209090501140405060102030c0a0303020903120405032113030f030e0d110f15070b041101020a05060109020703051b010b15090603010317070c180606090506 79
    0xe52012000c10072290418400e40e070366594800b038204d020f800c1961841d1189404514072500818180c000b0007141904101540c940381030150744c1c00e00310f40d907940300315120380124178560f2003041510070f241c42000030384070b0301d80480c40d0146c003d500018989000b8060210040c0c040c400714010369044440140191201c048000520303c044a81d025000d1107100043c0180c00f42580340c41412000f55100310048151a1040c0c00c01501180171402c070584101407608003540000d17402400322500030002e58611083c81c942c50f000036010b0014850500340d000380840c0800c10311460804450046014518410b58280b40380c004907100c0700351060140041e841440100052141035000b424400d0280c0f07007050510500e001540f4142048000f400b400d0b0791035851f5002d003171412003109006291800516858521070001023500ca0105101c090300a000b5200e103da01c402c074041c1100c0c0d0b0b40b0342c0804103811180c1c0b29050711705c201c8401250840c01c00c1c98510b02180650143c0b172000e0685034014a00e0341007107031 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 40086812 1250 40085562 40085567
    0x100b010219030306030c030305030a15120b090c0409060204090e0109030912030903060509160b04050d02131803051b0102030f01050613080d0201021c020901140708090303030117012a 80
    0x81c4124101c040603510040000402c8a043c50301e400b45100c0d503511035690400829000030f68180900c01c4a440c0440c0b141000729422803c0041c0b0080e500c04546c0c10580c5c0c480811904041c0040c182c1d50304a42002620801c015003a030060081e244925000c00803c50b002c08014225108120024041070281d601401841042c0320028207451007450b00005060710384e40e500050f0742c03080d10304807030650101050400c0751100700b00320300181c43d144022038101460b200021386a104d44500103800342d03a02504003540320070240c2008011552112080460300c45a04d4000c100354030900344981032074450383d41c50304962018000c5070300481e20880f41c901c0503400c01003002250b40c09004400b04040312104005001c00d02805462040d8429800050700c64032404054a9000703600800401c159104001550046e82c011044031850340121102503110019450800407038030078558056810701c00800000780007403038050201c020105003c002e20100304840e0b480001c6000c06204290187e8145c4201e00c41180b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 40088062 1250 40086812 40086853
    0xc050702060d02091509100c0302031b010603050a03020c1318020f0111010c03050907060c0b1f0f08030306150a080c092d0103050c03070516020a1d010305100b0102 72
    0x1010000014504403d04d03000441d1104140701c02009980e003c00c0e0030302181342c922801c0c03080300c40c0760500c220111500d44d4000c0d00d038404c0781c0700000110031140c40241d900f607095001070b011b103610004a40f104032413414040d50302c00b61807244a2080000c800c0d881010551802001c03203150380510782e103641d4402d981c00c02c50104a0f460313419041046c550f2624802c4442401401e40580013070b100040c0303030700341900740a0030203c2c9030f04101c1c203021903015003030001110065010341c410f03c00c43c8110501c0c142e20b0082c000009241d4407102e8081484000424a80c801000950040a04a4407400c2a0008001e0b04c452406a8103000010414807030000c2d20903903086000f0100304030b00400030345d001d40b40030070004250503900c00b802c021404500c4003902c4558240c4100d41d003040c000b0008a04518115000810ba84100324011944c80e003007404000464840000c00d0002e00074041c541210303088101c21059185401b40310a48075403040100240c01d000d000c2c0305010100300c040e405461000300300e00400420f031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 40089312 1250 40088062 40088077
    0x220506010302090904060603020f03030f16020604050603010303050d18030f0804060209030703030305040210080906010b1e040602010e12091804080c0708060a060609180504031707020708010f0c05070206 89
    0x55003c20840c031065035680c00e103612030352090034005201800c50041c001c40e0800c40c40903501940c41008004054903800080d5038600c40c038a41e0f9807803003001b9132020030058081c540c800c03a000f11010001204054020b00a042c031000c3e203460801040c5c9584104a04140100340b0107000300e244e4480002d40b141c483da11240d4801e0140d040507150021082c0440e1030040f0030390055000a9584047c4401c5190070300d4203100c140c08030b290100c101c0c10910305140d01c411061003841004500010600740c05a00d10b0552040c10031030300c0505490325a10740000c0e021702142c80c0703810300c9401042c11184010f061181958036101c070150009881e0b031102505c004d1000b0020b0002e4071202000e01c48030740625000c0011074007410764140585018200b8a0540c003e0711059002765060010020003489044080309460001c0a100000451152207904055170802c801d1550450440c07148400c0244180e00020b484c0211803510b4000c002038180e203220441240c1c5603601c410000342c000c00012002d40790038006064070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 40090562 1250 40089312 40089317
    0x1106060a0e0a0f091502090a050d05030a35010806060901181d010203040f020a0e0f1303120c02070f060302031005040c09080615040b010203090f04020a02010b0904060e0c22050601 79
    0x448034640717521425441c07070340d008948503030001100c1c0071604040c0400d000814050311600d51002c4190b0f42d242c0c0b24015000390804100788001c0840d12040d401d400c900a95140303000019107250541040040050b0900414095100d0040462658200440c080b4100e0341c1c0340c4010048048070804005c0a041030141a41c05000c80340542c91a00c0020320055024500c184460a42482c0c10301c10301001010590107403582040810802506a4900c101c19501106e84801c4281a03640d0349410351b821410085000b092903e4018040d10041c1c00180b0001035030054031043c08440c0c0c1e5264101c0130791200b140c0100020207000000c014500786500080103140d00ca04154007210b46513a01d0034a0310704215020580080f03003180510309802d00d4810031070005400c0c4081d52a00442c607004c145404070303442e1083d0240d540011100c3c1c0d40c0c0d1003980542010600100a0300042c2014240074001d00a2025181c01e640100c54003800c1c2864881d0003c100c0480100d100554000071500c40c00050000030400e505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 40091812 1250 40090562 40090571
    0x130b0705070b0a06060e060a08070e13050a050a050c1812120f0304030e0a0b0307080a0e150406051005100c03020319020f01060602011109060c0705040207031106060a0e0a0f 76
    0x2c800c590414400e24481e400000c03070516103100202400c840c08880c90040000700020640b01b5800565154880e00074204081c1f1200001c0100e8110300f980c0068103c8513140106010302d10005804c003900610103c08140815103030190010698171403403140d550202411918503d41b4180045840b48001d02d210135503074840303c200d80a00042e03200d01c0b201c4005035800020802050740203000ca511150342514a0303500d041c2040807442240c4070282c889030510000034009420465036400c0100b52106003019100c0440c00c0c60bc001c0c4106030166400c443e80c038100740004220302c01d1829524204d17800101100d0100f01d000d2410f031074610b1005026011030100300282007140404908160b155401c1354002e0002203c1d50101e5421076115800c95011641042030641c40f00c0c070444181c6903584400c441403603031003110300701c07980c9880d00b142d1005421030f0000c42c901050503080541c003c0300e80620b02c00e545441e41c44070200034030700043d801a81c10070142c440c0400c00e604081d80c0004018010001e0028 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 40093062 1250 40091812 40091827
    0xb120402060708040f0807060305010b04090e1204090c0305091504080d020403050a0b0402032a1306090f0b030706020a030212090d020d0c06020c0a0f050f010c0c030602030412020303130b0705 84
    0x2984c4560003580a21402400400c0a6401041180e0041c919807504002c0c0703504116000d48107104600c10190020340f0780b40780d880d81403014800c1c1c5004ca14400303426681c0b10780d039019200140c1031001c210008030b4a410300107045c412021407400f00b038002614207005141c2e076030f58402c8140d411030f501d10500c0c00e0b400c0c0808000503204114021559010707040b028050300e0903104045c40c1408400d803055450342510358688640c6c411448940300d12108070307440100406c0c0748504030000d200543c80405000c0c1481c030b40043c0001d603540300002d0010242c3c2510181500c81c501039035104200100100180c1c0b0420001d5440ea0300040900320100300208400364015150b00051070f810350a006c05d488200811104002d82070701040b106e2100d0000f55588008586403a98200c8994014414140130352039080804003203a2061445207483d5901c0160081c03c0b0303490f4140f4400a410884088070124501154030304118000010740e4840d400c0441200c0d11031f00d16640349010144089c00040502034140500c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 40094312 1250 40093062 40093073
    0xf0f030c050607021b04020702030a230102031005010207050904050d05030c040e090c01110a020d0b04030201060b0d02090a0909080d090302010204090f0509061003120e13090f02010e06040b1204020607 88
    0x60180607264000c1a0202442d17002880a02008600510036441048048010384020032150070080d08018501251303050304080c00e5a100f840d07615a800d5502c00000c1002014a440345281695001e0382240c1001c2d4541052081c06181a036016146910035890b4102c0c03035128000856010501100317103070401e40e0358401420100c6003612800b496410180d4001d0140d68030219810892080d000200360b422000e8000c80d0550a40103c0907012200b10720000c0c0030702d4000d4100d8401410303030103910303507640701d00310f92002c001e40054a400d0720500c0100c0d000603989030b442c00366103502c46e0020200c501d04941520f92800400c40c0800840940d5001d020014603400680308442100301024404151841c060036540d003002801414091180c0c1d0f01c48090001c9412076909190b1542d05091108080d01941c0009041703000000d01003000905200010f410011108000c050a6200fa00c44200d003501c10070401c06c21307020f90300906103882c1c1c09016a5580360341110301d01d5007180c0080d01803480c0c0811511074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 40095562 1250 40094312 40094323
    0x2030a090816030305160c020108060a12030207060f03050115050705070302100509090604020f0a12060803030c04060f0f0210020d060306090c080d030203130b1e150301060902070f0f030c05 83
    0x100b8003460010700c0084241901400b0313041d4410a60344809450f9008018054007440c075450000c1d0405c545240000c0d01c645622200da0042e0051004d07040400c0d0351454020f548140d00e02a8a0002c4c0009010001c0c1901074001d080c141c3d00480c44588050784911401c035a141c001c9803084ea0b00748075174080000507884012000b0840070456642c41c0e501d411000a1041c0c90303602816090255104100540c03a403811941030720a041224580b0803000007101e554034003c1c0034190842c50244c00004144401c0142c1e000091084811079201c1541130405941d0584010180f43d00040258021082c4074440c00f034260b0040031200b100820000f00c0588a071165422220b10110840704241c02440600c240c0c5020461255804214035056155140c01615400c1c00281500010126809140400d8041d51002d9000d08940819104508189080044625250117110185000b9480c00d0004624005030317000300c4031440d8220701c00b400d203075855542d990002000c0e840250200b00710f40b880c000001d1000d104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 40096812 1250 40095562 40095577
    0xc100c0b0708011a12180a080a030902040605030f060703020309011401080f1515060a0912030309030807050403032001110c0304030606050109080a02010e060c01020703020a050606030106030c0902030a0908 90
    0x1e900c0030640c104411090130303200204030000c1c0a8420710121420b9603034003646030352151540b0107081c520718200002614110010100400c02800419283e1409a065110410041c003c680c02e0045603541c0b8107041d19800601844262078000c6400901117502a4000f1a04082c2c5000001000c03042c04110341035032802030700845800d4201c800c108140c0031042080080c003030b00d14445140213003440c00e25017440c0c400d0105840d000302400700301c00390341c28000c01c0050020255000003006141c400d1900034024080080100c01003044e510205410f40d1158098409403581a22464a800d00c0410703c4d4800c42c0030802d0949141d900c40036803840c0800300f5000b030422408014010f64071142546030280568000740c02c0300d0304000d80100c08004007203000a036108400d0302803c0203403a00311124007280041c4100c410030700e42e84d0f0000030418100b50740007541e131041c140688255a42515010201401e0b5402840042d00c400400c40c0180402c8500b507005680042501e100020300250903a2410a150440351 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 40098062 1250 40096812 40096817
    0xb090303031501020f0a050f07060302030903160318120501060e06010c0602090d050f060a0608031905130302120d02010b1f08090f07090b010f030b0108011406090a0b0a0f0509030c100c0b07 83
    0x115100099108001c4c1030080d085904bc2542545401408030742d40e0f000d0b10342240c2c40950100201e80515001d21182440d02d041003016650050b103800e03070301d04c4450012404540c90340c0b82c9040000c120340603840c11806142c1c142d484812400c0c0c0d58403801d0181d044404010351210058510380002041040040406c04201d0050040c1d45000c0e1810412100d80d5400b07800190020003030000102c0380120310f034111071400c2c140503407203220018465010304410740009420a591500740c42c80e00100050409000703007a5402844a1480c11043c08000c0f0101c082000140445200513901c00e4040c1d044503034820000d904941d00004a5404d00c1e241000b5035008200d030076919410a025964071407814a03410000d4141440001c09420008000c080140b05007820340d019603140c0b880c2741ea05c540446034105001000e000300d107504c40075084825480580075030007180e80310000c4901ca41c000c000303031507425100a0260030945074070002d026051440c87c0c2c0040400c91040c0d4400005451500070501030000355 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 40099312 1250 40098062 40098073
    0x10e030705010903170606040504020304030e0d050304050f0406180203070c0b0403050304020103110903070e0a02091801080705010c05120f0c0102120106090504110d020708070f08130b090303031501020f0a05 91
    0x10300340a0151000641e0b1582d45c0085d501c2040080e0312a60101d0b0111501682c00507503a50303c13030500b1281d074050081029800f400981440051080000140c42900e80031510385001e02c034000200400c441040c800c14420220f012800080d1070010b50185038000c80609110514200c10740e01c180405104540031400700c0e00200c1400155689841503801014511030007620707104403080001e81e159000d1050349246160000040c0c001d4a0300d80541d0b5590502074403480c48043c5500540794805000d018800e44e1344540c0e0000100b039071045a0031401c0342c1d000005018030881c1c101c0720f40c8295000c0d043e80040f180c4100140d0540b440e00344000c2c4078001070300218032415418104010900300184c1e0102e03102e1401c01c0c0451280303441070300848400101003c001a500e18180c42d00494601888101070311241d40000d9403030a002c0003600410b86100b41c0c0d224a00303200c2e166090b03418140070303080300075070180e01c180005580001043c0c141001030320140100c420540700075080c01d00d85418a0012245500503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 40100562 1250 40099312 40099331
    0x3060106170105090906191b120c020c130209030304030b0c090109080d0f0813080304050708010506010212040e06010908010c0c020f0409020d08030c04091d160302010818010e03070501 81
    0x988070042c0035042c110740c2c0742298248040c01503a80e0341c0150101c514a117000341041d51101c0c2c503a10190001030501700521440c00501d0b030180003032503000c080045140c01c004c4140425480400d126100200060079a0681c1070400c0301c0c000250040e03001c1c1c41c0c1501c0b0400020000c114108102403107070b0f800545803a44c84002c0c0000411455181c0c1c030000480d40900c454031601071f004403045003c0185440c00e100343c0e40d288401191550040d140240101e44d00000740014054017041010982c2c6c0c10300028450707034072410012a550324003441d400c54010030500c414410718040c003040c113400640524210b00219100ca13040d03400c40d030210ba0980c0101d40401110000c5041040b040001180200c50400c003511140c0c002c03543c07580d9040001031034010000001415440480e098030041d00114501300501e030410030b9200c032a0304021020050700e2107002c9902c220200c203600c08070709903035060b0f44601e001d0722009060906084481e20749982e40d501c030a48503040940420103010910f00075000843d44080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 40101812 1250 40100562 40100597
    0x100302030d1d060c01140406060501020d1701060809010b100e0a05040b0d02040203060607062904051005090a0204030209100608010509070c02130b04090b0601110c010c0f03020a0203060106 83
    0x70758076603081c0701d03038a840100c0580c05080001480d980582c0d82c0c1d0b9840712070100c29401405810300300d8030411008018801800b00681c8020143c07042a0211464000414416a03294100142c04003903104600010311025220b80001600422542e0000c9409949000021420600c0d01152400140d01c081030341001d00e4005550001000c05840411840d6451008901a1012842c01034040d03500040890f58035200c3c10101c40d0300c950001020020035410044076904107461202440b03006090f140403c071617141c01c2c89000d0007860f0765820200c52034605001c2c0000054002c1c21001c100741e0070b105c00400f40e105c00032411310072040040b8469100d802c1c00341c058620041031300324501841205040040f4039410201e41e4241c10380480b2f032058640d03480399444000c1e280240c089a0040d007441035030410001c0701003c0900485090325405d0907440d098104550760002a090140080c6032418401d002c00c4c4002020304a4034001c0c81610560340035034011034a452420303480440020301c51081440c0c240e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 40103062 1250 40101812 40101823
    0x10c09050a0f050d0515040804180209011b0c08010c050d050a060807060302070f02041404020306070809070b03040c0902040f0314070b030c1326101103040308040c05040510030203 79
    0x440d4091041e5091600c00b4508103030501030030b400b60000d405124140a420010316008400104109485150515001d080c2d90054440c07801c40652031504000420000d00941e8107400040e2340b02103c00100c0f044000c602c0d8000c031402d4542200035072000c149030b0400e014a103203c10322604c6260392840c20f4002a0201c480c003d10f02c500351031814000744500c1c0e801103031142c100d511600e0b0144c0c4465250910444d10503241200079405840e02e0f9582003d014180e0105100c0c0c8d0084056079056075402c4015195560202c60385000c03a00200014840050014050f58015000d1118076452a4a0b650f5140c108d0340a504044114041c0e4034041007001070000586603004070010143c0174079440d00c0b401031031341c0c04054010036850340c0c0400c119089409070245a0002c0120b58840c1a102114003580c6002c9a5404c0c1800c0440c080d2181004640700c103030081c02c860886c04ad0200c0d181d5070b43c60320102c0c0c0306000544200c4004000e5200054503a45501800c2e015420a90085450500d148109480d29 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 40104312 1250 40103062 40103069
    0x3040611160c140303190201021903060e0703060b0301060f050c010e06060a091b0509010216091d010b0306040b040507030b070801240806040e120d06050f0a081b21010c09 75
    0x1450b8040c03d40510707100842981c11202403628541c008102c101000c1e400380c0100300104031407055a40792070035003070340c503400c01c804603404a4041c0c601d07612000ca08a040d29401e008510443c4d07010001042000d100c0c21000c0c118800c503281050411203c07540703081c207440308110510095406103090000c145024000701d4010014103d0800c16011a0f010007101c00e2035800102c0b0034040c5c08280c0310856402403200400810002040b5020760b0344560142d4014071010380e03695403090700742c200c1d00e50300c1328148624002c80d40024014400b42d40d542ea94a1f4442800900480755405203140010026001340c8011f0b014111540381c46516605086155120010b0041e0f00806030076120865003100b6000303804d194104009030f802289441001c8100f07450480c1d030300d03011a07190030009a6840350450070b0b4414015110304940c0c0c009409407190410142e45450b019110340f54004541000c40c440350b40500e0141c031000070f444480034440c00d019604140243e00d012100994440c03400b00e185907400016a0083d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 40105562 1250 40104312 40104329
    0x12021204060621200a050301090b0a050709030b010e06010513090b010f08071d0a18020705010c0c02060301140409080301061e0809070e0414070b1306020c09060603040611160c 77
    0x54a0154031120013007006148140408058182103888035110f085808003d042c1c050300031300003a580340c0b82135883c001c42220340411482c83c00022800852041025004582c1c1200d40003c0766401d20400721060840a4050343c18424101b00d070a03207a4505081500081c55403100001c0e01c0300b51140050000071160031141e040240e5502040003954106071070380d070b1100c400b41078080561a140702050202c5026006040c0300ca08070403d04540303070160f800501d00c40b0f10840084c071503a0041c03101a070381c008004000a6100d4010300c014003012800c1141e2080059005002203012911900c9a0703840d5402a04960002005031141c49210b600303007462020f0b201084d150a00c001c0c5810640d95850703500600600017400c803ca4040307001e00c0300c01040700c401c0c1e0541c001550605a9100e0720300c40568004460200c0b80e203c00300c00007840500100b034400d1841005080d10310117580348070411007682d00007482103a404d03944035003161219400d58007800d420100c0d02c4007100140310a0501411120380c5c0d600c006007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 40106812 1250 40105562 40105619
    0x16030c150e151b07081b0a060801121104050a050403180501050a0e06040305010e0309090c04060e0105071410020309010f0902033310030b09030a0906120212040606 72
    0x369031030b5407600d5a9241c4880c403810780c449075210840a40000210220300d224400e4030404180110080b0700302c080e404072034043c0d456099459043c85040520f0340316103404140c0365001000002d5241580f940e009118101d005103c3c05910001811950f050360440c0305590344104010405410101094490507009402c0112519041c0000d0041c4501950700d02044512a04601181c17281c00c1540c001e594010000d00c044480c8014541d80d80e0050604c0307501c60544030001c5107413031040c10308480a41f841c40e07641c07071006010140152426030104000b11010741a201400405800520500c528440740b040003681d030341041500781b404e450914820300c189a140c400d007000182e600003041007044440c6e0b0203449190115500052a015800c0351001c00041000c08000c0c0c1d114035034400a0079644a00020301054640d08081c958038000c0350401d0000c42c0a039941886403034026806103141d80d403110000b500e841818620607816441c2550101c40c6686c5520b0180120038240d0040080751190410001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 40107918 1106 40106812 40106837
    0xd06050a030f061401060c030f14030a050901150506040315020f07030c1a01121b0902040306060305010e0c06040905060f06190906050a020307031116030c15 69
    0x111001d01e0041003507010140192a00c0c16206d07103580c0c040c18154a541d0a03201d42c2061400e01c42403040e00e00303245010681000045128458164010a1324101040581e00350351145d40210003010402c0014011615a1429202100d4008403040084601c05072442c00a00c41e03d5007201c0c00c0d1400140350401d140d000441c24088a00c80c00c0127440c070503000c00c606603100100380502500c0303a550040364000709101c0c0c82c042d120311290071340c84030445030350701d81c1c0c20220f900c15401180c4203502c1d0002041802804e00c203145003a01e2000207800c000c02ca100008110344101c0c0103444c0c2041c3d450300440c0c110b8944212a551018002e0041541d40c00c00f004001200c00e280c85400c0009282810042101841101920f80b032a1650700254240705840c0c1e000e42d5001d013201034215803446600b4420b10288101c40f00000254051040d504059051500344601c941007101d10304107000c035125041 = true := by decide +kernel

theorem cover : BRFrame.Cov 39928062 40107918 := by
  have h0 := BRFrame.cov_init 39928062
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39928062 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 39928062 ≤ n) (h2 : n < 40107918) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
