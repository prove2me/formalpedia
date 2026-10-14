-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2033
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:29:42.608859+00:00
-- url     : https://prove2.me/submissions/91dcfc1a-75c9-42a0-8829-ccc40c519769

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 365467625 ≤ n < 365647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 365468875 1250 365467625 365467637
    0xd020c1201091707030516050703061506080f0c0904090602031501050708120705070f03030903171b0c0c0402070b0f0c040b12070324180b03030f07060603020d12 71
    0x8203828180c22220981c00c0501490700c1c26500001d9001504002c200c01c50107803500c00c5c80c0c460b402c4610074940c10564002c07191580840010020f000b40c0c5c1c030900c05a0060004220140351070318200510549018180044080039071021801140d027801c2140d290842c00b4006012120f4581031984c0250001c4403030f100e0841100d011810607601c035804440c0179692140c0c1c0c1c03a080403034143c000725203514010700e020207200301000070001040c0e900c00c06280c594400c3d80e000c5605005d034500144403803400600750005c0c82d0b940c2d062040480382c80342402d007444800740303815445100e0f00c2d5665182c52040380b00c00c1d42007803000078900240f250100c0924890202e80c1402c030503c0e1100c0c0c103104420f206900c41c02c4a4100300740018244121254030890301b01c01e0034a40031a150a0f818200240b00764006041003803110005401c1001c080c1c05483d4030280003600c44100414182400820b0701e0f03129480342c02001e2280000d142c020891150b203c1e00155801908a2a100b8010310f40003a0441c4414010380126030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 365470125 1250 365468875 365468899
    0x100605030f01020f03130c0e01030f030f020d050f09010207051206013609080d1b0e010203090609010f1101060305030301091b021507020a0816060e0601031e140d020c 73
    0xd0500880740078040e44034a417840c6035950302101c0d403402c04000f800c5841c9500110700040c04d100782c801c924003850140040741254000e0749006800794000044d25810b5400001e8416101c0303404c04251500f80060690792030b0744101c0c81b00100d0030f01070690000340c0d03c545d00c0030107900c20310b02c00a14a03050f04c00420107171241403c1003480d201840e01000b0303a102440301201084a81c001180c00812080f40708001d450f0400842c00c8145050340c00d100080300f184040000049070459100c0d1124281e11028005913103013500b10000b18905214001c200350600c61407483d901c540714402e540502941024200812143c1d45034603019449030310170f00c5070784100c50904480740c043d0824440c11040b101102d40040c106480354801c070091998006240384103502a000d55900418510320003480400400404030a104001d890300b401100d10707048085400c3e6101c0c50041c00010f10050003445500ca040c0f507900d0b15540d45180c0303a0300c05551f03481c207001e013800b5a0a80f541c80a4002441d52a50601114015a402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 365471375 1250 365470125 365470153
    0x20309030915030f24130507020c010504050d0b0c0705030703050c010c03050108060703052e0f09020304030f120b130c0806040507050a050f09121e070f060f1110060503 74
    0x302080c4e903580d140c0d906401c003051000090428588840d8143c0c0c09018014160400083c0c4c0e01402d012408900c0b03866208000d0056030610800002e01c10909000d420036041201203850320111481c000d2914010901181030800e0040640b01030aa00400310382e0384030528500107100383c01102600785079600701321340aa2403a02a004140c16070b40c199006000550700c101045000e803501410311000b100d40f4284c1000b149c0411030020040c460782600040d442d03031500031144030f000c18580c00350303400d1031041c014040003a91160150411000514100b0b00d102c0184205130000c00100100681c0020394490101068069410803500c1c6101500c0340cc01e140e4841d404e000039244206c0c0c0400001d5404c100b0707a05810b001d14082c215031159080a00d0924051401007103032824502103421a41e841412440b24604252a0254090300c0800150940616224461800032028090001408034040004d2500c0f8440c80c4041080666402240c02400c00140d101000340654081c1342d00074011900e10394290 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 365472625 1250 365471375 365471377
    0xb0c120c030112020d03090f0f05030f1605360106030b030708030d0f0b0607030512070903030c030528091e08070b070507080d0e040506010e01020705120709020309030915 75
    0x881203910303d060340c03500a80c200072190300700300800c034103010610310082941c0c80d82090b00400307050030014580303495003050109072400e001d04c0169403441d413040441c0303070398481c0c0102401c0c101d130829604210024124010310110b02030000e483c65000070b0003810062103903000396040303040301d1180e20208001241c03082410723191002400380c0e040c280c4c410041d0000140c0e50f648140109808c88034002244525140010b4041d0b000c0b8406400044010030182e00b28140c403a03480750481c1e03050030581130b10351540c2d5001d01000107266000e81030000c045030300c1003988010070f503d40d003440380e281a01c10b812503002c80c06014600c15000e14541c628102c0c0e50f14411082d465004400d8510541c0103127442c07407800c0c0364880c1c030303510a000072500b070b0040f12000640030800300100401d03900176444040404040406100403039600074002ca04011300765204c003810ba40c02044a50540328203403103060b480b4071000b202a141c0040395010900c001e1000007003010b07001011015013a902e03000c88944080056040008010b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 365473875 1250 365472625 365472629
    0x70512180d0b150a180b03070e151c02060d0c08010501020111041811030702010917070f1202190f0c090e0304120507050402030c03090c10020a0f02030a0b0c120c0301 73
    0x20050700c95001c10000ca040c8003440c0e07103c8100801003c00180c940e03500c0c03144000d1116075400d10945942c00709000d0310b4240181e40150891410001c2e131842c184540d038401c9101e1080803801100f082c5280c1443d6485103004002c940c2c3c0160420342c0d101e8100383c071240101100901c84000841090000c13495601c10301820f40000404015642041d041c0441c103c6d416045000e40c12010350b64800c440070b001074000c083c52041c02503070000507808440c2e0400c0710700a1451249034001000400032000010140c1d0211024a900b140c42d10001c0c40e00d001090b8540150500146a8008034525038810045416005c407107181c480d4840004543c0d0350b00c404000d46000c1503d02141340c009100512200d010040c0200080f0302a4084070741c465620310120b000c80e4420713540000c0b100d40c0041082946403041041010383d070f4060700d40511058031404006d40b50813a4840003030800d1800d41c2000103540c0e0800c074440f403075030b04013800103003d013000d0400c45441d9100c18940e800b00a49000001c050134020410790b81 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 365475125 1250 365473875 365473883
    0x7080c100b010f02100506030304030215030a050702030403030503070804020f060301090f0f15030f060f06230904020f04020d0912020c09010e01050102150705121f08010b0f040902010203070512180d 87
    0x38003500e40d01c5c201e101a050084c04290103200500c40000566144403c0e990000c40398034146659040c03103191901647d0b0010854800d641c002c010800000c0c1e07200084a50014051410020a40311031000071807400140404070ba0105000c0008105001b05070b00c84001c929002d1001c0020320340c0101d001090326503214401c2c610464850f420800308040380f40104030319104070000144a1a150010070454100d500101c0420031442018011002984054581100c0460705801c862074544c0c00600c80b840065800c40c00350345c001c6802941ca4059403c50b552060748255541060301090710300039070b20f00c4000f8006100e42250000028005c410051040c1628010390280181a081c404100c3c00b180001e0242c0f01080410401d00c1201c8400500e6a802211165030354160004c00b0400f095800d44190000586640f50030b00900603036982c0b001d0408418002e54022807860410300043c0d00314000c00343c02402038001c1090038030308030903000010f029520f141c0e28111590b82a20043c84100f0b002450020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 365476375 1250 365475125 365475133
    0x715081003060518030c01090b09011b0f11030705061b0406080403050a0509040507021c021f0e010b0d08040312170a050604060b0a110c010f02071401030207080c100b010f02 76
    0x4804180e8980050350b01c2505004c4800c0004c00c041031203461903100c0328482c4030301d0b55220760358000c100b15008000e40002c000c00007440701c08280203201e651036280c101d200e0140807024500f80d4025001e05030b02e111410b21003094903210000d60030019140d00d0100d4143c02c1340c543e0b001620f01080401000d0b5000c1c1c44c00caa60721702c01e039030b2a9941a42d056100c112072400b8450148420001342c2d0340c900405201d140582c0c060169100c860b40c00d442c01d40e1700b0a0311030382503410070300c0d00d5003e803070800400a00011040c40b01044240158072014010111001c4850700411200182020301c0004001003003207900c503518460001c030481e90101d41c0241d10b140c000c000307681d1071808038000340d0941c0c210a4100600400000d2540c1d61741408010603804001e81c080400e000801e0450449824080555001800c1c244510110100310b4001c1d29001c0d1030041016030070345025405042c1e44a0343c141e03042103a1080031981e8580c005c844c1c0680e5503a00604070040b0909100011100c1d5219130207200b246102c9070010 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 365477625 1250 365476375 365476379
    0x40509060a0b1e04090606020a1208130f06020d0510170106121415150108010e090d0f05091009090e2b030902041a1002030a020318030309040c0207150810 68
    0x124080c3e80703050a01d03440c2c298081c400454a0000c40c8038250040019800401594026151282e035030b40007030040c0e0092041c204e003000840c4408081d400c50466008103140c40b03080403403a05c0c400a002e42030829a41d545440d0821a40a181364480c009450707908283c94018150300950030f00303030342540c010803260740500c2d040e85000600e003400741406c080380310081c0c840d14030300c400416a403400c0480310001c4503c0780021021241d604004024050400f40c60921001e103000404e8954600f1600105010441c1c00d04040110502c20000e5400200b8010b0035101f08004881008000aa05010307505929240416114500f14000380d40c280f08220018241105c0344654000003654290100c01010300d80c9038603484005075640e00c24040300000040c0303410300440582d02404007500c1c10300840c9080d503004028045806800000340ea0255007482038540500e5030740c402003421402041962a00142060201e88010b6000319005e002c3c0c60600041c4103030307001034610840b091081914512a5141488c4007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 365478875 1250 365477625 365477647
    0x40c03021c0510110702090c0d1a030304030210110105070203030609010801020a0801030312060504022d0703020a08090d0f0501050117120909070c0f15061a180a0b040803040509060a0b 81
    0x40c3e80c040b02d0f4040d00e80c1802d8040d008140307115011160740103c03900014000c10010309c01e1050700461070720440a0080784c9981300210f0390720300c13903400040d108d0080b8101030700007540b184414a004a4403080240014248401c000c1d5590304190784940c411403c12002049080b014403c2d103001c10401da8590304a030f441d54506407003110241a148081b203884d400041103e4940d0300040042c904039583d031180442d2150b4400091280e034421000003480701700f04060220780e00280800d102500190101e646e8040100002c101e0314880500520f0b4201209031a07082c40010340c0414101c90b07400d803004c214000000ea0301ba80f00d034592100340b0310b4501e080c0103003a228145680e032694400501d0500a111641948500c1524604100c04481e20204042d45c130805451a0194800070004803000360516084070301030b407041d07000f201d0920258081280b9000295502c0d800c12070010414a4200755079940c68a403055241c0e031240c024140207010460108000342840c60010007142c0100a007207050030000d0036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 365480125 1250 365478875 365478881
    0x411121902190e0a080d08010305070503060708010e0a0207020405010602061f05010c03050c2805010c080f1807150906020606060301050a1a040302060d0c020c0a1a09120105040c03021c0510 83
    0x80c1180d00000d0032000407607501010032506d811040c4a480c2c0134040d600d1854201d10380b05560300801d010f40c0104062000050300404031a0558450050001807540c90040b180000c0c00388c0c03500a507006040c1000090850f4010038418010130300c3d104e4084819103403103079060346500c0d50f202e071500185070b03d000c95000c280300300060310214a80c07900f42c8004040c10341030601605240c11010401000c1280d0324810800e09101d20701c162521420031041038508441a0046000014400640e6400024041e104550188a81005000f04e6807011400d242451001004007940d4000c140c0507200b07940102d071071403400c04140e03070480d07400410042086050210b14410071401c4080300948840604c008801690340d00094803101802840c00240301840640080c80c050080038070368003848009405101c1c842000b60300c0a29101002c0704640d481c01584042480150f101a0410495181009000800c15081c507064116130086036200590300141c220300100b000d0005000b06698015040b5040c0c280c0030350 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 365481375 1250 365480125 365480147
    0x60408090d02030309030609070e091906020d02090310150503060f13050a0b07050a0e0103051b030702070e0a0c0206010e0903070f03171f0929041112190219 69
    0x3d002d490034010300310b020030718004055031900a40d400c40c441c01d100301c440c1500f102d680300c4284001480b114030007a582c5c420207503040c00068078140c1c00003003041004c2e01e075030111400310002901b00c034143c0e070712210882e00400089160103800c042034100080e0a240020b4143d00030404100280d40d80c1c1c072014403080c0101d11107242213034140100c0d180d0f000807412045844d844ac01103030325202da44c3e40d03480308002d003013905ca9007459060500d0003050050302c190604000d1481c00d240d110036907694480f9002030307140542aa02c0381014074200000c03c000030541ea00720281e0300005408586480e600d401811004010495081c1c4166105111042c0421140404941d8407406802e11204840c3e02c004460100d420880c1d070030f14420b0000140078a602d0b0050181c030001e104001d01008080e54007000034680c500b1707403000008001e6140c0c0b5150003d55481d0300003c402400004025540c02100c0004d00e400c0d2411580d0041d507000c050310404401c0e00e240204c905003003884e420b505221030802c2066480c3d161207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 365482625 1250 365481375 365481379
    0x10207020303220b0403030201090218091005071b030512070e060f03070309060207060c08010b0a0f12061203171005090c0a11010e0c0f1206010e041b06090611060408090d02 76
    0x1180013a0041d4002c2c01040914000c0d070000c20848618010302902c100d42c039038119540d41003002004407091011440d4911001400404031349034a4000302100e940c410030382050845a801c038142c2c1d08050b0004010200d5041c0018000b03a15a5080f801303544400c108510203401c0b00381044020002601034000795070100050030000350074551a102d54040740c200303010071503400381e40e40c1c9480d0a050300004494010700c1e8a00c0321a19001940f680100b0716082c0c082d80310107001031b038594408082c84035003029020704a00d50f07801c0002051801c009006010144201954001c0c2d10049440d2803842c6004405899020b007089605480d907052402455208048180411006945039141c0480038080c0c508a1002d03030000b0011280e902d410494a4501042103e1260700c0e050140b4501490104106044500d0300300c80468559550400086ca81d92081048502403d0a000458141c2c0c1140306c207026900242d949180d01c50302d41d60f05517a120000e440c003410314402400701d00401d16010306d100003007905c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 365483875 1250 365482625 365482687
    0xe0112211b14030a080a14010b1b15040501150e06030c0d031b0803070306080114040605190c050d050a020a120b060c01060902030a0e15070e060708030f0a0e010207020303 75
    0x2c80c0a070854006610500004e07001809004103103600380940030ba40c20144500301525490440044003a200d640703403c48240b000200785009031107007400f00820001c1441420082031805290450080c0803030401039200080040c000308180405c442141d1251401800821509100d030302004030b801c00b80c00e022000c0001d2690300300d00169444140c0c00b885803140200a0f2241050f010150640b025038001c040c0c2c60303162038030121940c0b45240c001e58029410040c0003072242c642c0051424100d429002c5100c029003041315401c8001c4c0d0100c01030040000410080086480c1c400c030310030036441241a4a4000f50700400c00601609080d40200c00300b0800410b041d1074024500b8066003035483d80e41c800e90030250301004210504005002c0e080c6041c014001900e44111f0026031000200c06c00790502c410091050086c00e181d403508800c0390740f0b49800c5481c040c1c0340d03d030a40144075501e0003280d000300e040d41450a003100c8010140203882911384c5c000e01850414448841c0341984044147e9000781e0300c00c0d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 365485125 1250 365483875 365483903
    0x1b1e06080a0b0d050a020307290c2103040204150b1e041701240b03010e0402060706020706091202210903010609020c100e06010b0304031101060e0112211b 68
    0xd200b0f4090604148030f04080c084280700c4d40105802c3c40b145a1000549800807040006104401c22050a45640c050806911864001e40c00e928083d0b0208411105031242c1c0310020700c800b64140a1841580708445c20300c04030100041c2404d0f600501c0c420783c0e01007a400c0c08030b02805c2c0000d48080450f55070100065003429030719406407441301d04000340c592099644440c0501c40d400c986442e0b0750001803400825402600d0036001040d00d1105110740070049417020041411592010100c458240e0000015922b8038003e0414034024440c088045800c0645580d5000e490350000c0b50384960f003c0100d4a002880b0700903e250300595001103202d59241d5038601c2d0200341c80e80a07102411110400800400682c074013000368004072007040c14200c4960340034000411918a00b03c1c100ea07030066141c0717405083c5040405425000d801c894004082d100301c80e0300003065014003030034504c41d0a402074030b140c1c011303a1904043c8804a4100341d42400040c4007040a184800218020318450310b2003044c0d01c0304444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 365486375 1250 365485125 365485129
    0x7030503062e0210060b09092806080c01020d080612070e0711060c0412022b0809011704020a03081e0d020a0e03060f190f05041b1e06080a0b 62
    0xc462140d41d00346001000780c10301081c0d83e0401c00e00c0c03810816418204529030408060001c180034940d601d6100e032804100290880b1150150844c83c501220484e6041c4040c40301d520014284901401c0d000f0b101e80020608250310000f0030002d07680d0b1640b01c201040d10780d071091009108514814001500c03901d03c002500c0405010f00c68803a240c0c580e074520701051058055420000080c100c079081e00d20900c010320a010b40011054000c55044910440294031703000007607071f200d81e003450400384601c0401c000020700035541c00400350b040003641e4103408030a4031510030940e05000e0760080d42155408038180300142e034520041c1100c4040419505c00d820003076541c0c032120342c00341d0a00b5003025000300312903100c2d58100c02440c140c1c48003103015105074070f000d0300b0319904624010038035051021451401d2401704499485001d80ca070312050180014a001e081c2084a0034170003950002c90020300380700151a01754a554000705c215044084112b00d0314207001100c0380139019010040250b6140fa09844607 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 365487625 1250 365486375 365486419
    0x314150a0c0e1f021207330926070c05060309120c0f0c060c1903050904020d06050a0f03030912020613140102070f0b0702060714060408030103060b040b01050703050306 74
    0x200c905807900c1d0f0380e0984142c8009003001070750301c074111800e03605100000c0001da603030710000025480c00d200000c81e175900e08401103041e06015070003840c1515111003070060250181001c500a10659040401200c9400c0325019a104a540c040d140c01640541030010703141140045d41c201c3c0c036101c202c0b01407116810310b070020340c0e0140380070f400f60740c0c028402c0b110700141c00d100400c403110040b1150b40c02d0040681403651141410888526510003103603081c41003501a0007a03d0004030042c0045403605010118000180f81714020720340304001c0d10200140080c80d0b000c1c000e05581e810741d41e0740000362501802402100c0006000c9a11110a2091424491800090038010802c49240c50300c030100200019042070142d030048035010703904080030301526224504071072025070305a8400d83da40026092060142d00f041a2040950180c4c3c0c0920040c410070f0400745041ea406408100101c40e600340c1008115510248824003007181404044003080c000c0300030f9940164041c10310007803400c00c10180605 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 365488875 1250 365487625 365487649
    0x30604020906040f06020f0a150c020a08041403010605030d21140c040509060d03090513061d0912040e070c0809040f0f0b152a0a06060314150a0c0e 65
    0x4d41000c4801c00c801a410007035880040741650103421591100c0e04c913030842000e04224a50700c51f44410068070b07a02d108000c0004911b07000540251102d4440340c6511220f04c105200301e22a60800201180d240b9012403403000300c00c03041d1141c0100c0c2000c000c0070300c102055200c0540c20300d41c0d9540404207042402662a1207010380450403070351242403070200a0030401c080e03d600d0003046070904e000002170b040200001555800c8429102902c614010a0060a40c0b40c1200007c596400301481d4415034003281e49000d6040042541d0608000307004c0358603280030b0340c17060641c16012100455440d502402d0910700581c001d1505624103206000403c054030342032148607042c6c955680c0d000204854511813850100800c484034442d00d07003109200d20321401140c800c0ca44190034102c0014170b88074a10303c906a403410b00070549603010854101a001801d25120545004262840440036030f400440e00d4505107030001d00c40440d0340c40380001d460081c0040100041817004200703250340c0ca90348401c12151 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 365490125 1250 365488875 365488889
    0x3070608090604141e030405210d031e140907120803072006070c150911040f0204030f030e0a150c110f0315011802070b0c0703031e090b150307090203060402090604 72
    0x61f40b0f0307240205110000b00c050908a05070240c14203849031145012880c1031103140289000320340854440108201100030b0f803102100589062020903803201050660781c071410024007036800da03d64030349440b12264803041000f03001c0d80c030400000300100c0c010b004034014001000490940002c5002056240c4041624200d0109511441550070400000001c1c607412000410600ca5129680c2d107079141102d0900500b0302c0b40d512515914192080c2d42e0503a4015a04400c001000500ca4200a0220980541c0250003550142800308a08000544900c0082900d40d1128140f010a840e0982400b10801501394464003600001c2580d030381c20043d00804d02d240c5292200f85514140714501001c0038448041c040c10700500c03140c0042124903000c80c1d4083c2901c0c40503503488081d80790443c018040f50350341080d100500301084504403210747c0554400e41c40f4010a0600c3c1c3c60307407a00c2204165040c180c541c2c3c10f030720005d000d01120280da006142c00010141c005820402104001690f82e081908941 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 365491375 1250 365490125 365490127
    0x90b040b04150e15070302040609140f0612010602120712051b01020a091d090a14031c0905011406030606010f050d050903250f060b1f080603070608090604141e03 71
    0x10513500c16003d01c85030000101d050843c030b040d1030300c00041c091031890300c5403081650a8285290300e03915004010980640020f100566030a42034081c0c032a0102c1c28050080188500e103000d8450380342010454401540000d001001146008812241a44601001150208011401040c803c400d001030003800302d240d00c2d140e058a050401c1840c20441405520020035106400d0100e541004521072460941100352000000022800c0c0e13440c40c45070320351006c1a00c0d00214800043d00700f41c0d01000007244500d009101c0c0d50940309040c09446421f8422551641002021030350560040140d55050b00540c1400d6090600441041040380c2c422a00c108560b040040d1450400c505d16101040310403903400135101d50801508ca02e40110071160000345003d40e50001e42c1455507407001d0b90809024400d40491401b4a15a001000500143d9889010340b04201010a610740a070340071900c5180c680005015a40d940d40711100841da01c50803880207405000c1d035101d1800001c8000c0004860404021 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 365492625 1250 365491375 365491393
    0x130b040c1d090c0f09010c0c290304150510090e0604120206010803070204020a0c08160b070c030509060a0903140106080705060405030309010807020c040905060f0a090b040b04150e 79
    0x1000012010305070151080201004210400304007006465122075281a01a102e0f143c0c0310041c1d5281c031440c00003801417145c00000160303c030042003520200301046844841400741c04680500709010a440040c068405040c11445200407070380f04a82c44006a13a180203115030342d52030359084412008026007550003010403c4184400d501034280d9a031407038401040e65600d00262151203026900f0000e1145170001200d1704403178130562141c50f4482e00402d038aa660780c901103003100344170b180c600d086619600550000d0840d80c085c000790b141c02501629070500d4a518002048401c1c0c1c0305507582c1c03081c0841c440300800895803500d52049802c2c044070000403c6801c01c00018a04441c2c2c1d4041031040038208014022600c1c0482a241c80c10400e003011310403911060303001d0782400c0880c258507400c1803601da4090180800020302d0b9001e684440c60140342c4e911204a1070090700d00a03400a804584401c0110300080c2c003a00c00301d0b40c07250140010403001d0303a00c140381d803090320350541c103071072055000b1210 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 365493875 1250 365492625 365492657
    0x27030809120d08010e04050a1203020c0d05090a1202041b021006090923010e0d020304170604170a05160c031a01050907030e0109060f020301081504050309130b040c 72
    0x11448546640300140044030b0b40640090410f41c0501515a07500e04e010042003c0202c20006201126408040c1091107060010001c00a4010b0410200a446515020160136000c0c0085032030000024000b07000340360070181c16119a0801100898205523210040e0707010b10104958101d100180ba0701070f2552200c2004194207503103a030340118180d40d00d00201100014500c041000080100050b4500c0c0e8901d240030b01401014102e460144c02c1c001e150224411075801300c02041500c6132010a080c104540c0348826940b076000f01d6006000301c032098020041c0c180c50001a1003081e510345402460500900c00711198160605011244000c40c0d407030a108119044401060720074500904559540c54400050445070010740b0007401d250380d942030028204002e4224448864000d8010700030389440b11141c00c0254030900c21810b0031301401c000c9400824518014074080c1e90030100860422020341b00300540b08100e01214640345685800c1e802c0d050b00d03140030b1030007041140c0c0c03a0300580801000e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 365495125 1250 365493875 365493889
    0x50d05031e090a0e0a1b0f09080303060d0f0804232b031206051512013303061710050c0c071511030715110901050a27030809 55
    0xc000c0800304010700103445903448540550f41101c076001c18007510340c1c4400c2c19603c02040207006894041c10000404164650480180510126595101400d4030f40e0780d4080d45e00e130301040c1c40c031a43c0202c440400354086030700c040001aa00d405102000d2515948007070721071009026038211803c0034040f03140b01c2403038902400711503c81e1802d0b110b400700c0404600c030780d02d5083c8040d14004040c000c000070300d000c858441e50302c05000f40002a00303585888801489000036a00030149403107284070f141c03001040203225841030b10003142c0344480103085a15007004141c15104043c04040070543e0380e010001d1681841c0c8520504845800007030030022004032604403d4039401410220081c0080088032594400024150122109616000029040c402c02126242c01c0c103041e10b1500e1201003a14800d024009905000c280d0703181c80200101d030044a112101c0d40140200f80d404103c06100c070401d0180100040040207802a1a20307201c260200100ca0009001d0b400036510903001207454401400c0c0701d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 365496375 1250 365495125 365495167
    0x528031401270506060a1206080703050a0210020c030604150b0603010902130b030c0f1b0d090609051503040320010e10050a020c060103230618060f01060806100207050d0503 76
    0x21080c003c0740f82c001c000c19000c1c0b092600311001c001d01814003440004c1e80342e2101014250101c00d480595540303061660f540c500c140d1090f48540e19109082204600001d40c0c4401184007034090942c513074441d2258840c4c1210714032005100c1d41c43d42c12116040ea1070400440c06400c4c80f141c01601c4000c0100c080602498079000200d0306c140410500c5240a0340780305541c0c00c8103884001c00da840b030b911100301608500700076000e15244506d0036000085500101002c041d5102940c6801d005c554901c1040a01440341002d4042d00c3c0041003c00d002c030b8400c1801b11401301c91941c01c4061113001428446c03c40f01c00e400d507a07216030403600c5040640c2115008640d00109504801e6081603200301580d51624030603c001071204203850180440daa540d0003980001c500d030b003420b8443c175142c07043c410300c0300340c6039010201d8403402a0000101f0b980421041c0030b050f03c400703903548030103540d8007001c3c04440c2c2c4c12a2101015072098590028142c0d81e45a041388000f442070000d15240c051081001003010340034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 365497625 1250 365496375 365496449
    0x305070506101d0601080109090f02130b120a03050706050402011e0519050301031703131b030210020f0604061104030c0b0901090602070b0a03050402130c0801080606010528031401 79
    0x42401060786e44445024151040c40c100011401d180d40b410420007040104000d41148064003501109a125031104240141c2034452100d0701c40000d000c543c0381c002c00c0c10020f011810902c182c4011039920780c0304592081c0306040c6400c0e11000e0040e020701c240701c9110440001100010710009060007060313002c1909041e03051160a5504590f100c0c5c0783c42c25103001e01c90b040300d00800060007104451401c902202e4206d034005038044122042542c80141302e00040e80900545102034002e184000794549403a15413901a2116894682e0f0701d1000c0d117689105425001800d120120104074604085002007006110841d510110500050700d40d60141d80550f003907400421301040700030f401100325030a42d442e03450005403d90351ba1001035214003001300b540301900e1402000c4010640c2050199042e0b82e9800708950705c0340e48003001110700b48203d1803268401440c880400d00d0b810744040f2a0301149407241008103542c00d0901e02c01d8102031090317108030038103180d40c124405105030f2209855000070306 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 365498875 1250 365497625 365497679
    0x504141807030b010312050f1308060c0906071103010608100b041a030304030314250501060905090307030c06020c011b0e010302070c0b03090c100e040b0604030c0302060304030507050610 82
    0x2d552226a890401440f000c0d0130100341400c4450740c5441041201c044100c2070640d240c07a24128910180046224003a111031481a40c2c003144000682e0f5007614080c081c000c003624036192150352000d20b01c668450605816640354480410200e00c02e000000505480c540001060352508080006403080200d003521072a510081d030101a44002c011078040e41d816041c60b908a41c00484075011611030300940003002045203620a050f018244054113200740940000c0c802240c82d42c501c1000c40e0f1041d90b10b00b955500c20001000000d002d51074042019004400c0141080c103032080700b500f903860044620361005d118014280400d60801e1004146007001e2a00f1810310050b83d03298500081140981d602140c0080000780c0d54142c01c10485080325005440700c080341060305030103030a5200711740a80e031040741468410380060809500382e8041341e40002c12013015602d10b400384a801c0d0f02c050425001c001c1c04010907070100f0002c00140c0d016280c540c0082a03450701d04551803241c8451501c2d81550001d07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 365500125 1250 365498875 365498879
    0x1002031302031002070b2e090608060f0c160204060302040513020102150f0f0627011404090c0605030c130e04060e0a0f021002100e010f15210c0504141807 68
    0x841c801409500008014211410380c8000ca04458401f0b20b900f4190142d5003000d80119900072903070005801c545032542100e00f42e85401308400310b021021500384511247c24000200c030700d0900801a402c01d8009400014000e40740d03004142070b208200c0d0055107248241c0028003c55a0411141c2d0702824000c1c901d182c0d0f820800340e4168001c60160001d186003c3c00c40c0456000d640381503c000d4007510010500001301c4421042c10541e030001d00c01c4a24a90f01402e0841060409000d2600841c1e4442518001380342451000e48260b00007520a85002c10240308194082c241640641c000d041c161844101e00d203032500d07101041c0c0d00e01c011219034980012a20400003030449605c0e411559044540303c4190b04001c070201e00c3c0079001034a05045a09002840c00c1c0c846040d8000c41050f0500007040c000380d0656400c980301036000d4890106c2d200c6100850a190340c4440c0c40c0c2c0104544074114420855a484001400b0760307807010044034541000c2418880362100081400120220150142c28494 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 365501375 1250 365500125 365500133
    0x11030d0c030903022e0206010e010f05010504032d050709050a090506060f19170d0201051608040c0f09020a0801051c0b0a090b010b030f010e130311100203130203100207 74
    0x58081c070000f4019080780981980e02a00180d0900d000c1030400d203041d00d179030b05500000350b6640c2d0a00c14507039640080400031910a070780c1814030b400d650060712118a018030b90750b00c00b4081c61300c0c10036481c2582e861554140592060201100b201d5000d00c0041160a0611411070111140030703040500751032400700c207c80040c00c0803800d80d078084c0d802c5030b00510307030a050300210320908005501420428941007005c176420040304042060540c08404032802c20400740000c2c0e00b02e4000f03691080980c43c48925411100380310b1420281e22912071406030521300c0d500d4049500030b803030301d4005880c0c40d600030500301140360740054042c0c01080e080391189142c5142810948011044d40c10152018100c103000801828040e00003e90140d07000d04070103000d69440c02d1480e965002641d0800a99a50100004800c403620404e1401810740341c061404904090364240d0b82c0b0f00c0d0703070070422410f030240d80c4d0801c40c89101440510301c540c41d50a1080006e4001d0700c101410705400da0001c00c00944180100d001013 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 365502625 1250 365501375 365501387
    0x6012103091413050901060603051e1b040b13210c0501030207060b0a030809010807020c01080c09180708061005030c041a12011d06010f0c030320030411030d0c03 71
    0x4504100c0c03540380c0403800c5004900026022240380c00341e1130814007402944181503104a040319065a820009501c40709100f00d090314090112500c2c044030000071840180002d00741019004001d5492494540e072035510015540041d20501120340c240750040044c0c404801c8807140c9030010301140342191200d0342e1902c500005500078241090740c0410410100301c0191710000340c90400400ba9503e041e0f40e440c100840f60b0100380b0590000d038060010a40042c0001880c2c08501030586801e0f00941d1142c1d40716690782c000041c1941c0c49220700103410b82d40f8507400d0700507005a1304c0b5950300c011450070b4000d00407402d03040b0070444100300d0200704020040c841007046d681540c00c54030741d4070408803014001c2500d9006051185903d00042000010103203100c1d42030382d0449284e22211131444d0b0340d000054403800e207164010004210485d03020300000740310364084c107a03050650b03c04085c15105000c9800780368000310740444880c200d43c40e890b41c40e0715003005645011038040c500300e00f400549540c02410 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 365503875 1250 365502625 365502629
    0x918031706280810020403061103010e0411150703030b030d051206131d0c090c0f030402041d07260115090207050312070c1a01081e0a140601210309 65
    0x481c00c03001d21000040100d01204200402c1810111000084403000944c001d5101c2e00c0100d07056450301c8007141388220f9103000e984c100d41c082054901a95034640351410b1001c0c0d001610f990048030320701000251a058400f0300b2980d400703590002410316480e028945040001c10384402800000d1200d0180b46125001c01940040c003681c1c055000c036100d50224005e80b540f01408031000c04942140305100000150710712071042e0880d080c6074141c5a1340c95040241c8103900070034104000c1040014058100385e0850042421028200e028138254040c1007030a0900f65000741d400369001603d141004148204080003a1025a0080080021043c2e0300b008801c2148509001503030003151800a2000602c150307012407211000f01310740c6184c89100140100402c1c00c0803100384034540580352008030520b8040d03040c5c698441c010f1000d40d50b050075018040200c2a5110303403620899007023000081c180e01040a4410210004042950400305070940d100700d040d80d0401c21501340d80c108408240d01c0f000c4481 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 365505125 1250 365503875 365503909
    0x61d07021b040e15040317060105070c090218041811040c0c1b09020d0e0d020a050705011103070609080322020109180b040603031d0307031110090918031706 69
    0x2500f001c0540c240303428101c0144124032400540000c000038540c00c004644806404400200303442d544100044d03541c1e02588201400400110100341314150b0a6801011855183c0c440024014000000501a10b4081425180f00b912403280881000b01c0412040c0e02c40070201e40511809070000e8005007a1403001c04098002e011503001152040c011022501c00790100f50000d40d42c0381001e00c2c0c000c0c007905510360340c15540c1c820385801401451000c210b682c841360784140039200080c03400004454009200d801e480e4240000c10a001c001a090b102d030f01030491207100c84035101e01c0d0540b16122019100e402c2e180c41150040740140060b070f4001c08500c162050242d481c0c0108003603200f05002080580321a5422502c0c020003c42496000451040510704400303000181c4401c0e0010f05d9200d030060303c0002e0040078a000301603d00d00c0c04884020072070341c543c580b007500f861340c5188080949903c1c840882ca0b41909280480030706521441d100700175100719225050310304008000c600c43c2020019116 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 365506375 1250 365505125 365505131
    0x804021e1314010e090105040b0a0209030f1c09050a030c050d0c1211240d0b03031204030c0c0e090604030c0c0f1707080d0507030f020a06061d07021b04 67
    0x4142580d800c0401d0200c020541002c00c19080d45000054940b04203028000000e81c1c284006410640140034841c440d56101140300300d42d42718010408041e401407140e40d68580546030491a04500800080c140320300708071180c06aa41201c03201a105440b0754100e58004d80d40c0d90703000c0c408243c6042c005000c65200382c6e484100c81e405030610314a618001c1d0490022039880040220a1000740002d0180c0d814084a101200140707204504681e040524200341100c03005000780003004000354442564804007130140e034509100c0d542042c00e16401264200c003c50001d55101003800b405020400251440209600e002c0c1003d900e89544c4100050000f02081140c1d00300348104665280030380010582e10803d040c06648406582d500f400c03400e08245030911404500050303c107400503c02e8902036068480c2407601c540c5480c100c0e090a801c40b0100158401c8804800000e102442040010710348000c1d40f00030601d142d560454521005440c3c8421903000d54074107107000140285541444408903800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 365507625 1250 365506375 365506429
    0x5010206280504031106060103050106090e0c0708030c0c07090902060f130807090209030f39030604060c0e010206010303120b150f0a2709020f0904150501020d080402 73
    0x32654a0456881c280d1094241424481003580000400d408028058262145940c0781307001101142e1092181c00700003802c0d01000c000c00f62608000395000034030903100341d141c070350907448050240d4825111910360110004030426070703403402d100801c060302203c4c40c11b11034050260005040c074014071011052041c00020411205048a040000100648003d5800f22540c231094a0001d42024150502900a01c0d40540ca1071b080418440313009103602c20701400d20810880c2c05550095002107070288400203001d40d40182d13904205007446284200c030f01040b10320280400070140d0300100c0c2440c2c1035606c0100140000790b0489602c000341e2003401c100107607041e10f0a001604050601e81d00c42c502c0e03800010641d001801e5a80200065161501da41c2002480312000183c0b000b03220407009100828014203004074401c0c0e8000b41100d81d40300c0f071141d0406001100040440c0c4440b0046c000d0f44542c2241084256018418562113951504100c0f03071901e488e40119540980c2d45e110220191140c02d50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 365508875 1250 365507625 365507671
    0x20d0207020901090f0f06122d0b0421091502030708130e010503071404051005030312041b03080906030702070314030408011803020a0f0c05191503020405010206 71
    0x10380e0806034006180c11100d50352400b0034001040410140401103040460194031020b490180034201c4010f90004090341005444114010f04a80800000885100b06841100b8024520000014003c02d582c0c04207007807501e0301902d16203c0740c010080f41c080103107845418940110030002210001c114004400c0c0c010309003241948542d4038010404000800d080d01c00440e0807140e001610000c1c20b0a10413070b41c81d5800c0559400d5644260740412018005070301d40707800c0c5504280d811850300c846403024261610002406c1d03400600a00008c50a0f41042000b80440440d90703d070050607100071441c5507070444e11801c0c11485031006c501d02071030001000c182058402c02080c0c0c015508008000340113030013040b42c0ca0b12580103221b1407100350f00b03246103030340e441505184840000c0ea0640040080d00341e030788c1ea0020040608401500c40d810b80c1040003690761110001c58801400c13280c550045903003010410484905e020406504040c4140400c0c001a40c00054040e040804c650030f11400b416500306c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 365510125 1250 365508875 365508877
    0x60602162115020f0403050c0a03051f0b09040b0604060905011203180503060c0a09090209130504050a06050907030b0f0606071e080f0703260a240305150a020c060109020d02 76
    0x581c082c030324400209000410011030142040c0c038801c0068070841c1032600d0802c502c81040d40009000c2c0e811040e0030b0300200c05401000390912007040000308059030000f001440071001102c040e07601d6051482005800c0c5421320404015140d240300c10444d650400018407a054910000181403142a001419005410311001c000421009007150101d1924185030080b50308880c10380d00100d03940c00d4004c10505514000d07140080030140005c891f4900018200d40038060150040c1e40781e006000c00c98000c10018002d26203c0c034100801452254a14601060202401000960f4140c426000e001556584034120f07510035800036001d440307200c42020140c0e548024074000a140840000341c00d20501603650142204502a40750354918a0f4501098403a0110502160301182e10b041b0005250b1403240e400b0120104961495080040041180120f654001e400c203a426a00040382d0b40e1880c2e840b0b96406911180c43c40b415410004114411a5601ca040c010501030580214040c4100042c6034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 365511375 1250 365510125 365510153
    0x6090605090a02090702010c05030a0209220203010503070f150522030606030b0a0506030a1407090e06090f0f0c0d1110030b01020118030509040203060a0512010606021621 75
    0x9040005090088031039545028501c002c9000e03148907400a40624010705c9614212a01c98940c0f900e15135072070000000940c014a905c13544000c001c00c1c0050800e200c46d80e86582e40004034401a03495042004045c607041855101c45032502c0d40c0340c424801c00c07240304007003801c05a0a0401a03141e00540d0525802c44420300d403800c0044040d600d0000c18014240c11050480b03020700b5207040c580c1c841014600550f802103400c66095403010b502c040c0003401d9103501b080c0032003414081c0c400b000d451710800000e5400302000030310303160301080c11b208451806201c0ba1603035418482c000d0082009000c03041e9200d040003605544a500f212410006024100140142e6040010424664041c0e00354000d001011503082c098010b40c80c03c0640d61403690f0125200600c9905a100d407401c05e181e01040002a500040003660407a8605c180044c8503241d0341c0c00c485095402c03900215102e03052090091421f038010017a2928403511136801c0212401000740c41c19051100a01c0600c00c02c0c090410b001144110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 365512625 1250 365511375 365511383
    0xd09082107110d06050403030c03050c0306011103190e03010e1908090f0409060e0c030309011416050d08041b05090a02030406110a0c0c090c090501082505091c080f070609 75
    0x3c00441003080b90507442548540d101c0e45080100c481940341c11012641c0844580c00c04020400108034158061032401001c1240d030000c407482e2210041400884500b58441c0c6404074101840c1c0700764070b01c0d0030b024610078034203d00014a035004030601d40104507440c52074040c2c1024400a110085a2101c42c000d00042c1c0d03029005000a4005d0f141800080c0400b14443c0f1039405165006441071402000311000c50f84141d60345c5014842c4410200619400301e902002164101500100001c40500c403503814040c8540720601c8a2419091224175419140c3c1143c1304400141c0c014801561035100558000240c075a0041c1c44e5510351424000404170244949006d0a000c2110412164854007108900e403060400c1c2015640d101a00420785480c3c24280020031322540040c0900d5204640c0560700008560007190f0b41206848000c40d407640f041c514000213940003e54401904007110b283d005140012039000a500c1140c271105400d0040318100c0440700341c0090164280031042d00310354125508 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 365513875 1250 365512625 365512639
    0x40b0a0c0c061e03060e0628031a0c0405010c030804022215080105060307170a060203010902032205060a0527030304020f060c070311011707020d0908210711 69
    0x1c44501600071a05800c40c48601e24444000294030344c0320780204811211002c0740056292036450800000b90b100c0088141e001072481c80000440c280f081c03115006601501c02460110030031035507040b007254004d007a0000414104010882a41d0040c24400000e8140ca022005611548006103e034188203491081044502510010056803540310829092900044000c03803907a80a4950981c0c1d001c13145294190812001080b0195010074001c40c003c054506403980c00c0d94595642d0101d07002038200440165002c000c00c40201c1021070030114100300f440135848a050b090382c445649500045c40c0e1030180d501c0e41d0110b22114002041c8080d066241580346170400d01303500d0565660303002200c09070b20440038082442418101300c8215881c40c94004003508103207055442d4089500284010b007410400500481e500710503e81504501030485070340906002881c411008140810627003058801e41c02c0b4114007096141c0500c0d2075071043c00140b00d01c54407003003d4280504c07401104c03401507400170301d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 365515125 1250 365513875 365513879
    0x8010317191716090905040515070504090c05192f0303190b1e0126060f010807090e040c1e090e07050108070809010b040612020103051605040b0a0c0c 66
    0x1400110a007412004032031184410b41d550050b907800f02c0c005a81d8940032455a01062142100a42080f0f900c98081c104a500c4010001ca200c0ca20340011204000000c202150501605840703008500b0085454901035081c02e0030045c8894100310a1200081406460300501030601072000141520305c0c80d0b0850604400e0403440780c2c944a0b1710071104200c4010043c0096608c1c0b50062103829800c0f90301600301a5940380751017840485001d225011814041c801000012100311403022000c2c16010f03850a40080c1010030601040380700c01e500c0b0a05014802040188003a4003505410807074203241041c40243d2103031308007800d25140300d81068200c0034411544070100b202c40041242100c0710200100030352020480840c2d107074440d6005135070000303040c5c0000c610094440c00d070054008040c440001034007041480003c2c00c4a00d55803041c1c1400075000c80100030340da058803482c0c1e40402c1201044401d0461000000c10391f108034080c0c0015810f006c1150340f45240320742c00104080b6886010218425 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 365516375 1250 365515125 365515127
    0x80a0f030e190b010f08071503090b0a0902040b0102060c0a0f0509040f05010e090304060e040b0118090e1b0d021002100c020313090b0108060105030603030d0911090906070801031719 80
    0x110b8010025a16010030000025201100414800441303008501801105003040c0840015004424400701010b8a5409050201d150090385501400e00d000740000c000d00140b0500003521903000e175803810354000c1c40401403004111070171901000924030b402c00e88a000d081c0c0c15100e030700801460380d070058a0440d07117602d40b011690005058883c40b91080c09aa60b4030b64226660344200d01032100000e070b04492108041c1003a4000350f0f0440c105060a080d40d44880348a0007050011354000c2d1001d507156403241c2c01000303040c0848200400003201c00806518028040707030407540c41c600000c4c06814000031941e159482030012001900b01014144692085034400035660f821404180009a510010010b50000c580c81024010103041c0c545041c0e80e034607000151b80c1d9070001084140c0502040001550344c0030703544103421640e4803607151444801144010700c20541c00c01008124154032103810321170140d42001540f41165030101c883c0c018004036215001d610b024020001032200d12a84c0035827211 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 365517625 1250 365516375 365516413
    0x72301060b0313050601050a03050307080306131b0306060903051c0c020307080607080a0e100c051b071a07050303040f02010201061512050f01150c02151611010c080a0f030e 76
    0x2444c00b90084134041d90721141009030181309440018802d500402c158000105407c02455020340c0c000d00e440c0406800b0400102035626000a0000c0740c240020401d604039098440c4e040540420315144c1c078254210b54030309940d0301001c01060b004901c0d03400f442689610400e511751416901034141c0d820300e556503d48aa0340c1e10280d804501003224480028900040c901c14086e141c81c0c0a00100381c07060450340100004c04407202c811041020400841142c000c1000405049010b103000500105203819108000072403100e0340c2401801040083c440841c40001c1901d810071b420600700070121000d0310040c2d0040115500c104e00b50080c3d41c2c020803e543e0008410b11220b90348013014455542da01c1c03c3c2240e80c1d8403d01818030200381310071f0349080184c42207804054131403001d03180c2909041d024000403510340000744510701e807408014813441004284228443c0340d000a003015100d001983e600d03001c0d14010b1007402d13030800200c10a003400c880c0c0301360000d0340201001003e4a00564000f0b101403d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 365518875 1250 365517625 365517661
    0x30804080c010201050c0a0309051515010201050903490c020c030c09070e1908010204030507090612020625052a06030601030905150c1c02072301060b03 67
    0xa14019050282202d50041c012184907135013010041340b40c801001c1040e002441080303c165064420992000b030307481006071031280104100c07062508000042000207003981c01c01031a40140307420601000c2c034005c80415950716801c1c2900b5200c02e120384a00249808032070b640c41494030a0300b40c5003884503201d417a03511000c4102c51b17a50a03607207220402c005040e900d40c00116007581021440f0000f50307a66104580b00c4e015000020280280045e81d0007442c0da8203002c60308003040a95000804104200c8100018801004020424040c881c41c00301529031104007000c019001e140c001405d202701200982c090305804204271080403601304942803480e51101c401203030b58140200342031380d4008d03820500303001c0e000e1100080880b8515030b904001100942810001102c80780702d00d810400f02303c551511003d1081114103031541d101c0d80d00d50b030b480030015950460b01840d14410000c00000c600d80d6512201c90b900d40c11940741860000030481801885940c0c4003a511040c00f00074414468441200c10074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 365520125 1250 365518875 365518889
    0x1020a0f06060518060306040305090f090a06080c010f0909020d0b090412030f0e0316291009112d0418060509061f0c0c0305031b070f03020415050406030804 69
    0x5a40c03410190070344ca0003001540ea059155018000082c0000d200b440103051040000d4106114405208049401e94905a0301051216141d035400c2c03103059030401c080000c00a092a00c0c000031911410050841c80ea603009405185400040d80d100c510f0316034101400d1894040c140e0b141916080c00c0c0b01014042c1925510300003802c1a4280411550038001d0b540c0b12140d50300914a0410300020f104c1080d040c0640455904041c0b180f00c00b145200002c024002e50317036005140451b0324240420311400708854100304070080c504041b000c081a14442554034540f80448040c0c104060071891108088048503a1880140002030104500191050300401140e50040a1001a49582c1003140c030000841d0071940050441a0090241c41081707044a244172060401a01928131790300d500d00d400c1025001a9003079400000d14100010140800300298001e240c0903161302420040c81410f03114040c8406442140c4030100c004c00307079201c0c80c4500024640240100405580d070315003240c80390040e2140384 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 365521375 1250 365520125 365520139
    0x825030e0106140a1206090501090803040b07020105011d0403111e0c0306161805090106050703120e0d0c0501020f0c0106050a0f030305032404050f014101020a0f060605 74
    0x30f44940030030951101030b800410302c01c182c50800c100c00701003001c00c510640e14151a5403100011030742c28402c0041c11405440215600c3c60b060501c000032440260070342c002c41e0f2402004200540c4030710203500401c440203545000985903030408848000e50010510001d0240111489400306da061000c07100060040079981d000684104060715000202c4200321040c241c004a1415644a001000d0402584810f200001ca1322000482c640c00000d030825400304000146050a058110710324104041005009202c5511141e181c40e4482e00c2007000390050100b004a010104882074040d10101e440c000240c40e01d030340d26082d48d42d0180840e40b2a840c0102d4030f854001c502240001c1a05040d01d405480f0a460341d1541015070305c14800e02a0b0401014690009060b00c0395601d015490241e1400801d15406506110ba198040c21150b8254605075119054804c403c104c0f030400803e0b00181c0500301d2a004a40c1d80043c0e06180c2255030081c516140d61030b8200c10820035600650070754600b580d41e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 365522625 1250 365521375 365521379
    0x140a02100f1103190c080d0906060f0b07030e0603130b040b010e0f0108061b040905040b061914040b030f070e04050c1507170d3e0a0825030e0106 64
    0x8541c0f40d01c00c00248189400c0b4012500c0e500c540101d00e140d401030303c00c0c1001ca203403c0750b629001007103c5480340b088410300e841d40e00c00c104032104000b083c00506101c41c080340c07030310000d40d40180001c0c1010362420300aa1012000034440755480419030500c40e04490300303031258078183c0b4000f0f51001c0c003400760440c140800300110b110450000c002038140c406d828020281601c84603034480b02004503110f80a84c140702088045a0004180103c40c0910310032004403600741818070401a8104900c231807000b40c21045982005101d105c02401074010030150b80014172891210042800c2455840c41075001d4402c00354001010403040074010303c1140140c00356580f0f00d40345401c0050355041008141060001444410301040c1410f00c0c105601600e02503035882d043c0a01d0203001070350700d88040710070055034501c4098000c440e907190001403c212090007551516402546407172500410418038104209840011132030451011040c440110030f442043c26200c0b00744009001d441c1c258045842d40d4213020f00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 365523875 1250 365522625 365522657
    0x9050d090303020d0804061e021306140d050a1404080d06050f010504092301080a0b0a0b01050301030807330b0d1709040209040c050a0f1b140a02100f 66
    0x565826030b07600d90b0180c00c0740c030764220003250341c0b00c2c024109591030b071340d1040361901449401c141f15401424070440175071582107420040040b0b944a50212051007013402e010b2064282000413900d80008810b03000401d40c49101d0110014001401d02c10041c01d40c81c0280401c3c841118040c0a45121056040c02090b480341c0c10f02c500d42c50030440d01d5000c00c1c800c0c8024030501c81c941e04482480d02c824461030310301080d1507401416040d0282e0082c0040d8021004410074441d10b1940340d0f9010350103110030310903c00c1d03500000b0103034481440050b10108001c51001d0410100e580c0f281310b0b082484080400c8102e02201c442c01e06030050151100c41c1d40f0b004462441800c001e030000724241d0700028466215160140d40d00744070360103503030700070780c07081e03080000c090f190307580b480364403070300b4000d0341d50980c58043c0918060001e41441d0141803e01c20414156801c1404070340d601c14101da0701140d520587c00d4a0480c0901d051311207080294009546614401c0969104565082006d01a6950046280c000030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 365525125 1250 365523875 365523887
    0x602040603240602031b010e060705040f080105060906060702012303060907020d020a06151206050a180507060c030e04020c060405060105040207031d3c0109080a0f06020c030406020109050d 83
    0x700300d00c0503030400d01000040400481c6c409501e08801c2d00080751920070440c2d841d080c0002181c140010a10120382445850003402525010f800000002c00c05030512100050995a0081695105100c00500c900443e403003a54001c0d40c20340900e80c10260016024180c61254104840301d44c050000040080c13201407002504c14030350f554076000303081d6a58040d180c2c00c01078194500d05448052400c407000403540525960103041c80d000704000103090600c6010101542d154030240230815070020040070200c0c07808209001110310b0b6080a03405043c540c60151003c480b2000c1316603010b880484c101203201d0f000700d1810321940c4a0010390b42681e0300da41c200012401900c401174000344075071a40890440b6030900c0f00101c00b0b001020649416181c140340c0c0c421244403420480100340480e40d000c0e80045140c05071446030001d08080c10414203100c40603075903018041001d4a6080300c03000140c144150b682c1190340c2400c0001c00d0b29503070361311100080d0103008201c0084445228840d04103040900c036235 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 365526375 1250 365525125 365525129
    0x9180a05010602010b011e0c110607050105040507240c05121b01111c090c0503010c020a030305130201080a1806020c010e070914040b1b040f080d0215070c050109060204060324 77
    0x80c821941fa0250b00012180c0b003901c804111b60308450181c85007100e55072580a010a05c3c07281002080c5454203140050812609910a00d0001046140301c1c0c1c146103088a0240c0810a51502240c12a90307810407900d0640707040d200e400807400002e800404450303110f01e40101865458002d0000907401d03160781100c1e00c6003c1d1600411240704040703d084003d0303034000c0c0b00b40c640146a950040c0e030b250780009007100d00101d05c91025a0061550908150305405150351044918070145c04441c0c050700081c11084009290b000f0450b600c03010300d0302c00c40c4007030462a20682c01c102c003103480d0000906127034002c0c10500c0c001c402900c107034080003030115a640160441013002c0c800140d41c2d612640e4903071422a00141c290304001401e181d041060b040740c0c0340500001d00d031515004005910303180c0d00900b444800348046007150800d855265040800c55a01ca0b00400b0b90b1600345042d401a0a04da401000121001008140000b5001541179410742046000b522050441601ea1b00c0030080d00300b1a5841e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 365527625 1250 365526375 365526407
    0x7050301060c0c030503030703050103150c0e09060d1b091d03073207050f060c07150e0307090c0e0d050601030b06061c0c08060a0f03020609180a05010602010b01 71
    0x8100600180e8400c6590380700152203014070654880e100d07070360b00b41541c0085070402c000a6641e0010024000000e03a4000a6550b1940c1000b40481c0c09400a00380f083d1034403054040c00d00c40c000310300c140d100e07040075400294100c1e03070315200884c0035031080c8044103180c0320344c4d8441340c00c0401681c00e154021003400c000202030b070700461902c94a03903129260b000e501102c1030700620691040c800c0d481130707401c800e80340350800e08041c0483c2418401080303252038010f00458059541030105010a0344001100c0c0d003542d00e250400c1c003848500d02d008130342000042800680601501ccc00000707010b5601e40100d0b51030341c02500c0d016100d241100034003c0704040c0000150442d80100010004920109480740d0010740103000300340f41040c11100b007080200c2d000040311195503201200708806038482d001907003003602103078072644040c40d080c1585000240c6001c080c2c401e0b40700046a501c40c0e580c425402c0c860f14032445044845103049081400140b109108200155003840345200c01d07984600007185230391000e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 365528875 1250 365527625 365527627
    0x61008060103020405070302040e09010902190605071b1d1602060f01140f04091505010e010803040e0a18030c050c010c080a030207151e0b06120402091e040b041a0705 73
    0x40c60b004c100c081c080181801d8281340d4200301c0070400d0304403a20f00d244922070303080003c1151079080c0f0512405644000304407480c0d0421030414440903501104441c081904881081041c00720012880380c203e00640c0600102c54600c2e1410840d841070f5004a481080d1342084400c40b2142204180e884200850745803030311140050050202e6445050300142078800038028520041349100854206c4081c000141c0b542448040c000858180c1030241902403d40c201e145016540341010032036a1380640c0c02030079008400a00060110b00817648103441c0c441d152403600c00c0040d0141405003d4004042c0103a65a0156420200142d4010541004881d610011113443c0120410085000350001482124903024440c1910700c00300060040c041140011503154021b0010001c0400c111803020303464902031041440034a078070540b0b002c4d9540d0302640640d1003200361307510703061180025050000044c01041d0317488184420b1222040809105500c81c40780714000b0420007061300390005d400c8940e8400100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 365530125 1250 365528875 365528879
    0x3040f0f050f070f0306050601021c0309020105071a040507121e0201020307060c020102040f061403010b0f040f0b070209070206091b040f0608030d150605040b0f07140c030610080601 80
    0x80245044080500800036608024541c50b8000d003071840c2a0310400c40060003040902c207210441c030403c0c2e0010300900080c03201c00c41c8844d01d6001c0581da1998001450b903140080070540e402413080f10181980104002403103010740048000d000001d0314144c6180c0304000003c01e01380c46180c400700d801074202228814003c0d2010440342d51202010040b8110b0100303012600002d4454050042403c080750000741c4c44030700b010207110b180c01c4184d04c60020486510301e0300080007182130403241512100c00540e60f65503815603881241d03200780d5100d4002c1c1c00b801c4d040002c9014003080a4030401e4400c035602c80e00ed8590f400c00f00d989a105541204a680010815080720005500c40d4000c3d000e0140000ca007030003524072000101c2d190355022036900d800025020141c0c0805200f948482004080000380550034000d008106004d14094000d640c00300150381c00d001d5641c0e0040e224400e81c40880080c034043c0403500f2a8a40000d52075490080c403403070011402e450481c01e84142a2001c203001042541c0c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 365531375 1250 365530125 365530133
    0x2906060304060f020304051c0203070b0109181b0602060106090e070c140a0605010315050103080d020903030906040605090a0e07050706240f060807031503020d0201140a0e03060c03040f 81
    0x64000350080b584150340302540d101d00300075800598400d0b405840604821a0711416000d4803200d105010702c1103400800400000568400fa00c1e410f550b04c0400015000c01c06407502440203101c81c0000d400f440c58100d1440710904003400c420252190360b8280c54035a40d9560b000c2e1a0351200740a20040c60906000103070b5020301c00c1507a094118010082c45101c564002d0269060a000321b41c2950040c0d0ac5000500c2802008a81a0464054254100200c1d80b4503100d040c0745015011000003101c1d000201804241e80400641300940d1005040c5980d495585001408980c8482c9040340a0741d03190b1400100c00f80745161707651040c1900c2c1c481b1443c040d050b50700e4000074071609200b082000c07080d51001900202c0d00701c00758040d00542054104841c05c059001c1e1000000610382c804050906150b0306610702c440310844c040380e80c181d0300c4039014440d81c401a41c1c0b151206242241480022132a0181c103170740103030719401145080d01664050b03210040b600c0c0040c802101d0181840034007201810000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 365532625 1250 365531375 365531377
    0x50a02061909050a150e0307030b15120a05060f0405030d0606030204180b01090b0a110615120c010f0809011d1b011d0609060408010f0f0f0e0d11010e06090703290606 73
    0x40d6070000c0940355003a0f12036889500d800030981d0580d80c5000bd007071080b003e90810012084503103134107034020555030300d0399600d2580d01e900041c8400811101140070404004040083e62a600b0b040302d024808141c842c64000c000390024411084045900c0116503103141441c03107441f14204041e034650903004c0c1040d0300c10b84154060f008403401c021144030000d0441205215042c0034600c0d6045d940b81a20f800f1081009240200c240180b682e00980d0009119a030001ca04082120003403c01da2400d5542c1d880003030050408203104400030081901d1180d5900d00441e0a500124803c00c2c00e282d40500e0200440f0070501c05071104d4180b5031000c0f900d01c0d0300e19150025040041000342860302e0261610010340c299455104c64240181d2180a00140d0201d68000c1c45240035500078100b00e1106120a038503540c0240c1e44409050150808940361000d100f034004002b00d1000310b04851540c142034000c80da07620701e140710584506401c0942c0106c039441c1d505440808440040c0710b10b440f512100200545 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 365533875 1250 365532625 365532647
    0x6240807020304030c0306050f06150d051b07061b02070807140409050a06090b060906091303020c03070303080609090f1c090f030b150922050a02061909050a15 70
    0x39407000f4000080010070482e2403001a42c030541c00896a81461100786803481c001422851048042010b07804031300003640c0988200840e490000b0945803140d80710011100c01500808054180010310030090014581024075409521b40610104444c00d80302281c8501e082e0140010a4001e80000c0000c1850040c460b01c0200000f400007a9115030365039000d2070f1805520301280c450740c681c0e100b2400e0207510044140c0c00380b4261031a1606145c124000342000c0c070010030b508241d203420a04076080c1803080000903041c040140407204d14607100d0401078080f8100711a0307284204200d0001030350080010032200c0404160070000d01180307203180ca9280800d50748800000400a04140c00158066810700010046014564480c654101703195424400780000c04858080c030f0405003846250040e89400030090003410417040001c10091038801d0502606203000f0b5801900498654030001480030608183c070001d80f5054180c544c1c60080c000400982c0c0f180b4610140d619550f41e0081e4000d05c08004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 365535125 1250 365533875 365533877
    0x1104120809040c02280210231303060b06040e0711160611010b0414010512030409020307080601022506050d0e0a080406110114010b0903070e0f04030306240807 70
    0x1080c03007801c0010900b202e10f5101c0900040e17009400c0c0040f03060080b206400841103410380b513400b241654011400008014550104000d03c1201c0ea8115043d01910100000024040030b03036503440502d20320300d5549070b600040d286203103418190380c4c3e24a8034000300d904540d04501da42e02e540c0c0e18290155188e410a60408030700c2d01515601c080701c00256140280500345039100d948594203820394103070840c0c0301844c0340c3e03000741c0c60040c1c2d4030440e0340816201030444a04595044008821038245030850180ba400884650b00200520400a400400303c8e072040c4000e03801c4803a4041e900100840e031114803800750110781d40d02201804024800c0c0001c0c050761a003000e010030390407458941c4500e440742e105c4060315880000720f0244100e0349d00626810320f10900f00d009004011103c0c0e60441e1048041c4a008841480043d8140058a0a00a40f001013031400c103803082c0c52800da0f03081648000121070490000b49032040110f00c03042401d8400d50103510190380f01100c502c441205030381d0803101070302040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 365536375 1250 365535125 365535127
    0x501020d1d30150c0a091701060902030907031406013005061023030606040e0a12031e06080a030e120f011a090402061818010b0a021011041208 63
    0x1035540414025115030002c0054001d081c0f980c40300c00c046842d03880280c025103002c3c504021440046921081c1d0006656142c256103542600310524580104856401070410764004020000600c00201d00d900440e805502a000d1070100b0554060300d5400034000c801040c00b0900d800305010078441151090b40c1c50b20000b2510202242d141c0600d0024100c0d03d00040d0300c0001428081c2000702550605890001d81480400c0309000c400a921244000c01c00d9020346e43d0b480c01007101e40c40401116074415040f00480b030100000b0b081c000c020b40b0000c994000019010807200707510340100d20481080381ca9185c040d001440a80c0c0d42101c40e0b114407007145502150b00301101c920080d0078000000200003000001644400c0b522554400d030300c10305146885046844200700142e12510100c075688058444c82c02c0a034040030340052000707020710340c001d402040c600340003007034241d108801401d1840e080d408407623100a1400f40c15064038680c4039058001c8000748410070090889800f9481c06c207114074916 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 365537625 1250 365536375 365536429
    0x103120c0803040b06010212180112060306020a12110306010f030506040b03030307020d09050306101814010b09031506060415140d0501031406040b0c03061f020102040501020d1d 78
    0x40801e40c0043d10141d480c6000310007030100c00d61301048500c0c00080510b60450604808042148500c0d0745100d0490502c4842515032801800c90f0303000c00061940840704640725009481c00030044807000300b6601c4194500100c14904160b600c050341c3c0300701416901c00d145001070081c214003400002c1e00030b540260300c82136441e000d80c2e014006144900d14a5006101c40c40d1080300003003074085151b1000b03020350003007820301c14200001c030200c0f029100c690301c01240d04400004003c0040501c0500314540080d15800851240b01c200000e043c4007808604455203a118040f6403601840280c404580c043d804020800440b0b0403803000c002c00c64041c3c1041e40200c0104c24030601c0c1a4896034030b05d11035a540318014010007443c0c01c114010f4415040080c0780d90b10386076842d20048000a016072189140210004a00ea03941c6808107407210300c580302c6980c0c0c82c04030580c044d010f5017003401501d0150140014180d80345102e03890f0404104413480107030700a41103520902519801a0480210002c910192 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 365538875 1250 365537625 365537633
    0x100e040b1b120c13120c0b07080c01050408030106030f1406010e010905030102070c0510020d02030936040302121809090a0f05070602060a090809010f090909140d02010b090103120c 79
    0x41207200d02000354075103079901c1500500d5520391130103400056007400d14803c0c1c040481d440104075000da400000c02c9550360340950074511240d00422041c0300c3c1540c2480b0810007000004406907048070847c0e2024880103203405140d074181c44007a4480444166100d002a240303601c10341010410760010705203204065104c1020a007643c2c0455402d81e0b41c500d80c0c603401c02043c02c203880c81c0410360b0014405003a120444004c020345910070b1655441c49014484d4a030079442513041c9002c0c1d0360310b250125040031006031211155050b0002c840540250080d5002010080c69103821a07c1e02040c07500d04244c442040010031620385806001402c4a00c21100b0b01c0b400250381440380782c8214056001801ca00e89840d0009191030001850b104c51142440c000000080d1002c0c02d82e0912340b03090030100c10500e8030001c12124108560b06c118401418840090b040c0141401412821404c034029648244800304040c0d080c1d46107810029040b115082c01000411f07000340440140c04d04902e00102c0c160090b440d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 365540125 1250 365538875 365538907
    0xc040f080604050f0d020d180e1906050102122b090309080c011701090203070c051f110408060117030c031219111602010c0c0806100e040b1b 62
    0x20410880d8442810b200522100700421486080d40307a00408000c454060003c0d1146241020030050203000d03a08100c0c204900c0200c0c0c030103002540c01c2100c0034549051403110550100302003001d4180340c40700108440d4808501061000081036003107103002d0603640c0c0d4034145400400c940b05a6019040104440d420714040d0150b030314041e40d6200c0040d41030a290906004001c0728490500400c009102480c0009281c0641160000d40006071651740710a030039907000081d45401031080c00340a0b40003102020f01c40c514a125800e00c00c0c204070303a42d0880c5c0e03440f45070302c51401199040d50051004004070810200040904140f01060724100001c1c0000103195400951042e2501e00484d81000b8200420410f001f00f2400307124818444810004181c10f480d10851803112902600845504256401000302d0020154403089402c00f80e036035110500c0c0c540c40c080d41e40f003804005040d8001b80140c1d0054841e03011366004510380200fa1030314503010030011040b1210003080c900030301c690500400703128 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 365541375 1250 365540125 365540129
    0x120f051005120303060108010311030a050a150c02150c0a0c08120106030b0118050111010b0604090e0d110d081e070905010801080115151803030201060305120a0f080c040f 75
    0x31001154036040004108440c526a15207180a078400d00410016a9100e03944c4c604407a0400105000101840c7c0441d05003001c400e0013030118424400c9502c200a00450342580300c001543c0e0400000070300c050100d8640d80154130900144c0d8094010030341012094006200e03404440c14120b008004655418203e42c01c0050150712801400004004143d018010380c840e07040c0074600506000c0035640440319000e054002c09040020f03050007086400030940c45099a44070040ca651340b9180c0d9200002c010307090380c00b4a0401e6000c1c4620910036a40202403803080418074002070252244940c0d070448100c180140300103d956684c80a1003011110321040a00804061750b4003100c2c0d50414001426840c03060b802030a9903807502a5140b0070741c418900601c181c4600c02c4191500403c08202101c0160a001d0108031755040040000201501503121200301c074402c9040d0b4146840e01e0001040741e001e80c20148010504409080ca0002d100385a465407003c1c0c2001e00d2420300da150715080d50811125 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 365542625 1250 365541375 365541391
    0x5070b030901051825090207050309030f03070309090f060504090803060406060207060212090f060c030a0e010e1021061502060a02040b1204030c1a010303170105060901120f05 77
    0x814416044000c1c0541c0d584401c14190f01c1060300e0040d20300d42e9440b841c0e550100038000081741c0f900e0f40b07440f40c81c03080130007001c0c5000c003036448038623a0411075241c0c2c0c0b00464040c0b0902ca80c40414403001e402000382c03441c10350542c0301c00807514034203100480a001c61002d10701e200340d526031021445540380d100d50242c8034002d03910b81340c40e450b1020500c42200c070990400015544640001c0003119070000c0c200074014854800191143d48590100d407802e20580c035080e910020216104139940d80000103080b805070306a90704480c281e04900103480c082d540402c0c550300010807440508a83e40903003042005540080380d400100e2032340c80c80d01021605541c01c4801d0b000c64800c0c07800c1c012a8100310950300310b44800c004600e02403800043c050b5501c5907a10100d490401500000c1c18540580310003000710350805c0b04138404070303428411110208002d004c01c5005c40c5043c0718504102640460f502d050b01c00140406140030414801510382a00c05540c02403442d031601d40320203041c0e4090148501490ba6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 365543875 1250 365542625 365542627
    0x3021005040e0907080319021606050307021002031b0c0a020d060b0f01030b031b0307030b0403080f010603090c0905060d060207060b04110703020c15210a0c020106080303010314070305070b 83
    0x107000c0d0b030b00700140e4080d02400c041d510005040c0510440801142c918a80380b03400e4500c00b036600c0c40247d0031700e58803540c4520600341c00007000a030039801400441c4038103030690a40c1c4180300e940e0640d0080340001e4640700c0f1007400034400c030184201020002c00c0e14112900484180607131690008020307450319401113a480c0d0f280e641140d094206603068000302d41c003d08050002a010342e0100356150a136030b28200342c3c0c1600a50f0f0307103100d44062041102458100f08070314118601410040d0a42c082505c1104006060100008142c3c7c0300c0c6c807901500075400307a4128080c03882c0c210380c0c0014041c0070317151581c00002c10340500c000030500c0c4000e0654a1180c42c0204d007040d60801004122281403191261007001000b017100041c2c0e01041e108541ca00454200e07114014020104545000c0e41081002c8c1d2840381c1d664502d001094591648500d000c154144050800010201c0c269100d5129081040d070060005000090a20b01f0b40b03d40c9006920803100d04641d02e1b26844d00d4501240e0004d8440d1074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 365545125 1250 365543875 365543879
    0x44107050a080a080906070809090c191b0b0c04170114060f150a0e060a0815060a1b02040f0908071109130602030601120507111528060302100504 64
    0x40c01d0840c04010000c0a010380040c01442e01da162076840b6542c4005e10510000031031004116001044c1c840403000075200752104d24043c2010a05a4802c840030b000c503041d80c1c551400b1842c4120007a8014690046034801c44034225078030300800007030243c40300150710810300000c92409003c10340444d85403400b500108003001c40b1400c00240c040007400c505e01400c2101581e02264035003d0f52400710300e40010b261580c0318802c541c111b40c081804080b580e4802c1e00080c80800d1303075500c10000f17400340b1b903200342c0d03402d40180c1c12003044a984144544000441d00f014543d00e03204806400550311030340050030104016050500301011540c40d1002100c0600c800300b10003042c0406991914001c550950b00301c0e10364100120102e1140c5030540d80103151980003c0010400d9101c0c400b05d042d10701031410140810300b040c9002070002121540420b0700b178451140000a071102508045009201d41da44025201845401ca01c164504010403403580913101c510000040c0c44d03c141c503041d08103032551001d4444d8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 365546375 1250 365545125 365545129
    0xd0e0f060702070f1e0b03070c020a120201022a15040302130e07140a0909110312030603280809030a080d0b010e100206010605090406081c020c010804410705 69
    0x481150813010141031840d110002c080c40780711210017500c0e0700c840310076107031742c1d23224011546000c1030103000750000000040011040762080d02144424401d800b0750320084154550290344100d100104420000d99006002003400d110103641c80c45404201c069103019280c0e00408e60612055072613044940d6681c07400652a041400703044007402102c0c0c40b125003442610001001d00340507004580b4003590b5105440d0400440c0c01c01e291200c0c1000d03007904c50b0003038034110089180c0c00c100d070154013a00504a001140c07190001c04407070440180741129205041c02c0c0c44000c00c680040200035054815070321308002041001018014203c0e540101180c20722601e4001400c100d24141c6e814015400c28000c2e0b02404d401042a81c10340c0e6052408907100d2038402c0000b80904990303401070744203001c1d1040300c0c03902000f41030700d62024a00a40880f61082c032a4001122024401c640c0980740c0b80b061030750095585a8051100082240651025400814107050100700451103a01c3e040c5940840030030010381c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 365547625 1250 365546375 365546399
    0x30f0c03010b15030a0c11010c03060612060b030c070311070807050f0409080306041a0d050304051c030f03020306181302010909060602032d07030c0b010f0302060d0e0f06070207 78
    0x7035031041c1c0d03d0400c030306500080e80586020181000d00340302d8840315405100c030321680c10311042d407100c00028440c0200b1040c1c0038000b0000c1f40156000600280140c8403c11030300d00900b0222100120810301d980e44507a01883e098009a9003102041801c1071040c00b14001000100c001d011160054003241d441e180c00c02408503a2803074024013813030400840002107890002030700d0340190165008900080ea001d90f0a07501c001c110415a400748203000722006008001002e403060710016940782c06011254526070b00e058070b0064000b000200400e210506841c0300c0d8000d03540040003d03050302d1a40460280305480a801210400c10300c510581c10030041d980d00403004001042c40d62010003c0c9414000c00079142e1080f001c40011401c007082d50320440130091000c600824a0b0b1f900c009440d041c0c1d030724000700b03000f001042c2600c030001c21100128082d11002290f100322540201484d133004a050408030181010352103551a0f4042c03a03480801d00341051003994403c0c021580a40150707414a40802c8030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 365548875 1250 365547625 365547641
    0x40f02090a08060907210b1302030d020f01060f0302060a23071110110d050c0a12030b1203030702031c1506080a180507060804080d0216060b03030901120b0d02030f0c0301 75
    0x1104000800180400a0f00300d0b040c6d03151780008440005581e82c0441c03c60000715081c000790144185000d840210340d002c15110309040d40c540092003043ea403554426003418107400060344c0802c00b0000c01481602501201003020703000c00c2c109a410703044000c03040c000c1c4c0000701d0996144900d03d59034010740c0ba11240c00700707030440d80b07061199030800d41225a41d80c3d6102c051844042c020001180c800218082141800866001070000c13081c010f80d40e8010003070003120740280d0240784600719810f002100482a2441100701c0d47c020341c1008a0320880201c09400640ca0ba051150344504400308225644620000381c091a200c40d106400c06040150071151030409001009814000c424002840820303500226201c510306003003d07442c0c07404c0220162040c182ca4105291000584031700010080301c500c145280600010404515410280350b200e114107000140001c0c4204a0754940c407000340d02c4800c00550260000080650560220b031030500c1d009401449544030603d6650285424000c54071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 365550125 1250 365548875 365548889
    0xc0b010b1204030806030f0a06060f0605070305090616050f06040b060a060e060a03181110300b030a0c08281101030908030f0f010807060509040f02090a08060907 71
    0x101d82180e8490002081c070016100404000380440818000c1d5001c10030540c865a640066480030f030031a04c1d0200052210380704800c100a0b46080009006001e8416034034200d4041c0c58152400c5440d10400c000c0d540021980c4002d01e030401c04e03440106400f080802401180c1ca402006942020304040030b4221000b0146c91250414540c14030034a5440680c090800000359104c80c0c07034090102064000d0256840b0640c8a80110300c800414403940d010103030b14483c0181c43c810540d55903820100e5020280e41c583c0034130300301340204e005402100124060403a00051000003020303914600000d081804582065800f007055200901802000b40840c1640103942904d03261610b00c816507403003244184040140c541118a9192561640a0340140e02001c1d84040e440b60f880c41e0401c1004803081d400d0f03600f0104200c079440045070a0342d000800f40e055900c0e070b468a905013212a0704010252160080e2034560980030f100da00483d8440d1041400689888ac2c080d015920b0030011091a00342d403540815 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 365551375 1250 365550125 365550127
    0x8090a110109262e05060d050d0203120a060e010b03090f030a09180c0207050603090a020a0603090b09010501060801120c260f0109030c15020c0615030727020306010909020a0c0b010b 80
    0x4152981240e1138039558240c240209550f541e48000591400610710301070050f00800e034441240c1036000c00245000d44c0711080101040c2c40b00e0b6842030031214680501100c410031a4018000c1c022400301840e030040d03903802100c5420758800c04030350075500a01009004220700c0c41d0b060000d929032190546620290320020050000c0110000f903660102d481001d01130340001010a078441424030502e800d80750068845880740355103200080042645100561b1030140c102c010400b2404103000381412550a90707622405071742040002c01000c18811012900e075105100700003601d0001c5482540601c40b9454411700d22600c4c00ca0580c105124224074191591410088400090b0022003140c5015041481c1000000ba210708800091007104444045031088a042007000d09900c80c131004110001d038140e0700d000da41d414a181e141c81e0651380040d841c40301c42c07c0401000010b0760241d940000149401420340b56280d05040032a413040e000f10340000c00d020704a00500000030005401000e42c40b40507 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 365552625 1250 365551375 365551423
    0x10020609030d020a180605070308180a02090618040f05010501061e050a0507060216020f0a05011403060117071805091e0403050d02040f080c0108090a11010926 70
    0x210786078070450001c49411680031494041c080d114824551801011601d020f503502e40320380018000344c2024604070005146a030005507031103480342d00d56030f108004100804580c4000da08100171008010150740c3c00c275004c51b00320414400f5200b295401a030203010005407150581c01c1042c2502d9050700080c007880f200880305401c84034080c4400743d61903032924245413126948902207906201e400c0c005440180042120554030b9003201280d044244212403a0020f000300380d043c0b00624016110744d6000c290100520515210914000d40d4000d034145445190400c0c1d008480a0360801075421200080b031818240034290030b44a1010702a00c422901201e56160802a442c0e0744055451110141032034440440d0030540200c00b038820881780c11106545841c5c03a01441c040009883c415294640300300d1201c00b0f0154010301070f20b800b80304050f010348070203202a1641421051090300050402030055000500d034400b4040040c9285034000c5010360208408011902e00914104050800310099801c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 365553875 1250 365552625 365552641
    0x20c1c1e0339090303090605030c120a050a0b040501060909050a0902030304081e07030210052d0a0201050a060506031605121003021206092505120609060106030209100507050a20100206 81
    0x140c0c2048558a14115540c4d41e0340652001c0240610951a45d0020703103142844cd107401d280e04100d208a900072401c1000040c02800c02c0251a001c1c0310f084041100090284600e160350340099902118074800812a0070866010a00d1030744140d004683c0c58100c000311990078001d000901480d008907800030400c440c11b540011352400c0a2807006000d1000010f01d200c01c25000c149802c414031f4034204074010030345c841c0f0300c1d00c506503200c14440801546044000340704e5401511410080d40c10280c031f09400c6544140307140f01c0f410f004911712810b01c42c042c00440342601c01d29032000d10400100100e074040700d00d14414800040d405502a0000e900414200540e4034000a80359101d18900400201000c020136200c1c101c0c41780300d8205079048a00550280003844000802d5805400e0000407241641c0ea07940e001c904900911140e290b10494598074000740c90301c00c0000c0d102c0c1c1400750066036081415640c60010917024981c1d0a0000024984c16210ba4a414010400900c8444c00904401d14101003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 365555125 1250 365553875 365553887
    0x15020414040506010e0a0303020309030d0203040e061c0c0f090f051e06010908030d200c0c060702010504050409151b08060405250201020c1c1e0339090303 68
    0x14514000c607502c50006915030f00c01e1403441888680a007002000c00c0d00d904009440c1d2f4800002140244140118451001d01c0001250101d5410001c55042500e9034010856689007071401a0b840a180c45002c40110f44400c244800510042034031558462802126800703032920b80a140048510b00b50403c4114410320a215400703004400b00d00b01c0390f5032074600517161861fa64011040600c004210406e207025103034050590820030300d40a0300140b46c00740780061213100c0c1e01640d00b60b80e00700184c40c06140c00c04074080e0060510505000c0c0c01c05407510302080441e0b192403000d403100c494121a5903840b2110344280c0e03183c010500545a15121a00701c05044070360301401490140e42d0752000580c884440c80c0048019180500700c14054041503039009007c1d401c0106e031503d250103101481040031440c404a0000550301e87c850398124640328841420000745d45605270b0500d07442d030315520201c50018241050030b0180d0b0882030b0b5003042c46110461b602c42030b0801c1784240301c44042d003480442d0300aa = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 365556375 1250 365555125 365555159
    0x307020a02010806040e01021c0b0d0f1b050603090a0b090610030b0613050405060403020c0f22090c08010603053307030b2d011d040b04020403050a0f150204 69
    0x708007400f5503194000410020507104660501c0e652000c10140d02e580e0110385c0303400100f10001000d01c0901c40000c10000003160444c001000051140600000140009443c94048940c43e60740320005540d403020030748603407003112400c01b25042492000200314010481603002499030001344114a800c7c5c50b51250f0111500018042c10940360000300595111403002404c24a9644180407908140c81c0041d900c0c0c20946003100036000740710103c0d5460510400000588400801d00300c00300307028030f0100f40e13031f1541d44c030024900b20f8807060f1070004501001c0104008092160001890500d5402d01508004002880003804605a21040302001c0380d00900c010451844098002c40d4030b5562050700245401d009494000b201c401d003031034032003c4600e5000d00e039950b050710700d602040001004481003042c5400605c5950707500f07030081084d030a160f403142c2021040604014035060301c035240d817450400c440000311114155131760000200002074120040781c2242034403c0d41418180a5045030b091a58 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 365557625 1250 365556375 365556377
    0xc0306060807030f0207050a0303020405180402032a0a03080c0d1e0f0c0b0411040c0e01081f0e040501050702011508060604020703031d010527120d1401060c030f050307020a0201 78
    0x21003400440711302950484d0a1550711000300c3d44241c045140240180d00180f15551280d400c41d442000101d90840a55114550082c05840181d42c031140041e41d403406140f070b64248024880500c1e03403035219403c4c06000745008030034241c0c4444030240b149260602c00d807004810480040c0c00c414a07100d008040d0103c0d0785030790402c441080c002c02070481e81d15145403000b0b054045030303405010a02211307112599114506403018860101500c0c0141e494804844a6500059140c0c00046809003908480040092440d642480c0c0b03a41d241340c90002c5580644050314242d41d0351003403282280c2c0901c036102078607059210202d03005140007401c0d42c50710002130050380104d40020344101058440c0d48103011580c03401d0004061802e9035410136008003003c40700e40002c2c0b0611078404034440c06181c0000c1304044044000d1510201d0607003110402d0708076000344180300740c07944a10055020b480c4002d601038400350f510248940c185003001004000c1c0325062800307005c1d0810501503401d42c003044107400780ba02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 365558875 1250 365557625 365557631
    0x11202030c12030f04060c03170402180421030203010f0806101403120408010905060a020f0f070f02031509071e0b0901020f120a12020a0215250c0203010c030606080703 74
    0x102c00d04282148a0424081c01c00038000901003201768001001e1032805c1c0c081d958020600c030509015034a010b90a44010f548800400c0b403040000c0384410003250302520400b0b0300031000c4c0341c80c10700c0c01244070703102e00400c0031a40101c0140704001c0c0348007500004010400050505060510007003c2e101d0560103441a5550411841c2109460402c24188160b00e40e00791540c2d03440c5e49809690083c254080100c40c60700400001c00c3d0000c881c2d000745d604124511004501d0082b1601003881d80b42e1218404a883c030008041680141e40d041c080450340318090102c60340300d80381c1890030f1410201c140c0c2207024403100c00c5902d8011041c4290001c8191000d0500150340d0303003000b800607072900002c0c5000c12818410030071400c90340c6100d04007800042a194462405820307010181800740e000d40144040140d016080400a451032609031940044260840380c0200c01c4540c0101c08546241041d00003040d5840d482d481107040034809d0340d480c2c0790280b808008041c00c140e4001c00780d071005400c0c1820191 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 365560125 1250 365558875 365558899
    0x10506090622030309080c030c130b030a06060b19020d230702040c021609110a0c0c090504080415081509100b131d07050d1107121106011202030c 64
    0x4000b0305074032000008080c0c00c24000d69640741c002c2202101c2e0180c0c1100340035a0076202c8003400e000541c1c805002000703040c80f214070000e11001c0024140411220341c10300c00c1070780c0f000224900b445400080e0003041c030503a40c1c0f854030b0841800b10040d04a101c80456000385540b244ca00d910560300c12995a004608540300c5800302c4500755075019541029601500e4014841041500064511800c0001030f460010403640c40c494003044400c0115402998901001615810791140031001c82d00c51252290140d0035454004c81c40894104a9040316400c900090a001c07201d040c403102c0421803540d241841240c940300c101c1214455015008901a800f420040382050003400d8156005e46888800e0a8980310360b50100240102244505c4122a40c480c042c200c4034200e030304d20b45c0c0c807030216500c89502d000c3c00c1c80c040f00300400111310507041001080c0720780ca00050422255600c07028096480d0f20382040c85095190805206038403404d82c20145e0720080c00180c80200703076412074a004031601c2c42521 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 365561375 1250 365560125 365560147
    0x3010b04090f090615030c0f05010215071107030b0103020f04050402032109030f01061401050f1914040602010506092202010806030109170c06070503070806060703091802091302030105060906 84
    0x2c02a06070081a1314100000342454840701d48503c421203005000b8055031580e903800c04038050005000386c03070041c0c00485010500b12241c16405070014207901d000c44c074644a441c1600c2c208030702500700300e03004500800100154500703c81d2000c0301140859080002d03050941c00643c2e19010218261310070300307514060700c040e000ca40f0241c40032004090151454101c9800c48103009042c0c900906c3c03540100503074415000d5104500765000e2001500045140034000401003098900d042c3c107002c1041100d0580510300802000684020040c035000400c007402c24030304000410301c004040c0f03040e00c00d003400750103203144020814456040e02030808030b0940d2101c402181c05480002000751064480400d03080c0e00d55440802000c0611880058495584134580c00b2141c0380f005a45060010b03050201080707540ca0b1550080023943d01c00d0800d1900c040d91503051190782c422404140d221580d001c5030514044c2482c42c0701a02842c040441180f440d8141000078900d405103588481c01520302160044041c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 365562625 1250 365561375 365561381
    0x3010312080c0f27120d0908010c080414070504090311100905030405060901090b040b0403050d021c052a03030603010609112b060b0307030c1803170904050a0c0e030303010b04090f 79
    0x80e050107440b11400c01c1c074805c01a40d440341c5081500c4002101e1039000100c40c0c00c1072042c1c02c83e801003a81e402d143d0b6107590302d0780b034440052444102c086010308540041c0941c4e0398882c41c800b00e88203845001618442400c0da9041c20303210100d030440e20303041003040340002c0c3d0003008507001d450040328555118241080101c1d9040101d421441042c10b0010b404183d24080001038400c07a88260107c610035125030100324ac503003411020f907404000c4030442d0685a20b008030040c0041d424140300300c0c010100c040001450030203d42c101c1c0200c0c1d400010611400703081c203000e0702c005851050341c1800055291506050188035200d007000010781d8031071321075030b0040816211000213519818248440e50700c0e004464010360040d141c1d100070a1030101c803003461a01030311513503002c40c200317841e000c5419141d40c41d0138007810510806030401000130040000075584511410b4065409042c0004800d4003050014000350700c00d0351044e100f540306000402895a4440c01c030f1702a0340348001c0104036a0b849403012005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 365563875 1250 365562625 365562697
    0x1f230c0a0618060f150b0f0904020304060f0203070804030f0302041a0705010e0313050a090603031b020307080d020610080f03070f022d0f010509030d18050603010312080c0f 76
    0x70084c00d040322541354000c00d030840d90302d13690702580d01c1403c1c0355280500c00c028800e00e01c042a1503c4144001020713450180e0145a016000b80808245e0f04a02d0140d14200c0c2c1c07044804601040150041c0300c01c1c96403000383c1484c0c00681c0d04045152904186020b00c4401031584130b0711517804009448803c0001c20740100e012418603100300c035283d40c040010344080661a009030b03070050011040005600055004400403290035440722018070b40ea840b001c55003442d850b40305030b800d0712a41000041d401d004010261a0410941c007408485c1004041405900483e81c403502d03140c3d1100740d00c101100700100c2150015607020302c40120f50b041c07607c040360303000402e5400119084841101c0c3d60807114941b000040f444412074502628405010055a01c2d01400902607010390083d4482e1403a2030107804010007082095508050303960380e542c0000c00700d41c001d80003246e096040304c80007550740b03030058011504440b5002c203950400340c0d04c0130600c00c82d000d42401c400c440a000c03410400031910491100b88 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 365565125 1250 365563875 365563883
    0x203100323070e0a0e0102040501050307052a070302032505101101020f0c15040302120c1e012a02030a050307030f0603050f1b0f0603061f230c0a0618 66
    0x20b082607850700001c0c6030082c00c032003803000030f810b00000b007120300d01c10710854050322016100c803402c0d038650050858039504422148482991040340f0001c2e010030074401c210740c0240c41c00003025028294418941801d20424442001420301c5c0c40c000c0c81500c03404a0300c001c0e42d0003a141e15800503000c103012240600742c0800080c20754030000703001c8001d220300d1000f01320102d15035086a03c6442d5550040d44079400c121009001070b0040e20000381c030414190000c1c08402c5401e4200d40d0ba01d4194000c1c8048141c040d01c40384039607175691250383d240f1803060b192481607000c5c0f0f803243c20040c0c05408019480f48103041d017020802000000183c04180a50701140300380c0d035402805c00150340c603403812503030313440f41503040b9100e0388150076101e00e070004004151449000d000d80035103520800407041c07000e030390005402c0692003c0441c000100f110a001c40a202646541c1ea034890a80c04212100c0110a03400392000100c907802c0140b500403120000700007501c40d50052000032003c0704008020038205550400030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 365566375 1250 365565125 365565133
    0x60e010e15190602010c0f2102030618090a02040608030703050901050702040204080114040302070b0c03160303061a181c1121010203090f0610090902130e0d09090203100323 76
    0xc80ca8550541c001131b880d40a5890740310680381d4440c403e45d11110701210219171059683d15071914513030307142c000d55000306c40500500b640e1080c032907445608035070458000d41154400500f030790562805018000c02070481e040a1403800c0c6090300e000f40a4415043ca0505101c40080c181c407c5441e2641140c000b00305240003007003984140402036848040c1030314150014440c030f900108018503190100e580e040d0700d039001036242c603000b13100c0c130340c101c40306108203406240d65448001200d414036056001c4164000740320540d07031540c2d28000d5195142e072803034650007400e86d800181008180604120350003a0002c00040c0c2200b901000a015075065451f0195600494040003140146c15000796006046400685550680c038194050751110201c030401c120b20f002c0340b810403400e4201d9001144244c005840b11004a801c086204142da44401d025aa0b0b03900402c52602040e0b8172401e0000a40400001540b82d800c00301092034148103140806084c2200480b0800c2d0701c004584103072820310300e40005039 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 365567625 1250 365566375 365566379
    0x60f07140a031b0201062d080609060103032c0603040501150b0c1b030a02060c0106120c05100305060a15090e10080601080a120f02030702031f060e010e1519 69
    0x401400d0550801e641094405a8540c3c500740107005a4065921000d4900407103148080c0b422840d41c02804501d01a40e416031022915100900c1084d00c0b45030201e00030522545585802449040d82038041c18150807171b512178592660501860740404601228140c1d12901c40d0300b0280c3c014011500c10510144c150000060040081c5000c1d0010503040c030207079141911944141d5401e105034030801079254014102c07150041c54180041c1040282c2800005807942c2c44003820a0034240100050b50030010244c800c2080b890455040c40c2c10543c5446c007400103003041d40208071f8000141c0684041c04922080c0384003000d10800c0080004c14a110b41e8101d5400c0201c0740640420450282c02c085010300000442c04c0e543c0051001d02803688081d402a40c80041d0310126040d00c0010300c014214042000140c2c0513a0b410851704021100c81e142502e08000008000b400700c0d903460744800c000c001200010020b20360480e140ba1b83c40302c1142d40550704c40c2180310001d8003402042c200c68210034112900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 365568875 1250 365567625 365567627
    0xe15010309061d0606131b030c051306050d0c0e090703110f031005100c0b071209050307050f060a060305030f0307030212150907033813050a061205060f07140a 70
    0x4818040c0d03400b62000c000006d180e1010205076a040c61614005100030f003080b0001c28401e0303200c00102c003110f20705642400c204904101b520000c99000100013003020442204283d5148a40e6641c1219030400d0441d105620001c100320420003003400042c580d032100e8912104081404940c141c1c400c0d03150044c0d40f07103414118280c1c0d6170740b1801480d000e9003502100c148000d00442440d00b1503500582d94050755960600d081b2100190105643c1c80a5113a0008000080081025005070307440780025203a210307040c2c007100b403070500b0060000c1d002c107081c030300104045803000c800c42d1794641c0c00008580e0750750b983c0c132030a030084d115407400703003600710660f1041120b941411881c1400794002210b44140e680c0b9a01301c1102912443e4042e40c034103280d00ca0503004206003248001040760041c6e81c01ea01c032840124002105075800c640c1c050b1a440e151020420311082900c0f50001a1201040985c62890940c0310b5507038a55008007040403144144d00460303e0940101c403450b920101d120881d03540d520702200 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 365570125 1250 365568875 365568883
    0x7081e180d050c0d1b06090804030b0c0702121f0e1603030f030c030c0e060306030703080f04030506010e010609261002071208150d02040209040501060201090209010e15010309061d 79
    0x1420380c0e050040004401880d03221700c01c903100c1150b48440101e030f01c00051300c2d0b010007005580d40848100c0004c00c000000203907d64550340c07243c02110820360301c070065070062108150085188081c0c0d6006140c0d4006180344000c0f0041000101e8000014410b08542c0c04918000b000400e04208880c0290000b04140d4400c40342c0100e10b0795a03409101880c00780d58143d080d147e01c100300c00041140c1c07110408036030800318091903000030b00070100d036010f56480d00c0d0840c1580c03019903440e02d50302c00040c090040c4041005100e0045c0516021142298905440188059032500800d15201000d0b605001c200d0780c1010400101104441a034201100e1a20f02d80d000794800f4004852461401040f10140c6000c0d41c11140728203210a407003401d15844a04014041c00d00e040102c0e0701660a01041c41d0790380366403203414064681600001030030100d60040205001c0140e01a18241e00752508000400c04071a4451148e04002e08000c070701d4114902e4188068004804c248180c10741c45802015601e034002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 365571375 1250 365570125 365570137
    0x9020d0b0601170606040b0c2e1808030f060d082208010203061503090118110406081c0311121501030b03010204030b0114061902030a0807081e180d05 66
    0x1896602e4010907001c02d59590440813902c042c3d0000060004020032007881005150003d000340a65030b41501090658400d00010400d00351641000d00030405884003503c200615008001c805145102507070391140c0b0144001440c42040d914060003040c4292140400301c030440e544044641d442e00011002201c07070120000d0086400c40450100003040c80c81032084034051100034007811050401c0311070b0140766503c050050145c82d9a1341c8110b541d80c028940384110481d00c1003140704c00442041d0b0401c01503032015000a561074008201200e400c401c150380000781c025450401140070034040c2c00c1e0004074001c28440014090030f400c10421010185942e409414100342c804004200842050601700d000d2800010b01c900c40240052002c0300302280420b4170100000d00d03031898800601084018200c4000310540583c0c004600043c2150b0800401c562200d05450400c0f1103241138403522a41e001184070142c048854800400c0145540681000d02d071030903003040304c5119410b5400202903500074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 365572625 1250 365571375 365571377
    0xc07120506100e06010f0203042105060a05010b04030f050c040929060a0303030f06050d0f0308130804050f041b0f090503062503020705070b03060f1206160309020d0b0601 75
    0x100005441e1003a920b502e1000d07600846860101a52504015680210700c8001041548011300001a6586050450b80030020b02403000701d40740207075480e00341c1c90b141c00039101041c120300f4900140300b5030403902c0540c0c2c03c0b203400075411804004542451030602401161490f001414a118007003400252002c001306042d1541030300044521503250b00840800940710f42c0d40c403800c61042080440c2c429049501d02c00a05100040c900d99142c1c00221002039000044a07000800d401403018141c102c04030302d5010018248542c00c90250b9030b038100b2075100c4c0d401040d00c5820008100304290305d490380490301c40b0b80027040c250020941d07650060013035640e9400d00c9000130700c0c8c083c0c08144c0342000300ba039900450080f0b40d190922140c0005070940c40c2c00c0e1055650070164240144000b16100300440e80c0105024991260340b8100711050050540c01c1a9a003070040148081001050500055195210760442007407100700c4d0b09040c04402030b100040d0042d501150a5400360180081c02c80614020b103c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 365573875 1250 365572625 365572633
    0xc0c091b020f06130201020f0a051f1a010809100906021b0115060c14030d0c120207030f1d030a080301170d020a0803042306061c0b0411060c071205 65
    0xc000200d9454000035100405504081c001c034500307015110b00c24010074414010354440351001c0c07a5030f500d42595440161610fa000300004071541514030860030b840c1580348028400c011045c6000c09d00c100864003200c0c104003280c80014444002800764004030001ca090902c091001030400e40040c0d000032941d031882005a511888507000148644101c03108001e00076050640740410a407070b024690721054400154100d0300702919002030004003003810100400085070003190f40d00401d03141c0c0d599850711910348100a10000302e500183c07810034501d914030340004803080460600e2880075000d1070f0381e0b815210740ca980208110b0040040c5050320030300180e4001c1d41e00300c00300741c5d56241c0c2020820340158111101c9040442c01105c01198003500074407510030f118000e8624214001418030002c1d419410200510045152030a15101415450ba00c42c115001e0607883d60f2050101c0a403000f00391205600003000c0035114074003070b50000b500c41410b40c1c1441340d0302e00d030704ea1a840c40c100c82207d403801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 365575125 1250 365573875 365573921
    0x30b0601210b010509150406031802220e1b04050c13090216080a021623130e01150e09030304030e060313140a02010809030a0f0c030c0c09 61
    0x12141c181400c0e80d46035401510314088000503624020940d01003054100072081021900d25114143c0c0e80e8003060010350825600c5180480045c1201e204681f072681450400014801507650a5014a0442084031a1603900180b0441003401001d0041c9860082c0c010b039104510f10071905111604107000c01c0c1c46c00d1183d65a81d8640c81c1081c4100650340028511303031501404169090740c050541c1c0d00f100e04032003601480c0c5807140207081d000f0686850060b80481c5020100c0511286014024440a01d0741e030710744203840c00824022a0f500c0b4180d40604191003006600511030382081e131071002820001c0040b0055401403464440c1c80f400f07100448407209000c40c440140000850b886640c01d903407510b090b0031001e0108926075001901044203400038031025808200d4940c3c400e50720f1500342000b000b104005100140a901e8002d000c1801d941040c0010825150008a203000040c1580381030700c4c044d00346140a4031540c0703500030301818041e684203010500f04016800408180444100c03508608 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 365576375 1250 365575125 365575127
    0x301141e060d0c1512050f0603010b10051b10020406020d18060806100e03100c02010b0303070c1e03060e0703061a0a05010305100e0a05070e0a08030a210c09030b0601 73
    0x1c40803038801040d44448030000c0101c0c4190200d5034410250078038261074003040074405c403011344206580d04189407811000b40000b03440c0902c50204092420b40d0012007405a910b40605035006141d10f04500c1c014508070348800641c2805005c840000360001151126114003009540d0500c0464200106003850f01d050141c21141c200e20b0f0881b03080d40e98295448e078801041c04540b400c04400a001d01ca02c6014a000380c2c0d03014460141d420401c4400020000381d0308000034251182047c500c2c1c000d80003000010041040c8070403840545054a50102c1110b905440c04407150440c4d90010b4032907440c1041c0c6440075000810b402e412640140003e024820f00c0300720840e000368110b0a82c0740c0c4080645010000c950003604099030110201d0000c90440da6500003c0b051440c0c1110440c42842d610303401c0184403a000351440e0803550041d5410841c1c0c030b0412801c0307540e03403184141e030606101c0340001700e07010601040c417401d68410344403106124007145003a018020140e240811501543d4400c005010340d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 365577625 1250 365576375 365576389
    0x150102032803140f0403031503060f0c09060c05210705061e061818032b050f0105210c1f02060c1303020f04060815040606061b03030b0301141e06 64
    0x42c40c13085101d0540303850343d42d01034008090761035a414155262010010100d0068030030720442111000011500e8000d40d5802010407819400c0035042c4840000c0c00c0c408a1800621003103040e924070340928021070325081a044a014180b4001c01c0303841030208001402d4070040da0071000d0309001081484a40781d25082207050040342031041c07410480540001c180c44a0710000d406042100e01c00d807840c0414602c0311045600140440801d1080315040a0121030b02c18400e0035485aa0085048580d50603e400500805c1620410240040c002103900c48090340c1400b8500c05030b2801050f1520030682c00d0b111395030760341c010b030510b40141c060600015502c0710004120f8581d05002040101f11908560800c00e030404072030f00441c0c00550390030b800f11300803008020102d1200700501003071849151614000d0252955134000c0c108206000c05080000c0c5a54289100d206625007800300d02a49510046801440c0f48483c0c0003d0141c06004e2108814103041e0b41b01c00461070fa041038200e41d450006121700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 365578875 1250 365577625 365577631
    0x31208091504030c0c030c090e1c02120f0409060f080f010c02121e0301080a150902132d1b090510200615040605040b0915010203280314 60
    0x1c0544580025000904c00c407030f03441a8038032407004400300300d4807a1126600c6080d035811089800ba51074440c982002c034100501c40381603c12401e6811248800304000303480394414940e00b101c00d00d0200307010021602e10740a43c1c0107447c6690040000d240d9a03d80a5400000c80c440c40c4194001c101074230781c20000600404041c1d41c090740080000d10040d500c610650340c811049000b160a1120313a010752081b031000110300a001400050845c2d115a041c4070b01c43e001f003e4405804245411006001601c4500064802007000e40700001c54041c1c0204103140d8180c12800c0c21800022042581d40f4250a54006541041001280c2c0048a44500c003592020b01c2d500801d0340c0006007180d9038081a01c03801c888550003500c100501012031060f01c02615002c01902c6516403824822003104650078648901002450f0890302030000118010128502d0080130b061403404401c25038a011140c0d008104840c02d242142c01902c107152a10503281d030b81015801c1d51180081d05004120318000360803291030b40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 365580125 1250 365578875 365578903
    0x6020d020706050624091203030f0f090d0e0d0f1505010e060a0302012a020a0e0a27020409210801030210030204081203041b0303020307030305160e06030a110403120809 74
    0x1017143d466800c07181c1c85c0d03042038041551000d580790254041840500180d80240e0f016513810341542410f4041c103103603980003040c00c255544040d1090002c0c0d903120018064150301502c210401151a0800400c07a442c1544007810039444144030403084806940041e0480341214500c0b4495100c5000b003200040c002c1c40042c0c0040c0ea11105052000352042500c0140018075824200114056002c981481d030103500c11703241c2c50415000c001e0a50300b81d004d80608181c070101c45d003881a081c0c805610024000c120044c1c01607039100e40510420200094009800c0e0306101c10104c01180d07504d00900c001000d0100700d000700c6c0520801c12481c1e000c0d000b95070603100404090030341060341c0358201e0000d800003441956611010a0b6407102c010b07086141d040070b10300943c080c50340c030065810080e0030340b1805800c0c0200c0c02c20040e50042050b5000300361130b03e03588040b10003d540b503c0340b0350362402400e002c00100210260000d07001003000850b030000522070354141c540007020390b00d20000c00d1301c40840c459980c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 365581375 1250 365580125 365580169
    0x90f060408030703180801230709030210210e07030611070503091c0b040602030406150305070b07030905060a02070524030408030702190b010918080a0e030a06020d0207060506 77
    0x880083d0260000e07400020340050360340c001a80d074040c6e03d0300b0f482e1810b008a4001c40100c0440d14045c0b110f580c0b8650041d01c0c1d04140700b078545550702051408103c0b2446c1c508102015007083c040034402040e110b8401c02003401441418142905162640203610040f150780d0b00c2c00421181c440200c00583d80c0158125001e10705051061040c481d4050030380044a440008446100000032815500e00f0b0045001c3c800042e12460140340002c1220300003034400030b010307522000c04c00001e140050240300740d41c07450500b40d450b41014501903a00390707065005154040d10200c0d949041070ba0000d00741301210000c4900d00824501090144440780e002201ca1485103000c000040100e4206c80045070810f05034811078151168480e10510382252502040311a505050010080c19509008070100d140e03109040000c00c0c3d5aa54458840f0f108181c002c000740204108a0685550140182c04060f07401030030940d03440b1019048407000354480c41d011540c031803074003022900314188402c01c0410000b400caaa0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 365582625 1250 365581375 365581387
    0x803011403030403050303070305010f1e060f020f070b1e1206041d0102030a0f0606140304021c080301030b0f0a020708310902070c05030a020a0608101a090f06040803 73
    0x340320414908494250144420400000080c0e8100000d500c80e581981d40042e483d410155060384400040d4400c403581d51055136803944404504890200311101d905100040d0034400205038144400881c41186038019144000b90b640504001000c01071031025240010311108031032903404d4002c40641140b031900e90310014406080030751202e800304020008100c1d410300c02d00383c1503007a03a008544020403030b521101034022440d5180074950151035181064401891012121001e41c0030062002e4030900140114124000103500c03940c100c190020740d00e507039039a12428a0b85a080307042d5412601a605030000901c106110300c00c5d104110b9100c0e6005140584200034000c1720b0210720045031512220403420704001003849105c8008100c100303400f50311841d540c20300c1060114039038010740c080d80000444100580d1020842070070380308a4141011079454008145821045681101000155003000a802906480007401c0550b10840e07000540310350600502516029502ca40b08203a40103000c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 365583875 1250 365582625 365582639
    0x30206070806010203070606230319020105030606120705071407180203043e060f0412050712030804020306071103040b4e16050705010212070f110a080301 68
    0x107140d004001441240d04040c913944440007241d10a500c030070540241107200401c2c0c030701ca280108002d50b40440141026041c20300a500a4584044000381085000800202995102c00542d520f400b01692003481612700701001900550242c1819620101d54180d400d010303100001d00794041d9224072181088a001000d034042c041e4102510803240b241d803412115512060484c1306100491002c0d99400341d0741c0700c0fa8007541c507a881000c2110b01500c0f0811840c001003510100304e400316150b901501c01a02c3c41418100c0c1001d0498001001010100e2410f105040d44030949070700582c0200e084c1d602c9030300c887e0001c0d649022170900030b865640040c0400c1043d0407484001d810750300007801d1581c0040c05540704054100721040220800e04142040c4203d20a5020386160b00c0c0d250040c0ca004400c0c102080c1b0f0160703060a010400c0104040040ea48c01044002e4060f80c0c41c0c0c2d00c01e101101c0342814620006401044034110f10800103440d840c0c0c0d0740b83c103080090108101601b200a007441c41e420084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 365585125 1250 365583875 365583887
    0x60c0c1b081e0f06070203130f0803161a0103061d011833020c07050307031a070e09090a02030c06131509030c1d01050a060519091d0901110703020607 66
    0x107010707004030250321103c05014452948190100e6014613640c100d1310107583c1c2c8203040e0b0b803c802002e60a16109102060000084601c641c1200b400181d003170046240501d0a44515000040300c904c00400000030000c0c1500030802c59007411141400601d014001d05080301d01300340010003801c1e07100056001040c9000900c0e52544820300a144408030181c03595040208035070142d4102c01e5000980602e01071080c041c2d80058003044015040491564442e0030003c0c801c05c02034460300c2e1000000c6010f140c09420030120141c0050400000751921540003520f4601c01d24003a80a40039100704280f00c0c0c44e0801c102c0c3e4001009895004005050140c080036400c03010389c1460504c10066000b002003402e119040b0000c24919024000c42c850078004050704080680c0030720b0060104000038440781c3d400c1300687d0030244840d000405d02182020040711600c00c282d2104c00381100d80140c80c0000041c02d06041d124902c4000240070760714191628a41502c1303104405401038000340081140303103202d81 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 365586375 1250 365585125 365585173
    0x20102030d0e10091109060f030a080d14010605090a0e190f020405060c2128030617010b15040e01050919020307030e0f06040b06130603060c0c1b08 65
    0x401c6442071a0f141a0140440e010081300f503c01c07031307075100c0c1400b40c0d8a40803404a0303200f002602d002e5801203070303107011980e100172114004bc140c04001c110f806499959078000c16200096903000c0040e540d540101070302c9980100c142c507001d4040c021010550b004018503042c014254071446208103050100413000811211040304503d54081000040d280d8403c0098070011902134050aa000300740f03000b03000c070340305a007040f40d5a00d6418810031343c160701e5889030780d50501d92481000d4030f8902c2e618400c400609590704420b28603507a00c405203110641c1544900ca41d04415500c1c01e6080f00740c0032140205000f03d00c01d100740001c84130f00511003401e04440240d04206508882d004040c160380924040e0303001140c04c00002995505006601c480800c0009901c40001c0080e0185051984482c034060700001e05960150b1403400c90000405515401207001b5500708900308030000c0707803810042c4440d4183e07101f529200507824418100c03801c10f040280031102400000d1280442501031604075030341c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 365587625 1250 365586375 365586401
    0x519020a02060724050601021f0902180109060b0f0d020702060d11030402010801050603040b04021212070c050102010e0d08071404050607030903031407030206010e0c1b061909020102030d 82
    0x3224010b8079150b0140403058443c04109603c0d00c150151060110094141007441d0b500706828031440c0d980100f032111055140c0303455141e40c0c1c840007481e0307400351240d07180094212001e00d6140440f1001a04800c0c103a0354110428000c070b40d503524520503a401010705041d160801000b40b04940d01c5150f00402c00b440c03001c0d14035404c21480b90303030b40310407240341120362070105030000f00b0401190307800300416001d0102104c01c40d08500b441e07295205032141c02400280681d00b10303440c0d01c03080002042034821203090100711603030300e034420301d000c01c2c00480170701c203a03400744d8206000390f280d00300080344080b1a05450fa8459500e59034600c02220042d00c08541614100ba08100205558607414010000c482c002d841c0c9251031b514502d0028501d048148941749500c10620841d00041c2d8003085040c110703840100102c550391104d9140414038411100f40103041c81c640d201ea0341145101041c064841c8ac24017204442b00c10142c50013005a8000d010000c0c0181c004000c51640003642c0c0d800b0302444402 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 365588875 1250 365587625 365587633
    0x3030909100f030501020a02071a0d0906060510090906080a02090c03070513140a0905011a0d0e0304121b141e1e1207081e010b090414010c0f051902 65
    0x2a40c0b1980c0c4180301d240d00140d8060750001010b2a80a0301080400d0080a0020002c80081c40e03c201d65403042c000c00c1d00114005031510854030a20003150450809454020421003a10385c92560150900e425886254490b42c244040000d070030f02c1c0802c02140c1141c0140c2419904d607503c21124403160b00052000c010f200c03040c081120000ca104c41c00c40c1c083c00300060f4200c0400340082c00c015866049a11a400c00790801005014618081003c02000e140e0411001c0d2540e02a11102c000340c281000e004100e0322000c0b0780040c0d445070441400203e18000c2005410a50141d05d035640d0101311070040841030f91201c200384e02c1904101c81c07119080c4504184810110f85844000340b144401118101c80800000030002d40c80e16101d9900f40706280b140e03008101c10f61030310300c1103074a4185e0210180944034480400c07400244081d00100910701c0020301d0038103d0f292501e01051049000c68030f10450350300e0800e0600409018101e11200e0a400307440f05402d0050b0740307a88100d000300c0c0c01403100031400727 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 365590125 1250 365588875 365588879
    0x411070219030c060504030303050f0402061b030d150e0c0703020c0f1309050d0f0c020906010c0807050102030a23040323130b0901030c08040803041e0506150901060e0303090910 78
    0x80300f68180740508003564a9a82d2585142401400e40344040c01010a060001c03040c440141d40b03070011620304101190300410b203000c1804405e4258011200c242c21075038100f0000112a0150800c034405448070400d04c2620707038507a03000c01012406030f914000d0150744402c1d400201d610303140c061100d00c401e0080c06a2003000440003c0f40543d0680c0004a520758030440340c030a1919000301200004241500d02004081116000981c2c500c00141070281444014660441488040021130b20b2864000c4001c0d5520b0501c102050018502351400c4030f0f940c1c541d0f07407081042c0c00030583c01c5401a03406540f030405c20303080b014180720a03000b05400c44240390300400c010000c20070500a4080103085840000c5d49510101c8e0000d801d070f5580c94845810485410200400110740c9001c0c1e0fa0419082155003070781c007510380c0c0d9240c41110740e010301030914400c000800040804041c2e465000039016984819a641d8821043e2000c040c481c072420b41c541c001744803008a90900d02c0000398416030b01c1c068020130503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 365591375 1250 365590125 365590133
    0xd0204060b0a111b091504060305030408071406030f040611190306050310020333090c09010306050306090a0f0807020405012d0e07050a1806030902040506041107021903 74
    0x39000c00009404100010750000c081d5106008042e001d208113000080d40c0c0100d040081d1010300c00034400d0754030390321503940b404854a0310307400403021313641c04011a555641ca41c000e581c2e440b05c1611a8008021140d8950080c504083d0242c0b8020708841070703071000c1e41c1c95594810b0301519080740380384100034051005030042c10360f006000480c0103103503c002468500f014140750400c07200a000501e41401001070103041c254251500346503070941101214044c480315103618443d1142c5421540c031115000a000c08071459400501240d0400d8804001440e41c030014582c58040c1100e0368541500300403480d001240c10007601c0000c451140000b1443c2c81000c0e030004044501c00c0c0c010110f034037503500608280240f40c40b55200200002c01c45810500e2a00d5000604034200070030a40803c031000c5200790605000d0001d5560700c131070180006011540f01d00005004005046043e44a00d05040110b80181041d2140b01c00b1488219801480e149071502403250303000e902202d001c243c080c5260000041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 365592625 1250 365591375 365591377
    0xa05070215033309041e170307030b01020f0d0c0804081209030d0924211e02070809120709110d060608060f090903040909050a0302010e12090d0204060b 67
    0x80c0c8a141071410469080080034038440803e00010010f0504000c0c0441981d5100302c20aa0310644c861110390341084520b0100c0745410200000416444081039507603250101d03480a188903031040d03034003085508000d8004aa940c02c600c08001c2c0c80b500504032100140348566802c00340e03203008100aa180c01c0d543d020261408803904039801428a02241c0c140c1070749003c0c0403200480c9024600311454500f0403034201d200992002042d903201070305401c0740a585005048408841c0e42c06ea01c107481100028659201500086110350b030034040c1c8807c00d02d8000003c0c400e49032702c3c0c0c2d01f000750f483c00c1495990600c04141c114250090b4984124180001c0d1442c603406068408009401aa51201030900310030041c0c3e030792a041a010f1194600070400c035503e829030046134000003103980003643d8070b44c103070410b0851080740c2042101c1e50901c0319480502c07800240b2030a00350f100e40e00800800003020749494941d50502c00c0d00020340d5080140707124500c1e220100262150005200180c4c0d19510340c030385241 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 365593875 1250 365592625 365592631
    0x30c090b040f03020a060c170711030609011d0a08090f03030906030103060b13060501050d0b19030503091f0504061101140f0f01090b0f0405090f1501080706050405060a0507021503 79
    0x240060b0500841c141004214010001800c0c20203840d081707582d4010403458100206a906000451500140916a0280c1c440c5007001b4064036100e05142d8640ea010b0250b0030403845528240330380c2074110f44000034428034071075040310f00241031001c1c40c5c082151020314030b0003081e40b51205018004840d500c000056008600c203420000e500c001403014080c03420b20320080540b599280038002c00150760800708542d4101081d90300000e001e04890300040481204101c07950f01c081740d0302c1002c01000310002c01402628011200c0801000d184820f0100d074007694900368000400c203000130009180502900f0326081000c00001c680c400c00200319140b811000c403400106840c0c254107001c0c0c6c0b20302d1241d4290151141c00705c1480890f100d9400b0035140342140341502c1c01140d86000064070f04c00c0500880c01c0d0200280c0a50b01c003005a4035100c3c400000031301a602c51070251250018629004004030b0f411601d0241546083c4010408165040d40040100740e030061070203025890350143e80c200070b40c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 365595125 1250 365593875 365593889
    0x111030403260c070e0a15180608121803011b0c0c21060b03010b1005071106071a0f010302030c0d0302010e060c130806100302090c120702101119030c090b04 69
    0xd003180c60a040300c0517007100505151100e0b40707011400100440304171056402c0d00c2c01d040c070613205c02c0143c462440081c47c056100c18090302891964900148132800101801c02c21844048200c1205a00705401c85c0e0014815a0045480718000313801d280c0140d10f02407800e801401072070011a43c0781c240b108200500e440180c825996018680d041005600c9040d2408030305400070411401040007007013003014800080b0051100101d1341808201c14400c0140c41404041c04c07071515410703280344c01000b1455680c40d50000036030030030015a10071740c8450800c2c12030b50002c000f0005150541d0900c41c5807024140c2c29001c5540724a102404001c0800466002d841003000c00e681d2140b46130000d80000085400c00c142c9a0080018403141c00080310003402540d404a075410f4050b11101c2c0f00001030322611040041010741c82081142c034079004075a44c00c40c582240d40a000158406220391a0340c4a03507055070900100b007a4660038070510036400a51117481c141002a48503480c0d410f16100c40e006644251 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 365596375 1250 365595125 365595133
    0x3030b010203120403020610080a0308150f03070308070605060613180207050604030f120b060405040f0b0d0807050d051c0906150e0103060b010807020a261908060111030403260c 78
    0x14120505d41c404c1070041035409d01802d01e070052650001e00c1c2e62800740941c0144014002c3c41407481d076030048600e066060003801c4900141d9285840c01564120076401d40d0310070302d400b0005040e818040f00311819588007200d040307002402c14400075805000c2d17000202803940d0900030f00b40018020400140200d0081d201d84954162406c002046060f1800d8540c10301402c6c00202c1e00a91120001c0d1400c1c0d91f802c0318003007000500815404000c102c1e241056900410a1041400340100400104400c4e030254059400136900e40c4001d64540c82000030100c0500105800e1441003e110340c4243c102d103100b900041000380b08015808008100341c1c01084c1042800c100400170031038248900d2a03000d5080c2805c81c07141c507001c100a0b442d070030300c204094540a0048102d4012000c40d40c16144551542603030191101c1d0050280d8640d1030043c00f032000410002000f28070158003640381c5a0741340d40203500841c50107007940d07210200990224141c0e078242c030300c2c040c64401100c0c40c0340192903a894440028 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 365597625 1250 365596375 365596381
    0x727060b03090f010225020301020c01020a0906020d050a1403060f100e0102010b030703050c1201021312150603081b0304080607020d0f110303012102031b040f0e0a03030b0102031204030206 83
    0x1942081c00b1903c0c2444143c0c4100844200d8000e60302e4440481c405148002401c00c1003400481c1c064411611100f046520004091102c6500140050113540705a400c444005041c0882910a031048074080c00215141851003808011080700a5501803400f40c0310501110b9850007180001c490040c00001080700724030060070650342407141e26814030044005025442c0b4580392203445114080310f80b40a843c2404003940340a50940484900d5960090700d01401641d802074000e03513038000441205c1410707281e001900c2100b2a80511400d0f0790700180c985113840400351841c0040990707914003020f140000e010010348898140485172140c18160090103440d040c0000003081500a6825a01071020701982c06207034041c00001c2d230781510004440e0341c0c882c0d032441920641c03401d0301120083d0715100f40c0100c2d1101c207503083c400044482c1d0075039040c844c0800c00380b40030040c3d0b05801c3c5a1030341a80070307280d0140841d200b0b030414400c00c801801a00d00c1c0080500703985209050488065000d0f034412024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 365598875 1250 365597625 365597641
    0xe03040911090f01140c06130311010b09070f020f0613050609060f07050a14031003050c0f1f051e09012a060b03030409021b0f0a050727060b03 63
    0x707880350705048001c4840c030b40ba44110004215064056606041101140100d40700344103110840d584c140076003048401c50302e41031a0301d804d6014048400c900240d5864032090240205029200b1000402000e4104030742d04c489040741c0744103859922500b10300c40d800031042206418004140110346103401d5915050b020300302240b501402629060181c2e22031820002c2c000100d44880d60402103515003213079110f5015004442070305001d01002c02051001050210030305406406404403441102a60101c000c04001c00c07622408000702c80d600004c42d641f855900c038012141ca00000d41c0c15003040c5040c20403000040e500303083c600c0092041003000054017031a940e00b04400081c4803c1c40b10304042d01c907000284440c40c41c4a06480180100e031210707500b810302c5c4da061060300c0244c040071030300f152660401c01c44400340f10707025050300425001d10940c1c84229031000c00d08a02d0b2035000b4008090310b82c54102d422000741203021900c6004000d6040041059045018250040c402205d00a40328149981 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 365600125 1250 365598875 365598881
    0x3031b0e1008010f06050d060302040c030c02061503251203020a0303110702012c04111e0408060f070201061a0c0c120c0103020d0213121407230102100e030409 70
    0xa40d900b404922401009050f10140c10f0700e054406900e042c0380c880d502440030401a102941000b0340c00f50070b1140c1c0031255541a8094040b0250300d40c00c0344c00c04d8441d10301c03890300740f6441075060341c240d004107050486e607201c490407c1c81420800740c2c2c4181e109907220010003254202d000c04900507082401108103155240c05101d00c600c1c04111102c0c03401075039a0020b403442d401680c41c0e448400303c00d00500e0401e00382c50602d6541c030b003014000b0700442c1500200c0300341d00e50102e0745a6801301e03400c1c06005204103800060f20283d50b16000246510788076a640d00020307142c01403140003159280d85021403a007102c002c01140759042100c0c0b464544004c800d005046c104180d5a15008080361000007001c5540060003101e01032080c00d005039200b0101a01d14080d2141048180305030710310050006400240d40403881d03201e402540b10440c5000c1d01c2015944942c0c41d8840e40a2180c000c520032068003040034070358103400f041401110302d00403002c1d440303000381c444a140816007a080402c041000c90b0440c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 365601375 1250 365600125 365600149
    0xc070c0f05030c010c1a0106031e0618050612031c0501080d0c02091509010e0f090a050304270f05010503100e15060105040b03090f0d080f04020d03031b0e 68
    0x19031041421800d21002c6035440009520603070422000e66018414041d01c0b0002d0200c1c80101100c1101075070b182e204c05800741c074034101000380c0c66459000d089405411441003d050f0b070411a10511100320702d0b1454405000040d215030f9004550024080d1103c80400080c0050103284901502c0203038400b00c00c10445005074040e001c0d079013003004e20000840e804070050130440e0303045521031001d403600116440341203040103074103400110f0354001003828102c00c01d006100c2c41e00200200050303600c5002454030342e03c42c01340c000c0c0954070600080c4500c400554001c4024008481c0840341c0c05c1c50114010250b4100f4001c80d840d46071f9810040c0582d05080c4802c16020800c20b000b404031201e240c01c2140e5841504c0040c07180b0848550100d00203030702c41c1048400a02003801e51035181d003409410a031701c505612190a440e40700d90581c0d2458280619101c61040c20b00c2000c1c25034030740d01d9400b40b00040b00c1340007007102011341d500d190380f03880c0500c00174801d60307141d440c0d0b100c9585525a40038000c000b4510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 365602625 1250 365601375 365601389
    0x1031a0a0605010503040f030519021b0301090b0114010519080711161406070501020a0203192a030c0203032a03120c0703020705040f090308060907050405190e0c070c 73
    0x40341c01403000d40d801c0030480750072960200441c48503450b9810103c40500400380b4009400c4840440700d00aa0b03800190100321187c050316290104000b81e00b0142203c101100007402e0f001105d0040026115000c0c51381907038001814030034545030182507140440038a6490700e401040340d000074801600e6000380c0301e041c3c4041d07100080850f55482d0005005240c1c1c54450f10b688102c40c2c040c00ea20130303101c3c80c0a0368001e642c010001c1d91940383c1050b0181d200d802c10042d100342c244220300c0d05000e03180710305440d0b00300b50403a1800628000c21a41c1c0c1651520203c02c05606120407843d02d0320041c0c508000415440a071148610166010070089605403210140200410303031007070018103032403417143d040c0130b4000701c03200901e0b55a1401490280c0c2040b6069015583c0245402c4440031900c4440e00400210351280d41c0301400b0b41d590f58201b240c040010307144440081e5082c4424002c50400e11718541c401d6402e42b1201801c01d41d1a4020200444115115049903501003100410440103503200d40182101d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 365603875 1250 365602625 365602631
    0x30103230601060503180f0d0503010e0f01050a060c030e13020306031209100c03091701050604050106050c07030206160501060f0504181a070306170c0109050105070f0b09120301031a0a 81
    0x240400003000c9001c00381801c07892140d030306c0301900c200c1410050701c404141c04400340c40f60500c410030b0107850340c0c1007441204503040704030000600660412200d581660300044c689e810043c104681290060b004410860500401980842007036079414900303a2594030003480980c0d00d24201c014075040c050300041d91318101074240580d02c1c1c0760b640d103003120302910494540181d0010b010304007260b44c500203a00104404032102c81d0a62000e4040d001284640c00c2614244200e03642d0b400c0889451103030750940c1403503030000038051006140640c010205800d0050b200040506107441301401c444087d0710490502030f41203801c000900707050190007200d400f05910020f824143c1c1c2c45c2c0d880c0c141e000007441c8030100c0003140019480c60080d806503001e000090f064400780c003030b83d5450580c1c4d2180003520f2404103401d0700001903551300c07c80855040c90340c00f040e284100804d560316201440e002814082c080d00441c40e00740181e05580c0090b6000b180201c0101c26080e00c5010018560f40002d042e0708440ba007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 365605125 1250 365603875 365603879
    0xd02070c12060b041a0a0e0405010b09041a0606040518090c220b090c0406030b041e0903090f140108040503040905040f140d050301052707020f070b16081e030103230601 74
    0x582d90146001f00d0300761081c214040ea07982e1515900501e030141c1901d07400442402404188001c08ae0030030203061180ca009400c41d15001d0030000c880c010303841442e0b030080c043c5d128881d030070114145040e0041c07601000c446a001d05000000c0010000e214800800466107509801da1040d81c0900448020140e60076400c0f82800c21080c8a00d1299028410034162103941c88142c07910707190b204980320300302242c8581ca10300c0c0c0c030166000900301c0c5100c254000341d81c1c5c280c045869941651041d0484034001c0e60f900300074600000548a44a00a106445502042c0300014910715540030700e80c400c0344240c500110003d00c0c1d01c0d00d42e0084d005a4110760140c0e002140060310030340c10108480c10340d04c0489860f01c8074000f20f02d40c0401c40c110710300d0810041c0e003a201445061500011410150a45001070396141920b8440d070310301600591180c0406000125100c0c0086500f03140142003174010803403040e48040000c010314095500c207078402c81c4c01156071b04d82400b400ba040364480d81400c15aa0180620394 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 365606375 1250 365605125 365605129
    0x519030212190507050304050411030106080f06030705010f0e090f010e160509010309140a06021b0a05060106050304020a0f080a0215090a0b090a03021201090b06010c080d02070c12060b041a 83
    0x4202d9010003041c00800100e41042c0036040050b40c000740b40c002c2c405c1c050401f400141061a42003803284c94041200d500110b521240311888862080c040580103103102490030307004440b0310701c0c039140c1e94091080b800326100254440c51802e6100340c03516440424154981460502d8540000700380030808002d6401c5030480746e41c0079044440c10301003441c0208030212942032184810a05000e91122403060445000800540c1e07005031085002111014899400850002d502d66a590740004d1080e0040401449854010009503805c640094821000300d03880300e281c0800c1c210240c02c031484550000300d0030004c41c9801c000a599030329034011010304105d040000714912500d18050a01c0000340401c011600341c403050074020007150001e184801c1802850031080c020708461409070740e412100400200b69501668030b06410544c00320130715281c00c020b603110f100250418042100e0b801c108210000e440301d0746070b82155419004031000100440f50804220446411f5451500c80620f0500421695 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 365607625 1250 365606375 365606407
    0xf140405010923030708130b0a0903020307050a1220090a090b100b1801120606270e0411040b100509040c02340503060f01090b0301091e0f0519030212 66
    0x829489400142c86400020f001100311f4455000205c01c03080201d0115520b130360000080702103070b0013503080c0e843c01c40d11030701440840280760160201d000000c800e120001100e860009052002010403d01c5c0041464000707030071841c00751140007039140c441000380140880114815040004900801d003030529100e4051072a00032084411010000700d8090415039010386031002112500d074108002480d11844042e00c85085215180c03054101d074440004002c00f0011004182e070010421482d840d030725903440c0c241c0648012081a08540c403070350480c1c0e064031035483e102c2000b41d0075140c1a45a011103c00c0c00212000c000100085500000c01108a942c41601d0010701c00c030314400181140c0102d051031314440e000360380aa901845003008120000c1300921889040e00c8800c1070601c50341c108201003500383c900103503018102d400c82104104141a4110a00e4440d07482840c800340300c0c041e075803682c80c00e011004c0081004c819545100404240d0305004070701e41e02c507540f00c41c039040400d050065140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 365608875 1250 365607625 365607637
    0x606060203071a09210406030501090e03040513150f030506060108010303080c0d1104090606120516320d140c070821271f0f14040501092303 62
    0x208030500300400c80030b00040c002101d00f0715074445c040d2401e50800c6441580c0d6031181c8562000130f450f1030000320341c00b0200d005920b08210036800a41c1802d003403a08100c1d0f200d0440c0c8051320400d586815200310030050a0300100101546800d103100540795003011410200700906203410071806800610009400200c40d50b00100820030598407032908850700401041c2c0b01c64880a10b0a002c82c002500101d982c00200c19641c85a841c002200506400e4030280c405c1558041c2800000d0038612080d2442000740c00b4000808a901c10168400c03882000400761550048860000c400500381d0140c0140e405207040220720350302140c101d0328094444409601640c00010241500003949001840c2180c0301d44075600d203400420259070914421808803401c5040000880c0382607190b113920140c0740171484100340120001004421616555140010580f0300b8481051903038030b89280200170040740c1c21070303c100e01c14000080c0f4182582800e01c1e079490000024140840340c006030030b22214004c07041d103013 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 365610125 1250 365608875 365608913
    0x619120906051e0f0f1909050703020117010308090603070918090204060b0913020919060819020a050d0e100f020301080c0609030a0b0a11070f06050108010204440604060606020307 79
    0x401d40c580c041c01d500002d406c14041c40321141055004802d02c5008035000040b030b4400d807130380c5110301c9244107111444102480094000d00092003402c00c542800801950301c41354500d0001021910f6181c0c0003180d50310583c0c1050070681e14040b0404604261083c40042c0048103001810501c04034005094074403441c04100d5010b4000c940e00300c40703031101504010212080d1245882660311507070020800001107690b50001401c20b42007205100b036074400c1b25140c0d0500e0740e90920f000e64081b1000081c10003071114054600c2018940e8003031540521130714142e07003044440580c0c0da5240811807490702403005240380c800c07501041018035641c2c000070350500c46030f80452088100d40d03c0a0445000341040c2042075404c210006019042007030a00200c985284207140800141c0d80b1228058200c1c0601d00541e092000b50380140164140c0740303170b030351122002c0d05204a0000146c001152032410074880c42518542d20800c240410426140162009070580344001c508000c0c841e00c40c401c81c104c0100d19a8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 365611375 1250 365610125 365610151
    0xa02010b121f0b0d260a0f0e0111010501081b0a05010801170c21010c0c0320010e0d0e090702010c17040203190803060f060304020619120906051e0f 65
    0x214a00b00c60307810034400307002d008000c0390000e041350a04010100d10041c00382e0504602d0300b105a4400d18000c166410007101c0c1c3d56240380c0c0203034030710181c1e12498184800c1703051203510400c11408480900515001c1c01010024160b0b841c0175545040114401644081c46041c143c01d080c845a6441038006045034004100c81140214120700c86090044491500c0d0f00300c04800c80c480034031080050519040601c10f0b00030003141448507000c031840c44469000400003850f6880000341500c2011b1080c01115503a00000354a681c5455011b1070107900c00c44210126081c2c48500c590346c0340c40800781c0c0d8404221b000a00448103103a13401441280401d0000c0010008140818159201089407400200c400700c0003102c2e618150070032600c55003048035101c0c8190b04418940c2110704001080d41d001d540c0c003414003420b11b114402c19164691500740110108a8510030741582c01c0802c0c0101c0d4450750044100091908003402e10110400341e40441d00503510f02d140901100350280c0b128150700c1041c014404e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 365612625 1250 365611375 365611423
    0x3200f180a0e0a0c080114010804030503090304260d051602060f0c060a050603010c09060c121403070f030510030f1103010605060c060a050915070806030c0909030a02010b12 76
    0x103101c22400e41010760890701560810005050940c01140711020a441e5813440340e13a184c8000741a40203144c052400580e1031008900000e0094001e5904092440700b5641040d84901c0018040c080c040f4a180c41c8200c07561200300c4642c030502c80c120001c0b4443c03812500d018407239003882150380c801040080c02001d0002d4140c2c041640901074443c0b1082c4e902c2034030346500300404081e000c0c100c151001d900c07135464444101c0301d55015000c40c0f0704407078140d10b51020310299038540114030b4030b4000c00107040c0300c5030480000c0304841c2c641c021481a405034403030051810340044000c0485e4401091042c8100200740144080b032000340560003102ea01c404900610801040442e0250260b0349c02541c010b000800c0002c945040402c0041c8101c81140d010043c590303404010b240d5500c0d810f24924000e048000100d195a07114407400c03907000f40082d04a070000305902c2d02242082504484183c1590004918810010307070a001d1074000100032180c0034130495103000780c0c40d00e07800c2580504900441c40307104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 365613875 1250 365612625 365612629
    0x90109030b07260901062907050a0b0403050c060901050f06060c0f12091507020901050d06021903020d0c112a100221040803030f04140d03200f18 64
    0x2206403900a103002506880c00c40c10070f01d1007454030541c1c4011665007868004210031816483c1c502c114282c40302004540c452105c0030040c2540001c0d015916802041e404e0000707d0400c8a00078081c030b11a40d541981c90041d0058581015400b40009110364108024040580c0700140362540020044030015a54040d00e010710b4548282c819400c98140a038403054905032080001601c602c0c181501d0020200341111402000c5212303a60000350301c40211001802641440146c04110601c03410b0b006141c4842040b07250f00020303500001100013600007031806a40601c50041d9a05c8039180d0504501425500704903d840791050101c1040c01082450406040d191a010142241501400c0c0003400309003548001e46429402046c0c4518001600d84038601035000422a02110f003614041e41c203540740d0f0800d000c0c0c1410054170550306d4200302d0301c817240c800c0c0c0140060403161016440000c0e8911518070350704090000240281c040c07400c14420021841510402c507401c9074041020584100400c01c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 365615125 1250 365613875 365613887
    0x40e0a15140303130e1b03010e1315060b0d0b0102010209030d050306010306030f0609050606090403020a030509010e060d0917090108160908031c05010909120c110d031e05090109030b07 81
    0x140c5415550385082c0005c0300b082d010702d5a8051100c94448801c000304ea85450300046c44280700e0020142080d60025520060512800c1105071143c5c15a0040c5810041004240d418540201c04d22500015034804820444c2c492400000300c00c1c0025410400b0110020f0388138074035044000700f0320100000043e0140c0c480c3d40060065a40030040600103685814108010001120112214410369001c40c0d075a2030080718051140ba4180c2c02031845181a9230121096080034200074188484c0c24041c504942d41d41c0c0c003a02016800d20b0340012142c0c106d00f81296000d10b0680090f402030001c00a2035466640901296446001c45240d0010710255050840d07a1401b00e90000806000c003103640d0900c05c44881a208126001030400e000c0c598940444c601103d010f0700005150444c4c001e0482c0e0401d0045641601844c0118214030014203200c0120b030780c136501e408080300054200034419002100c4080071090310b100914003282800d40443c006402c010f641d000103000540100300140700e6034410a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 365616375 1250 365615125 365615137
    0x1050d1103031603020a0c0504060b0f0a030b06210c09241207111216030e040f15060912050a0312090602070606051f0f050706060515040e0a15140303 66
    0x548221034202035404e000352501d441101c00c45000c800160006002d103000d0050400f6038820581c500e2030b1002e4107040c90025800220380a00345901c03810141c81e0ba0703442ea006020b0b20080d84c0c031250203101c0700ca03140280654000701080d02c454400d10800001d81c0320903894403120182c8003124441003000d104603601e18010f10044440301c05e03c1104001d0b82581c88071039200e040b8403400460f418018074a0111005005d50b0905401d01109030756803a02103481003011050000700030b03000007032000a503c414020740c2c00160b01c40e030b00c03105d00e24801c02409a00c401c100d001000000c80c00b071150405c43e17503029211240c802000d020800000d4105a85080316030050355160b40c41a4210350340c02c1d0924005010384002d1003124410007900074003d1000000310a901810712403071384d400b844401504810b07100d9800c1110152400307a0b4401010035280c035503030901000740402c00b0a280d01d46186c540501c0c44008000c00000449081c20a003655401c0111000d109480e5480b00c4a18214110300200c0e00e035008031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 365617625 1250 365616375 365616397
    0x7050a02070e040602070b0f13080a18060305090f062208040b13030c0b030610030519050406140603030403120311091914010905030a020d050106080f0c010207090501050d110303 78
    0xb030390501040012903030083c0002031145445200a0b554102e4999200404445e02e20701c41c9001542c01c0f0000300700e90001c0168008a0034034150f64422050780007144240c540241c8003003660398013800748900f001c01c003031140000600001c1243c0d18003694040b14030a901d03001c088216209c00d030713a0001c0140e5030099030041d240da031a00907212244200350341d4903100f0724401070750500013090021450031140400c6030700c22000600780c00c9110116480c200c00805000702104103124020301039007800f04060192a010320f018070070100e241a000d0188036405080642034504c694400c10040000581d20450912074001a0030000307188003401c80c4d00980c0f03110f183c402c550704c071000d00d026203007011a10080c0c1096405800b180d000c100e200d040150f410500c00c0c080e0390340c981c1c0110703941001440e081017000441c0c5d129070004280305580c2ea008910703141c0c50000e1507070030b40c0042e6030300c40c4e855034100030400c020030600c041486a54544400304044089007a00608203000c0e4000703210458804000702c031210010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 365618875 1250 365617625 365617649
    0x21803010f110f0a0203042d060c211b0308040516080a08090a03061407030506040b03101116140c010c030e0910030803010801021215060412050703170903061e07050a0207 75
    0x2149a04404038440b6007240d0300b084040307000460f81c0c521a0ad864403400340c3c440c41954010707003210981201c81400c09050410047c058206845405010102d141c56520076103c10503a0b0415140450030310441c01400c43c0044800301042000c07080000d65020340c280c00804a541d110900004200ca22105030405851142046400d5401d6111101e0040c40360041b640c0c20807880c0c8441c410482520a1007007050343c03650110000d11500c611580c4070b614078646400449240502002a980c1c0044c0408030a0f1945002c415524616440600c06c03c041c0c1f50091800324400702480c0c0c0c01030103054138112140d0082070000c4c005160042e030304214601550b0003c0303d482c2c480da036601c02d55002c0e602c00d0441e200041d4100011414003201c10000344040341c0c0060803241805d00748046944581400380055a051240910020228000d0740b0703098100405d082c040350740d800c80d0f80181440e0800141c0000c100c070f5030440e00d01601c00303000c2c400700303421041616009640c0c40062200728545450754100c4580020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 365620125 1250 365618875 365618909
    0x1203040308091009050717010605040906090201020d0f0203040e0601020c180a0c021c030207150906060627060809010e1e0d1e0c080c01021803010f110f0a020304 71
    0x50044881d51054410310b04564401003030406060503540812001800c40d80038080c1030000c0c40242e0098406052240c4c0002406a41e40b00094140c60085030705940d40f60365152a801956070502540c0804042d0342000c06440b461a00000e43d00e00c0f8905c40c0110007010900450500d81c0b0920a00c210250018094bd544112000300d5024154040d41e001905607e8090750300381c024004a1080e07001416442c041d42080034010003900072b5030100c20112140300604a643d050308080e407241541c0c850081c000003488a08203900940f00082c0071490000080e001826240c4003122014004207031156880d10388039a8440c0c104550241c03140d0560300c0040d02500d21008445c410710b010940411811404a42001007190801d8a100c0e040d600d030f100851880410074024130b4010501d50003100c1c840e150a40c0342c42c2d8250300301800ca1b00301c0c0040c0e04422090b407641d42513a140034050007920820040040019506e12001d0342c0091140c007c10710072001021810000190003401a24002c28419104410103d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 365621375 1250 365620125 365620127
    0x4051305010f17060103080c0c060c0a1106090d110103020c251203080a0e030415020a0c090218010c0807020a1e09050f0420040606050d050c07121112030403 69
    0x2009016548521140c0c2c58005514405015410002100e19019052603402c5840c1c0918a5105803200805446159004005500d50800404d80d140480c0c0c00340001c050141340c0f12050340e5003a10f400c2c0c40344030306100a01040d59101210a201035211085001e2011182c006038040e020f49480411039001c0c10154030b980010410440100c21031140014810307640b1903001c03905698003481c0280c001101040061100c3c0c103d54010a410584081100d0815694811480d048400c0c44840030040e0003100c004400c02462204035005031a45910a42c2000f002c0781d5407000c00300382e014100d410031010205010502c0b40400440d000c99401400e04101c49440e8095002d201c201d207017680e01c0c10100b400d000035038014180708441c0156051211000907403155100e548400310901c1c011100001d41d4415401c407650707544100d4000b00000e48030307192146103846c2e105084620080801c01c1d00c00c41001004002541040c82144214403800d0404034018426151450108581e440c1a49a240002032100341 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 365622625 1250 365621375 365621381
    0x130602030c0408060a090807030c03050f07062435060f0f070305060f01350a110702030a020103111b010231091d01060308070c06050301030b130305040513 68
    0x5103040000310f070219202e17003988000715101c004002e01160018010480001d1184549202c014003c0c944581091078049118009070302c400d50403200c650396944512010600002c048001810090040400c1c62400105031030005072038150324810042050068110b41040b00c044e080d00c0c3c0c0c20710442d241031901125003400c952003590f900003410120400196402d1090007401d1040c9805011841d9000d0407000640c2c0032104404030804403503020b0390a94240c90651700340c2d0310800003090b80511038180302d0b081000f180c407104841c5036125402c01425015803800124001180d5082c60001182c2c030740c1005100b2030380a2000c0201c4c66107082215848040015001f900ca0315100c4044000c0c40d4403800301c0c025000609542c43c2d03005610303800c0100700c200b5403540188112066100001c0c00c02005502c101e013100d0f19500120317200100031406405002d000c02070000a4015410b04c40c0c0746504513220201c6040d4004d0003038803151041c0404404151148058400800d000b44c444842c0404c0c10001c1409 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 365623875 1250 365622625 365622629
    0x62403020c01021b15060a0b2b0c0215370207020312070201030f230402011b0308091c02120702011e0507060f291f02030406030605011d010305130602030c04 69
    0x10b030545c503030042401454054030082c12100342e030405a00d443c07903030485a200b00e06581805007501902042c00ca030a1069401082e42d484034a6016003101c1d43e0314008a0222640075100c0c6d600c208030f50fa250300380d841c044084400c1d10148050341e80900c200c1030000201074441d1440c000d4050103141001300036030b03000c040a064114400d88085c04800e003400d8100c000c444c0408001d43c20040d03480ba011602000b000c4403150418010b240064201180d82000c01c08004000d10482c0002c01c2141084400242400303034440540d400c0c82d01d034880c1045400000c1d51000703481d0104017500b4000071250110780c002c140441054640000d8044081c0440d44040d21641102e1001da0300d140c20541d042d141c440040c4108405030800c80c1241c01c003c0d03d07103102070002d08041c2d00d41c241c01a031600a06c80045c4260102d55030001580d0303005541d5141000b80003020307256150b01060501038000000c0c1c0c03c08000340c2d9528184402842c0019503591181c100b000c100c2222040500b0b1640300109004542d00d2882c001e01c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 365625125 1250 365623875 365623903
    0x4080f0705100c020f0f04060f170a0201090b03090a0c0b07030e030106051c02040b030303090d11010501051834092c090a140c04062403020c01021b 65
    0x5036900240142d0b00c1c50041664000740d00801c0040042c50400d0390442c00c1135014044a0801501c000483c00f03c42c80d980003450715200402e020480b02e048140340800542241d005008490a1540083c0503a0103034024020703401342c04000500211410803801400030740045222940301c0d51440b003203d203035000c100280d0001d410080700f00164201401454201e55002d05010240c0c6502c8240c01c0e044078034070208036841f85d22540d84050303554003080698003611165010f012000071100001d0308148204403445c0c841d034104401040169079100b4541c02600a4204070301c52655208207000106603001503003010344034400244010108401043c12900c290394a44501158582450800003420751150515400d5140900340d1452001400582c000039214202c8080d84c1c000da42e51800314040c00481c158540c0103a40d45a05494680182402004d10300c0c1d121888500064006221400d600482c0c4281a0001032403402a00250304880514000a1039102e2074103800700120b0b1a1408060111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 365626375 1250 365625125 365625133
    0x7021f05010e011712180303030405010605040b0d0b0408030a020706090c06081008030f0703180b0c10060e07081f08060901061e030330020a020d11070303030504050a020604080f 78
    0x1c103c4041a44103010301c2c00e0520010007203016204005c850541c4a00300c15086100030105c081d0141e201003019600942c45403001007046801d1005200c100c13050350b11124422000c0c45150301c0402c1920102d81c1d04a030300000ba480e52075407480c10184c0a032041000c028007051803d002c41051060050000b800c2e01c0403581d807400c0e191a29040085040301c113000da045a904108410404c99225000500c04580310b803c00f45a21507250250460581d4250b04c030340140312000580214010b0203021568014440304010488a4101407041020784401401d15040c802000003146440f01414002429406a0b2400c02c11003925145415183c0d101680c00d2401507081420200741d48401402c295030082d9031000049595280d0380701210f404200c0b03c05442000b4604200c0b00c0714440d0751082c1040d40580300fd000d40c2c2e828000034000e00d80150ba0383c00c1020044400c011200c07210b008a8407404a130307010300d004240b64a9504204d4142a445a002035101000240004a525001c51002e8042c006a4166 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 365627625 1250 365626375 365626379
    0x406050d0f14160612060306050106210c08061908010e010207051504080702090a0e0a0f020f03011103270d080907060e03070315020715050a060b19030507021f05010e01 74
    0x400d40d51600144440c485461284044c00654440e4007140030b4011400740129080b640ea40315881141ea00f03802980000d08000d0440002c0101c03510200c140341c45501c1c040100b1102c07000c00421006d40a403500348900c039026030b1010070100f40342c242e00c00b40080c440200700f040340c2904054000c0d88012812140c0d4001c0040e941c29225070001003034821500900000e18140944c0d00700003222800a101e460b9169803404d129501d0401044002c6445118006d405586010350040003540c80130f00013040c3c8280c1c1003100004942c041401665088140030300511882c00c2d42149550582800d600c042c0e2003481040114000c403988845154004d0405005440b507080e100c0f2011100451104031884e010781c46a0310800000d0301d4009456250314400000608040050340c5614003540c142050356256901c41c0180072415200d840b80700003c00c2c0c503044007072400d038101040c0e08007140320405aa0a0680e00c80004000314020b000081d000c14454044400b1000450710001c02070000b03000c3c28000110f41800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 365628875 1250 365627625 365627663
    0x90a150c1707030c1d030c190819060f0203130311030405190e0f0c120a0b092703130b070602120906101205031902030c0a150507030606050f090406050d0f 68
    0x1111170b50301d014000d1706682c0340f44414041c3c0f19181c454000190080580009203a1200b40f104c011440359050804407002c803503003000782c1a902e2030f14101294a1041040c425221000d20f2084240d5a141c1082000f030b20107484014154001c81c4c1c080307a0017a4910000c0341144483c0d800780d40c280d506099440c030064a0b100c000110564045528501e181001c110030b6103041169604960f000700b416401060500c1d102000c500190004c0d1410215080038039200342040125100120104200c04011070a02c0c0418148480b083e15a10891102e030200151f40c90a00c1442d804850300340c1c1800da1036480900b4800e41460ba2100100c42400108541000c0031400d005400c0520203201d40000c0258100344212000c0703805100243c07215001e40c882002100342d90b070700900c5207040c000d02a08880e42c0c800d160030032307020954400070b000008240c0360607428045640c10000340d40403140e40070403103070f01c8007807040c003003002000d80307400c000d0b80240d0303606101c0308002c0220456a0803d00c14090b1030a40412444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 365630125 1250 365628875 365628917
    0x30f031b0c020406060e01120b0f0a031a072303091009050f06060f01050301090209130c050706060b070b04120207050418121706010c0206090a061106090a150c1707030c 74
    0x6106c5000a102c3c0c0708500d000c18041d0000701140c60018542c4091022003000074190081e01c0d8022201840c2c0710308250300000740319401d07551042a07030914004180d00c514408401c101c100340d0b11410340801202082d59004c3c100803400404405c400100850343c2503052660f511141d00c5e0b00c807106885600c000840ca0f0405c41c180ca03801e810182c40b2103007185d003401d041a02030340280040302e8100b4400600505058018051110446242e842e801e98403807080c200381058940c1d503084081c40400420030702c00010b403200641caa20640003a4076800d11003800e1002c9080183e02d03840035601a003403034a24040051118505070405114058000ca40080d80b20292081c0440c41030f0780703460200100004529502035220f0b5442a480140360b00d140c0b00fa8800044e50403d201d4203c040021810b28500080510400c1295042405d5200505680b056036032900d54280f801a0034040c0700f503c0d4107410700a17074000c1c0e80d0007110540140d95105e540ca01164018010300c0d10005010014541c125800e802e0b5401315 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 365631375 1250 365630125 365630147
    0x11070311131103040609060f050a05100509090d23040b03010f140d0b060307030602130503390f09070e0f060a0512070504080d020a060f05060d030f031b0c02040606 72
    0x1003941419580c2d1520317140014020f211003030b114141c90700f40120301420384c1d2042c544510609600003d940c03c0034600c0300350200b09600b11034082c00b04031081c060720320710001e00c4194105481c601581424807840ba000e01031001014243c0301240e002c01d022808104c200c001e1416036030085a1401d0407a55924002c0e403101da510403490301b2015054260000c24030012445a2001000e411600190750320755852049a200350758003a15210016000d0000d46014810201403003a002200c6806650700528241001d4506062415080c1c101c0c1c81e410070341e21007101d41403040d04002c1400c45146403144001e0720407004140e1301d510503241c42590103920306c1e10030f081d10740484580c0d4440d410304c840d4411640c0c0d140303009070066050000920001906007820407414038a4200c2d6405070240b03003114903200d4180d480082401c648981400100b060340c1c2c80d1010400002074061400d042480d08103002500209014900c08041c103c912665882d22900b015049080c280300b40d0342004041d0f41d4100841c2c0107900f403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 365632625 1250 365631375 365631401
    0xc09130807030f0201110d1415060d0902031c0507050c01050406050f030603030c0313090609050c091c02060301080a1401050903040e0703060b04060c03030b0a030b0105010f1107031113 81
    0x50003101c001c43d200e041c4500c4a10722600001031a401da100b1441a150029210207021b0707038481c5501140c02c815154001d0300903803400d80d60950304011718006400360140e182c04500007a80c880c10313403080d0f40e42003242e4140000800d03902d95038a0a0721000902c5a4803c110640d1244030340c1418030110752064040300d0484a40355101d9040500300840404141c1c409855130b0751510080c03000c1103801e90148000e22204a540c0b10355034041c0d1400c014201510315560000e1942c9152800304204c5042000468550007001c81c6d03043c1c41c420611f08524003070914036030f0194210601000116031440d0000f101060300d1300a64802c0c0c0240701c503a1000d03003a58022036144060ba0410b03c0b00300680d2510f110423039080794043c1004507a5a0311242d0010b80c980095000000042d5a00f0190040c1030700762141c415407000c10b0350710200b028219203654540720070600c24141040849840b400c0c23100c0c420010781d4504281c1c1c4c0c040d10045030392400c00d480c204000c032000700d100384860599240c2103085849076508034035074 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 365633875 1250 365632625 365632627
    0x1802060a0302070203071806030c060c0c0603240824100e04020d120207060e031b010815120c03120703020616051b0d030f0e0730050c091308 62
    0x51403011070180d080040202e03010300c81d207400416111120340c0c0100c81c0d1150b50000160151660500400445c03c1d64041ca0511817190402c82c0840c4030310600009460840c2000304112035440d100b030b50184403a1031001e1307040004150115150201042d44251101204041c102d45158840d1802d031102c0255a010445803c1a03410000c0003100d804042d07000e0300040c28107055441948078090004c02c0916400010b030019402449196088003025101000031341c0140107546094069524001194502c1414007205d000050561070088820700354260010745003120103100364035419500c415180b0058402c0c0581c0c440001100450300c151032170700d070b010340c01044c587c0c86020009032084202600c00040110801000302c1c901c07511440440c0c94070300c240041c1182e65082900400f210342c00a061501507040801e60b01116100050b1030050b03d10308000340743e451304034120909080c40302c50440c501601c074415040d01400404522101c030090152810482030752201c14104e5407050441c0000c0050784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 365635125 1250 365633875 365633887
    0x309060c05130515040b12061c0b150a080f010506040506011e0c11040212070215010f060e030709050405060403030501120819022a13020a050412031809050901180206 73
    0x2030207070f0700c60002c13402c51440940b4060303c2d8500680c4580c02035111504603803106042c024581400c0c4e440e900360160640a8a005c0c08196540107415407025180c1240d1542c8102c14003460381d10840c111005082e100c003142d08524860f04124081c044c216505489a0318081c00540554042d00005040491450702c0542d5400b4080d020303100035800b400c0954401c0301d00400e042e21600c6a100501d411301d0109411852450300c1580240390004600544080880f508010002e040e00c0226000668540f07040483c5618514404245000d1013640010304081c100014003090040104055000c0c500941e024400d50383c81d002c0d0220003064181000b00700c1a0204000503245220b07444020021580e4410780f00074100080b91100c8201d5404a18008441204459042881c01030410742d4902d29aa10039070920700c032881e014140740520721418a401c03c00003124001c145c81511500d0442101ca429110740c0d580f240302210041c901201c1d1800998038201c03d00110840d40418025225402802546031203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 365636375 1250 365635125 365635129
    0x60915161710030b0c030105090a110901110a050604140f0d05090f040912120b0f0f10020a0602030c040923010b0d0b090f041109070509101106070309060c051305 71
    0xc0000b8022460080848070210000d5148188a030181120400403034480d41000c1c10030906080241228511a242c50078501002c00f00e5419554000301c242418905003946108040c1048a0b0407402407041c01503204201c20001c240c4490f24101d4010b0b4111508041c84541040da207101c9003506030080b034010b00054820745001e03881c04680400150011980c000c960ba101c07812000a51885008100081c9110380c0201c0d0501c1400d8140c40201c6945030f4a218003800302e10101031200741036001d100f0004881070614000c00c02090b8059000c54215a00d01c0e081c6949041354100d405200401818407124615000c801d03510070100241031510044180d01e0a01d00700410343c007003000c8800c401e0310b42c40c0e40c000564502900d540300790a000042c01d11403500e4508645002c02040580384034201d0841400080750740700090301c07100601070f11418400d809030f00e41681d4031801140b004505200e024200010b055145d046060042d00c1083c0030711801c00360007410703240350207242880200c50351081006c01145c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 365637625 1250 365636375 365636417
    0x906050d0c03090f0b04030e01031a040203060d020310091b0311092814090303010e010905130606140a0b0a050a051303080a05120601031b180806091516 67
    0x54015060000f0302201a603100c0c00002080b281c00d880f40025141000181038004110a04620003481c00300804200c1000c1960072600a000b1540610790100014449031035030070312001010340080c100c03940490080354400c00b034803040d0000c4a0303a61200d031103512121400824181075950014042003d2443c410501082600041806185001d034240c0d20007280c40e060500d941602c00d044004c503020158524410b210240940001c03110b61040004200754845207107032074150368100c5404520341c1c030780d411758000c4504640c9026102c03902e0700d600011914003040000b640b400080e03c509920507a02c0315410024024408810302242d8200710700a49180b0480c010f0804081c42181d4000700b580fa40c683c0f4010303400a902c1d01010400002e0203000c000c1d03161880c668003030024a4144281c25103500101480a01070104805004000350602090b0b401190300308090020301c0304403920703450040301990752514030004120382000b0341c4001c078054400705e030540d2100300510f032524404603104110418403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 365638875 1250 365637625 365637641
    0x18010c0504120309051002011a1017070905030303190f06080d14042117040b0403080c010209090f1603052e0b0c031306180b0c010902040e010f0c0906050d 68
    0x4104c101c01c0003041e1a5510520000701a030241e00004031aa030041d0f030914003000d42951039114151404000c01001c1c0e04c2004041002c41c040c84407090707600c0e00301041d109100141c10080d0300d07020100808c4590100003c180910b100800021b018a40744041d50700c3c12100680100407140d003002d40e0560380203020f807103d800d4041c000d209884c80c0583c1c5a0006201c5241443c80400c0ca18141c0c14480034020000c440054114001100b1881e041c9089140c002d148680c0c4230042c8000d501050410603e03000b90f040e80c1180c00060900e0095141c412040c9505407070490351520035040313a408400e5001d03c03078840e81e8410400da8105000c01c00c05034000341180c10240600d850902603020012a15003c510302400d9000e4142000f59142c0810307010411010f07c40360009010481c8080c0042c02e050130300056041115260f240003551581c41020032030141c6518240070350010301740712154141c0c2405602c000d490070114081040175204039002255078900c14496200010720500c1003066444165101a40c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 365640125 1250 365638875 365638877
    0x111e0313021206010302030c01091d060a210b0c0414040e0a0c031b1a07020f0111030a08041a01061409031906020a120501060f260f18010c05041203 65
    0x1260603125070004200e0103800d01081c986402c0030004004500f020000c0301c50110b02400d28505180c1802d844807400d004400b90f5601c0b40409001190345511504401d00103061011035075149440c031a060f40c0c000850413201140c48100100019401d800403009480541c0c591181d01c41254080c4001c2002a0061034001840d502410751164009044100e9480080d80b01e078100402200448411038440881903001400ca120ba6a80211403000c12400b102e4210764100c0d20b60750000704050040f038840d145401005000d1000041003c0d4107030f04407010900c103074030a1802605100d034036130300280300c00702c20711445020440d40e0381d10401c5104801c01501d0707030300b402900b180c04042030759a40a24000200d071041c2caa065002400c903510315404048e50302000da0744034051180d540740c810014141400c9200c0601002101140f540510340b841d40d0154404c2c10303001e84003005081440c90100d80900544803009010550005000160418021051441c15585030b190601e8940030142620802c0394000314 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 365641375 1250 365640125 365640151
    0x1b0206090a170703121806080a0908040602010b03011b020303190209030106060e040b150d090602040b040303030b090f0f040605060402090405100906120206070809010216090906111e03 81
    0x4280b10701802c141018034200b51000f004183d00d9420100000e41c0d40407000713003c004241076031b500b00301c031020b17a810200c0d00c6900e8408141c1c5e682c2c0e00032070020040d60070010900390001800050b1964150040c04510100b10002c0000540c400c4502d1030544000c250800560010300c00a03140c4000240c0d50124900301200c050b1030180000b000900f10b800d5600840e0210368102c4800710141091700c10a2a079a0041c4d56820a00b00280524000d81c0580460303e4441500c032000e8904200054040d50300601413400b03020340b1241c581c900035025011003000140035414500001c0c0c220300c1c24010b1540a41d00403000d1601980b1640c451001518004021035040354080040300303c40d440700e120711445520707140140c002050a100c240c40035140d003984000019608040d1410141e41e48604850441c0d90103a940d55035100c1090050b800c0c072200d0250a1002d12000600003103140039604000149889968104010594061243e0740c500134012b01801843d2000300052601e04020001d40c2c02030300d80380d095 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 365642625 1250 365641375 365641379
    0x4050f030a081e040302060a050601110a0b0103020415060f120b030303040c1a1c05100f08010507090608070219031413080d030903020613020d0b04050610061b0206090a 74
    0x1151640d8041c01c84040021801002c000c9000504001103201c548402c808000c0c2d4181031710002e540f52000342000e60301a581382c0106146a000e030b000c0764010010070f000e42e0420407175818080c0c1d00701c03c24402130340901c0c10403841c25031402a000c0c500c03044d2411a01c0d81e8080c0c2110f41d0044075000840911020103941d03481d01d541842d41c013000510302c95881900c80d000403504040000382081c6058808121601c41808100015207504034148840642d000c00043c0d29650204108080a8507030301c6003800f0001040e0106520790107421180c401e90b20740d150285040d554410407907800c1030440d41d80c401030f006500d04031030320710741050b100315802d0103498400d031200b1a450002c8200d03841010401e119401d64041042010428441c0d9856010380d81030070444d011a68501940300c02000300b2040341d81404280c84806c5640e10720000c69110703080041d0301e001780341610b17040340d0b114020354120140520a00c1d0009030341e4070503060046010040e500d5078500c500e503503082c8410340e08261500d540c00801d0b4400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 365643875 1250 365642625 365642653
    0x15170307060f0b2407081309090302030d18020f01050c120307050a09050a060507240203100503060f04051e010609020a020c0a0605090a050d02010203190f020f0f0c06030405 76
    0x900d800c4600c07100c0380003810f28100d00030000c0c0e0180e409118142c0c850f1001850745442c82d400103603003e440e00610801d54031041c00b812801a291b554001801203440c00c4018800e055001028141000b070201c400c00c0305a040346822408100c1c000c9000b948141d464610003019440341d40907003a80e030b801d5821503411003000ca0f047d04164004442030400030f0004200074400b903900440400c000c0c82c5c00e44000d420705041c001e00600794455400d000c1d151350080001c0d503030480c07070b0340041d0441103000c51400c40d1030742071a5000c008811124400c00703100303201e010086060248070042c12030017164480c00900100c00b40c45050784120a81c40c80d410100c1d507a074030000950070000c0c0010440350141c0c0e40a01400c141c00e80800070000e030f09401500030014280049100c0b500d440006a01b80c07071044841c288a0040743c80103e1841c407034140e0540c81e80c40804020760545d42c100800440502da1234003a82da989101000f00c40d5503204030000406954082851055241041d1000b150490700900540b20307803441401e4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 365645125 1250 365643875 365643881
    0x109050a0302030a0f1827020d02090a0803120414070513050f01080a0f0303020331020406140616020303040f060809010605121c05092706041517030706 67
    0xe01940075800c00101ca080840d4022550b41c02c080040c00e1059514030004d4400c140b91115000d0070406101c00740000c0f5000301204210500545000310540d0780780c0c01d24540c0e0001c0d402190304103000340325030383e00803809800c04000d40302e2260b043d00701d5054070781e50703603d45005c1c0d0700007005018540d001d00c2c50040740c0b5440d08407154004d00c4d403181d0b003c00c0c60b05024501c4e165000c416884043c0d0350300004150300000701480038a007005071b003520b00980c481c0c03100d440d02d1040c403038048800103c1c81c843c0002e0049010341c4241d14001e80c1e0007214100001559503801800b00459260155407100303040004000c01015640d0000b4800d0024049900781911040b2602401c81c860300701c0380109403d10100701803200d090080340c0c040c5c82c00b503c9103a00e40c50201e0b5055500c2e41c3c1c01071603151100042803040c0d8064800c10071354188500007001c83e00c9030404000103070500c0406209651225044e00c0014580303080070300413018401c40038000c00301c00600c1c101110058801c007044404880c0002c11091002c035060740 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 365646375 1250 365645125 365645143
    0xf031509020a0203270d0f05010b0a08011a01020c3105100312020a0c0e07030902060f090913050c060f271f0509040c1e03090b0a0612020f03010905 65
    0x28000b1a6140c81c102c01895030a46105000202980c40034121741e00e580358040c840c1041a400000d400141c0942d16040c1e002d0b007030200701d046d0001102d52000699a005420032442e5000480c2c414500140c8040126250030507510303046d801c0700014060402a90001c14030104001c00e2442c2c6500d5501c01e10301510030784405403605030b09880c0c1900e0500074060012401000e181046c00108442c0c5c0c840d9440c020510094070403400040d020a0000364010301980000c3c4001c0c5d801082030340d80b048981ea802c041a00248035550254100100040406500e84040c1d80a41e410800400e580c041403c1084003550011107408001c11080c44100007902c8240d004d000c01d2545200280c0e10b150101080c8408401f0308001903400410503401c107900c0c107800904454000105890205091914002c251440e410b0000c240c10281d03038140740200c2095066100140c82d5200e030754030705819202c94943c181074400318060010400c0184034042c0040c500040016524180900080741a80241d194203080044403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 365647482 1107 365646375 365646377
    0xb010b03060f060306030c1003060602010608160b090a0324050a020921030f04080601080c03030a050301090c11100506190f03020907230c07150f031509020a 69
    0x107000443c00340c1f8018080c100003030703451500140204100d00c550401546400c20105449002090601c3e4580b42038080141c0241020341c2c1052607400388044503402150a000040001c0e06e422800580c60480e518095940319401a01026640e0003031504515900c100312100127075441d101c00c0f0310b2a850340015070224981c0c02e00074074554401d60707803007280a000110f00020f00c04d100085081c16143d000c01501c6c002c400d0081070540e280121076003000410002d0005004a40d8280d201d66800183d070b00d000503030841000529800c02040c014a11506622001003000d83e00304160000482c40c15445106002458a84e0100c0340780a18000248540459400308032201c0c814141c0110040601c401034000080c0250300041c10b50040c5031040d15801010341c00980303441d5030802040c02c506182c035030a0070300030884000c80c003c10340150381c01840c0701003103400b19000c0000e1000c2d000c18912 = true := by decide +kernel

theorem cover : BRFrame.Cov 365467625 365647482 := by
  have h0 := BRFrame.cov_init 365467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 365467625 ≤ n) (h2 : n < 365647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
